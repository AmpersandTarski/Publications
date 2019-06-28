theory EventStructures
  imports Main
begin

locale dependencies =
  (* dep_list representeert de afhankelijkheid tussen resultaat (bijv "3+4") en zijn argumenten ("3" en "4")
     door "3+4" af te beelden op "3" en "4".
  *)
  fixes "dep_list" :: "'e \<rightharpoonup> 'e list"
begin           
definition events :: "'e set" where
  "events = dom dep_list"

  (* preorder representeert de tijdsvolgorde   *)
definition preorder :: "( 'e \<times> 'e ) set" where
  "preorder \<equiv> {(e\<^sub>1,e\<^sub>2) | e\<^sub>1 e\<^sub>2 l.
                  e\<^sub>2 \<in> events \<and> dep_list e\<^sub>1 = Some l \<and> List.member l e\<^sub>2 \<and> e\<^sub>2 \<noteq> e\<^sub>1}"

definition event_order :: "( 'e \<times> 'e ) set" where
  "event_order \<equiv> preorder\<^sup>+"
definition cycle_free where
  "cycle_free \<longleftrightarrow> irrefl event_order"

(* This lemma says that preorder is a directed graph, in which events is the set of vertices. *)
lemma preorder_digraph:
  "Domain (preorder) \<subseteq> events"
  "Range (preorder) \<subseteq> events"
  unfolding events_def preorder_def by auto

(* This lemma says that event_order is a directed graph, in which events is the set of vertices. *)
lemma event_order_digraph:
  "Domain (event_order) \<subseteq> events"
  "Range (event_order) \<subseteq> events"
  by (auto simp add: event_order_def preorder_digraph)

definition minima :: "( 'e \<times> 'e ) set \<Rightarrow> 'e set"  where
  "minima evs \<equiv> {e\<^sub>2 | e\<^sub>1 e\<^sub>2 e\<^sub>3. (e\<^sub>1,e\<^sub>2) \<notin> evs \<and> (e\<^sub>2,e\<^sub>3) \<in> evs}"

definition maxima :: "( 'e \<times> 'e ) set \<Rightarrow> 'e set"  where
  "maxima evs \<equiv> {e\<^sub>2 | e\<^sub>1 e\<^sub>2 e\<^sub>3. (e\<^sub>1,e\<^sub>2) \<in> evs \<and> (e\<^sub>2,e\<^sub>3) \<notin> evs}"

definition is_minimum :: " 'e set \<Rightarrow> 'e \<Rightarrow> bool" where
   "is_minimum E e \<equiv> e\<in>E \<and> (\<forall> e\<^sub>1\<in>E. (e\<^sub>1,e) \<notin> event_order)"

definition is_maximum :: " 'e set \<Rightarrow> 'e \<Rightarrow> bool" where
   "is_maximum E e \<equiv> e\<in>E \<and> (\<forall> e\<^sub>1\<in>E. (e,e\<^sub>1) \<notin> event_order)"

(* To substitute a set of events by a single event may compromise the integrity of the time structure.
This means that the resulting time structure must be cycle free.
We call a set of events "atomic" if that set can be substituted by a single event safely,
i.e. without introducing cycles in the time structure.
First we must define this substitution within event_order.
Then we must show that substituting the subgraph consisting of events E can indeed be substituted
by one event such that no new cycles are introduced in the resulting time structure.
*)
definition atomic :: "'e set \<Rightarrow> bool" where
  "atomic E \<equiv> \<forall> ext \<in> events - E. \<forall> i\<^sub>1 \<in> E. \<forall> i\<^sub>2 \<in> E.
    (ext, i\<^sub>1) \<notin> event_order \<or> (i\<^sub>2, ext) \<notin> event_order"

lemma atomic:
  shows "atomic E \<longleftrightarrow> event_order `` E \<inter> event_order\<inverse> `` E \<subseteq> E"
proof
  assume ev:"event_order `` E \<inter> event_order\<inverse> `` E \<subseteq> E"
  thus "atomic E" using atomic_def by auto next
  assume at:"atomic E"
  { fix ext
    assume ext:"ext \<in> event_order `` E \<inter> event_order\<inverse> `` E"
    then obtain i\<^sub>1 where i1:"(ext, i\<^sub>1) \<in> event_order" "i\<^sub>1 \<in> E" by auto
    obtain i\<^sub>2 where i2:"(i\<^sub>2,ext) \<in> event_order" "i\<^sub>2 \<in> E" using ext by auto
    have ext_E:"ext \<notin> events - E" using at atomic_def i1 i2 by blast
    with event_order_digraph i1 have "ext \<in> E" by auto
  }
  thus "event_order `` E \<inter> event_order\<inverse> `` E \<subseteq> E" by auto
qed

lemma singleton_atomic:
  "(\<forall> e \<in> events. atomic {e}) \<longleftrightarrow> well_formed"
proof
  have pr:"(e,e) \<notin> preorder" for e using preorder_def by auto
  assume "\<forall>e\<in>events. atomic {e}"
  hence "\<And> e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>2) \<in> event_order \<Longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> event_order \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
    using atomic_def atomic by blast
  hence "\<And> e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>2) \<in> event_order \<Longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> event_order \<Longrightarrow> False"
    by (metis event_order_def pr converse_tranclE trancl.r_into_trancl)
  thus well_formed unfolding well_formed_def irrefl_def by blast
next
  assume "well_formed"
  hence "\<And> e. atomic {e}"
    unfolding atomic well_formed_def event_order_def
    using irrefl_def trancl_trans by force
  thus "\<forall> e \<in> events. atomic {e}" by blast
qed


end

locale ordered_events =
  fixes "dependencies" :: "'h \<Rightarrow> ( 'e \<rightharpoonup> 'e list )"
begin
abbreviation events
  where "events h \<equiv> dependencies.events (dependencies h)"
abbreviation event_order
  where "event_order h \<equiv> dependencies.event_order (dependencies h)"
abbreviation well_formed
  where "well_formed h \<equiv> dependencies.well_formed (dependencies h)"
definition less_h where
  "less_h h\<^sub>1 h\<^sub>2 \<longleftrightarrow> (events h\<^sub>1 \<subseteq> events h\<^sub>2) \<and> ((event_order h\<^sub>1)\<^sup>+ \<subseteq> (event_order h\<^sub>2)\<^sup>+)"
end

locale timed_system = ordered_events +
  fixes "history" :: "'t::order \<Rightarrow> 'a"
  assumes "t\<^sub>1 \<le> t\<^sub>2 \<Longrightarrow> less_h (history t\<^sub>1) (history t\<^sub>2)"
    and "well_formed (history t)"
begin

definition durable_set where
  "durable_set E \<equiv>
    \<forall> e \<in> E. \<exists> s. \<forall> t. (dependencies t e = Some s \<and> set s \<subseteq> E)
                      \<or> dependencies t e = None"

lemma durable_set_union [intro]:
  assumes "Ball S durable_set"
  shows "durable_set (\<Union> S)"
  unfolding durable_set_def
proof(standard)
  fix e assume "e \<in> \<Union> S"
  then obtain s where es:"s \<in> S" "e \<in> s" by blast
  with assms have "durable_set s" by auto
  then obtain lst where "\<forall>t. dependencies t e = Some lst \<and> set lst \<subseteq> s \<or>
                 dependencies t e = None"
    unfolding durable_set_def using es(2) by auto
  hence "\<forall>t. dependencies t e = Some lst \<and> set lst \<subseteq> \<Union> S \<or>
            dependencies t e = None"
    using subset_trans[OF _ Union_upper[OF es(1)]] by metis
  thus "\<exists>s. \<forall>t. dependencies t e = Some s \<and> set s \<subseteq> \<Union> S \<or>
                dependencies t e = None" by blast
qed

lemma durable_set_collect [intro]:
  shows "durable_set (\<Union> (Collect durable_set))"
  by auto

definition durable where
  "durable e \<equiv> \<exists> E. e \<in> E \<and> durable_set E"

lemma durable_collect:
  "durable e \<longleftrightarrow> e \<in> \<Union> (Collect durable_set)"
  "Ball (set s) durable \<longleftrightarrow> set s \<subseteq> \<Union> (Collect durable_set)"
  unfolding durable_def by auto

lemma durable:
  "durable e =
    (\<exists> s. \<forall> t. (dependencies t e = Some s \<and> (Ball (set s) durable))
              \<or> dependencies t e = None)" (is "_ = (\<exists> s. \<forall> t. ?rhs s t)")
proof
  assume "durable e"
  then obtain E where E:"e \<in> E" "durable_set E" using durable_def by blast
  then obtain s where "\<And> t. (dependencies t e = Some s \<and> set s \<subseteq> E)
                             \<or> dependencies t e = None"
    unfolding durable_set_def by blast
  hence "?rhs s t" for t using E(2) durable_def subsetD by metis
  thus "(\<exists> s. \<forall> t. ?rhs s t)" by blast next
  assume as:"(\<exists> s. \<forall> t. ?rhs s t)"
  hence "\<exists>s. \<forall>t. dependencies t e = Some s \<and>
            set s \<subseteq> \<Union> (Collect durable_set) \<or>
            dependencies t e = None" unfolding durable_collect.
  have "durable_set (insert e (\<Union> (Collect durable_set)))"
    unfolding durable_set_def[of "insert _ _"] ball_simps
  proof
    show "\<exists>s. \<forall>t. dependencies t e = Some s \<and>
            set s \<subseteq> insert e (\<Union> (Collect durable_set)) \<or>
            dependencies t e = None" using as unfolding durable_collect
      by (metis (no_types, lifting) DiffI Diff_eq_empty_iff empty_iff insert_absorb subset_insert_iff)
    show "\<forall>ea\<in>\<Union> (Collect durable_set).
       \<exists>s. \<forall>t. dependencies t ea = Some s \<and>
               set s \<subseteq> insert e (\<Union> (Collect durable_set)) \<or>
               dependencies t ea = None"
      using durable_set_collect unfolding durable_set_def[of "Union _"]
      using subset_insertI2[of "set _" "\<Union> (Collect durable_set)" e]
      by metis
  qed
  hence "e \<in> \<Union> (Collect durable_set)" by auto
  thus "durable e" unfolding durable_collect.
qed

end

(* Als er locaties zijn:
  Robust = locaties mogen uit de lucht gaan zonder dat er functionele eigenschappen veranderen
  Natural = 
*)
locale invalid_actions =
  fixes "apply" :: "'a \<Rightarrow> 's \<Rightarrow> 's"
    and "inverse" :: "'a \<Rightarrow> 'a"
  assumes
    inverse: "apply (inverse a) (apply a s) = s"
    and
    idempotent: "apply a (apply a s) = apply a s"
begin
lemma one_action: "apply a = (\<lambda> x. x)"
proof fix s
  have "apply a s = apply (inverse a) (apply a (apply a s))"
    by (fact inverse[symmetric])
  also have "\<dots> = apply (inverse a) (apply a s)"
    unfolding idempotent by (fact refl)
  also have "\<dots> = s" by (fact inverse)
  finally show "apply a s = s".
qed
end

locale actions = 
  fixes "apply" :: "'a::monoid_add \<Rightarrow> 's \<Rightarrow> 's" 
  assumes compose: "apply b (apply a s) = apply (a + b) s"
      and universality: "\<And> s. \<exists> b s'. apply b s' = s" (* typically provable using 'apply 0' *)
begin

lemma compose_o[simp]:
  "apply a o apply b = apply (b + a)"
  unfolding o_def compose by auto

lemma apply_zero_exists[simp]:
  "apply 0 = (\<lambda> s. s)"
proof
  fix s::'s
  obtain b s' where ap:"apply b s' = s" using universality by blast
  hence "apply 0 (apply b s') = s" unfolding compose by auto
  thus "apply 0 s = s" unfolding ap.
qed

lemma apply_zero_ident_fcomp:
  "apply a o apply 0 = apply a"
  "apply 0 o apply a = apply a"
  by auto
end


locale actions_apply = 
  fixes "apply" :: "'a::monoid_add \<Rightarrow> 's \<Rightarrow> 's" 
  assumes compose: "apply b (apply a s) = apply (a + b) s"
      and universality: "\<And> s. \<exists> b s'. apply b s' = s" (* typically provable using 'apply 0' *)
begin

lemma compose_o[simp]:
  "apply a o apply b = apply (b + a)"
  unfolding o_def compose by auto

lemma apply_zero_exists[simp]:
  "apply 0 = (\<lambda> s. s)"
proof
  fix s::'s
  obtain b s' where ap:"apply b s' = s" using universality by blast
  hence "apply 0 (apply b s') = s" unfolding compose by auto
  thus "apply 0 s = s" unfolding ap.
qed

lemma apply_zero_ident_fcomp:
  "apply a o apply 0 = apply a"
  "apply 0 o apply a = apply a"
  by auto
end

(* Not transitive and therefore not an equivalence *)
fun eq_if_defined (infix "=\<^sub>s" 50) where
  "None =\<^sub>s _ = True"  |
  "Some _ =\<^sub>s None = True"  |
  "Some a =\<^sub>s Some b = ((a::'s) = b)"

locale actions_wrong =
  fixes "apply" :: "'a \<Rightarrow> 's \<Rightarrow> 's"
    and "compose" :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and "merge" :: "'a \<times> 'a \<Rightarrow> 'a \<times> 'a"
    and "inverse" :: "'a \<Rightarrow> 'a"
  assumes
    compose: "apply (compose a b) s = apply a (apply b s)"
    and
    merge: "apply (fst (merge (a, b))) (apply a s) =
            apply (snd (merge (a, b))) (apply b s)"
    and
    inverse: "apply (inverse a) (apply a s) = s"
    and
    idempotent: "apply a (apply a s) = apply a s"
begin
end


fun historic_structure where
  "historic_structure (E,prec)
  = ((prec \<subseteq> E \<times> E)
  \<and> finite E
  \<and> asym (trancl prec))"

lemmas hi = historic_structure.simps

fun occur where
  "occur P e (E,prec)
  = (insert e E,prec \<union> (P \<times> {e}))"

lemma asym_simp:
  "asym x \<longleftrightarrow> (\<forall> (a, b) \<in> x. (b,a) \<notin> x)"
  unfolding asym.simps irrefl_def by auto

lemma historic_structureI[intro]:
  "(prec \<subseteq> E \<times> E)
  \<Longrightarrow> finite E
  \<Longrightarrow> asym (trancl prec)
  \<Longrightarrow> historic_structure (E,prec)"
  by auto

lemma historic_structureE[elim]:
"historic_structure H \<Longrightarrow> 
 (finite (snd H) \<Longrightarrow>
  finite (fst H) \<Longrightarrow>
  (snd H) \<subseteq> (fst H) \<times> (fst H) \<Longrightarrow>
  asym ((snd H)\<^sup>+) \<Longrightarrow>
  (\<And> a b. (a, a) \<in> (snd H) \<Longrightarrow> False) \<Longrightarrow> P) \<Longrightarrow> P"
  apply (cases H, simp add:asym_simp finite_SigmaI[THEN rev_finite_subset])
  by (metis case_prodD r_into_trancl')

lemma trancl_asym:
  assumes "asym (b\<^sup>+)"
    "e \<notin> fst ` b" "e \<notin> P"
  shows "asym ((b \<union> P \<times> {e})\<^sup>+)"
proof(rule ccontr)
  assume "\<not> asym ((b \<union> P \<times> {e})\<^sup>+)"
  then obtain x1 x2 
    where a:"(x1,x2) \<in> (b \<union> P \<times> {e})\<^sup>+"
      and b:"(x2,x1) \<in> (b \<union> P \<times> {e})\<^sup>+"
    unfolding asym_simp by auto
  have inb:"x2 \<noteq> e \<longrightarrow> (x1,x2) \<in> b\<^sup>+"
  proof(rule trancl.induct[OF a],goal_cases)
    case (2 x y z)
    thus ?case using assms(2-) by (auto simp:image_def)
  qed auto
  have ina:"x1 \<noteq> e \<longrightarrow> (x2,x1) \<in> b\<^sup>+"
  proof(rule trancl.induct[OF b],goal_cases)
    case (2 x y z)
    thus ?case using assms(2-) by (auto simp:image_def)
  qed auto
  have "x2 \<in> Domain ((b \<union> P \<times> {e})\<^sup>+)"
       "x1 \<in> Domain ((b \<union> P \<times> {e})\<^sup>+)"
    using a b unfolding Domain_fst by force+
  from this[unfolded trancl_domain]
  have "x2 \<noteq> e" "x1 \<noteq> e" using assms(2,3)
    by (auto simp:image_def)
  hence "\<not> asym (b\<^sup>+)"
    unfolding asym_simp using inb ina by auto
  thus False using assms(1) by metis
qed

lemma occur_preserves_hs:
  assumes "historic_structure H" "P \<subseteq> fst H" "e \<notin> fst H"
  shows "historic_structure (occur P e H)"
  using assms by(cases H,auto intro!:trancl_asym)

end