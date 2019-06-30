theory EventStructures
  imports Main
begin


abbreviation evs :: "( 'e \<times> 'e ) set \<Rightarrow> 'e set" where
  "evs order \<equiv> Domain order \<union> Range order"

(* The order of events in real time is always a cycle-free partial order.
An information system must maintain the integrity of its time structure.
So it must ensure that every change of this structure results in a cycle-free partial order.
*)
abbreviation cycle_free :: "( 'e \<times> 'e ) set \<Rightarrow> bool" where
  "cycle_free order \<equiv> irrefl (order\<^sup>+)"


fun minima :: "( 'e \<times> 'e ) set \<Rightarrow> 'e set"  where
  "minima order = {e\<^sub>2 | e\<^sub>1 e\<^sub>2 e\<^sub>3. (e\<^sub>1,e\<^sub>2) \<notin> order \<and> (e\<^sub>2,e\<^sub>3) \<in> order}"

fun maxima :: "( 'e \<times> 'e ) set \<Rightarrow> 'e set"  where
  "maxima order = {e\<^sub>2 | e\<^sub>1 e\<^sub>2 e\<^sub>3. (e\<^sub>1,e\<^sub>2) \<in> order \<and> (e\<^sub>2,e\<^sub>3) \<notin> order}"

definition is_minimum :: "'e set \<Rightarrow> 'e \<Rightarrow> ( 'e \<times> 'e ) set \<Rightarrow> bool" where
   "is_minimum E e order \<equiv> e\<in>E \<and> (\<forall> e\<^sub>1\<in>E. (e\<^sub>1,e) \<notin> order)"

definition is_maximum :: "'e set \<Rightarrow> 'e \<Rightarrow> ( 'e \<times> 'e ) set \<Rightarrow> bool" where
   "is_maximum E e order \<equiv> e\<in>E \<and> (\<forall> e\<^sub>1\<in>E. (e,e\<^sub>1) \<notin> order)"

(* Atomicity is about substituting a set of events by one event .
So before we define the property atomic, let us define what we mean by
substituting a set of events E by one event e in a time structure "order":
*)
definition atomize :: "'e set \<Rightarrow> 'e \<Rightarrow> ( 'e \<times> 'e ) set \<Rightarrow> ( 'e \<times> 'e ) set" where
  "atomize E e order \<equiv> { ( if e\<^sub>1\<in>E then e else e\<^sub>1 , if e\<^sub>2\<in>E then e else e\<^sub>2 )
                       | e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>2) \<in> order \<and> (e\<^sub>1\<notin>E \<or> e\<^sub>2\<notin>E)}"

lemma atomize_pair_e:
  assumes "e \<notin> evs order - E"
  shows "(a,e) \<in> atomize E e order \<Longrightarrow> \<exists> i \<in> E. (a,i) \<in> order"
    and "(e,a) \<in> atomize E e order \<Longrightarrow> \<exists> i \<in> E. (i,a) \<in> order"
  using assms unfolding atomize_def
  by (auto split:if_splits)

lemma atomize_pair_not_e:
  assumes "a \<noteq> e" "b \<noteq> e"
  shows "(a,b) \<in> atomize E e order \<Longrightarrow> (a,b) \<in> order"
  using assms unfolding atomize_def by auto

lemma atomize_paths:
  assumes "e \<notin> evs order - E" "(a,b) \<in> (atomize E e order)\<^sup>+ " "(a,b) \<notin> order\<^sup>+"
    "a \<noteq> e" "b \<noteq> e"
  shows "(a,e) \<in> (atomize E e order)\<^sup>+ \<and> (\<exists> i \<in> E. (i,b) \<in> order\<^sup>+)"
  using assms(2)[unfolded trancl_power]
proof(rule exE)
  fix n::nat assume "0<n \<and> (a, b) \<in> atomize E e order ^^ n"
  thus ?thesis using assms(3-) proof(induct n arbitrary:b)
    case (Suc n)
    then obtain c where c:"(a, c) \<in> atomize E e order ^^ n" "(c,b) \<in> atomize E e order" by auto
    { assume "n = 0" hence ac:"a = c" using c by auto
      with Suc.prems(3,4) c(2) have "(c,b) \<in> order" unfolding atomize_def by auto
      hence False using ac Suc.prems by blast
    }
    hence ind1:"n > 0 \<and> (a, c) \<in> atomize E e order ^^ n" using c(1) by auto
    show ?case proof(cases "c = e")
      case True
      have "((a, e) \<in> (atomize E e order)\<^sup>+) \<and> (\<exists>i\<in>E. (i, b) \<in> order\<^sup>+)" 
        using c atomize_pair_e(2)[OF assms(1)] unfolding True
        by (meson ind1 trancl.r_into_trancl trancl_power)
      then show ?thesis using assms(1,4) by blast
    next
      case False
      { assume "(a,c) \<in> order\<^sup>+"
        with atomize_pair_not_e[OF False Suc(5) c(2)]
        have "(a,b) \<in> order\<^sup>+" by auto
        hence False using Suc by blast
      }
      hence ind2:"(a, c) \<notin> order\<^sup>+" by auto
      from Suc(1)[OF ind1 ind2 Suc(4) False]
           atomize_pair_not_e[OF False Suc(5) c(2)]
      show ?thesis
        by (meson trancl.trancl_into_trancl)
    qed
  qed auto
qed

lemma atomize_path_e:
  assumes "e \<notin> evs order - E" "a \<noteq> e" "(a,e) \<in> (atomize E e order)\<^sup>+"
  shows "\<exists> i \<in> E. (a,i) \<in> order\<^sup>+"
  using assms(3)[unfolded trancl_power]
proof(rule exE)
  fix n::nat assume "0<n \<and> (a, e) \<in> atomize E e order ^^ n"
  thus ?thesis using assms(2) proof(induct n arbitrary:a)
    case (Suc n) note ind = this
    with ind(2) obtain c where c:"(a, c) \<in> atomize E e order" "(c,e) \<in> atomize E e order ^^ n"
      by (meson relpow_Suc_D2)
    show ?case proof(cases "c = e")
      case True
      show ?thesis using atomize_pair_e(1)[OF assms(1) c(1)[unfolded True]] by auto
    next
      case False
      hence "n > 0" using c(2) by (cases "n=0", auto)
      hence "0 < n \<and> (c, e) \<in> atomize E e order ^^ n" using c by auto
      from ind(1)[OF this False] atomize_pair_not_e[OF ind(3) False c(1)] show ?thesis
        by (meson trancl_into_trancl2)
    qed
  qed auto
qed

(*
We call a set of events "atomic" if that set can be substituted by a single event,
while preserving the integrity of the time structure.
In other words: the substitution may not introduce cycles and must preserve the order of events.
So how do we know that substitution of set E by a single event introduces no new cycles?
Assume there is a path from an event in E and to another event in E, which visits an event
outside of E. Then that path will show up as a cycle in the substituted graph.
Note that (x,y)\<in>order\<^sup>+ implies a path from x to y.
*)
definition atomic_order :: "'e set \<Rightarrow> ( 'e \<times> 'e ) set \<Rightarrow> bool" where
  "atomic_order E order \<equiv> 
                    (\<forall> ext. \<forall> i\<^sub>1 \<in> E. \<forall> i\<^sub>2 \<in> E.
                    ((ext, i\<^sub>1) \<in> order \<and> (i\<^sub>2, ext) \<in> order) \<longrightarrow> ext \<in> E)"

(* An easy test of atomicity is to compute "order `` E \<inter> order\<inverse> `` E \<subseteq> E".
Which we must prove, of course...
*)
lemma atomic_order:
  assumes "trans order"
  shows "atomic_order E order \<longleftrightarrow> order `` E \<inter> order\<inverse> `` E \<subseteq> E"
proof
  assume ev:"order `` E \<inter> order\<inverse> `` E \<subseteq> E"
  thus "atomic_order E order" using atomic_order_def assms by blast next
  assume at:"atomic_order E order"
  { fix ext
    assume ext:"ext \<in> order `` E \<inter> order\<inverse> `` E"
    then obtain i\<^sub>1 where i1:"(ext, i\<^sub>1) \<in> order" "i\<^sub>1 \<in> E" by auto
    obtain i\<^sub>2 where i2:"(i\<^sub>2,ext) \<in> order" "i\<^sub>2 \<in> E" using ext by auto
    have ext_E:"ext \<in> E" using at atomic_order_def i1 i2 by metis
  }
  thus "order `` E \<inter> order\<inverse> `` E \<subseteq> E" by auto
qed

(* We would expect the time structure to be cycle-free at all times.
So function "atomize" may assume the argument "order" to be free of cycles.
To prevent new cycles, we require order to be atomic as well.
Also, e must be a new event, i.e. an element of evs order.
A counterexample is: atomize {e\<^sub>2} e\<^sub>1 {(e\<^sub>2, e\<^sub>1)}, which clearly yields a cycle.

Now we must prove that the result, atomize E e order, is cycle free as well.
*)
lemma preserveAtomic :
  assumes trans:"trans order"
   and atomic:"atomic_order E order"
   and e:"e  \<notin>  evs order - E"
  shows "cycle_free order \<Longrightarrow> cycle_free (atomize E e order)"
proof(standard,standard)
  note tran: trancl_id[OF trans]
  from e have e':"e \<in> evs order \<Longrightarrow> e \<in> evs order \<inter> E" by blast
  let ?at = "atomize E e order"
  fix a
  assume cf:"cycle_free order" and aa: "(a, a) \<in> ?at\<^sup>+"
  note * = assms this
  from cf have aao:"(a, a) \<notin> order\<^sup>+" unfolding irrefl_def by auto
  from cf have cf_e:
    "(e,c) \<in> order \<Longrightarrow> e \<in> E"
    "(c,e) \<in> order \<Longrightarrow> e \<in> E" for c using cf e unfolding irrefl_def by auto
  show False proof(cases "a \<in> E")
    case True
    then show ?thesis sorry
  next
    case False
    { assume "a = e"
      with False e have "a \<notin> evs order" by auto
      hence False using aa by auto
    }
    with aa e have not_e:"a \<noteq> e" unfolding atomize_def apply auto try sorry
    from atomize_path_e[OF e not_e] atomize_paths[OF e aa aao not_e not_e]
    have "\<exists>i\<in>E. (a, i) \<in> order\<^sup>+" "\<exists>i\<in>E. (i, a) \<in> order\<^sup>+" by auto
    thus False using atomic unfolding atomic_order_def
      using False tran by blast
  qed
  obtain b where b:"(a, b) \<in> ?at" "(b,a) \<in> ?at\<^sup>+" by blast
  have "b\<noteq>a" using cf b(1) cf_e unfolding atomize_def irrefl_def by (auto split:if_splits)
 
  show "False" using * sorry
qed



locale dependencies =
  (* dep_list representeert de afhankelijkheid tussen resultaat (bijv "3+4") en zijn argumenten ("3" en "4")
     door "3+4" af te beelden op "3" en "4".
  *)
  fixes "dep_list" :: "'e \<rightharpoonup> 'e list"
begin           
definition events :: "'e set" where
  "events = dom dep_list"

(* preorder represents the time structure.
    (e\<^sub>1,e\<^sub>2)\<in>preorder\<^sup>+ means that e\<^sub>1 has happened before e\<^sub>2.
*)
definition preorder :: "( 'e \<times> 'e ) set" where
  "preorder \<equiv> {(e\<^sub>1,e\<^sub>2) | e\<^sub>1 e\<^sub>2 l.
                  e\<^sub>1 \<in> events \<and> dep_list e\<^sub>2 = Some l \<and> List.member l e\<^sub>1 \<and> e\<^sub>2 \<noteq> e\<^sub>1}"

definition event_order :: "( 'e \<times> 'e ) set" where
  "event_order \<equiv> preorder\<^sup>+"

lemma event_order_trans: "trans event_order" unfolding event_order_def by auto

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

lemma evs_events :
 "evs event_order \<subseteq> events" using event_order_digraph by auto
(* not equal: choose dep_list such that it yields Some [].
   This gives a set of events but no ordered pairs *)

definition atomic :: "'e set \<Rightarrow> bool" where
  "atomic E \<equiv> (\<forall> ext \<in> events - E. \<forall> i\<^sub>1 \<in> E. \<forall> i\<^sub>2 \<in> E.
                 \<not>((ext, i\<^sub>1) \<in> event_order \<and> (i\<^sub>2, ext) \<in> event_order))"


lemma atomic_atomic_order:
  shows "atomic_order E event_order = atomic E"
proof
  show "atomic_order E event_order \<Longrightarrow> atomic E" unfolding atomic_order_def atomic_def by auto
  assume "atomic E"
  thus "atomic_order E event_order" unfolding atomic_order_def atomic_def
    using event_order_digraph 
    by (meson DiffD2 DiffI Domain.DomainI subsetD)
qed

lemma atomic:
  shows "atomic E \<longleftrightarrow> event_order `` E \<inter> event_order\<inverse> `` E \<subseteq> E"
  using atomic_order[OF event_order_trans,of E] atomic_atomic_order by auto

lemma singleton_atomic:
  "(\<forall> e \<in> events. atomic {e}) \<longleftrightarrow> cycle_free preorder"
proof
  have pr:"(e,e) \<notin> preorder" for e using preorder_def by auto
  assume "\<forall>e\<in>events. atomic {e}"
  hence "\<And> e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>2) \<in> event_order \<Longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> event_order \<Longrightarrow> e\<^sub>1 = e\<^sub>2"
    using atomic_def atomic by blast
  hence "\<And> e\<^sub>1 e\<^sub>2. (e\<^sub>1,e\<^sub>2) \<in> event_order \<Longrightarrow> (e\<^sub>2,e\<^sub>1) \<in> event_order \<Longrightarrow> False"
    by (metis event_order_def pr converse_tranclE trancl.r_into_trancl)
  thus "cycle_free preorder" unfolding irrefl_def event_order_def by auto
next
  assume "cycle_free preorder"
  hence "\<And> e. atomic {e}"
    unfolding atomic event_order_def
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
  where "well_formed h \<equiv> cycle_free (event_order h)"
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