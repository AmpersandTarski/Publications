theory EventStructures
  imports Main
begin

fun historic_structure where
  "historic_structure (E,prec)
  = ((prec \<subseteq> E \<times> E)
  \<and> finite E
  \<and> asym (trancl prec))"

fun occur where
  "occur P e (E,prec)
  = (insert e E,prec \<union> (P \<times> {e}))"

lemma asym_simp:
  "asym x \<longleftrightarrow> (\<forall> (a, b) \<in> x. (b,a) \<notin> x)"
  unfolding asym.simps irrefl_def by auto

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
  assumes "historic_structure H"
    "P \<subseteq> fst H" "e \<notin> fst H"
  shows "historic_structure (occur P e H)"
  using assms by(cases H,auto intro!:trancl_asym)

end