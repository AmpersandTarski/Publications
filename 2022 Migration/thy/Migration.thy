(*
    Author:     SJC Joosten
*)

section \<open>Migration\<close>

theory Migration
  imports Graph_Saturation.LabeledGraphs
begin

datatype ('l,'v,'c) graphTyping
 = GT (lblTyping : "'l \<Rightarrow> 'c \<times> 'c")
      (vertTyping : "('v \<times> 'c) set")

fun wellTypedEdge :: "('l,'v,'c) graphTyping \<Rightarrow> _ \<Rightarrow> _" where
"wellTypedEdge (GT lt vt) (l, x, y)
  = (case lt l of
      (xt,yt) \<Rightarrow> (x,xt) \<in> vt \<and> (y,yt) \<in> vt)"
fun typedVertex :: "('l,'v,'c) graphTyping \<Rightarrow> _ \<Rightarrow> _" where
"typedVertex (GT lt vt) x
  = (x \<in> Domain vt)"

fun typedGraph where
  "typedGraph gt lg = 
  (graph lg \<and> Ball (edges lg) (wellTypedEdge gt)
            \<and> Ball (vertices lg) (typedVertex gt))"

definition trivialTyping where
  "trivialTyping = GT (\<lambda> _. ((),())) UNIV"

lemma trivialTyping :
  assumes "graph lg"
  shows "typedGraph trivialTyping lg"
  using assms unfolding trivialTyping_def by auto

fun augmentTypeToVertex where
  "augmentTypeToVertex gt v = (v, vertTyping gt `` {v})"
fun augmentTypeToEdge where
  "augmentTypeToEdge gt (l,x,y) = ((l,lblTyping gt l), augmentTypeToVertex gt x, augmentTypeToVertex gt y)"

fun pairToRel where
  "pairToRel (v,ts) = (\<lambda> t. ((v,ts),t)) ` ts"

definition explicitTyping where
  "explicitTyping = GT snd (Union (pairToRel ` UNIV))"

definition augmentTypes where
  "augmentTypes gt lg
  = LG (augmentTypeToEdge gt ` edges lg) (augmentTypeToVertex gt ` vertices lg)"

lemma augmentTypes_is_graph[intro]:
  assumes "graph lg"
  shows "graph (augmentTypes gt lg)"
  using assms unfolding augmentTypes_def by fastforce

lemma elm_in_augmentTypes[simp]:
  "((a, aa, b), (ab, ba), (ac, bb)) \<in> edges (augmentTypes gt lg)
  \<longleftrightarrow> ((a,ab,ac) \<in> edges lg \<and>
      (aa,b) = lblTyping gt a \<and>
      (\<forall> b. (b\<in> ba \<longleftrightarrow> (ab,b) \<in> vertTyping gt)) \<and>
      (\<forall> b. (b\<in> bb \<longleftrightarrow> (ac,b) \<in> vertTyping gt)) )" (is "?lhs = ?rhs")
proof
  show "?lhs \<Longrightarrow> ?rhs" unfolding augmentTypes_def by auto
  assume rhs:?rhs
  hence at:"augmentTypeToEdge gt (a,ab,ac) \<in> augmentTypeToEdge gt ` edges lg"
    by blast
  from rhs have "augmentTypeToEdge gt (a, ab, ac) = ((a, aa, b), (ab, ba), (ac, bb))"
    by auto
  with at show ?lhs unfolding augmentTypes_def by auto
qed


lemma augmentTypes_preserves_typedness:
  assumes "typedGraph gt lg"
  shows "typedGraph explicitTyping (augmentTypes gt lg)"
  using assms apply auto
end