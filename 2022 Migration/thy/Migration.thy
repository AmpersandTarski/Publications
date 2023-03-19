(*
    Author:     SJC Joosten
*)

section \<open>Migration\<close>

theory Migration
  imports Graph_Saturation.LabeledGraphs
begin

text "The datatype graphTyping is meant for typing datasets."
datatype ('l,'v,'c) graphTyping (* 'l=\<real> (\Rels), 'v=\<bbbA> (\Atoms), 'c=\<complex> (\Concepts) *)
 = GT (decl : "('l \<times> ('c \<times> 'c)) set")
      (inst : "('v \<times> 'c) set")

(* This function corresponds to \ref{eqn:wellTypedEdge} in the article.  *)
fun wellTypedEdge :: "('l,'v,'c) graphTyping \<Rightarrow> 'l \<times> 'v \<times> 'v \<Rightarrow> bool" where
"wellTypedEdge (GT lt vt) (l, x, y)
  \<longleftrightarrow> l \<in> Domain lt \<and>
      {b. \<exists> e. (l, (b,e)) \<in> lt} \<subseteq> {b. (x, b) \<in> vt} \<and>
      {b. \<exists> e. (l, (e,b)) \<in> lt} \<subseteq> {b. (y, b) \<in> vt}"

lemma wellTypedEdgeI[intro]:
  assumes
    "\<exists> x y. (fst e,x,y) \<in> decl gt"
    "\<And> x y. (fst e,x,y) \<in> decl gt \<Longrightarrow> (fst (snd e),x) \<in> inst gt"
    "\<And> x y. (fst e,x,y) \<in> decl gt \<Longrightarrow> (snd (snd e),y) \<in> inst gt"
  shows "wellTypedEdge gt e"
  using assms by (cases gt;cases e;auto)
lemma wellTypedEdgeE[elim]:
  assumes "wellTypedEdge gt e"
  shows
    "\<exists> x y. (fst e,x,y) \<in> decl gt"
    "\<And> x y. (fst e,x,y) \<in> decl gt \<Longrightarrow> (fst (snd e),x) \<in> inst gt"
    "\<And> x y. (fst e,x,y) \<in> decl gt \<Longrightarrow> (snd (snd e),y) \<in> inst gt"
  using assms by ((cases gt;cases e);force)+

fun typedVertex :: "('l,'v,'c) graphTyping \<Rightarrow> 'v \<Rightarrow> bool" where
"typedVertex (GT lt vt) x
  = (x \<in> Domain vt)"

lemma typedVertexI[intro]:
  assumes "x \<in> Domain (inst gt)"
  shows "typedVertex gt x"
  using assms by(cases gt,auto)

definition typedGraph where
  "typedGraph gt lg = 
  (graph lg \<and> Ball (edges lg) (wellTypedEdge gt)
            \<and> Ball (vertices lg) (typedVertex gt))"

lemma typedGraphI[intro]:
  assumes isGraph:      "graph lg"
   and wellTypedEdges:  "\<And> e. e \<in> edges lg \<Longrightarrow> wellTypedEdge gt e"
   and typedVertices:   "\<And> v. v \<in> vertices lg \<Longrightarrow> typedVertex gt v"
  shows "typedGraph gt lg"
  using assms unfolding typedGraph_def by auto

lemma typedGraphE[elim]:
  assumes "typedGraph gt lg"
  shows "graph lg"
    "\<And> e. e \<in> edges lg \<Longrightarrow> wellTypedEdge gt e"
    "\<And> v. v \<in> vertices lg \<Longrightarrow> typedVertex gt v"
  using assms unfolding typedGraph_def by auto

definition trivialTyping where
  "trivialTyping = GT (UNIV \<times> UNIV) UNIV"

lemma DomainUNIV[simp]: "Domain UNIV = UNIV" by auto

lemma trivialTyping :
  assumes "graph lg"
  shows "typedGraph trivialTyping lg"
  using assms unfolding trivialTyping_def by auto

fun augmentTypeToVertex where
  "augmentTypeToVertex gt v = (v, inst gt `` {v})"
fun augmentTypeToEdge where
  "augmentTypeToEdge gt (l,x,y) = ((l,{t.(l,t)\<in> decl gt}), augmentTypeToVertex gt x, augmentTypeToVertex gt y)"

fun pairToRel where
  "pairToRel (v,ts) = (\<lambda> t. ((v,ts),t)) ` ts"

lemma pairToRelUNIV[simp]:
  "(a, b) \<in> Domain (\<Union> (range pairToRel)) \<longleftrightarrow> b\<noteq>{}"
  by fastforce

definition explicitTyping :: "('l \<times> ('c \<times> 'c) set, 'v \<times> 'c set, 'c) graphTyping" where
  "explicitTyping = GT (Union (pairToRel ` UNIV)) (Union (pairToRel ` UNIV))"

definition augmentTypes where
  "augmentTypes gt lg
  = LG (augmentTypeToEdge gt ` edges lg) (augmentTypeToVertex gt ` vertices lg)"

lemma augmentTypes_is_graph[intro]:
  assumes "graph lg"
  shows "graph (augmentTypes gt lg)"
  using assms unfolding augmentTypes_def by fastforce

lemma pairABHelper[simp]:
  shows "(x, e) \<in> Pair c ` bs \<longleftrightarrow> e \<in> bs \<and> x=c"
  by auto

export_code augmentTypes

lemma augmentTypes_preserves_typed_vertex[intro]:
  assumes
        "a\<in>vertices lg \<longrightarrow> typedVertex gt a"
        "(a, b) \<in> vertices (augmentTypes gt lg)"
  shows "typedVertex explicitTyping (a, b)"
  using assms unfolding explicitTyping_def
  by (cases "gt";auto simp: augmentTypes_def)

lemma augmentTypes_preserves_typed_edge[intro]:
  assumes
    "(e',fst l,fst r) \<in> edges lg \<longrightarrow> wellTypedEdge gt (e',fst l,fst r)"
    "((e', s),l,r) \<in> edges (augmentTypes gt lg)"
  shows "wellTypedEdge explicitTyping ((e', s),l,r)"
proof
  from assms(2) have "(e',fst l,fst r) \<in> edges lg" by (auto simp: augmentTypes_def )
  with assms(1) have wt:"wellTypedEdge gt (e',fst l,fst r)" by simp
  from wellTypedEdgeE(1)[OF wt] obtain c1 c2 where "(e', (c1,c2)) \<in> (decl gt)" by auto
  with assms(2) have "(fst ((e', s), l, r), c1, c2) \<in> decl explicitTyping"
    unfolding explicitTyping_def by (cases gt;auto simp:augmentTypes_def)
  thus "\<exists>x y. (fst ((e', s), l, r), x, y) \<in> decl explicitTyping" by auto
  show "\<And> x y. (fst ((e', s), l, r), x, y) \<in> decl explicitTyping \<Longrightarrow>
           (fst (snd ((e', s), l, r)), x) \<in> inst explicitTyping"
    using wellTypedEdgeE(2)[OF wt] assms(2)
    by (auto simp: explicitTyping_def augmentTypes_def)
  show "\<And> x y. (fst ((e', s), l, r), x, y) \<in> decl explicitTyping \<Longrightarrow>
           (snd (snd ((e', s), l, r)), y) \<in> inst explicitTyping"
    using wellTypedEdgeE(3)[OF wt] assms(2)
    by (auto simp: explicitTyping_def augmentTypes_def)
qed

lemma augmentTypes_preserves_typedness:
  assumes "typedGraph gt lg"
  shows "typedGraph explicitTyping (augmentTypes gt lg)"
  using assms unfolding typedGraph_def by auto

subsection \<open>(Disjoint) union\<close>

text \<open> We show that regular unions preserve typing,
       then we show that the mapping that helps make our unions
       disjoint will preserve typing. Adding those two results
       will establish that disjoint unions preserve typing. \<close>

(* Regular unions preserve typing *)
lemma graph_union_wellTyped_then_parts_wellTyped:
  assumes "typedGraph gt (graph_union g1 g2)"
  shows   "graph g1 \<longleftrightarrow> typedGraph gt g1"
          "graph g2 \<longleftrightarrow> typedGraph gt g2"
using assms unfolding typedGraph_def by auto

lemma graph_union_wellTyped_if_parts_wellTyped:
  assumes "typedGraph gt g1"
          "typedGraph gt g2"
  shows   "typedGraph gt (graph_union g1 g2)"
  using assms unfolding typedGraph_def by auto

definition map_types_in_graphtype where
  "map_types_in_graphtype gt f
    = GT (apsnd (map_prod f f) ` decl gt) (apsnd f ` inst gt)"

lemma map_types_in_graphtype_inst[simp]:
  "inst (map_types_in_graphtype gt f)
    = apsnd f ` inst gt"
  unfolding map_types_in_graphtype_def by auto
lemma map_types_in_graphtype_decl[simp]:
  "decl (map_types_in_graphtype gt f)
    = apsnd (map_prod f f) ` decl gt"
  unfolding map_types_in_graphtype_def by auto

lemma map_types_in_graphtype_preserves_wellTypedness:
  assumes "typedGraph t G"
  shows "typedGraph (map_types_in_graphtype t f) G"
proof(intro typedGraphI,goal_cases)
  case 1 show "graph G" using assms by auto
next
  case (2 e)
  have [intro!]: "\<And> a b s. (a,b) \<in> s \<Longrightarrow> (a, f b) \<in> apsnd f ` s" by force
  obtain l x y where e[simp]: "e = (l,x,y)" by (cases e;blast)
  with assms 2 have wte:"wellTypedEdge t (l,x,y)" by auto
  show "wellTypedEdge (map_types_in_graphtype t f) e"
    using  wellTypedEdgeE[OF wte] by (intro wellTypedEdgeI;force)
next
  case (3 v)
  have [simp]:"\<And> x. Domain (apsnd f ` x) = Domain x" by force
  from 3 assms have "typedVertex t v" by auto
  thus "typedVertex (map_types_in_graphtype t f) v"
    by (intro typedVertexI,cases t,auto)
qed


definition map_vertices_in_graphtype where
  "map_vertices_in_graphtype gt f
    = GT (decl gt) (apfst f ` inst gt)"

lemma map_vertices_in_graphtype_decl[simp]:
  "decl (map_vertices_in_graphtype gt f) = (decl gt)"
  unfolding map_vertices_in_graphtype_def by auto

lemma map_vertices_in_graphtype_inst[simp]:
  "inst (map_vertices_in_graphtype gt f) = (apfst f ` inst gt)"
  unfolding map_vertices_in_graphtype_def by auto

lemma map_graph_preserves_wellTypedness:
  assumes "typedGraph t G"
  shows "typedGraph (map_vertices_in_graphtype t f) (map_graph_fn G f)"
proof
  have [intro!]: "\<And> a b s. (a,b) \<in> s \<Longrightarrow> (f a, b) \<in> apfst f ` s" by force
  show "graph (map_graph_fn G f)" by auto
  { fix e
    assume e:"e \<in> edges (map_graph_fn G f)"
    obtain l x y where lxy:"(l,x,y)=e" by (cases e;blast)
    with e have "(l,x,y) \<in> edges (map_graph_fn G f)" by auto
    then obtain x' y' where xyprime:
      "(l, x', y') \<in> edges G"
      "x = f x'"
      "y = f y'"
      by auto
    with assms
    have "wellTypedEdge t (l,x',y')" by auto
    from wellTypedEdgeE[OF this] 
    have "wellTypedEdge (map_vertices_in_graphtype t f) (l,x,y)"
      by (intro wellTypedEdgeI;force simp:xyprime)
    thus "wellTypedEdge (map_vertices_in_graphtype t f) e" unfolding lxy.
  }
  { fix v
    assume "v \<in> vertices (map_graph_fn G f)"
    then obtain v' where vprime:
      "v' \<in> vertices G"
      "v = f v'"
      by auto
    with assms
    have "typedVertex t v'" by auto
    thus "typedVertex (map_vertices_in_graphtype t f) v"
      by (intro typedVertexI,cases t;auto simp:vprime(2))
  }
qed

definition map_labels_in_graphtype where
  "map_labels_in_graphtype gt f
    = GT (apfst f ` decl gt) (inst gt)"

definition map_labels_in_graph where
  "map_labels_in_graph g f
    = LG (apfst f ` edges g) (vertices g)"

lemma map_labels_preserves_wellTypedness:
  assumes "typedGraph gt g" "inj_on f (Domain (decl gt))"
  shows "typedGraph (map_labels_in_graphtype gt f) (map_labels_in_graph g f)"
proof
  show "graph (map_labels_in_graph g f)"
    using typedGraphE(1)[OF assms(1)]
    unfolding map_labels_in_graph_def
    by fastforce
  fix e assume e:"e \<in> edges (map_labels_in_graph g f)"
  then obtain e' where e2:"apfst f e' = e" unfolding map_labels_in_graph_def by auto
  thus "wellTypedEdge (map_labels_in_graphtype gt f) e"
    unfolding map_labels_in_graphtype_def using e assms(2)
    apply(cases gt;cases e;auto) sorry
next
  fix v assume v:"v \<in> vertices (map_labels_in_graph g f)"
  hence "v \<in> vertices g"
    unfolding map_labels_in_graph_def by auto
  hence "typedVertex gt v" using assms by auto
  thus "typedVertex (map_labels_in_graphtype gt f) v"
    unfolding map_labels_in_graphtype_def
    by(cases gt;auto)
qed

definition union_typing where
  "union_typing gt1 gt2
    = GT (decl gt1 \<union> decl gt2) 
         (inst gt1 \<union> inst gt2)"

lemma union_typing_sym: "union_typing a b = union_typing b a" using union_typing_def
  by (metis sup_commute)

lemma union_typing_preserves_welltyped_left:
  assumes "typedGraph gt1 g" "\<And> l s. (l,s) \<in> edges g \<Longrightarrow> l \<notin> Domain (decl gt2)"
  shows "typedGraph (union_typing gt1 gt2) g"
proof
  from assms(1) show "graph g" by auto
  { fix e
    assume e:"e \<in> edges g"
    hence wt:"wellTypedEdge gt1 e" using assms(1) by auto
    thus "wellTypedEdge (union_typing gt1 gt2) e"
      unfolding union_typing_def using assms(2) e
      by(cases gt1;cases e;auto)
  }
  { fix v
    assume v:"v \<in> vertices g"
    hence wt:"typedVertex gt1 v" using assms(1) by auto
    thus "typedVertex (union_typing gt1 gt2) v"
      unfolding union_typing_def by (cases gt1;auto)
  }
qed

lemma union_typing_preserves_welltyped_right:
  assumes "typedGraph gt2 g" "\<And> l s. (l,s) \<in> edges g \<Longrightarrow> l \<notin> Domain (decl gt1)"
  shows "typedGraph (union_typing gt1 gt2) g"
  using union_typing_preserves_welltyped_left assms union_typing_sym
  by metis

(* did not use 'map_types_in_graphtypes', checking if neccessary first... *)
definition disjoint_union_typing where
  "disjoint_union_typing gt1 gt2
     = union_typing (map_labels_in_graphtype (map_types_in_graphtype (map_vertices_in_graphtype gt1 Inl) Inl) Inl)
                    (map_labels_in_graphtype (map_types_in_graphtype (map_vertices_in_graphtype gt2 Inr) Inr) Inr)"

lemma move_types_left:
  assumes "typedGraph gt1 g1"
  shows "typedGraph (disjoint_union_typing gt1 gt2)
             (map_labels_in_graph (map_graph_fn g1 Inl) Inl)"
  unfolding disjoint_union_typing_def
  apply(rule union_typing_preserves_welltyped_left[OF assms[THEN map_graph_preserves_wellTypedness,
             THEN map_types_in_graphtype_preserves_wellTypedness,
             THEN map_labels_preserves_wellTypedness]])
  unfolding map_labels_in_graph_def map_labels_in_graphtype_def by auto

lemma move_types_right:
  assumes "typedGraph gt2 g2"
  shows "typedGraph (disjoint_union_typing gt1 gt2)
             (map_labels_in_graph (map_graph_fn g2 Inr) Inr)"
  unfolding disjoint_union_typing_def
  apply(rule union_typing_preserves_welltyped_right[OF assms[THEN map_graph_preserves_wellTypedness,
             THEN map_types_in_graphtype_preserves_wellTypedness,
             THEN map_labels_preserves_wellTypedness]])
  unfolding map_labels_in_graph_def map_labels_in_graphtype_def by auto


definition disjoint_union_graphs where
  "disjoint_union_graphs g1 g2
    = graph_union
         (map_labels_in_graph (map_graph_fn g1 Inl) Inl)
         (map_labels_in_graph (map_graph_fn g2 Inr) Inr)"

lemma disjoint_union_well_typed:
  assumes
    "typedGraph gt1 g1"
    "typedGraph gt2 g2"
  shows
    "typedGraph (disjoint_union_typing gt1 gt2) (disjoint_union_graphs g1 g2)"
  unfolding disjoint_union_graphs_def
  using graph_union_wellTyped_if_parts_wellTyped[OF move_types_left move_types_right]
    assms by auto

end