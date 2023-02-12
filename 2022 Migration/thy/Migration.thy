(*
    Author:     SJC Joosten
*)

section \<open>Migration\<close>
(* TODO: introduce schemas
Question: can we rename "typedGraph" to "typedDataset", to let this predicate refer to datasets rather than graphs.
Question: can we rename "graphTyping" to "dataset", to let this datatype match closer to the paper?
Question: can we reorganise and rename triples "(l, x, y)" to resemble triples in the paper better?
Question: can we rename "wellTypedEdge" to "wellTypedTriple", to let this predicate refer to triples?
*)

theory Migration
  imports Graph_Saturation.LabeledGraphs
begin

text "The datatype graphTyping is meant for typing datasets."
datatype ('l,'v,'c) graphTyping (* 'l=\<real> (\Rels), 'v=\<bbbA> (\Atoms), 'c=\<complex> (\Concepts) *)
 = GT (decl : "'l \<Rightarrow> 'c \<times> 'c")
      (inst : "('v \<times> 'c) set")

(* This function corresponds to \ref{eqn:wellTypedEdge} in the article.
TODO: add specialization.
See articleMigration.tex, where I adapted equation \ref{eqn:wellTypedEdge}. *)
fun wellTypedEdge :: "('l,'v,'c) graphTyping \<Rightarrow> 'l \<times> 'v \<times> 'v \<Rightarrow> bool" where
"wellTypedEdge (GT lt vt) (l, x, y)
  = (case lt l of
      (xt,yt) \<Rightarrow> (x,xt) \<in> vt \<and> (y,yt) \<in> vt)"

lemma wellTypedEdgeI[intro]:
(* "e" represents a triple <a,n[A*B],b> with  l=n[A*B]  and  x=a  and  y=b.
*)
  assumes
    "(fst (snd e),fst (decl gt (fst e))) \<in> inst gt" (* so "(a,A) \<in> inst gt" *)
    "(snd (snd e),snd (decl gt (fst e))) \<in> inst gt" (* so "(b,B) \<in> inst gt" *)
  shows "wellTypedEdge gt e"
  using assms by (cases gt;cases e;auto)
lemma wellTypedEdgeE[elim]:
  assumes "wellTypedEdge gt e"
  shows
    "((fst (snd e)),fst (decl gt (fst e))) \<in> inst gt"
    "((snd (snd e)),snd (decl gt (fst e))) \<in> inst gt"
  using assms by (cases gt;cases e;force)+

(* typedVertex represents a predicate that determines whether a concept is in \<C> (\concepts) *)
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
  "trivialTyping = GT (\<lambda> _. ((),())) UNIV"

lemma DomainUNIV[simp]: "Domain UNIV = UNIV" by auto

lemma trivialTyping :
  assumes "graph lg"
  shows "typedGraph trivialTyping lg"
  using assms unfolding trivialTyping_def by auto

fun augmentTypeToVertex where
  "augmentTypeToVertex gt v = (v, inst gt `` {v})"
fun augmentTypeToEdge where
  "augmentTypeToEdge gt (l,x,y) = ((l,decl gt l), augmentTypeToVertex gt x, augmentTypeToVertex gt y)"

fun pairToRel where
  "pairToRel (v,ts) = (\<lambda> t. ((v,ts),t)) ` ts"

lemma pairToRelUNIV[simp]:
  "(a, b) \<in> Domain (\<Union> (range pairToRel)) \<longleftrightarrow> b\<noteq>{}"
  by fastforce

definition explicitTyping :: "('l \<times> 'c \<times> 'c, 'v \<times> 'c set, 'c) graphTyping" where
  "explicitTyping = GT snd (Union (pairToRel ` UNIV))"

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

lemma augmentTypes_preserves_typed_vertex[intro]:
  assumes
        "a\<in>vertices lg \<longrightarrow> typedVertex gt a"
        "(a, b) \<in> vertices (augmentTypes gt lg)"
  shows "typedVertex explicitTyping (a, b)"
  using assms unfolding explicitTyping_def
  by (cases "gt";auto simp: augmentTypes_def)

lemma augmentTypes_preserves_typed_edge[intro]:
  assumes
        "(e',fst l,fst r)\<in>edges lg \<longrightarrow> wellTypedEdge gt (e',fst l,fst r)"
        "((e', etl,etr),l,r) \<in> edges (augmentTypes gt lg)"
  shows "wellTypedEdge explicitTyping ((e', etl,etr),l,r)"
  using assms unfolding explicitTyping_def
  by (cases "gt";auto simp: augmentTypes_def)

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
    = GT (map_prod f f o decl gt) (apsnd f ` inst gt)"

lemma map_types_in_graphtype_inst[simp]:
  "inst (map_types_in_graphtype gt f)
    = apsnd f ` inst gt"
  unfolding map_types_in_graphtype_def by auto
lemma map_types_in_graphtype_decl[simp]:
  "decl (map_types_in_graphtype gt f)
    = map_prod f f o decl gt"
  unfolding map_types_in_graphtype_def by auto

lemma map_types_in_graphtype_preserves_typing:
  assumes "typedGraph t G"
  shows "typedGraph (map_types_in_graphtype t f) G"
proof(intro typedGraphI,goal_cases)
  case 1
  then show "graph G" using assms by auto
next
  case (2 e)
  have [intro!]: "\<And> a b s. (a,b) \<in> s \<Longrightarrow> (a, f b) \<in> apsnd f ` s" by force
  obtain l x y where e[simp]: "e = (l,x,y)" by (cases e;blast)
  with assms 2 have "wellTypedEdge t (l,x,y)" by auto
  from wellTypedEdgeE[OF this]
  show "wellTypedEdge (map_types_in_graphtype t f) e"
    by auto
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
      by (auto simp:xyprime)
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
    = GT (decl gt \<circ> f) (inst gt)"

definition map_labels_in_graph where
  "map_labels_in_graph g f
    = LG (apfst f -` edges g) (vertices g)"

lemma map_labels_preserves_wellTypedness:
  assumes "typedGraph gt g"
  shows "typedGraph (map_labels_in_graphtype gt f) (map_labels_in_graph g f)"
proof
  show "graph (map_labels_in_graph g f)"
    using typedGraphE(1)[OF assms]
    unfolding map_labels_in_graph_def
    by fastforce
  fix e assume e:"e \<in> edges (map_labels_in_graph g f)"
  hence "apfst f e \<in> edges g"
    unfolding map_labels_in_graph_def by auto
  hence "wellTypedEdge gt (apfst f e)"
    using assms by auto
  thus "wellTypedEdge (map_labels_in_graphtype gt f) e"
    unfolding map_labels_in_graphtype_def
    by(cases gt;cases e;auto)
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
    = GT (\<lambda> l. case l of Inl v \<Rightarrow> (decl gt1 l) | Inr v \<Rightarrow> (decl gt2 l)) 
         (inst gt1 \<union> inst gt2)"

(* did not use 'map_types_in_graphtypes', checking if neccessary first... *)
definition disjoint_union_typing where
  "disjoint_union_typing gt1 gt2
     = union_typing (map_labels_in_graphtype (map_vertices_in_graphtype gt1 Inl) (inv Inl))
                    (map_labels_in_graphtype (map_vertices_in_graphtype gt2 Inr) (inv Inr))"

end