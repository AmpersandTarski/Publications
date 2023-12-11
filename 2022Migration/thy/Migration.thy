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

fun wellTypedEdge :: "('l,'v,'c) graphTyping \<Rightarrow> 'l \<times> 'v \<times> 'v \<Rightarrow> bool" where
"wellTypedEdge (GT lt vt) (l, x, y)
  \<longleftrightarrow> l \<in> Domain lt \<and>
      {b. \<exists> e. (l, (b,e)) \<in> lt} \<subseteq> {b. (x, b) \<in> vt} \<and>
      {b. \<exists> e. (l, (e,b)) \<in> lt} \<subseteq> {b. (y, b) \<in> vt}"

(* This lemma shows that wellTypedEdge corresponds to \ref{eqn:wellTypedEdge} in the article.  *)
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

(* Relations can have multiple types, and wellTypedEdge requires that
   the population satisfies each of those types.
   This allows us to give a nice (i.e. symmetrical) definition of a type union later on. *)

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

lemma apfst_helper: "\<And> a b s. (a,b) \<in> s \<Longrightarrow> (f a, b) \<in> apfst f ` s" by force

lemma map_graph_preserves_wellTypedness:
  assumes "typedGraph t G"
  shows "typedGraph (map_vertices_in_graphtype t f) (map_graph_fn G f)"
proof
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
      by (intro typedVertexI,cases t;auto simp:vprime(2) intro:apfst_helper)
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
  from e obtain l x y where e2:"apfst f (l,x,y) = e" "(l,x,y) \<in> edges g"
    unfolding map_labels_in_graph_def by auto
  hence wt:"wellTypedEdge gt (l,x,y)" using assms(1) by auto
  from e2 have [simp]:"e = (f l,x,y)" by auto
  from wellTypedEdgeE[OF wt] e2(1)
  show "wellTypedEdge (map_labels_in_graphtype gt f) e"
    unfolding map_labels_in_graphtype_def
    by (auto intro:apfst_helper dest!:inj_onD[OF assms(2) _ DomainI DomainI])
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

(* did not use 'map_types_in_graphtypes', since those aren't necessary *)
definition disjoint_union_typing where
  "disjoint_union_typing gt1 gt2
     = union_typing (map_labels_in_graphtype gt1 Inl)
                    (map_labels_in_graphtype gt2 Inr)"

lemma move_types_left:
  assumes "typedGraph gt1 g1"
  shows "typedGraph (disjoint_union_typing gt1 gt2)
             (map_labels_in_graph g1 Inl)"
  unfolding disjoint_union_typing_def
  apply(rule union_typing_preserves_welltyped_left[OF assms[THEN map_labels_preserves_wellTypedness]])
  unfolding map_labels_in_graph_def map_labels_in_graphtype_def by auto

lemma move_types_right:
  assumes "typedGraph gt2 g2"
  shows "typedGraph (disjoint_union_typing gt1 gt2)
             (map_labels_in_graph g2 Inr)"
  unfolding disjoint_union_typing_def
  apply(rule union_typing_preserves_welltyped_right[OF assms[THEN map_labels_preserves_wellTypedness]])
  unfolding map_labels_in_graph_def map_labels_in_graphtype_def by auto


definition disjoint_union_graphs where
  "disjoint_union_graphs g1 g2
    = graph_union
         (map_labels_in_graph g1 Inl)
         (map_labels_in_graph g2 Inr)"

lemma disjoint_union_well_typed:
  assumes
    "typedGraph gt1 g1"
    "typedGraph gt2 g2"
  shows
    "typedGraph (disjoint_union_typing gt1 gt2) (disjoint_union_graphs g1 g2)"
  unfolding disjoint_union_graphs_def
  using graph_union_wellTyped_if_parts_wellTyped[OF move_types_left move_types_right]
    assms by auto

datatype ('l,'v,'c) pre_dataset
  = DS (tripleset: "('l,'v) labeled_graph") (dsTyping : "('l,'v,'c) graphTyping")

fun disjoint_union_pre_dataset where
  "disjoint_union_pre_dataset (DS g1 gt1) (DS g2 gt2)
    = DS (disjoint_union_graphs g1 g2) (disjoint_union_typing gt1 gt2)"

abbreviation dataset where
 "dataset y \<equiv> y \<in> {ds. typedGraph (dsTyping ds) (tripleset ds)}"

(* This lemma shows that the disjoint union of two datasets is again a dataset *)
lemma disjoint_union_pre_dataset:
  assumes "dataset ds1" "dataset ds2"
  shows "dataset (disjoint_union_pre_dataset ds1 ds2)"
  using assms disjoint_union_well_typed
  by(cases ds1;cases ds2;auto)

fun map_labels_in_dataset_pre where
  "map_labels_in_dataset_pre f (DS g gt)
    = DS (map_labels_in_graph g f) (map_labels_in_graphtype gt f)"

lemma map_labels_pre_dataset:
  assumes "dataset ds" "inj_on f (Domain (decl (dsTyping ds)))"
  shows "dataset (map_labels_in_dataset_pre f ds)"
proof(cases ds)
  case (DS g gt)
  hence "typedGraph gt g" "inj_on f (Domain (decl gt))"
    using assms by auto
  from map_labels_preserves_wellTypedness[OF this]
  show ?thesis by (auto simp:DS)
qed

(* Isabelle documentation on typedef is found in the 'datatypes' tutorial *)
typedef ('l,'v,'c) dataset = "{ds :: ('l,'v,'c) pre_dataset. typedGraph (dsTyping ds) (tripleset ds)}"
proof
  let ?emptyset = "DS (LG {} {}) (GT {} {})::('l,'v,'c) pre_dataset"
  show "?emptyset \<in> {ds. typedGraph (dsTyping ds) (tripleset ds)}" by auto
qed

lemma typedGraph_datasetI[intro]:
  "typedGraph (dsTyping (Rep_dataset ds)) (tripleset (Rep_dataset ds))"
  using Rep_dataset by blast

definition map_labels_dataset where
"map_labels_dataset f ds = Abs_dataset (map_labels_in_dataset_pre f (Rep_dataset ds))"

abbreviation relations where
  "relations ds \<equiv> Domain (decl (dsTyping (Rep_dataset ds)))"

lemma map_labels_dataset_Rep[simp]:
  assumes "inj_on f (relations ds)"
  shows "Rep_dataset (map_labels_dataset f ds)
  = map_labels_in_dataset_pre f (Rep_dataset ds)"
  unfolding map_labels_dataset_def
  using Abs_dataset_inverse[OF map_labels_pre_dataset[OF Rep_dataset assms]].

definition disjoint_union_dataset where
"disjoint_union_dataset ds1 ds2 =
  Abs_dataset (disjoint_union_pre_dataset (Rep_dataset ds1) (Rep_dataset ds2))"

lemma disjoint_union_dataset_Rep[simp]:
  "Rep_dataset (disjoint_union_dataset a b)
  = disjoint_union_pre_dataset (Rep_dataset a) (Rep_dataset b)"
  unfolding disjoint_union_dataset_def 
  Abs_dataset_inverse[OF disjoint_union_pre_dataset[OF Rep_dataset Rep_dataset]]..

fun filter_edges where "filter_edges f (LG es v) = LG {e\<in> es. f e} v"

lemma filter_edges_graph[intro]:
  assumes "graph g"
  shows "graph (filter_edges f g)"
  using assms by(cases g, force simp:restrict_def)

lemma filter_edges_vertices[simp]:
  shows "vertices (filter_edges f g) = vertices g"
  by(cases g,auto)

lemma filter_edges_edge[simp]:
  shows "e \<in> edges (filter_edges f g) \<longleftrightarrow> e \<in> edges g \<and> f e"
  by(cases g,auto)

lemma filter_edges_subgraph:
  assumes "graph g"
  shows "subgraph (filter_edges f g) g"
  by(rule graph_homomorphismI[OF _ _ _ _ filter_edges_graph[OF assms] assms],auto)
   
abbreviation filter_labels_graph where
  "filter_labels_graph L \<equiv> filter_edges (\<lambda>(l,_,_). l\<in> L)"

fun filter_labels_type where
  "filter_labels_type L (GT d i) = GT {(l,v)\<in>d. l\<in>L} i"

fun filter_with_labelset_pre where
  "filter_with_labelset_pre L (DS lg tg) = (DS (filter_labels_graph L lg) (filter_labels_type L tg))"

definition filter_with_labelset where
  "filter_with_labelset L ds = Abs_dataset (filter_with_labelset_pre L (Rep_dataset ds))"

lemma filter_with_labelset_pre_welltyped:
  assumes "dataset ds"
  shows "dataset (filter_with_labelset_pre L ds)"
proof(standard,standard)
  obtain lg tg where ds[simp]: "ds = DS lg tg" by (cases ds,blast)
  have tg:"typedGraph tg lg" using assms by auto
  show " graph (tripleset (filter_with_labelset_pre L ds))"
    using assms by auto
  { fix e assume e:"e \<in> edges (tripleset (filter_with_labelset_pre L ds))"
    obtain x y z where [simp]:"e=(x,y,z)" by (cases e, blast)
    from e have wte:"wellTypedEdge tg (x,y,z)" and [simp]:"x\<in> L \<longleftrightarrow> True"
          using tg by auto
    show "wellTypedEdge (dsTyping (filter_with_labelset_pre L ds)) e"
      using wte by(cases tg;intro wellTypedEdgeI;auto dest!:wellTypedEdgeE)
  }
  { fix v assume v:"v \<in> vertices (tripleset (filter_with_labelset_pre L ds))"
    thus " typedVertex (dsTyping (filter_with_labelset_pre L ds)) v"
      using tg by(cases tg;cases lg;auto simp:typedGraph_def)
  }
qed

lemma filter_with_labelset[simp]:
  "Rep_dataset (filter_with_labelset L ds)
   = filter_with_labelset_pre L (Rep_dataset ds)" (is "?lhs=?rhs")
  unfolding filter_with_labelset_def
  using Abs_dataset_inverse[of ?rhs, OF filter_with_labelset_pre_welltyped[OF Rep_dataset]].

lemma filter_with_labelset_twice[simp]:
  shows "filter_with_labelset L (filter_with_labelset R ds)
   = filter_with_labelset (L \<inter> R) ds" (is "?lhs=?rhs")
proof -
  have "Rep_dataset (filter_with_labelset L (filter_with_labelset R ds)) =
    Rep_dataset (filter_with_labelset (L \<inter> R) ds)"
    apply (cases "Rep_dataset ds")
    apply (cases "tripleset (Rep_dataset ds)"; cases "dsTyping (Rep_dataset ds)")
    by (auto simp:restrict_def)
  thus ?thesis using Rep_dataset_inject by blast
qed

lemma map_labels_in_graph_filter [simp]:
  assumes "inj_on f (L \<union> Domain x1a)" "typedGraph (GT x1a x2a) (LG x1b x2b)"
  shows "(apfst f ` {e \<in> x1b. case e of (l, uu_, uua_) \<Rightarrow> l \<in> L}) =
          {e \<in> apfst f ` x1b. case e of (l, uu_, uua_) \<Rightarrow> l \<in> f ` L}"
  using wellTypedEdgeE[OF typedGraphE(2)[OF assms(2)]] inj_onD[OF assms(1)]    
  by (auto intro!:apfst_helper) blast

lemma map_labels_in_dataset_pre_filter[simp]:
  assumes "inj_on f (L \<union> Domain (decl (dsTyping ds)))" "dataset ds"
  shows
  "map_labels_in_dataset_pre f (filter_with_labelset_pre L ds) =
    filter_with_labelset_pre (f ` L) (map_labels_in_dataset_pre f ds)"
  using assms 
  apply(cases ds;cases "dsTyping ds";cases "tripleset ds",simp)
  by(auto simp:map_labels_in_graph_def map_labels_in_graphtype_def
        intro!:apfst_helper Domain.DomainI dest!:inj_onD[OF assms(1)])

lemma relations_filter[simp]:
  "relations (filter_with_labelset L ds)
  = L \<inter> relations ds" by (cases "Rep_dataset ds"; cases "dsTyping (Rep_dataset ds)", auto)

lemma relations_filterI[intro]:
  "relations (filter_with_labelset L ds)
  \<subseteq> relations ds" by (cases "Rep_dataset ds"; cases "dsTyping (Rep_dataset ds)", auto)

lemma filter_map_range[simp]:
  assumes "inj_on f (relations ds)"
  shows
    "filter_with_labelset (range f) (map_labels_dataset f ds)
  = map_labels_dataset f ds"
  apply (subst Rep_dataset_inject[symmetric])
  by (cases "Rep_dataset ds",
      auto simp:map_labels_dataset_Rep[OF assms]
      map_labels_in_graph_def
      map_labels_in_graphtype_def)

lemma map_filter[simp]:
  assumes "inj_on f (L \<union> relations ds)"
  shows "map_labels_dataset f (filter_with_labelset L ds)
        = filter_with_labelset (f ` L) (map_labels_dataset f ds)"
proof (subst Rep_dataset_inject[symmetric])
  have inj:"inj_on f (relations ds)" using assms unfolding inj_on_Un by auto
  from map_labels_in_dataset_pre_filter[OF assms Rep_dataset] inj
       inj_on_subset[OF inj relations_filterI]
  show "Rep_dataset (map_labels_dataset f (filter_with_labelset L ds)) =
    Rep_dataset (filter_with_labelset (f ` L) (map_labels_dataset f ds))"
    by auto
(* auto does the following:
    unfolding map_labels_dataset_Rep[OF inj_on_subset[OF inj relations_filterI]]
              filter_with_labelset
              map_labels_dataset_Rep[OF inj]
    using map_labels_in_dataset_pre_filter[OF assms Rep_dataset]
*)
qed

locale rule_violations =
  fixes violation :: "'u \<Rightarrow> ('l,'v,'c) dataset \<Rightarrow> 'x :: {order_bot, wellorder}"
  and   relevant_labels :: "'u \<Rightarrow> 'l set"
assumes filter[simp]:"violation u (filter_with_labelset (relevant_labels u) g) = violation u g"
begin

fun satisfies where
  "satisfies u ds \<longleftrightarrow> violation u ds = bot"
lemma satisfies_relevant[simp]:
  "satisfies u (filter_with_labelset (relevant_labels u) g) = satisfies u g"
  by simp
fun satisfies_set where
  "satisfies_set U ds \<longleftrightarrow> (\<forall> u\<in>U. satisfies u ds)"

fun violation_mapped where
  "violation_mapped f u = violation u o map_labels_dataset f"

fun relevant_mapped where
  "relevant_mapped f u = f -` relevant_labels u"

end

locale mapped_rule_violations = rule_violations + 
  fixes f :: "'l \<Rightarrow> 'b"
  assumes inj:"inj f"
begin

interpretation mapped: rule_violations "violation_mapped f" "relevant_mapped f"
proof(standard)
  fix u
  fix g :: "('l, 'c, 'd) dataset"
  have inj1:"inj_on f (relations g)" 
   and inj2:"inj_on f ((f -` relevant_labels u) \<union> relations g)"
       using subset_inj_on[OF inj] by auto
  have "violation u (filter_with_labelset (relevant_labels u)
                    (filter_with_labelset (range f) (map_labels_dataset f g)))
      = violation u (map_labels_dataset f g)"
    using filter_map_range[OF inj1] filter by metis
  then show "violation_mapped f u (filter_with_labelset (relevant_mapped f u) g) =
                   violation_mapped f u g" by (auto simp:map_filter[OF inj2])
qed

end

type_synonym ('l,'v,'c) dataset_seq = "nat \<Rightarrow> ('l,'v,'c) dataset"

definition "subdataset a b \<equiv> subgraph (tripleset (Rep_dataset a)) (tripleset (Rep_dataset b))
             \<and> dsTyping (Rep_dataset a) = dsTyping (Rep_dataset b)"

definition chain :: "('l,'v,'c) dataset_seq \<Rightarrow> bool" where
  "chain S \<equiv> \<forall> i. subdataset (S i) (S (i+1))"

lemma subdataset_transitive:
  assumes "subdataset a b" "subdataset b c"
  shows "subdataset a c"
proof -
  from  assms[unfolded subdataset_def]
  have "subgraph (tripleset (Rep_dataset a)) (tripleset (Rep_dataset b))"
       "subgraph (tripleset (Rep_dataset b)) (tripleset (Rep_dataset c))"
    by auto
  hence "subgraph (tripleset (Rep_dataset a)) (tripleset (Rep_dataset c))"
    by(rule subgraph_trans)
  thus ?thesis using assms unfolding subdataset_def by auto
qed

lemma subdataset_refl[intro]:
  shows "subdataset a a"
  unfolding subdataset_def using typedGraph_def by auto

lemma subdataset_in_chain[elim]:
  assumes "chain s"
  shows "i \<le> j \<Longrightarrow> subdataset (s i) (s j)"
proof(induct "j-i" arbitrary:j)
  case 0
  then show ?case by auto
next
  case (Suc delta j)
  from Suc have i_less:"i < j" by auto
  hence "\<exists> j2. Suc j2 = j" by presburger
  then obtain j2 where j2:"Suc j2 = j" by auto
  hence subd:"subdataset (s j2) (s j)" using assms unfolding chain_def by auto
  have "delta = j2 - i" "i \<le> j2" using i_less Suc(2) j2 by auto
  from subdataset_transitive[OF Suc(1)[OF this] subd]
  show ?case.
qed

locale enforced = rule_violations +
  fixes repair :: "'e \<Rightarrow> ('b, 'c, 'd) dataset \<Rightarrow> ('b, 'c, 'd) dataset"
  assumes viols_solved:
          "let viol1 = (violation u ds) in 
           let viol2 = violation u (repair viol1 ds) in
           viol1 > viol2"
  and mono: "subdataset ds (repair viol ds)"
begin
definition repair_chain where
  "repair_chain S \<equiv> \<forall> i. \<exists> u. S (i+1) = repair (violation u (S i)) (S i)"

lemma repair_chain_is_chain:
  assumes "repair_chain S"
  shows "chain S"
  unfolding chain_def
proof
  fix i
  show "subdataset (S i) (S (i + 1))"
    using mono assms unfolding repair_chain_def by metis
qed

end

(*
 Bewijslijn aantekeningen
  in het migratie verhaal zijn diverse stappen:
   stap: migratie systeem wordt aangezet.
     bewijslasten:
      - alle invarianten van het migratiesysteem gelden
      - migratiesysteem copieert data uit het oude systeem
         (zonder invarianten te overtreden)
      - de business constraints die in het nieuwe systeem invariant zijn,
        leveren een eindige lijst werk (aanname?)

   stap: werk wordt gedaan in het migratie systeem door de business
      - in de business constraints die in het nieuwe systeem invariant zijn,
        nemen de overtredingen monotoon af
      - (corollary) als een business constraint die in het nieuwe systeem invariant is, overtredings vrij is,
        is deze invariant.
      - na voldoende werk zijn alle business constraints die in het nieuwe systeem invariant zijn, invariant.
      - aanname: de enforce regels voor bovenstaande reageren 'snel genoeg'.
      - enforce regels uit het nieuwe systeem mogen gewoon mee doen
        (vraag: mogen ze sneller zijn dan de enforce regels uit bovengenoemde
         punt?)

   stap: als alle business constraints die in het nieuwe systeem invariant zijn, invariant zijn,
        kan het nieuwe systeem in gebruik genomen worden. (thm: mapped_rule_violations.mapped)
        (ihb: ik kan de oude data en het migratie-systeem laten vallen)

*)

end
