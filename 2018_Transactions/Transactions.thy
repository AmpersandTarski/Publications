(*  assumes disjInsDel: "ins\<inter>del=\<emptyset>"

  File:    Transactions.thy
  Author:  Stef Joosten <stef.joosten@ou.nl>

  Proofs for Semantics of Transactions
*)

theory Transactions imports Main
begin

datatype 'a Action = Action (src:"'a set")
                            (tgt:"'a set")
                            (mark:"'a set")

find_theorems name:Action

fun ins where "ins x = tgt x - src x"
fun del where "del x = src x - tgt x"
fun change where "change x = ins x \<union> del x"

fun isAction where
  "isAction x = (change x \<subseteq> mark x)"

lemma ins_del_excl: "ins x \<inter> del x = {}" by auto

fun dom where "dom (Action c _ _) = Action c c {}"
fun cod where "cod (Action _ c _) = Action c c {}"

fun composition where
  "composition (Action _ t2 m2) (Action s1 _ m1)
    = Action s1 t2 (m1 \<union> m2)"

abbreviation comp (infixr ";" 55) where "comp x y \<equiv> composition y x"
abbreviation dom_abbrev ("\<box>_" [61] 60) where "dom_abbrev x \<equiv> dom x"
abbreviation cod_abbrev ("_\<box>" [61] 60) where "cod_abbrev x \<equiv> cod x"

lemma case_free_comp[simp]:
  "src (x;y) = src x"
  "tgt (x;y) = tgt y"
  "mark (x;y) = mark x \<union> mark y"
  by(cases x,cases y,auto)+

lemma is_category[simp]:
  "isAction x \<Longrightarrow> isAction (\<box>x)"
  "isAction x \<Longrightarrow> isAction (x\<box>)"
  "(\<box>x)\<box> = \<box>x"
  "\<box>(x\<box>) = (x\<box>)"
  "\<box>(x;y) = \<box>x"
  "(x;y)\<box> = y\<box>"
  "x;(y;z) = (x;y);z"
  "\<box>x;x = x"
  "x;x\<box> = x"
  "isAction x \<Longrightarrow> isAction y \<Longrightarrow> x\<box> = \<box>y \<Longrightarrow> isAction (x ; y)"
  by (cases x;cases y;cases z;force)+
  (* Note on the associativity rule:
     this rule goes from no-brackets to brackets in notations,
     this helps discover why `auto' doesn't get lemma's automatically:
     if brackets are missing, I tend to forget about them. *)

lemma src_tgt_eqs[simp]:
  "\<box>x = \<box>y \<longleftrightarrow> src x = src y"
  "\<box>x = y\<box> \<longleftrightarrow> src x = tgt y"
  "x\<box> = \<box>y \<longleftrightarrow> tgt x = src y"
  "x\<box> = y\<box> \<longleftrightarrow> tgt x = tgt y"
  by(cases x,cases y,force)+

fun action_converse where
  "action_converse (Action s t m) = (Action t s m)"

fun allg_intersection where
  "allg_intersection (Action s t m1) (Action _ _ m2) = (Action s t (m1 \<union> m2))"

abbreviation intr (infixr "\<sqinter>" 59) where "intr x y \<equiv> allg_intersection x y"
abbreviation conv ("_\<^sup>\<circ>" [62] 62) where "conv x \<equiv> action_converse x"
abbreviation subs (infix "\<sqsubseteq>" 50) where "subs x y \<equiv> x \<sqinter> y = x"

lemma is_allegory: shows
  "isAction R \<Longrightarrow> isAction (R\<^sup>\<circ>)"
  "isAction R \<Longrightarrow> isAction S \<Longrightarrow> \<box>R = \<box>S \<Longrightarrow> R\<box> = S\<box> \<Longrightarrow> isAction (R \<sqinter> S)"
  "\<box>R\<^sup>\<circ> = R\<box>" "R\<^sup>\<circ>\<box> = \<box>R"
  "(\<box>R)\<^sup>\<circ> = \<box>R" "R\<^sup>\<circ>\<^sup>\<circ> = R"
  "\<box>(R \<sqinter> S) = \<box>R"
  "R \<sqinter> R = R"
  "\<box>R = \<box>S \<Longrightarrow> R\<box> = S\<box> \<Longrightarrow> R \<sqinter> S = S \<sqinter> R"
  "R \<sqinter> (S \<sqinter> T) = (R \<sqinter> S) \<sqinter> T"
  "(R;S)\<^sup>\<circ> = S\<^sup>\<circ>;R\<^sup>\<circ>"
  "(R \<sqinter> S)\<^sup>\<circ> = R\<^sup>\<circ> \<sqinter> S\<^sup>\<circ>" (* for "= S\<^sup>\<circ> \<sqinter> R\<^sup>\<circ>" as in FS, definedness is needed *)
  "R ; (S \<sqinter> T) \<sqsubseteq> R ; S \<sqinter> R ; T"
  "R ; S \<sqinter> T \<sqsubseteq> (R \<sqinter> T ; S\<^sup>\<circ>) ; S"
  by(cases R,cases S,cases T,force)+

lemma ident_is_largest:
  "isAction R \<Longrightarrow> \<box>R \<sqsubseteq> R \<Longrightarrow> \<box>R = R"
  "isAction R \<Longrightarrow> \<box>R \<sqsubseteq> R ; S \<Longrightarrow> \<box>R = R"
  "isAction R \<Longrightarrow> isAction S \<Longrightarrow> R\<box> = \<box>S \<Longrightarrow> \<box>R \<sqsubseteq> R ; S \<Longrightarrow> \<box>R = S"
  by (cases R,cases S,force)+

lemma mark_converse [simp]:
  "mark (x\<^sup>\<circ>) = mark x" by(cases x,force)


lemma comm_diag_props:
  assumes "x;x2 = y;y2" "isAction x" "isAction y" "isAction x2" "isAction y2" "x\<box>=\<box>x2" "y\<box>=\<box>y2"
  shows "\<box>x=\<box>y" "x2\<box>=y2\<box>"
        "mark x \<union> mark x2 = mark y \<union> mark y2"
  using assms by (cases x,cases y,cases x2,cases y2,auto)+

lemma cycle_types:
  assumes "x2 = x\<^sup>\<circ>;y;y2" "y2 = y\<^sup>\<circ>;x;x2"
  shows "x\<box>=\<box>x2" "y\<box>=\<box>y2" "x2\<box>=y2\<box>" 
  using assms(1,2) is_allegory(3) is_category(5) by (force,metis,simp)

lemma cycle_mark:
  assumes "x2 = x\<^sup>\<circ>;y;y2" "y2 = y\<^sup>\<circ>;x;x2"
  shows   "mark x2 = mark y2"
proof -
  have "mark x2 = mark (x\<^sup>\<circ>;y;y2)" "mark y2 = mark (y\<^sup>\<circ>;x;x2)" using assms(1,2) by auto
  hence "mark x2 = mark x \<union> mark y \<union> mark y2" "mark y2 = mark x \<union> mark y \<union> mark x2" by auto
  thus ?thesis by simp
qed

lemma cycle_commutes_implies_commutes:
  assumes "x2 = x\<^sup>\<circ>;y;y2" "y2 = y\<^sup>\<circ>;x;x2" "\<box>x=\<box>y"
  shows   "x;x2 = y;y2"
proof -
  have "mark x \<union> mark x2 = mark y \<union> mark y2"
    apply (rule subset_antisym)
    using assms(1,2) case_free_comp(3) le_sup_iff sup_ge2
    by (metis)+
  thus ?thesis using cycle_types[OF assms(1,2)] assms(3) by (intro Action.expand) simp
qed


fun merge :: "'a Action \<Rightarrow> 'a Action \<Rightarrow> ('a Action \<times> 'a Action)"
  where
"merge x y = (let t = tgt x \<union> ins y - del y
               in ( Action (tgt x) t (mark x \<union> mark y)
                  , Action (tgt y) t (mark x \<union> mark y)))"

lemma merge_valid:
  assumes "(x2,y2) = merge x y" "\<box>x=\<box>y" "isAction x" "isAction y"
  shows "isAction x2" "isAction y2" "x\<box>=\<box>x2" "y\<box>=\<box>y2" "x2\<box>=y2\<box>"
  using assms by (cases x;cases y;auto simp:Let_def)+

lemma merge_commutes:
  assumes "(x2,y2) = merge x y" "\<box>x=\<box>y"
  shows "x;x2 = y;y2"
  using assms by (cases x,cases y,auto simp:Let_def)

lemma merge_cycle_commutes:
  assumes "(x2,y2) = merge x y"
  shows "x2 = x\<^sup>\<circ>;y;y2" (is ?t1) "y2 = y\<^sup>\<circ>;x;x2" (is ?t2)
proof -
  have "?t1 \<and> ?t2"
  proof (cases x)
    case x:(Action x1 x2 x3) show ?thesis proof(cases y)
      case y:(Action y1 y2 y3)
      show ?thesis using assms unfolding x y by (auto simp:Let_def)
    qed
  qed
  thus ?t1 ?t2 by blast+
qed


end