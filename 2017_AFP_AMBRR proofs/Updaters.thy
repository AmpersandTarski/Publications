(*
  File:    Increments.thy
  Author:  Sebastiaan J.C. Joosten <sjcjoosten@gmail.com>

  Proofs for Preserving Invariant Rules in Relation Algebra
*)

theory Updaters imports Increments
begin

section \<open>Linking Code Fragments to Invariants\<close>
text {*
	Now let's write some code that can preserve invariance of rules by insertion and deletion into and
  from relations.
*}

subsection \<open>Population of the system, and changes to the population\<close>
datatype ('binding,'statement,'string,'template) Population
  = Pop (p_phrase         : "('binding   \<times> 'string) set") (* \<times> can be typed by \times *)
        (p_inStatement    : "('binding   \<times> 'statement) set")
        (p_resetS         : "'statement rel") (* syntax sugar for "('statement \<times> 'statement) set" *)
        (p_substituted    : "('binding   \<times> 'statement) set")
        (p_template       : "('statement \<times> 'template) set")
        (p_tmplParsedText : "('template  \<times> 'string) set")
        (p_stmtShowText   : "('statement \<times> 'string) set")

datatype ('binding,'statement,'string,'template) Delta
  = Delta (d_insert : "('binding,'statement,'string,'template) Population")
          (d_delete : "('binding,'statement,'string,'template) Population")

fun change where
  "change (Pop   phrase   inStatement   resetS   substituted   template   tmplParsedText   stmtShowText)
   (Delta (Pop i_phrase i_inStatement i_resetS i_substituted i_template i_tmplParsedText i_stmtShowText)
          (Pop d_phrase d_inStatement d_resetS d_substituted d_template d_tmplParsedText d_stmtShowText)) =
   (Pop ((phrase          \<union> i_phrase         ) - d_phrase         )
        ((inStatement     \<union> i_inStatement    ) - d_inStatement    )
        ((resetS          \<union> i_resetS         ) - d_resetS         )
        ((substituted     \<union> i_substituted    ) - d_substituted    )
        ((template        \<union> i_template       ) - d_template       )
        ((tmplParsedText  \<union> i_tmplParsedText ) - d_tmplParsedText )
        ((stmtShowText    \<union> i_stmtShowText   ) - d_stmtShowText   )
   )"


fun augment_change where
  "augment_change
   (Delta (Pop i1_phrase i1_inStatement i1_resetS i1_substituted i1_template i1_tmplParsedText i1_stmtShowText)
          (Pop d1_phrase d1_inStatement d1_resetS d1_substituted d1_template d1_tmplParsedText d1_stmtShowText))
   (Delta (Pop i2_phrase i2_inStatement i2_resetS i2_substituted i2_template i2_tmplParsedText i2_stmtShowText)
          (Pop d2_phrase d2_inStatement d2_resetS d2_substituted d2_template d2_tmplParsedText d2_stmtShowText)) =
   (Delta (Pop (i1_phrase         \<union> i2_phrase        )
               (i1_inStatement    \<union> i2_inStatement   )
               (i1_resetS         \<union> i2_resetS        )
               (i1_substituted    \<union> i2_substituted   )
               (i1_template       \<union> i2_template      )
               (i1_tmplParsedText \<union> i2_tmplParsedText)
               (i1_stmtShowText   \<union> i2_stmtShowText  ))
          (Pop (d1_phrase         \<union> d2_phrase        )
               (d1_inStatement    \<union> d2_inStatement   )
               (d1_resetS         \<union> d2_resetS        )
               (d1_substituted    \<union> d2_substituted   )
               (d1_template       \<union> d2_template      )
               (d1_tmplParsedText \<union> d2_tmplParsedText)
               (d1_stmtShowText   \<union> d2_stmtShowText  )))"

fun delta_substituted where
  "delta_substituted ins del = (Delta (Pop {} {} {} ins {} {} {}) (Pop {} {} {} del {} {} {}))"

subsection \<open>Invariants: code for testing the invariant\<close>

fun rule_substitute where
  "rule_substitute (Pop phrase inStatement resetS substituted template tmplParsedText stmtShowText) =
     ((Id \<inter> phrase O phrase \<inverse>) O inStatement O (Id - resetS) \<subseteq> substituted)"
fun rule_substitute_violations where
  "rule_substitute_violations
     (Pop phrase inStatement resetS substituted template tmplParsedText stmtShowText) =
     (((Id \<inter> phrase O phrase \<inverse>) O inStatement O (Id - resetS)) - substituted)"
lemma no_rule_substitute_violations:
  "rule_substitute_violations p = {} \<longleftrightarrow> rule_substitute p" by(cases p,auto)

subsection \<open>Basic blocks: code for inserting and deleting\<close>
text {*
	We again start with the low hanging fruit,
	which consists of changes in a single relation
*}

definition
  "rule_substitute_action pop \<equiv> delta_substituted (rule_substitute_violations pop) {}"

lemma rule_substitute_action_preserves_invariant:
  "rule_substitute (change pop (rule_substitute_action pop))"
  by (cases pop,auto simp:rule_substitute_action_def)

end