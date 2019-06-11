(*
  File:    Increments.thy
  Author:  Stef Joosten <stef.joosten@ou.nl>

  Proofs for Preserving Invariant Rules in Relation Algebra
*)

theory Increments imports Main
begin

section \<open>Code Fragments\<close>
text {*
	Which code can preserve invariance and can we produce that code for arbitrary rules?
  That is one of the issues addressed in a paper entitled ``Ampersand uses Relation Algebra as Programming Language''~\cite{Joosten-JLAMP2017}, which uses the proofs documented in this paper.
	The question how to preserve invariance of rules in relation algebra is key for deriving code from invariants.
	The means to preserve invariance is to insert or delete a set of pairs into and from relations.

	Inserting (a set of) pairs @{term "\<Delta>"} into a relation @{term "r"} yields @{term "r\<union>\<Delta>"}.
	Likewise, deleting pairs @{term "\<Delta>"} from a relation @{term "r"} yields @{term "r-\<Delta>"}.
	The code we derive is built around the basic operations insert and delete.
	Since rules are built with relations as bricks and operators as mortar,
	we are wondering whether a change in on relation can be compensated by one or more changes in other relations.
	That is what the preservation of invariance is all about.
*}

subsection \<open>Zero step lemmas\<close>
text {*
	We will start with the low hanging fruit,
	which consists of changes in rules with boolean operators $\cup$, $\cap$, and complement.
	We use a number of properties, which we have formulated such that the changes (inserts and deletes)
	are made explicit in the formulas.
  Each lemma is given a number, which corresponds to the numbers in the accompanied paper~\cite{Joosten-JLAMP2017}.
*}
lemma "34":
  shows "r=-s \<Longrightarrow> r\<union>\<Delta>=-(s-\<Delta>)" by auto
    
lemma "35":
  shows "r=-s \<Longrightarrow> r-\<Delta>=-(s\<union>\<Delta>)" by auto
    
lemma "36":
  shows "t=r\<inter>s \<Longrightarrow> t\<union>\<Delta>=(r\<union>\<Delta>)\<inter>(s\<union>\<Delta>)" by auto
    
lemma "37":
  shows "t=r\<union>s \<Longrightarrow> t-\<Delta>=(r-\<Delta>)\<union>(s-\<Delta>)" by auto
  
lemma "38":
  shows "t=r\<inter>s \<Longrightarrow> t-\<Delta>=(r-\<Delta>)\<inter>s" by auto
    
lemma "39":
  shows "t=r\<union>s \<Longrightarrow> t\<union>\<Delta>=(r\<union>\<Delta>)\<union>s" by auto

(* The following is not needed in the publication in AFP, so I have commented it out.
subsection \<open>Proofs with intersection\<close>
text {*
	Take a term of the form @{term "r\<inter>s"}, which is the intersection of @{term "r"} and @{term "s"}.
  Suppose we insert @{term "\<Delta>"} into @{term "r"}.
	It makes us wonder what is needed in @{term "s"} to have the entire expression return to its original value.
  For symmetry reasons, we need not investigate insertion into @{term "s"}.
*}
lemma "Keep r inter s constant with Del":
  assumes "\<Delta> \<inter> r \<inter> s = -UNIV"
  shows "(r-\<Delta>)\<inter>s = r\<inter>s" (is "?lhs = ?rhs")
proof-
  have "?lhs = r \<inter> -\<Delta> \<inter> s" by auto
  also have "\<dots> = ?rhs" using assms by auto
  finally show ?thesis by auto
qed

text {*
	Take a term of the form @{term "r\<inter>s"}, and suppose we insert @{term "\<Delta>"} into that term.
  For symmetry reasons, we need not investigate insertion in @{term "s"}.
	It makes us wonder what is needed in @{term "s"} to have the entire expression return to its original value.
*}
lemma "Preserve r inter s on Del Delta from r":
  assumes "\<Delta> \<inter> r \<inter> s = -UNIV"
  shows "(r-\<Delta>)\<inter>s = r\<inter>s"
proof-
  have "(r-\<Delta>) \<inter> s = r \<inter> -\<Delta> \<inter> s" by auto
  also have "\<dots> = r \<inter> s" using assms by auto
  finally show ?thesis by auto
qed

text {*
	Take a term of the form @{term "r\<inter>s"}, and suppose we insert @{term "\<Delta>"} into @{term "r"}.
  For symmetry reasons, we need not investigate insertion in @{term "s"}.
	It makes us wonder what is needed in @{term "s"} to have the entire expression return to its original value.
*}
lemma "Keep r inter s constant with Ins":
  assumes "\<Delta> \<subseteq> r \<inter> s"
  shows "(r\<union>\<Delta>)\<inter>s = r\<inter>s" 
proof-
  have "(r\<union>\<Delta>) \<inter> s = (r\<inter>s) \<union> (\<Delta>\<inter>s)" by auto
  also have "\<dots> = r \<inter> s" using assms by auto
  finally show ?thesis by auto
qed

lemma "Preserve r inter s on Ins Delta into r":
  assumes "UNIV \<subseteq> r \<inter> s"
  shows "(r\<union>\<Delta>)\<inter>s = r\<inter>s"
proof-
  have "(r\<union>\<Delta>) \<inter> s = (r\<inter>s)" using assms by auto
  show ?thesis using assms by auto
qed

subsection \<open>Proofs with union\<close>
text {*
	Take a term of the form @{term "r\<union>s"}, and suppose we insert or delete @{term "\<Delta>"} into or from  @{term "r"} or @{term "r\<union>s"}.
	It makes us wonder what is needed to have the entire expression return to its original value.
*}
lemma "Keep r union s constant with Del":
  shows "(r-\<Delta>) \<union> (s\<union>(\<Delta>\<inter>r)) = r\<union>s" by auto

lemma "Preserve r union s on Del Delta from r":
  assumes "UNIV \<subseteq> r \<union> s"
  shows "(r-\<Delta>) \<union> (s\<union>\<Delta>) = r\<union>s"
proof-
  have "(r-\<Delta>) \<union> (s\<union>\<Delta>) = (r \<inter> -\<Delta>) \<union> s \<union> \<Delta>" by auto
  also have "\<dots> = (r\<union>s\<union>\<Delta>) \<inter> (-\<Delta>\<union>s\<union>\<Delta>)" by auto
  also have "\<dots> = r\<union>s\<union>\<Delta>" by auto
  also have "\<dots> = r\<union>s" using assms by auto
  finally show ?thesis by auto
qed

lemma "Keep r union s constant with Ins":
  assumes "\<Delta> \<subseteq> r \<union> s"
  shows "(r\<union>\<Delta>) \<union> s = r\<union>s"
proof-
  have "r \<union> \<Delta> \<union> s = r \<union> s" using assms by auto
  show ?thesis using assms by auto
qed

lemma "Preserve r union s on Ins Delta into r":
  assumes "UNIV \<subseteq> r \<union> s"
  shows "(r\<union>\<Delta>) \<union> s = r\<union>s"
proof-
  have "(r\<union>\<Delta>) \<union> s = (r\<union>s) \<union> \<Delta>" by auto
  also have "\<dots> = r \<union> s" using assms by auto
  finally show ?thesis by auto
qed
*)

subsection \<open>Proofs with relational operators\<close>
text {*
  This section studies how to insert or delete pairs into or from terms of the form @{term "r O s"}.
  We omit proofs with left residuals because they have dual counterparts with right residuals.
*}

(* right residual *)
definition residual :: "('a \<times> 'b) set \<Rightarrow> ('a \<times> 'c) set \<Rightarrow> ('b \<times> 'c) set" where
  "residual R S \<equiv> \<Union> {Q . R O Q \<subseteq> S}" (* biggest Q s.t. R O Q \<subseteq> S *)

lemma residual_RA[simp]: (* an alternative definition and proof of equivalence *)
  shows "residual R S = - (R\<inverse> O (- S))"
  proof
    show "residual R S \<subseteq> - (R\<inverse> O - S)" unfolding residual_def by auto
    have "R O (- (R\<inverse> O - S)) \<subseteq> S" by auto
    then show "- (R\<inverse> O - S) \<subseteq> residual R S" unfolding residual_def by auto
  qed

lemma 42: (* introduce NEWPAIRS *)
  assumes pre : "t = r O s"
      and newpairs : "\<Delta>\<^sub>r O \<Delta>\<^sub>s = \<Delta>-t"
      and newRpairs : "r O \<Delta>\<^sub>s \<subseteq> \<Delta>\<union>t"
      and newSpairs : "\<Delta>\<^sub>r O s \<subseteq> \<Delta>\<union>t"
  shows "t\<union>\<Delta> = (r\<union>\<Delta>\<^sub>r) O (s\<union>\<Delta>\<^sub>s)"
  proof-
    have " t\<union>\<Delta> = t\<union>(\<Delta>-t)" by simp
    also have "\<dots> = r O s \<union> \<Delta>\<^sub>r O \<Delta>\<^sub>s" by (simp add: newpairs pre)
    also have "\<dots> = r O s  \<union>  r O \<Delta>\<^sub>s  \<union>  \<Delta>\<^sub>r O s  \<union>  \<Delta>\<^sub>r O \<Delta>\<^sub>s"
      by (smt "39" calculation newRpairs newSpairs sup.orderE sup_commute)
    also have "\<dots> = (r\<union>\<Delta>\<^sub>r) O (s\<union>\<Delta>\<^sub>s)" by auto
    finally show ?thesis by auto
  qed

lemma 44: (* Keeping @{term "r O s"} constant when  @{term "r"} grows *)
  assumes defDelta: "\<Delta>\<^sub>s \<equiv> s-residual (r\<union>\<Delta>) (r O s)"
  shows "(r\<union>\<Delta>)O(s-\<Delta>\<^sub>s) \<subseteq> r O s"
proof-
  have "(r\<union>\<Delta>)O(s-\<Delta>\<^sub>s) \<subseteq> r O s \<longleftrightarrow> s-\<Delta>\<^sub>s \<subseteq> residual (r\<union>\<Delta>) (r O s)" by auto
  also have "\<dots> \<longleftrightarrow> s - residual (r\<union>\<Delta>) (r O s) \<subseteq> \<Delta>\<^sub>s" by auto
  also have "\<dots> \<longleftrightarrow>True" using defDelta by auto
  finally show ?thesis by auto
qed

lemma 47: (* Keeping @{term r O s"} constant when  @{term "r"} shrinks *)
  assumes defDelta: "\<Delta>\<^sub>s \<equiv> residual (r-\<Delta>) (r O s)"
      and defX: "x\<equiv>r-\<Delta>"
      and defY: "y\<equiv>r O s"
  shows "(r-\<Delta>)O(s\<union>\<Delta>\<^sub>s) \<subseteq> r O s"
proof-
  have "(r-\<Delta>)O(s\<union>\<Delta>\<^sub>s) \<subseteq> r O s \<longleftrightarrow> (r-\<Delta>)O \<Delta>\<^sub>s \<subseteq> r O s" by auto
  also have "... \<longleftrightarrow> (r-\<Delta>)O residual (r-\<Delta>) (r O s) \<subseteq> r O s" using defDelta by simp
  also have "... \<longleftrightarrow> x O residual x y \<subseteq> y" using defX defY by simp
  finally show ?thesis by auto
qed

lemma largest_delta_s:
  assumes defDelta: "\<Delta>\<^sub>s \<equiv> residual (r\<union>\<Delta>) (r O s)"
      and defX: "x\<equiv>r-\<Delta>"
      and defY: "y\<equiv>r O s"
  shows "(r-\<Delta>)O(s\<union>\<Delta>\<^sub>s) \<subseteq> r O s"
proof-
  have "x O residual x y \<subseteq> y \<longleftrightarrow> (r-\<Delta>) O residual (r-\<Delta>) (r O s) \<subseteq> r O s" using defX defY by auto
  also have "\<dots> \<longleftrightarrow> (r-\<Delta>) O \<Delta>\<^sub>s \<subseteq> r O s" using defDelta by auto
  also have "\<dots> \<longleftrightarrow> (r-\<Delta>) O (s\<union>\<Delta>\<^sub>s) \<subseteq> r O s" by auto
  finally show ?thesis using assms by auto
qed

text
{*Suppose we want to keep @{term "r O s"} constant,
but there is an action that deletes @{term "\<Delta>"} from  @{term "r"}.
The following derivation shows that @{term "(r - \<Delta>) O (r \<inter> \<Delta>) O s"} satisfies this requirement,
but on one condition: for every pair in @{term "r O s"} there must be a pair remaining
behind in @{term "r-\<Delta>"}.
*}

lemma 48:
  assumes deltaS         : "(r-\<Delta>)\<inverse> O (r\<inter>\<Delta>) O s \<subseteq> \<Delta>\<^sub>s"
      and totalRminDelta : "(r O s O s\<inverse> O r\<inverse>) \<inter> Id \<subseteq> (r-\<Delta>) O (r-\<Delta>)\<inverse>"
  shows "r O s \<subseteq> (r-\<Delta>) O (s\<union>\<Delta>\<^sub>s)"
proof-
  have "(r-\<Delta>)\<inverse> O (r\<inter>\<Delta>) O s \<subseteq> \<Delta>\<^sub>s" using deltaS by auto
  hence "(r-\<Delta>) O (r-\<Delta>)\<inverse> O (r\<inter>\<Delta>) O s \<subseteq> (r-\<Delta>) O \<Delta>\<^sub>s" by auto
  hence "(r\<inter>\<Delta>) O s \<subseteq> (r-\<Delta>) O \<Delta>\<^sub>s" using totalRminDelta by blast
  hence "(r-(r-\<Delta>)) O s \<subseteq> (r-\<Delta>) O \<Delta>\<^sub>s" by auto
  hence "(r O s)-((r-\<Delta>) O s) \<subseteq> (r-\<Delta>) O \<Delta>\<^sub>s" by auto
  hence "r O s \<subseteq> (r-\<Delta>) O s \<union> (r-\<Delta>) O \<Delta>\<^sub>s" by auto
  hence "r O s \<subseteq> (r-\<Delta>) O (s \<union> \<Delta>\<^sub>s)" by auto
  then show ?thesis using assms by blast
qed

end