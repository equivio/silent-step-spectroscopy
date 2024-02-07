section \<open> Hennesy-Milner-Logic (HML)\<close>
theory HML
  imports Main LTS
begin


section \<open> Hennesy-Milner-Logic (HML) \<close>

text \<open>
The mutually recursive data types \<open>hml\<close> and \<open>hml_conjunct\<close> represent arbitrary HML formulas.

In particular:
\begin{itemize}
  \item in \<open>hml\<close>
  \begin{itemize}
    \item \<open>TT\<close> encodes \<open>\<top>\<close>
    \item \<open>Obs \<alpha> \<phi>\<close> encodes \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> and is to be read as '\<open>\<alpha>\<close> can be observed and then \<open>\<phi>\<close> holds'.
    \item \<open>Internal \<phi>\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> and is to be read as 'after arbitrarily much internal behaviour \<open>\<phi>\<close> holds'.
    \item \<open>Silent \<phi>\<close> encodes \<open>(\<tau>)\<phi>\<close> and is to be read as '\<open>\<phi>\<close> holds after possibly no or exactly one internal step'.
    \item \<open>Conj I \<psi>s\<close> encodes \<open>\<And>\<Psi>\<close> where \<open>\<Psi> \<equiv> \<psi>s ` I\<close>  and is to be read as 'all formulas in \<open>\<Psi>\<close> hold'.
  \end{itemize}
  \item in \<open>hml_conjunct\<close>
  \begin{itemize}
    \item \<open>Pos \<phi>\<close> encodes \<open>\<phi>\<close> when used as a conjunct and is to be read exactly as \<open>\<phi>\<close> is.
    \item \<open>Neg \<phi>\<close> encodes \<open>\<not>\<phi>\<close> in position of a conjunct and is to be read as '\<open>\<phi>\<close> does not hold'.
  \end{itemize}
\end{itemize}

When a variable is of type \<open>hml\<close> then \<open>\<phi>\<close> is used in most cases.
In case a variable is of type \<open>hml_conjunct\<close> then \<open>\<psi>\<close> is used.

Note that in canonical definitions of HML \<open>TT\<close> is not usually given, but is instead synonymous to \<open>\<And>{}\<close>.
We include \<open>TT\<close> in the definition to enable Isabelle to infer via syntax only, that the types \<open>hml\<close>
and \<open>hml_srbb\<close> are non-empty.  If this data constructor is omitted, Isabelle will reject the definition.
\<close>


datatype 
  ('act, 'i) hml =
    TT |
    Obs 'act "('act, 'i) hml" |
    Internal "('act, 'i) hml" |
    Silent "('act, 'i) hml" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_conjunct"
and
  ('act, 'i) hml_conjunct =
    Pos "('act, 'i) hml" |
    Neg "('act, 'i) hml"


context LTS_Tau
begin

text \<open>
Definition of the meaning of an HML formula in the context of an LTS.

Note that this formalization and semantic allows for conjunctions of arbitrary width,
even of infinite width.
\<close>

primrec
      hml_models          :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
  and hml_conjunct_models :: "'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool"
where
  "(_ \<Turnstile> TT) = True" |
  "(p \<Turnstile> (Obs a \<phi>)) = (\<exists>p'. p \<mapsto> a p' \<and> (p' \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Internal \<phi>)) = (\<exists>p'. p \<Zsurj> p' \<and> (p' \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Silent \<phi>)) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (p' \<Turnstile> \<phi>)) \<or> (p \<Turnstile> \<phi>))" |
  "(p \<Turnstile> (Conj I \<psi>s)) = (\<forall>i \<in> I. hml_conjunct_models p (\<psi>s i))" |

  "(hml_conjunct_models p (Pos \<phi>)) = (p \<Turnstile> \<phi>)" |
  "(hml_conjunct_models p (Neg \<phi>)) = (\<not>(p \<Turnstile> \<phi>))"


text \<open>
While \<open>T\<close> and \<open>\<And>{}\<close> differ syntactically, they mean exactly the same thing.
Every process will satisfy both of these formulas.
\<close>
lemma tt_eq_empty_conj: "(state \<Turnstile> TT) = (state \<Turnstile> Conj {} \<psi>)"
  by simp

text \<open> \<open>\<And>{\<phi>}\<close> (i.e. the single element conjunction) is satisfied iff \<open>\<phi>\<close> is satisfied. \<close>
lemma conj_\<phi>_is_\<phi>:
  "(state \<Turnstile> \<phi>)
 = (state \<Turnstile> Conj {state} (\<lambda>i. if i = state then (Pos \<phi>) else (Pos TT)))"
  by simp

lemma opt_\<tau>_is_or: "(p \<Turnstile> (Silent \<phi>)) = ((p \<Turnstile> (Obs \<tau> \<phi>)) \<or> (p \<Turnstile> \<phi>))"
  by simp


text \<open>
\<open>HML_soft_poss \<alpha> \<phi>\<close> represents \<open>(\<alpha>)\<phi>\<close>,
which is to be interpeted as \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> if \<open>\<alpha> \<noteq> \<tau>\<close> and as \<open>(\<tau>)\<phi>\<close> otherwise.
\<close>
abbreviation HML_soft_poss :: "'a \<Rightarrow> ('a, 'i) hml \<Rightarrow> ('a, 'i) hml" where
  "HML_soft_poss \<alpha> \<phi> \<equiv> if \<alpha> = \<tau> then Silent \<phi> else Obs \<alpha> \<phi>"

text \<open>
\<open>(\<alpha>)\<phi>\<close> is satisfied if either \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> (note that here \<open>\<alpha>\<close> may be equal to \<open>\<tau>\<close>) or
if \<open>\<alpha> = \<tau>\<close> and \<open>\<phi>\<close> is already satisfied.
\<close>
lemma soft_poss_to_or[simp]:
  "p \<Turnstile> (HML_soft_poss \<alpha> \<phi>) = (p \<Turnstile> Obs \<alpha> \<phi>) \<or> (\<alpha> = \<tau> \<and> p \<Turnstile> \<phi>)"
  by auto

end (* context LTS_Tau *)

context Inhabited_LTS
begin

text \<open>
Binary conjunction (\<open>\<and>\<close>) is reduced to a conjunction over sets,
whereby the LTS needs to be inhabited so that at least two indices are available.
\<close>
abbreviation
  HML_and :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct
              \<Rightarrow> ('a, 's) hml"
  ("_ \<and>hml _" 70) where

  "left_conjunct \<and>hml right_conjunct \<equiv> 
   Conj {left, right} (\<lambda>i. if i = left
                           then left_conjunct
                           else if i = right
                                then right_conjunct
                                else Pos TT)"

end (* context Inhabited_LTS *)

context Inhabited_Tau_LTS
begin

text \<open> \<open>hml_and_and\<close> lifts satisfaction of a hml conjunction from HML logic to HOL logic. \<close>

lemma hml_and_and[simp]:
  "(p \<Turnstile> (\<psi>l \<and>hml \<psi>r))
 = (hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r)"
  unfolding hml_models.simps and hml_conjunct_models.simps
proof (rule iffI)
  assume "\<forall>i\<in>{left, right}. hml_conjunct_models p (if i = left then \<psi>l else if i = right then \<psi>r else Pos TT)"
  then have for_all_l_and_r: "\<forall>i\<in>{left, right}. (if i = left then hml_conjunct_models p \<psi>l else if i = right then hml_conjunct_models p \<psi>r else hml_conjunct_models p (Pos TT))"
    by presburger
  then show "hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r"
    by (metis Inhabited_LTS_axioms Inhabited_LTS_def insertCI)
next
  assume "hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r"
  then show "\<forall>i\<in>{left, right}. hml_conjunct_models p (if i = left then \<psi>l else if i = right then \<psi>r else Pos TT)"
    by auto
qed

end (* Inhabited_Tau_LTS *)


context Inhabited_Tau_LTS
begin

text \<open> \<open>(HML_not \<phi>)\<close> represents \<open>\<not>\<phi>\<close> and is realized via a one element conjunction. \<close>
abbreviation HML_not :: "('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "HML_not \<phi> \<equiv> Conj {left} (\<lambda>i. if i = left then (Neg \<phi>) else (Pos TT))"


text \<open> \<open>\<not>\<not>\<phi>\<close> is satisfied iff \<open>\<phi>\<close> is satisfied. \<close>
lemma hml_not_not:
  shows "(state \<Turnstile> \<phi>)
       = (state \<Turnstile> HML_not (HML_not \<phi>))"
  by simp

text \<open>
\<open>HML_not \<phi>\<close> is satisfied, iff \<open>\<phi>\<close> is not satisfied.
This lifts the negation from HML to HOL.
\<close>
lemma hml_not_not_models[simp]:
  shows "(state \<Turnstile> HML_not \<phi>) = (\<not> state \<Turnstile> \<phi>)"
  by simp

abbreviation hml_falsum :: "('a, 's) hml" ("\<bottom>\<bottom>") where
  "\<bottom>\<bottom> \<equiv> HML_not TT"

text \<open> No process ever satisfies falsum. \<close>
lemma never_models_falsum[simp]:
  shows "\<not> state \<Turnstile> \<bottom>\<bottom>"
  by simp

text \<open> \<open>(\<phi> \<or> \<phi>')\<close> represents \<open>\<phi> \<or> \<phi>'\<close> (read "or") and is realized by using binary conjunction and negation. \<close>

definition HML_or :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> ('a, 's) hml" ("_ \<or> _" 70) where
  "\<phi>l \<or> \<phi>r \<equiv> HML_not (Neg \<phi>l \<and>hml Neg \<phi>r)"

lemma hml_or_or[simp]: "(p \<Turnstile> (\<phi>l \<or> \<phi>r)) = ((p \<Turnstile> \<phi>l) \<or> (p \<Turnstile> \<phi>r))"
  unfolding HML_or_def 
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_conjunct_models.simps(2) hml_models.simps(1) hml_models.simps(5) by force

end (* context Inhabited_Tau_LTS *)


context LTS_Tau
begin

subsection \<open> Pre-Order \<close>

text \<open> An HML formula \<open>\<phi>l\<close> implies another (\<open>\<phi>r\<close>) if the fact that some process \<open>p\<close> satisfies \<open>\<phi>l\<close>
implies that \<open>p\<close> must also satisfy \<open>\<phi>r\<close>, no matter the process \<open>p\<close>. \<close>
definition hml_impl :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Rrightarrow>" 60)  where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"

lemma hml_impl_iffI:
  "\<phi>l \<Rrightarrow> \<phi>r = (\<forall>p. (p \<Turnstile> \<phi>l) \<longrightarrow> (p \<Turnstile> \<phi>r))"
  using hml_impl_def by force

text \<open> HML formula implication is a pre-order. \<close>
lemma hml_impl_preord: "reflp (\<Rrightarrow>) \<and> transp (\<Rrightarrow>)"
  by (metis hml_impl_def reflpI transpI)


text \<open> Duplicating these definitions and lemmata for the inner type \<open>hml_conjunction\<close>. \<close>

definition hml_conjunct_impl :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool"
  (infix "\<and>\<Rrightarrow>" 60) where
  "\<psi>l \<and>\<Rrightarrow> \<psi>r \<equiv> (\<forall>p. (hml_conjunct_models p \<psi>l) \<longrightarrow> (hml_conjunct_models p \<psi>r))"

lemma hml_conjunct_impl_iffI:
  "\<psi>l \<and>\<Rrightarrow> \<psi>r = (\<forall>p. (hml_conjunct_models p \<psi>l) \<longrightarrow> (hml_conjunct_models p \<psi>r))"
  unfolding hml_conjunct_impl_def by auto

lemma hml_conjunct_impl_preord: "reflp (\<and>\<Rrightarrow>) \<and> transp (\<and>\<Rrightarrow>)"
  by (metis hml_conjunct_impl_def reflpI transpI)


subsubsection \<open> Pre-Substitution \<close>

text \<open>
The following lemmata provide means to manipulate an HML implication
by substituting other HML implications into it.

This substitution may only occur on the right hand side of the implication.
A notable exception is \<open>neg_pre_subst\<close>, so when substituting into a negation, where one may only
substitute on the left hand side of the implication.
The lemmata differ in the choice of context, i.e. what formula is substituted into.
\<close>

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<langle>\<alpha>\<rangle>\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<langle>\<alpha>\<rangle>\<phi>''\<close>. \<close>
lemma obs_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms and hml_impl_def by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<langle>\<epsilon>\<rangle>\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<langle>\<epsilon>\<rangle>\<phi>''\<close>. \<close>
lemma internal_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Internal \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_impl_iffI by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<tau>)\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> (\<tau>)\<phi>''\<close>. \<close>
lemma silent_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Silent \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_impl_iffI by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<And>{\<phi>', ...}\<close> follows \<open>\<phi> \<Rrightarrow> \<And>{\<phi>'', ...}\<close>,
as long the remainder of the conjunction is unchanged. \<close>
lemma conj_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>l else \<psi>s i))"
  shows "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>r else \<psi>s i))"
  using assms and hml_impl_iffI by fastforce

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<phi>''\<close>.
This simply lifts hml implication into the \<open>hml_conjunct\<close> data type.\<close>
lemma pos_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Pos \<phi>l)" 
  shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)" 
  using assms by (simp add: hml_conjunct_impl_def hml_impl_iffI)

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<not>\<phi>' \<Rrightarrow> \<phi>\<close> follows \<open>\<not>\<phi>'' \<Rrightarrow> \<phi>\<close>.
Note that here substitution occurs on the left hand side.\<close>
lemma neg_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<and>\<Rrightarrow> \<psi>" 
  shows "(Neg \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms and hml_conjunct_impl_def hml_impl_iffI by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<alpha>)\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> (\<alpha>)\<phi>''\<close>. \<close>
lemma soft_pos_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (HML_soft_poss \<alpha> \<phi>l)"
  shows "\<phi> \<Rrightarrow> (HML_soft_poss \<alpha> \<phi>r)"
  using assms obs_pre_subst silent_pre_subst by auto

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<phi>' \<and> \<phi>o)\<close> follows \<open>\<phi> \<Rrightarrow> (\<phi>'' \<and> \<phi>o)\<close>. \<close>
lemma hml_and_left_pre_subst:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (\<phi>l \<and>hml \<phi>o)"
  shows "\<phi> \<Rrightarrow> (\<phi>r \<and>hml \<phi>o)"
  using assms hml_conjunct_impl_iffI hml_impl_iffI by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<phi>o \<and> \<phi>')\<close> follows \<open>\<phi> \<Rrightarrow> (\<phi>o \<and> \<phi>'')\<close>. \<close>
lemma hml_and_right_pre_subst:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (\<phi>o \<and>hml \<phi>l)"
  shows "\<phi> \<Rrightarrow> (\<phi>o \<and>hml \<phi>r)"
  using assms hml_conjunct_impl_iffI hml_impl_iffI by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<not>\<phi>' \<Rrightarrow> \<phi>\<close> follows \<open>\<not>\<phi>'' \<Rrightarrow> \<phi>\<close>.
Note that here substitution occurs on the left hand side.\<close>
lemma not_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
    and "HML_not \<phi>l \<Rrightarrow> \<phi>"
  shows "HML_not \<phi>r \<Rrightarrow> \<phi>"
  using assms hml_impl_iffI by auto

end (* Inhabited_Tau_LTS *)


subsubsection \<open> Pre-Congruence \<close>

text \<open>
The following lemmata provide means to manipulate an HML implication
by wrapping both sides of the implication in the same HML formula context.

The lemmata differ in the choice of context, i.e. how both sides are extended.
\<close>

context LTS_Tau
begin

text \<open> Prepending an observation (\<open>\<langle>\<alpha>\<rangle>...\<close>) preserves implication. \<close>
lemma obs_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms and hml_impl_iffI by auto

text \<open> Prepending an epsilon (\<open>\<langle>\<epsilon>\<rangle>...\<close>) preserves implication. \<close>
lemma internal_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_impl_iffI by auto

text \<open> Prepending an silent observation (\<open>(\<tau>)...\<close>) preserves implication. \<close>
lemma silent_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_impl_iffI by auto

text \<open>
Wrapping both sides of an implication in the same conjunction,
will preserve the implication.
\<close>
lemma conj_pre_cong: 
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl l \<and>\<Rrightarrow> \<psi>sr r" 
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms
  by (smt (verit) Un_insert_right hml_conjunct_impl_def hml_impl_def hml_models.simps(5) image_iff insert_iff sup_bot.right_neutral)

text \<open>
Wrapping a set of implying conjuncts in the same conjunction,
will preserve the implications.
\<close>
lemma conj_pre_congs:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i \<in> I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i"
  shows "(Conj (I \<union> I') \<psi>sl) \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms
  by (smt (verit, ccfv_threshold) LTS_Tau.hml_conjunct_impl_def UnE UnI1 hml_impl_iffI hml_models.simps(5) imageE imageI)

text \<open> Simply lifting hml implication to hml conjunct implication. \<close>
lemma pos_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Pos \<phi>l \<and>\<Rrightarrow> Pos \<phi>r"
  using assms
  by (simp add: hml_conjunct_impl_def hml_impl_iffI)

text \<open> Turning both sides of an implication into a negated conjunct will invert the implication direction.
Note: \<open>\<phi>l\<close> and \<open>\<phi>r\<close> switch sides in the conclusion! \<close>
lemma neg_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Neg \<phi>r \<and>\<Rrightarrow> Neg \<phi>l"
  using assms and hml_conjunct_impl_def hml_impl_def by auto

text \<open> Prepending an soft observation (\<open>(\<alpha>)...\<close>) preserves implication. \<close>
lemma soft_poss_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "HML_soft_poss \<alpha> \<phi>l \<Rrightarrow> HML_soft_poss \<alpha> \<phi>r"
  using assms and obs_pre_cong and silent_pre_cong 
  by auto

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> Appending a conjunct (\<open>... \<and> \<psi>\<close>) preserves implication. \<close>
lemma hml_and_left_pre_cong:
  assumes "\<psi>l \<and>\<Rrightarrow> \<psi>r"
  shows "\<psi>l \<and>hml \<psi> \<Rrightarrow> \<psi>r \<and>hml \<psi>"
  using assms and conj_pre_congs 
  by (simp add: hml_conjunct_impl_iffI hml_impl_iffI)

text \<open> Prepending a conjunct (\<open>\<psi> \<and> ...\<close>) preserves implication. \<close>
lemma hml_and_right_pre_cong:
  assumes "\<psi>l \<and>\<Rrightarrow> \<psi>r"
  shows "\<psi> \<and>hml \<psi>l \<Rrightarrow> \<psi> \<and>hml \<psi>r"
  using assms and conj_pre_congs 
  by (simp add: hml_conjunct_impl_iffI hml_impl_iffI)

text \<open> Prepending a negation (\<open>\<not>...\<close>) inverts implication. \<close>
lemma not_pre_cong:
  shows "\<phi>l \<Rrightarrow> \<phi>r
       = HML_not \<phi>r \<Rrightarrow> HML_not \<phi>l"
  using hml_impl_def by auto

end (* Inhabited_Tau_LTS *)


subsubsection \<open> Know Pre-Order Elements\<close>

context LTS_Tau
begin

text \<open> If \<open>\<phi>\<close> is satisfied, then also \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> must be satisfied. \<close>
lemma pre_\<epsilon>:
  shows "\<phi> \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable.intros(1) hml_impl_def by fastforce

text \<open> If \<open>\<phi>\<close> is satisfied, then also \<open>(\<tau>)\<phi>\<close> must be satisfied. \<close>
lemma pre_\<tau>:
  shows "\<phi> \<Rrightarrow> (Silent \<phi>)"
  using hml_impl_def by fastforce

text \<open> If \<open>\<langle>\<epsilon>\<rangle>\<langle>\<tau>\<rangle>\<phi>\<close> is satisfied, then also \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> must be satisfied. \<close>
lemma \<epsilon>_eats_\<tau>:
  shows "(Internal (Obs \<tau> \<phi>)) \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable_append_\<tau> hml_impl_def by fastforce

text \<open>If \<open>\<And>{\<psi>, ...}\<close> is satisfied, then also \<open>\<And>{...}\<close> is satisfied.
One may freely drop conjuncts, the conjunction slimmed in this way will still be satisfied. \<close>
lemma drop_conjunct:
  shows "Conj (I \<union> {s}) \<psi>s \<Rrightarrow> Conj (I - {s}) \<psi>s"
  using Un_Diff_cancel2 hml_impl_iffI by auto


subsection \<open> Equivalence \<close>

text \<open>
A HML formula \<open>\<phi>l\<close> is said to be equivalent to some other HML formula \<open>\<phi>r\<close> (written \<open>\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r\<close>)
iff process \<open>p\<close> satisfies \<open>\<phi>l\<close> iff it also satisfies \<open>\<phi>r\<close>, no matter the process \<open>p\<close>.

We have chosen to define this equivalence by appealing to HML formula implication (c.f. pre-order).
\<close>

definition hml_eq :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infix "\<Lleftarrow>\<Rrightarrow>" 60)  where
  "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

text \<open> \<open>\<Lleftarrow>\<Rrightarrow>\<close> is truly an equivalence relation. \<close>
lemma hml_eq_equiv: "equivp (\<Lleftarrow>\<Rrightarrow>)"
  by (smt (verit, del_insts) equivpI hml_eq_def hml_impl_def reflpI sympI transpI)

text \<open>
The definition given above is equivalent, i.e. formula equivalence is a biimplication on the
models predicate.
\<close>
lemma hml_eq_equality: "(\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r) = (\<forall>p.( p \<Turnstile> \<phi>l) = (p \<Turnstile> \<phi>r))"
  using hml_eq_def hml_impl_iffI by blast


definition hml_conjunct_eq :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool" (infix "\<Lleftarrow>\<and>\<Rrightarrow>" 60)  where
  "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<and>\<Rrightarrow> \<psi>r \<and> \<psi>r \<and>\<Rrightarrow> \<psi>l"

lemma hml_conjunct_eq_equiv: "equivp (\<Lleftarrow>\<and>\<Rrightarrow>)"
  by (smt (verit, best) equivpI hml_conjunct_eq_def hml_conjunct_impl_def reflpI sympI transpI)

lemma hml_conjunct_eq_equality: "(\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r) = (\<forall>p.(hml_conjunct_models p \<psi>l) = (hml_conjunct_models p \<psi>r))"
  using hml_conjunct_eq_def hml_conjunct_impl_iffI by blast


subsubsection \<open> Substitution \<close>

text \<open>
The following lemmata provide means to manipulate an HML equivalence
by substituting other HML equivalence into it.

While one may substitute on both sides of the equivalence, only substitutions on the left hand side
are shown.  If one needs a substitution on the other side one may to use \<open>hml_eq_equiv\<close>.
The lemmata differ in the choice of context, i.e. what formula is substituted into.
\<close>

lemma obs_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Obs \<alpha> \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (meson hml_eq_def hml_impl_iffI obs_pre_cong)

lemma internal_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Internal \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (simp add: hml_eq_equality)

lemma silent_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Silent \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (meson LTS_Tau.hml_impl_def LTS_Tau.silent_pre_cong hml_eq_def)

lemma conj_subst:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>l else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>r else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms
  by (smt (verit) LTS_Tau.hml_impl_iffI hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def hml_models.simps(5))

lemma pos_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Pos \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms
  by (meson LTS_Tau.hml_conjunct_eq_def LTS_Tau.hml_eq_def LTS_Tau.pos_pre_cong hml_conjunct_impl_preord transpE)

lemma neg_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Neg \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms
  by (meson LTS_Tau.neg_pre_subst hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def)

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma and_subst_right:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>l)"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>r)"
  using assms
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_equality by auto

lemma and_subst_left:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi>l \<and>hml \<psi>)"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi>r \<and>hml \<psi>)"
  using assms
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_equality by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin


subsubsection \<open> Congruence \<close>

text \<open>
The lemmata in this subsection all follow a similar form:
  Given that two formulas (\<open>\<phi>l\<close> and \<open>\<phi>r\<close>) are equivalent,
  then these two formulas wrapped in the same context are also equivalent.
The lemmata differ in the choice of context.
\<close>

text \<open> Prepending an observation (\<open>\<langle>\<alpha>\<rangle>...\<close>) preserves equivalence. \<close>
lemma obs_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms
  by (meson hml_eq_def hml_impl_def hml_models.simps(2))

text \<open> Prepending an epsilon (\<open>\<langle>\<epsilon>\<rangle>...\<close>) preserves equivalence. \<close>
lemma internal_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_eq_def and hml_impl_def by auto

text \<open> Prepending a silent observation (\<open>(\<tau>)...\<close>) preserves equivalence. \<close>
lemma silent_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_eq_def and hml_impl_def by auto

text \<open>
Wrapping two equivalent conjunction formulas in otherwise the same conjunction,
will result in two equivalent conjunctions.
\<close>
lemma conj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "(\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r)"
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms
proof -
  assume "\<psi>sl ` I = \<psi>sr ` I"
     and "(\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r)"
  hence "(\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r))
       \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l))"
    unfolding hml_conjunct_eq_def
          and hml_conjunct_impl_def by auto
  then have
        IHL: "\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r)"
    and IHR: "\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l)" 
    apply blast 
    using \<open>(\<forall>p. hml_conjunct_models p (\<psi>sl l) \<longrightarrow> hml_conjunct_models p (\<psi>sr r)) \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr r) \<longrightarrow> hml_conjunct_models p (\<psi>sl l))\<close> by blast
  
  show "(Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
    unfolding hml_eq_def
          and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {l}) \<psi>sl \<longrightarrow> p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {l}) \<psi>sl"
      hence "\<forall>i\<in>I \<union> {l}. hml_conjunct_models p (\<psi>sl i)"
        unfolding hml_models.simps.
      then have "hml_conjunct_models p (\<psi>sl l)"
        by blast
      then have "hml_conjunct_models p (\<psi>sr r)"
        using IHL by simp
      then show "p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
        using \<open>\<psi>sl ` I = \<psi>sr ` I\<close> 
        by (smt (verit) Un_insert_right \<open>\<forall>i\<in>I \<union> {l}. hml_conjunct_models p (\<psi>sl i)\<close> hml_models.simps(5) image_iff insert_iff sup_bot.right_neutral)
    qed
  next
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {r}) \<psi>sr \<longrightarrow> p \<Turnstile> Conj (I \<union> {l}) \<psi>sl"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {r}) \<psi>sr"
      hence "\<forall>i\<in>I \<union> {r}. hml_conjunct_models p (\<psi>sr i)"
        unfolding hml_models.simps.
      then have "hml_conjunct_models p (\<psi>sr r)"
        by blast
      then have "hml_conjunct_models p (\<psi>sl l)"
        using IHR by simp
      then show " p \<Turnstile> Conj (I \<union> {l}) \<psi>sl" 
        by (smt (verit, best) Un_empty_right Un_insert_right \<open>\<forall>i\<in>I \<union> {r}. hml_conjunct_models p (\<psi>sr i)\<close> \<open>\<psi>sl ` I = \<psi>sr ` I\<close> hml_models.simps(5) image_iff insert_iff)
    qed
  qed
qed

text \<open>
Wrapping two equivalent conjunction formulas in otherwise the same conjunction,
will result in two equivalent conjunctions.
This differs from \<open>conj_cong\<close> in how the index set is extended.
\<close>
lemma conj_cong':
  assumes "s \<notin> I"
      and "\<psi>sl ` I = \<psi>sr ` I"
      and "(\<psi>sl s) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr s)"
  shows "(Conj (I \<union> {s}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {s}) \<psi>sr)"
  using assms and conj_cong by presburger

text \<open>
Wrapping two sets of equivalent conjunction formulas in otherwise the same conjunction,
will result in two equivalent conjunctions.
\<close>
lemma conj_congs:
  assumes "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
      and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  shows "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms
proof -
  assume "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
     and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  hence conjunct_eq: "\<forall>i\<in>I'. (\<forall>p. hml_conjunct_models p (\<psi>sl i) \<longrightarrow> hml_conjunct_models p (\<psi>sr i))
                   \<and> (\<forall>p. hml_conjunct_models p (\<psi>sr i) \<longrightarrow> hml_conjunct_models p (\<psi>sl i))"
    unfolding hml_conjunct_eq_def and hml_conjunct_impl_def by auto
  show "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
    unfolding hml_eq_def and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> I') \<psi>sl \<longrightarrow> p \<Turnstile> Conj (I \<union> I') \<psi>sr"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> I') \<psi>sl"
      hence "(\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i))
           \<and> (\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i))" 
        by simp
      then have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i)"
            and "\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i)" by blast+

      from \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>sl i)\<close>
       and \<open>\<forall>i\<in>I. \<psi>sl i = \<psi>sr i\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>sr i)" 
        by force

      from conjunct_eq
       and \<open>\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sl i)\<close>
      have "\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sr i)" 
        by blast

      from \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>sr i)\<close>
       and \<open>\<forall>i\<in>I'. hml_conjunct_models p (\<psi>sr i)\<close>
      show "p \<Turnstile> Conj (I \<union> I') \<psi>sr"
        unfolding hml_models.simps 
        by blast
    qed
  next
    show "\<forall>p. p \<Turnstile> Conj (I \<union> I') \<psi>sr \<longrightarrow> p \<Turnstile> Conj (I \<union> I') \<psi>sl" 
      using Un_iff \<open>\<forall>i\<in>I. \<psi>sl i = \<psi>sr i\<close> conjunct_eq by auto
  qed
qed

text \<open>
Wrapping two sets of equivalent conjunction formulas in otherwise the same conjunction,
will result in two equivalent conjunctions.
This differs from \<open>conj_congs\<close> in how the index set is extended.
\<close>
lemma conj_congs':
  assumes "I \<inter> I' = {}"
      and "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
      and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  shows "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms and conj_congs by presburger

text \<open> Two equivalent formulas are also equivalent when used as conjuncts. \<close>
lemma pos_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>r)"
  using assms
  by (simp add: hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_def hml_impl_def)

text \<open> Two equivalent formulas are also equivalent when negated. \<close>
lemma neg_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
  using assms
  by (meson hml_conjunct_eq_def hml_conjunct_impl_def hml_conjunct_models.simps(2) hml_eq_def hml_impl_def)

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma and_cong_right:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
  shows "(\<psi> \<and>hml \<psi>l) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>r)"
  using assms
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_equality by auto

lemma and_cong_left:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
  shows "(\<psi>l \<and>hml \<psi>) \<Lleftarrow>\<Rrightarrow> (\<psi>r \<and>hml \<psi>)"
  using assms
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_eq_equality by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin


subsubsection \<open> Know Equivalence Elements\<close>

text \<open> \<open>\<langle>\<epsilon>\<rangle>(\<tau>)\<phi>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> \<close>
lemma \<epsilon>\<tau>_is_\<tau>: "(Internal (Silent \<phi>)) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  unfolding hml_eq_def
proof (rule conjI)
  from pre_\<tau>
  have "\<phi> \<Rrightarrow> (Silent \<phi>)".
  then show "Internal \<phi> \<Rrightarrow> Internal (Silent \<phi>)"
    using internal_pre_cong by simp
next
  show "Internal (Silent \<phi>) \<Rrightarrow> Internal \<phi>"
    unfolding hml_impl_def
  proof (rule allI, rule impI)
    fix p
    assume "p \<Turnstile> Internal (Silent \<phi>)"
    hence "p \<Turnstile> Internal \<phi> \<or> p \<Turnstile> Internal (Obs \<tau> \<phi>)" by auto
    then show "p \<Turnstile> Internal \<phi>"
      apply (rule disjE) apply assumption
    proof -
      assume "p \<Turnstile> Internal (Obs \<tau> \<phi>)"
      then show "p \<Turnstile> Internal \<phi>"
        using \<epsilon>_eats_\<tau> and hml_impl_iffI by simp
    qed
  qed
qed

text \<open> \<open>\<langle>\<epsilon>\<rangle>\<top>\<close> is equivalent to \<open>\<top>\<close> \<close>
lemma \<epsilon>T_is_T: "(Internal TT) \<Lleftarrow>\<Rrightarrow> TT"
  by (simp add: LTS_Tau.pre_\<epsilon> hml_eq_def hml_impl_def)

fun n_\<epsilon>\<tau>s_then :: "nat \<Rightarrow> ('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "n_\<epsilon>\<tau>s_then 0 cont = cont" |
  "n_\<epsilon>\<tau>s_then (Suc n) cont = (Internal (Silent (n_\<epsilon>\<tau>s_then n cont)))"

text \<open> \<open>[\<langle>\<epsilon>\<rangle>(\<tau>)]^n \<langle>\<epsilon>\<rangle>\<phi>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> \<close>
lemma \<epsilon>\<tau>_stack_reduces: "n_\<epsilon>\<tau>s_then n (Internal \<phi>) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  apply (induct n)
  apply (simp add: LTS_Tau.hml_impl_iffI hml_eq_def)
  unfolding n_\<epsilon>\<tau>s_then.simps(2)
  using \<epsilon>\<tau>_is_\<tau>
  by (smt (verit, del_insts) hml_eq_def hml_impl_iffI hml_models.simps(3) pre_\<epsilon> silent_reachable_trans)

text \<open> wrapping two equivalent formulas into n \<open>\<langle>\<epsilon>\<rangle>(\<tau>)\<close> prefixes, yields two equivalent formulas. \<close>
lemma n_\<epsilon>\<tau>s_then_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "n_\<epsilon>\<tau>s_then n \<phi>l \<Lleftarrow>\<Rrightarrow> n_\<epsilon>\<tau>s_then n \<phi>r"
  using assms
  by (induct n) (simp add: internal_cong silent_cong)+

text \<open> \<open>[\<langle>\<epsilon>\<rangle>(\<tau>)]^n\<top>\<close> is equivalent to \<open>\<top>\<close> \<close>
lemma "n_\<epsilon>\<tau>s_then n TT \<Lleftarrow>\<Rrightarrow> TT"
  using n_\<epsilon>\<tau>s_then_cong
    and \<epsilon>\<tau>_stack_reduces
    and \<epsilon>T_is_T
    and equivp_def
    and hml_eq_equiv
  by metis

text \<open> \<open>\<top>\<close> is equivalent to \<open>\<And>{}\<close> \<close>
lemma T_is_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Conj {} \<psi>s"
  using tt_eq_empty_conj
    and hml_eq_equality
  by blast

text \<open> \<open>\<top>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<And>{}\<close> \<close>
lemma T_is_\<epsilon>_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using \<epsilon>T_is_T
     and T_is_empty_conj
  by (meson LTS_Tau.internal_subst equivp_symp hml_eq_equiv)

lemma soft_\<tau>_is_silent:
  assumes "\<alpha> = \<tau>"
  shows "Silent \<phi> \<Lleftarrow>\<Rrightarrow> HML_soft_poss \<alpha> \<phi>"
  using assms by (simp add: hml_eq_equality)

lemma soft_non_\<alpha>_is_obs:
  assumes "\<alpha> \<noteq> \<tau>"
  shows "Obs \<alpha> \<phi> \<Lleftarrow>\<Rrightarrow> HML_soft_poss \<alpha> \<phi>"
  using assms
    and hml_eq_equality
  by auto

end

context Inhabited_Tau_LTS
begin

text \<open> \<open>\<phi>l \<and> \<phi>r\<close> is equivalent to \<open>\<phi>r \<and> \<phi>l\<close> \<close>
lemma hml_and_commutative: "(\<phi>l \<and>hml \<phi>r) \<Lleftarrow>\<Rrightarrow> (\<phi>r \<and>hml \<phi>l)"
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_eq_equality by fastforce


text \<open> \<open>\<top> \<and> \<phi>\<close> is equivalent to \<open>\<phi>\<close> \<close>
lemma hml_and_left_tt: "(Pos TT \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_eq_equality by fastforce

text \<open> \<open>\<phi> \<and> \<top>\<close> is equivalent to \<open>\<phi>\<close> \<close>
lemma hml_and_right_tt: "(Pos \<phi> \<and>hml Pos TT) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using hml_and_commutative and hml_and_left_tt
  by (simp add: hml_eq_equality)

text \<open> \<open>\<phi> \<and> \<phi>\<close> is equivalent to \<open>\<phi>\<close> \<close>
lemma hml_and_same_no_and: "(Pos \<phi> \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  by (simp add: hml_eq_equality)

text \<open> \<open>\<And>({\<psi>} \<union> \<Psi>)\<close> is equivalent to \<open>\<psi> \<and> \<And>\<Psi>\<close> \<close>
lemma conj_extract_conjunct:
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml Pos (Conj I \<psi>s))"
  using assms
proof -
  assume "s \<notin> I"
  show "Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml Pos (Conj I \<psi>s))"
    unfolding hml_eq_def and hml_impl_def
  proof (rule conjI)
    show "\<forall>p. p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<longrightarrow> p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)"
      with \<open>s \<notin> I\<close>
      have "p \<Turnstile> Conj I \<psi>s \<and> hml_conjunct_models p \<psi>"
        by (smt (verit, ccfv_threshold) IntE Un_Int_eq(3) Un_upper2 hml_models.simps(5) singletonI subsetD)
      then have "p \<Turnstile> Conj I \<psi>s" and "hml_conjunct_models p \<psi>"
        by auto

      show "p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
        unfolding hml_and_and
      proof (rule conjI)
        from \<open>hml_conjunct_models p \<psi>\<close>
        show "hml_conjunct_models p \<psi>".
      next
        from \<open>p \<Turnstile> Conj I \<psi>s\<close>
        show "hml_conjunct_models p (Pos (Conj I \<psi>s))"
          unfolding hml_conjunct_models.simps.
      qed
    qed
  next
    show "\<forall>p. p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s) \<longrightarrow> p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)"
    proof (rule allI, rule impI)
      fix p
      assume "p \<Turnstile> \<psi> \<and>hml Pos (Conj I \<psi>s)"
      then have "hml_conjunct_models p \<psi> \<and> hml_conjunct_models p (Pos (Conj I \<psi>s))"
        using hml_and_and by simp
      then show "p \<Turnstile> Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i)" 
        by simp
    qed
  qed
qed

text \<open> \<open>\<And>({\<top>} \<union> \<Psi>)\<close> is equivalent to \<open>\<And>\<Psi>\<close> \<close>
lemma
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> Conj I \<psi>s"
  using assms
proof -
  assume "s \<notin> I"
  then have "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (Pos TT \<and>hml Pos (Conj I \<psi>s))"
    by (rule conj_extract_conjunct)
  with hml_and_left_tt
  show "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> Conj I \<psi>s"
    by (meson equivp_transp hml_eq_equiv)
qed

text \<open> \<open>(\<tau>)\<phi>\<close> is equivalent to \<open>\<langle>\<tau>\<rangle>\<phi> \<or> \<phi>\<close> \<close>
lemma silent_is_or: "(Silent \<phi>) \<Lleftarrow>\<Rrightarrow> ((Obs \<tau> \<phi>) \<or> \<phi>)"
  unfolding hml_eq_equality
        and hml_or_or
        and opt_\<tau>_is_or
  by (rule allI, rule refl)

text \<open> \<open>\<phi>\<close> is equivalent to \<open>\<not>\<not>\<phi>\<close> \<close>
lemma hml_not_not_eq: "\<phi> \<Lleftarrow>\<Rrightarrow> HML_not (HML_not \<phi>)"
  unfolding hml_eq_equality
  using hml_not_not by auto

text \<open> \<open>\<phi> \<and> \<not>\<phi>\<close> is equivalent to \<open>\<bottom>\<close> \<close>
lemma hml_absurdity:
  shows "Pos \<phi> \<and>hml Neg \<phi> \<Lleftarrow>\<Rrightarrow> \<bottom>\<bottom>"
  by (smt (verit) Inhabited_LTS_axioms Inhabited_LTS_def LTS_Tau.hml_eq_equality hml_conjunct_models.simps(1) hml_conjunct_models.simps(2) hml_models.simps(5) insertCI never_models_falsum)

text \<open> \<open>\<phi> \<or> \<not>\<phi>\<close> is equivalent to \<open>\<top>\<close> \<close>
lemma hml_tertium_non_datur:
  shows "TT \<Lleftarrow>\<Rrightarrow> (\<phi> \<or> HML_not \<phi>)"
  using hml_absurdity and hml_not_not_eq 
  by (simp add: hml_eq_equality)

subsection \<open> HML Equivalence X HML Pre-Order \<close>

text \<open>
These lemmata provide means to substitute HML equivalences and implications into each other,
thereby providing further support for equational reasoning on HML formulas.
Of note is the fact that this always yields an HML implication.
\<close>

subsubsection \<open> Observations \<open>\<langle>\<alpha>\<rangle>...\<close> \<close>

lemma obs_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Obs \<alpha> \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Obs \<alpha> \<phi>r) \<Rrightarrow> \<phi>"
  using assms by (meson hml_impl_iffI hml_eq_def obs_pre_cong)

lemma obs_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)" 
  using assms and hml_eq_def and obs_pre_subst by blast

lemma obs_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms by (simp add: hml_eq_def obs_pre_subst)

subsubsection \<open> Internal Behavior \<open>\<langle>\<epsilon>\<rangle>...\<close> \<close>

lemma internal_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Internal \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Internal \<phi>r) \<Rrightarrow> \<phi>"
  using assms by (meson hml_impl_iffI hml_eq_def internal_pre_cong)

lemma internal_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Internal \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms using hml_eq_def internal_pre_subst by blast

lemma internal_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Internal \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms and hml_eq_def and internal_pre_subst by blast

subsubsection \<open> Silent Step \<open>(\<tau>)...\<close> \<close>

lemma silent_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Silent \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Silent \<phi>r) \<Rrightarrow> \<phi>"
  using assms by (simp add: hml_eq_equality hml_impl_iffI)

lemma silent_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Silent \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_eq_def and silent_pre_subst by blast

lemma silent_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Silent \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms and hml_eq_def and silent_pre_subst by blast

subsubsection \<open> Conjunctions \<open>\<And>\<Psi>\<close> \<close>

lemma conjunction_left_impl_subst_equal:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<Lleftarrow>\<and>\<Rrightarrow> \<psi>sr i"
      and "(Conj (I \<union> I') \<psi>sl) \<Rrightarrow> \<phi>"
    shows "(Conj (I \<union> I') \<psi>sr) \<Rrightarrow> \<phi>"
  using assms by (smt (verit, del_insts) hml_conjunct_eq_def conj_pre_congs hml_impl_preord transp_def)

lemma conjunction_right_impl_subst_equal:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<Lleftarrow>\<and>\<Rrightarrow> \<psi>sr i"
      and "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sl)"
    shows "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms by (meson hml_conjunct_eq_def conj_pre_congs hml_impl_iffI)

lemma conjunction_equal_subst_impl:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sl)"
    shows "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms by (meson conj_pre_congs hml_eq_def hml_impl_iffI)

subsubsection \<open> Positive Conjunct \<close>

lemma conjunct_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Pos \<phi>l) \<and>\<Rrightarrow> \<psi>"
    shows "(Pos \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms hml_conjunct_impl_def hml_eq_def pos_pre_cong by auto

lemma conjunct_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Pos \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)" 
  using assms and hml_eq_def and pos_pre_subst by blast

lemma conjunct_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)"
  using assms by (simp add: hml_conjunct_eq_def pos_pre_subst)

subsubsection \<open> Negative Conjunct \<close>

lemma neg_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<and>\<Rrightarrow> \<psi>"
    shows "(Neg \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms and hml_eq_def and neg_pre_subst by blast

lemma neg_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Neg \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Neg \<phi>r)" 
  using assms by (meson hml_impl_iffI hml_conjunct_impl_def hml_conjunct_models.simps(2) hml_eq_def)

lemma neg_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
    shows "\<psi> \<and>\<Rrightarrow> (Neg \<phi>l)"
  using assms by (meson hml_conjunct_impl_def hml_conjunct_eq_def neg_pre_cong)

subsubsection \<open> Negation \<close>

lemma not_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "HML_not \<phi>l \<Rrightarrow> \<phi>"
    shows "HML_not \<phi>r \<Rrightarrow> \<phi>"
  using assms by (smt (verit) hml_conjunct_impl_def hml_eq_def hml_impl_iffI hml_models.simps(5) neg_pre_cong)

lemma not_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> HML_not \<phi>l"
    shows "\<phi> \<Rrightarrow> HML_not \<phi>r"
  using assms by (smt (verit) hml_conjunct_impl_def hml_eq_def hml_impl_iffI hml_models.simps(5) neg_pre_cong)

lemma not_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> HML_not \<phi>r"
    shows "\<phi> \<Rrightarrow> HML_not \<phi>l"
  using assms by (smt (verit) hml_conjunct_impl_def hml_eq_def hml_impl_iffI hml_models.simps(5) neg_pre_cong)

subsubsection \<open> And, i.e. Binary Conjunction \<close>

lemma and_lr_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi> \<and>hml \<phi>l \<Rrightarrow> \<phi>'"
    shows "\<phi> \<and>hml \<phi>r \<Rrightarrow> \<phi>'"
  using assms by (simp add: LTS_Tau.hml_impl_iffI hml_conjunct_eq_def hml_conjunct_impl_def)

lemma and_ll_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>l \<and>hml \<phi> \<Rrightarrow> \<phi>'"
    shows "\<phi>r \<and>hml \<phi> \<Rrightarrow> \<phi>'"
  using assms by (simp add: LTS_Tau.hml_impl_iffI hml_conjunct_eq_def hml_conjunct_impl_def)

lemma and_rr_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>l"
    shows "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>r"
  using assms hml_conjunct_eq_def hml_conjunct_impl_def hml_impl_iffI hml_models.simps(5) by auto

lemma and_rl_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Rrightarrow> \<phi>l \<and>hml \<phi>"
    shows "\<phi>' \<Rrightarrow> \<phi>r \<and>hml \<phi>"
  using assms hml_conjunct_eq_def hml_conjunct_impl_def hml_impl_iffI hml_models.simps(5) by auto

lemma and_left_equal_subst_impl:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Lleftarrow>\<Rrightarrow> \<phi>l \<and>hml \<phi>"
    shows "\<phi>' \<Rrightarrow> \<phi>r \<and>hml \<phi>"
  using assms by (simp add: LTS_Tau.hml_conjunct_impl_def hml_eq_equality hml_impl_def)

lemma and_right_equal_subst_impl:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Lleftarrow>\<Rrightarrow> \<phi> \<and>hml \<phi>l"
    shows "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>r"
  using assms by (simp add: hml_conjunct_impl_def hml_eq_equality hml_impl_def)

subsubsection \<open> Falsum and Verum \<close>

text \<open> If satisfaction of a formula entails that falsum must be satisfied means that this formula
can never be satisfied. \<close>
lemma entails_falsum_equals_falsum:
  assumes "\<phi> \<Rrightarrow> \<bottom>\<bottom>"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> \<bottom>\<bottom>"
  using assms 
  by (simp add: LTS_Tau.hml_eq_equality LTS_Tau.hml_impl_iffI)

text \<open> If we can show that verum entails the satisfaction of a formula, the formula must be equivalent
to verum. \<close>
lemma follows_verum_equals_verum:
  assumes "TT \<Rrightarrow> \<phi>"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> TT"
  using assms 
  by (simp add: LTS_Tau.hml_eq_equality LTS_Tau.hml_impl_iffI)

end (* Inhabited_Tau_LTS *)

subsection \<open> Distinguishing Formulas \<close>

context LTS_Tau
begin

text \<open> A formula is said to distinguish two processes iff one process satisfies the formula,
while the other does not. \<close>

definition distinguishes_hml :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's \<Rightarrow> bool" ("_ <> _ _" [70, 70, 70] 80) where
  "(p <> \<phi> q) \<equiv> (p \<Turnstile> \<phi>) \<and> \<not>(q \<Turnstile> \<phi>)"

text \<open> The formula \<open>\<top>\<close> can not distinguish anything. This holds since for a formula to distinguish
two processes, one process must not satisfy given formula, but \<open>\<top>\<close> is satisfied by all processes. \<close>
lemma vertum_cant_distinguish:
  shows "\<not> (p <> TT q)"
  using distinguishes_hml_def by simp

text \<open> No matter the formula chosen, a process may never be distinguished from itself. \<close>
lemma cant_self_distinguish:
  shows "\<not> (p <> \<phi> p)"
  using distinguishes_hml_def by simp

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> If a formula \<open>\<phi>\<close> distinguishes the processes \<open>p\<close> and \<open>q\<close> then the inverted formula
(i.e. \<open>\<not>\<phi>\<close>) will distinguish both processes, but in inverted order. \<close>
lemma inverted_distinguishes:
  shows "(p <> \<phi> q) = (q <> (HML_not \<phi>) p)"
  using distinguishes_hml_def by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin

text \<open>The previous definitions and lemmata need to be replicated for the inner type \<open>hml_conjunct\<close>.\<close>

definition distinguishes_conjunct_hml ::"'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes_conjunct_hml p \<psi> q \<equiv> (hml_conjunct_models p \<psi>) \<and> \<not>(hml_conjunct_models q \<psi>)"


text\<open>One may lift this notion to sets of processes, i.e. that a formula distinguishes a singular processes
from a whole set of processes iff this formula distinguishes the processes from each processes
in the set (\<open>distinguishes_from_hml'\<close>).
For this project, we require a stronger notion of this lifted predicate, namely, that the process \<open>p\<close>
must satisfy the distinguishing formula \<open>\<phi>\<close> while all processes in \<open>Q\<close> must not (\<open>distinguishes_from_hml\<close>).  
This differs from the other way of lifting in that \<open>p\<close> must satisfy the formula even if the set of
processes to distinguish from \<open>Q\<close> is empty.\<close>

definition distinguishes_from_hml :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's set \<Rightarrow> bool" ("_ <> _ _" [70, 70, 70] 80) where
  "(p <> \<phi> Q) \<equiv> (p \<Turnstile> \<phi>) \<and> (\<forall>q \<in> Q. \<not>(q \<Turnstile> \<phi>))"

definition distinguishes_from_hml' :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's set \<Rightarrow> bool" where
  "(distinguishes_from_hml' p \<phi> Q) \<equiv> (\<forall>q \<in> Q. p <> \<phi> q)"

lemma distinguishes_from_hml_prime:
  assumes "Q \<noteq> {}"
  shows "(p <> \<phi> Q) = distinguishes_from_hml' p \<phi> Q"
  using distinguishes_from_hml_def assms distinguishes_from_hml'_def distinguishes_hml_def by fastforce

lemma distinguishes_from_hml_priming:
  fixes Q :: "'s set"
  assumes "p <> \<phi> Q"
  shows "distinguishes_from_hml' p \<phi> Q"
  using assms distinguishes_from_hml'_def distinguishes_from_hml_prime by blast


definition distinguishes_conjunct_from_hml :: "'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> 's set \<Rightarrow> bool" where
  "(distinguishes_conjunct_from_hml p \<psi> Q) \<equiv> (hml_conjunct_models p \<psi>) \<and> (\<forall>q \<in> Q. \<not>(hml_conjunct_models q \<psi>))"

definition distinguishes_conjunct_from_hml' :: "'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> 's set \<Rightarrow> bool" where
  "(distinguishes_conjunct_from_hml' p \<psi> Q) \<equiv> (\<forall>q \<in> Q. distinguishes_conjunct_hml p \<psi> q)"

lemma distinguishes_conjunct_from_hml_prime:
  assumes "Q \<noteq> {}"
  shows "(distinguishes_conjunct_from_hml p \<phi> Q) = distinguishes_conjunct_from_hml' p \<phi> Q"
  by (meson distinguishes_conjunct_from_hml_def distinguishes_conjunct_hml_def assms distinguishes_conjunct_from_hml'_def equals0I)

lemma distinguishes_conjunct_from_hml_priming:
  assumes "distinguishes_conjunct_from_hml p \<phi> Q"
  shows "distinguishes_conjunct_from_hml' p \<phi> Q"
  by (meson distinguishes_conjunct_from_hml_def distinguishes_conjunct_hml_def assms distinguishes_conjunct_from_hml'_def equals0I)

text \<open> If a conjunction distinguishes a processes \<open>p\<close> from another process \<open>q\<close> then there must be
at least one conjunct in this conjunction that on its own distinguishes \<open>p\<close> from \<open>q\<close>. \<close>

lemma dist_conjunction_implies_dist_conjunct:
  fixes q :: 's
  assumes "p <> (Conj I \<psi>s) q"
  shows "\<exists>i\<in>I. distinguishes_conjunct_hml p (\<psi>s i) q"
  using assms distinguishes_conjunct_hml_def distinguishes_hml_def by auto

text \<open> Inversely, If there is a conjunct that distinguishes \<open>p\<close> from \<open>q\<close>, then a conjunction containing
this conjunct will itself distinguish \<open>p\<close> from \<open>q\<close>, provided that \<open>p\<close> satisfies all other conjuncts
as well.\<close>

lemma dist_conjunct_implies_dist_conjunction:
  fixes q :: 's
  assumes "i\<in>I"
      and "distinguishes_conjunct_hml p (\<psi>s i) q" 
      and "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"
  shows "p <> (Conj I \<psi>s) q"
  using assms distinguishes_conjunct_hml_def distinguishes_hml_def
  by auto


subsubsection \<open> Distinguishing Conjunction Thinning \<close>

text \<open>
This subsection provides proofs regarding conjunctions that distinguish a process \<open>p\<close> from a set of
processes \<open>Q\<close>.
In particular the property of distinguishing conjunction thinning is proven.

This property states that if a conjunction distinguishes \<open>p\<close> from \<open>Q\<close> with some arbitrary index set
\<open>I\<close>, then one can construct another conjunction with the index set \<open>Q\<close> (i.e. with one conjunct per
process to be distinguished from) that also distinguished \<open>p\<close> from \<open>Q\<close>.

Intuitively, this proposition should hold, since for the conjunction to distinguish from \<open>Q\<close> it must
contain at least one conjunct for each element \<open>q\<close> of \<open>Q\<close> that is not satisfied by \<open>q\<close>.
One may now constructed the 'thinned' conjunction with index set \<open>Q\<close> by picking for each \<open>q\<close> in \<open>Q\<close>
a conjunct that \<open>q\<close> does not satisfy, thereby guaranteeing that all elements of \<open>Q\<close> can not satisfy
this new conjunction.
The process \<open>p\<close> must still satisfy this new conjunction since all conjuncts originate from the old
conjunction which \<open>p\<close> satisfies and thereby all conjuncts hold for \<open>p\<close>. Said in another way: since
no new conjuncts are constructed there is no opportunity for p to not satisfy the new conjunction.
\<close>

text \<open>The following proof is a prove of a underspecified variant of the distinguishing conjunction thinning.
It is underspecified in the sense that we do not know anything about the new set of conjuncts.
For purposes of the silent step spectroscopy, this is problematic, since we might want to relate the
expressiveness price of the new distinguishing conjunction to the old distinguishing conjunction.
The proof diverges from the proof sketch given above in that the new conjunction simply copies the
old conjunction in each new conjunct.
\<close>
lemma
  fixes Q :: "'s set"
  assumes "p <> (Conj I \<psi>s) Q"
  shows "\<exists>\<psi>s'. p <> (Conj Q \<psi>s') Q"
  using assms
  unfolding distinguishes_from_hml_def and distinguishes_hml_def
proof -
  assume "p \<Turnstile> Conj I \<psi>s \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s)"

  define \<psi>s' :: "'s \<Rightarrow> ('a, 's) hml_conjunct" where
    "\<psi>s' \<equiv> (\<lambda>_. Pos (Conj I \<psi>s))"

  from \<open>p \<Turnstile> Conj I \<psi>s \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s)\<close>
  have "p \<Turnstile> Conj Q \<psi>s' \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Conj Q \<psi>s')"
    by (simp add: \<psi>s'_def)

  then show "\<exists>\<psi>s'. p \<Turnstile> Conj Q \<psi>s' \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Conj Q \<psi>s')" by auto
qed

text \<open> This is the main proof and implements the proof sketch given above. \<close>
lemma dist_conj_thinning:
  fixes Q :: "'s set"
  assumes "p <> (Conj I \<psi>s) Q"
  shows "p <> (Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i))))) Q"
  using assms
proof -
  assume "p <> Conj I \<psi>s Q"
  hence conj_dist_from_Q: "p \<Turnstile> Conj I \<psi>s \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s)"
    unfolding distinguishes_from_hml_def and distinguishes_hml_def.

  show "p <> (Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i))))) Q"
    unfolding distinguishes_from_hml_def and distinguishes_hml_def
  proof (rule conjI)
    from conj_dist_from_Q
    have "p \<Turnstile> Conj I \<psi>s" and "\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s" by auto

    from \<open>\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s\<close>
    have "\<forall>q\<in>Q. \<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)"
      using hml_models.simps(5) by blast

    from \<open>p \<Turnstile> Conj I \<psi>s\<close>
    have "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"
      unfolding hml_models.simps.

    have "\<forall>q'\<in>Q. hml_conjunct_models p (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i)))"
    proof (rule ballI)
      fix q'
      assume "q' \<in> Q"
      with \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)\<close>
       and \<open>\<forall>q\<in>Q. \<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)\<close>
      show "hml_conjunct_models p (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i)))" 
        by (metis (no_types, lifting) tfl_some)
    qed

    then show "p \<Turnstile> Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)))"
      unfolding hml_models.simps.
  next
    from conj_dist_from_Q
    have "p \<Turnstile> Conj I \<psi>s" and "\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s" by auto

    from \<open>\<forall>q\<in>Q. \<not> q \<Turnstile> Conj I \<psi>s\<close>
    have "\<forall>q\<in>Q. \<exists>i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)"
      using hml_models.simps(5) by blast

    then have "\<forall>q\<in>Q. \<not>(hml_conjunct_models q (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i))))"
      by (metis (no_types, lifting) tfl_some)

    then have "\<forall>q\<in>Q. \<exists>q'\<in>Q. \<not>(hml_conjunct_models q (\<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q' (\<psi>s i))))"
      by auto

    then show "\<forall>q\<in>Q. \<not> q \<Turnstile> Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (\<psi>s i)))"
      unfolding hml_models.simps by auto
  qed
qed


text \<open> The following three lemmata prove that the first condition of a distinguishing conjunction
(i.e. that the distinguished process \<open>p\<close> satisfies the conjunction)
for a somewhat more complex strategy of picking conjuncts. 
These become necessary when one wants to lift the distinguishing conjunction thinning lemma to \<open>hml_srbb\<close>.
Confer to the file of \<open>hml_srbb\<close> for more insight into the background.

The strategy for picking the conjuncts -- defined as \<open>distinguishing_conjunct\<close> in each lemma head --
is robust against original conjunctions with empty index sets or that do not contain distinguishing
conjuncts for some elements of \<open>Q\<close>. While these cases are impossible for normal distinguishing 
conjunctions in hml (how can an empty conjunction distinguish anything; a distinguishing conjunction
must have a subformula that actually distinguishes), in our formalisation of \<open>hml_srbb\<close> these cases
are relevant and in particular it is important that well defined conjuncts be present in such cases.
So the strategy works as follows: if I is empty, just pick \<open>\<top>\<close> (encoded in different ways);
if there is no distinguishing conjunct just pick any conjunct for the original conjunction;
otherwise pick a distinguishing conjunct.
\<close>

lemma dist_conjunct_image_subset_all_conjuncts:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos TT
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  shows "(distinguishing_conjunct I \<psi>s) ` Q \<subseteq> (\<psi>s ` I) \<union> {Pos TT}"
proof (cases "I = {}")
  assume "I = {}"
  then show "distinguishing_conjunct I \<psi>s ` Q \<subseteq> \<psi>s ` I \<union> {Pos TT}"
    by (simp add: assms image_subsetI)
next
  assume "I \<noteq> {}"

  then have "(\<lambda>q. if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
             then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
             else \<psi>s (SOME i. i \<in> I)) ` Q \<subseteq> \<psi>s ` I"
    by (smt (verit, ccfv_threshold) empty_subsetI image_eqI image_is_empty image_subsetI subset_antisym tfl_some)

  then show "distinguishing_conjunct I \<psi>s ` Q \<subseteq> \<psi>s ` I \<union> {Pos TT}"
    using \<open>I \<noteq> {}\<close> and distinguishing_conjunct_def
    by auto
qed

lemma models_full_models_dist_subset:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos TT
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  assumes "p \<Turnstile> (Conj I \<psi>s)"
  shows "p \<Turnstile> (Conj Q (distinguishing_conjunct I \<psi>s))"
  using assms(2)
  unfolding hml_models.simps
proof -
  assume "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"

  from dist_conjunct_image_subset_all_conjuncts
  have "\<forall>q\<in>Q. (\<exists>i\<in>I. distinguishing_conjunct I \<psi>s q = \<psi>s i) \<or> (distinguishing_conjunct I \<psi>s q = Pos TT)"
    unfolding distinguishing_conjunct_def
    apply (cases "I = {}")
    apply simp
    using some_in_eq some_eq_ex by (smt (z3))

  with \<open>\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)\<close>
  show "\<forall>q\<in>Q. hml_conjunct_models p (distinguishing_conjunct I \<psi>s q)"
    using distinguishing_conjunct_def by fastforce
qed

lemma models_full_models_dist_subset':
  fixes \<psi>s'
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Internal (Conj {} \<psi>s'))
           else if \<exists>i \<in> I. \<not>(hml_conjunct_models q (\<psi>s i))
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))
                else \<psi>s (SOME i. i \<in> I))"
  assumes "p \<Turnstile> (Conj I \<psi>s)"
  shows "p \<Turnstile> (Conj Q (distinguishing_conjunct I \<psi>s))"
  using assms(2)
proof (cases "I = {}")
  assume "I = {}"
  then have "distinguishing_conjunct I \<psi>s = (\<lambda>q. Pos (Internal (Conj {} \<psi>s')))"
    unfolding distinguishing_conjunct_def by simp
  then show "p \<Turnstile> Conj Q (distinguishing_conjunct I \<psi>s)"
    using silent_reachable.intros(1) by auto
next
  assume "p \<Turnstile> Conj I \<psi>s"
      and "I \<noteq> {}"
  then show "p \<Turnstile> Conj Q (distinguishing_conjunct I \<psi>s)"
    using models_full_models_dist_subset
      and distinguishing_conjunct_def
    by (smt (verit, ccfv_threshold) hml_models.simps(5))
qed


lemma dist_conj_non_empty_conj:
  fixes p :: 's and q :: 's
  assumes "p <> (Conj I \<psi>s) q"
  shows "I \<noteq> {}"
  by (metis distinguishes_hml_def assms empty_iff hml_models.simps(5))

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma hml_and_dist_disj: "p <> (\<psi>l \<and>hml \<psi>r) q = (p \<Turnstile> (\<psi>l \<and>hml \<psi>r) \<and> (\<not>hml_conjunct_models q \<psi>l \<or> \<not>hml_conjunct_models q \<psi>r))"
  using Inhabited_Tau_LTS.hml_and_and Inhabited_Tau_LTS_axioms distinguishes_hml_def by fastforce

end (* Inhabited_Tau_LTS *)

end
