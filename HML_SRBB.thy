text \<open>\newpage\<close>
section \<open> Stability-Respecting Branching Bisimilarity (HML$_\text{SRBB}$) \label{sect:hmlSRBB} \<close>
theory HML_SRBB
  imports Main LTS_Semantics
begin
text \<open>This section describes the largest subset of the full HML language in section \ref{sect:HML} that we are
using for purposes of silent step spectroscopy. It is supposed to characterize the most fine grained
behavioural equivalence that we may decide: Stability-Respecting Branching Bisimilarity (SRBB). While
there are good reasons to believe that this subset truly characterizes SRBB (c.f.\cite{bisping2023lineartimebranchingtime}),
we do not provide a formal proof. From this sublanguage smaller subsets are derived
via the notion of expressiveness prices (\ref{sect:ExpressivenessMeasure}). \<close>

text \<open>
The mutually recursive data types @{term "hml_srbb"}, @{term "hml_srbb_inner"} and @{term "hml_srbb_conjunct"}
represent the subset of all @{term "hml"} formulas, which characterize stability-respecting branching
bisimilarity (abbreviated to 'SRBB').
\\\\
When a parameter is of type @{term "hml_srbb"} we typically use \<open>\<phi>\<close> as a name,
for type @{term "hml_srbb_inner"} we use \<open>\<chi>\<close> and for type @{term "hml_srbb_conjunct"} we use \<open>\<psi>\<close>.

The data constructors are to be interpreted as follows:
\begin{itemize}
  \item in @{term "hml_srbb"}:
  \begin{itemize}
    \item @{term "TT"} encodes \<open>\<top>\<close>
    \item \<open>(Internal \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \item \<open>(ImmConj I \<psi>s)\<close> encodes $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \end{itemize}
  \item in @{term "hml_srbb_inner"}
  \begin{itemize}
    \item \<open>(Obs \<alpha> \<phi>)\<close> encodes \<open>(\<alpha>)\<phi>\<close> (Note the difference to \cite{bisping2023lineartimebranchingtime})
    \item \<open>(Conj I \<psi>s)\<close> encode $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \item \<open>(StableConj I \<psi>s)\<close> encodes $\neg\langle\tau\rangle\top \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \item \<open>(BranchConj \<alpha> \<phi> I \<psi>s)\<close> encodes $(\alpha)\varphi \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \end{itemize}
  \item in @{term "hml_srbb_conjunct"}
  \begin{itemize}
    \item \<open>(Pos \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \item \<open>(Neg \<chi>)\<close> encodes \<open>\<not>\<langle>\<epsilon>\<rangle>\<chi>\<close>
  \end{itemize}
\end{itemize}

For justifications regarding the explicit inclusion of @{term "TT"} and
the encoding of conjunctions via index sets @{term "I"} and mapping from indices to conjuncts @{term "\<psi>s"},
reference the @{term "TT"} and @{term "Conj"} data constructors of the type @{term "hml"} in section \ref{sect:HML}.
\<close>

datatype 
  ('act, 'i) hml_srbb =
    TT |
    Internal "('act, 'i) hml_srbb_inner" |
    ImmConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_inner =
    Obs 'act "('act, 'i) hml_srbb" |
    Conj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    StableConj "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct" |
    BranchConj 'act "('act, 'i) hml_srbb"
               "'i set" "'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct"
and
  ('act, 'i) hml_srbb_conjunct =
    Pos "('act, 'i) hml_srbb_inner" |
    Neg "('act, 'i) hml_srbb_inner"


subsection \<open> Semantics of HML$_\text{SRBB}$ Formulas \<close>

text \<open>
This section describes how semantic meaning is assigned to HML$_\text{SRBB}$ formulas in the context of a LTS.
We define what it means for a process @{term "p"} to satisfy a HML$_\text{SRBB}$ formula @{term "\<phi>"},
written as \<open>p \<Turnstile>SRBB \<phi>\<close>.
\<close>

context LTS_Tau
begin

primrec 
      hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infixl "\<Turnstile>SRBB" 60)
  and hml_srbb_inner_models :: "'s \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  and hml_srbb_conjunct_models :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" where
  "hml_srbb_models state TT =
    True" |
  "hml_srbb_models state (Internal \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> (hml_srbb_inner_models p' \<chi>))" |
  "hml_srbb_models state (ImmConj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))" |

  "hml_srbb_inner_models state (Obs a \<phi>) =
    ((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)" |
  "hml_srbb_inner_models state (Conj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))" |
  "hml_srbb_inner_models state (StableConj I \<psi>s) =
    ((\<nexists>p'. state \<mapsto> \<tau> p') \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))" |
  "hml_srbb_inner_models state (BranchConj a \<phi> I \<psi>s) =
    (((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)
    \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))" |

  "hml_srbb_conjunct_models state (Pos \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)" |
  "hml_srbb_conjunct_models state (Neg \<chi>) =
    (\<nexists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)"

sublocale lts_semantics \<open>step\<close> \<open>hml_srbb_models\<close> .
sublocale hml_srbb_inner: lts_semantics where models = hml_srbb_inner_models .
sublocale hml_srbb_conj: lts_semantics where models = hml_srbb_conjunct_models . 

subsection \<open> Different Variants of Verum \<close>

lemma empty_conj_trivial[simp]:
  "state \<Turnstile>SRBB ImmConj {} \<psi>s"
  "hml_srbb_inner_models state (Conj {} \<psi>s)"
  "hml_srbb_inner_models state (Obs \<tau> TT)"
  by simp+

text \<open>\<open>\<And>{(\<tau>)\<top>}\<close> is trivially true. \<close>
lemma empty_branch_conj_tau:
  "hml_srbb_inner_models state (BranchConj \<tau> TT {} \<psi>s)"
  by auto

lemma stable_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close>
    \<open>i \<in> I \<close>
  shows \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms by auto

lemma branching_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
    \<open>i \<in> I \<close>
  shows \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms by auto

lemma branching_conj_obs:
  assumes
    \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
  shows \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
  using assms by auto

subsection \<open> Distinguishing Formulas \<close>

text \<open>Now, we take a look at some basic properties of the \<open>distinguishes\<close> predicate: \<close>

text \<open> \<open>\<top>\<close> can never distinguish two processes. This is due to the fact that every process
satisfies \<open>T\<close>. Therefore, the second part of the definition of \<open>distinguishes\<close> never holds. \<close>
lemma verum_never_distinguishes:
  "\<not> distinguishes TT p q"
  by simp

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term "p"} from @{term "q"},
then there must be at least one conjunct in this conjunction that distinguishes @{term "p"} from @{term "q"}.
\<close>
lemma srbb_dist_imm_conjunction_implies_dist_conjunct:
  assumes "distinguishes (ImmConj I \<psi>s) p q"
  shows "\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q"
  using assms by auto

text \<open>
If there is one conjunct in that distinguishes @{term "p"} from @{term "q"}
and @{term "p"} satisfies all other conjuncts in a conjunction
then $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ (where $\psi s$ ranges over the previously mentioned
conjunctions) distinguishes @{term "p"} from @{term "q"}.
\<close>
lemma srbb_dist_conjunct_implies_dist_imm_conjunction:
  assumes "i\<in>I"
      and "hml_srbb_conj.distinguishes (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)"
    shows "distinguishes (ImmConj I \<psi>s) p q"
  using assms by auto

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term "p"} from @{term "q"},
then there must be at least one conjunct in this conjunction that distinguishes @{term "p"} from @{term "q"}.
\<close>
lemma srbb_dist_conjunction_implies_dist_conjunct:
  assumes "hml_srbb_inner.distinguishes (Conj I \<psi>s) p q"
  shows "\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q"
  using assms by auto

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for simple conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_implies_dist_conjunction:
  assumes "i\<in>I"
      and "hml_srbb_conj.distinguishes (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)"
  shows "hml_srbb_inner.distinguishes (Conj I \<psi>s) p q"
  using assms by auto

text \<open>
We also replicate @{term "srbb_dist_imm_conjunction_implies_dist_conjunct"} for branching conjunctions
$(\alpha)\varphi\land\bigwedge\nolimits_{i \in I} {\psi s}(i)$.
Here, either the branching condition distinguishes @{term "p"} from @{term "q"} or there must be
a distinguishing conjunct.
\<close>
lemma srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch:
  assumes "hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  shows "(\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q)
       \<or> (hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q)"
  using assms by force

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for branching conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models p (\<psi>s i)"
      and "hml_srbb_inner_models p (Obs \<alpha> \<phi>)"
      and "(i\<in>I \<and> hml_srbb_conj.distinguishes (\<psi>s i) p q)
         \<or> (hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q)"
  shows "hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  using assms by force

subsection \<open> HML$_\text{SRBB}$ Implication \<close>

abbreviation hml_srbb_impl
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"  (infixr "\<Rrightarrow>" 70)
where
  "hml_srbb_impl \<equiv> entails"

abbreviation
  hml_srbb_impl_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  (infix "\<chi>\<Rrightarrow>" 70)
where
  "(\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.entails"

abbreviation
  hml_srbb_impl_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool"
  (infix "\<psi>\<Rrightarrow>" 70)
where
  "(\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.entails"

subsection \<open> HML$_\text{SRBB}$ Equivalence \<close>

text \<open>
We define HML$_\text{SRBB}$ formula equivalence to by appealing to HML$_\text{SRBB}$ implication.
A HML$_\text{SRBB}$ formula is equivalent to another formula if both imply each other.
\<close>

abbreviation
  hml_srbb_eq
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"
  (infix "\<Lleftarrow>srbb\<Rrightarrow>" 70)
where
  "(\<Lleftarrow>srbb\<Rrightarrow>) \<equiv> logical_eq"

abbreviation
  hml_srbb_eq_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  (infix "\<Lleftarrow>\<chi>\<Rrightarrow>" 70)
where
  "(\<Lleftarrow>\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.logical_eq"

abbreviation
  hml_srbb_eq_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool"
  (infix "\<Lleftarrow>\<psi>\<Rrightarrow>" 70)
  where
  "(\<Lleftarrow>\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.logical_eq"

subsection \<open> Substitution \<close>

lemma srbb_internal_subst:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
      and "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>l)"
    shows "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  using assms by force

subsection \<open> Congruence \<close>

text \<open> This section provides means to derive new equivalences by extending both sides with a given prefix.  \<close>

text \<open> Prepending $\langle\varepsilon\rangle\dots$ preserves equivalence. \<close>
lemma internal_srbb_cong:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
  shows "(Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  using assms by auto

text \<open>If equivalent conjuncts are included in an otherwise identical conjunction, the equivalence is preserved.  \<close>
lemma immconj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  shows "ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
  using assms 
  by (auto) (metis (mono_tags, lifting) image_iff)+

text \<open> Prepending $(\alpha)\dots$ preserves equivalence. \<close>
lemma obs_srbb_cong:
  assumes "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<chi>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms by auto

subsection \<open> Known Equivalence Elements \<close>

text \<open>The formula $(\tau)\top$ is equivalent to $\bigwedge\{\}$. \<close>
lemma srbb_obs_\<tau>_is_\<chi>TT: "Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s"
  by simp

text \<open>The formula $(\alpha)\varphi$ is equivalent to $(\alpha)\varphi \land \bigwedge\{\}$. \<close>
lemma srbb_obs_is_empty_branch_conj: "Obs \<alpha> \<phi> \<Lleftarrow>\<chi>\<Rrightarrow> BranchConj \<alpha> \<phi> {} \<psi>s"
  by auto

text \<open> The formula $\top$ is equivalent to $\langle\varepsilon\rangle\bigwedge\{\}$.\<close>
lemma srbb_TT_is_\<chi>TT: "TT \<Lleftarrow>srbb\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using LTS_Tau.refl by force

text \<open> The formula $\top$ is equivalent to $\bigwedge\{\}$.\<close>
lemma srbb_TT_is_empty_conj: "TT \<Lleftarrow>srbb\<Rrightarrow> ImmConj {} \<psi>s"
  by simp

text \<open>Positive conjuncts in stable conjunctions can be replaced by negative ones.\<close>
lemma srbb_stable_Neg_normalizable:
  assumes
    \<open>i \<in> I\<close> \<open>\<Psi> i = Pos \<chi>\<close>
    \<open>\<Psi>' = \<Psi>(i:= Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
  shows
    \<open>Internal (StableConj I \<Psi>) \<Lleftarrow>srbb\<Rrightarrow> Internal (StableConj I \<Psi>')\<close>
proof (rule logical_eqI)
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have \<open>\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>\<close>
    using assms(1,2) by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms(3) using p'_spec by auto
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec(2) have other_conjuncts: \<open>\<forall>j\<in>I. i \<noteq> j \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi> j)\<close>
    using assms stable_conj_parts fun_upd_apply by metis
  from p'_spec(2) have \<open>hml_srbb_conjunct_models p' (\<Psi>' i)\<close>
    using assms(1) stable_conj_parts by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    unfolding assms(3) by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by (auto, metis silent_reachable.simps)
  then have \<open>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using LTS_Tau.refl by fastforce
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close>
    using p'_spec assms other_conjuncts by auto
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>)\<close>
    using p'_spec(1) by auto
qed

text \<open>All positive conjuncts in stable conjunctions can be replaced by negative ones at once.\<close>
lemma srbb_stable_Neg_normalizable_set:
  assumes
    \<open>\<Psi>' = (\<lambda>i. case (\<Psi> i) of 
      Pos \<chi> \<Rightarrow> Neg (StableConj {left} (\<lambda>_. Neg \<chi>)) |
      Neg \<chi> \<Rightarrow> Neg \<chi>)\<close>
  shows
    \<open>Internal (StableConj I \<Psi>) \<Lleftarrow>srbb\<Rrightarrow> Internal (StableConj I \<Psi>')\<close>
proof (rule logical_eqI)
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have
    \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> (\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>)\<close>
    by fastforce
  with \<open>stable_state p'\<close> have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence pos_rewrite: \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>
      hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms using p'_spec
    by (auto, metis (no_types, lifting) hml_srbb_conjunct.exhaust hml_srbb_conjunct.simps(5,6)
        pos_rewrite)
  thus \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>')\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec(2) have other_conjuncts:
      \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Neg \<chi> \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi> i)\<close>
    using assms stable_conj_parts by (metis hml_srbb_conjunct.simps(6))
  from p'_spec(2) have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi>' i)\<close>
    using assms(1) stable_conj_parts by blast
  hence \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>
      hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    unfolding assms by auto
  with \<open>stable_state p'\<close> have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by (auto, metis silent_reachable.simps)
  then have pos_conjuncts:
      \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using hml_srbb_conjunct_models.simps(1) silent_reachable.simps by blast
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close>
    using p'_spec assms other_conjuncts 
    by (auto, metis other_conjuncts pos_conjuncts hml_srbb_conjunct.exhaust)
  thus \<open>p \<Turnstile>SRBB Internal (StableConj I \<Psi>)\<close>
    using p'_spec(1) by auto
qed

end (* Inhabited_Tau_LTS *)

end
