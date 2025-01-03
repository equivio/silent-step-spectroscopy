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
The mutually recursive data types @{term \<open>hml_srbb\<close>}, @{term \<open>hml_srbb_inner\<close>} and @{term \<open>hml_srbb_conjunct\<close>}
represent the subset of all @{term \<open>hml\<close>} formulas, which characterize stability-respecting branching
bisimilarity (abbreviated to 'SRBB').
\\\\
When a parameter is of type @{term \<open>hml_srbb\<close>} we typically use \<open>\<phi>\<close> as a name,
for type @{term \<open>hml_srbb_inner\<close>} we use \<open>\<chi>\<close> and for type @{term \<open>hml_srbb_conjunct\<close>} we use \<open>\<psi>\<close>.

The data constructors are to be interpreted as follows:
\begin{itemize}
  \item in @{term \<open>hml_srbb\<close>}:
  \begin{itemize}
    \item @{term \<open>TT\<close>} encodes \<open>\<top>\<close>
    \item \<open>(Internal \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \item \<open>(ImmConj I \<psi>s)\<close> encodes $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \end{itemize}
  \item in @{term \<open>hml_srbb_inner\<close>}
  \begin{itemize}
    \item \<open>(Obs \<alpha> \<phi>)\<close> encodes \<open>(\<alpha>)\<phi>\<close> (Note the difference to \cite{bisping2023lineartimebranchingtime})
    \item \<open>(Conj I \<psi>s)\<close> encode $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \item \<open>(StableConj I \<psi>s)\<close> encodes $\neg\langle\tau\rangle\top \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
    \item \<open>(BranchConj \<alpha> \<phi> I \<psi>s)\<close> encodes $(\alpha)\varphi \land \bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$
  \end{itemize}
  \item in @{term \<open>hml_srbb_conjunct\<close>}
  \begin{itemize}
    \item \<open>(Pos \<chi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close>
    \item \<open>(Neg \<chi>)\<close> encodes \<open>\<not>\<langle>\<epsilon>\<rangle>\<chi>\<close>
  \end{itemize}
\end{itemize}

For justifications regarding the explicit inclusion of @{term \<open>TT\<close>} and
the encoding of conjunctions via index sets @{term \<open>I\<close>} and mapping from indices to conjuncts @{term \<open>\<psi>s\<close>},
reference the @{term \<open>TT\<close>} and @{term \<open>Conj\<close>} data constructors of the type @{term \<open>hml\<close>} in section \ref{sect:HML}.
\<close>

datatype
  ('act, 'i) hml_srbb =
    TT |
    Internal \<open>('act, 'i) hml_srbb_inner\<close> |
    ImmConj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close>
and
  ('act, 'i) hml_srbb_inner =
    Obs 'act \<open>('act, 'i) hml_srbb\<close> |
    Conj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close> |
    StableConj \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close> |
    BranchConj 'act \<open>('act, 'i) hml_srbb\<close>
               \<open>'i set\<close> \<open>'i \<Rightarrow> ('act, 'i) hml_srbb_conjunct\<close>
and
  ('act, 'i) hml_srbb_conjunct =
    Pos \<open>('act, 'i) hml_srbb_inner\<close> |
    Neg \<open>('act, 'i) hml_srbb_inner\<close>


subsection \<open> Semantics of HML$_\text{SRBB}$ Formulas \<close>

text \<open>
This section describes how semantic meaning is assigned to HML$_\text{SRBB}$ formulas in the context of a LTS.
We define what it means for a process @{term \<open>p\<close>} to satisfy a HML$_\text{SRBB}$ formula @{term \<open>\<phi>\<close>},
written as \<open>p \<Turnstile>SRBB \<phi>\<close>.
\<close>

context LTS_Tau
begin

primrec
      hml_srbb_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close> (infixl \<open>\<Turnstile>SRBB\<close> 60)
  and hml_srbb_inner_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  and hml_srbb_conjunct_models :: \<open>'s \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close> where
  \<open>hml_srbb_models state TT =
    True\<close> |
  \<open>hml_srbb_models state (Internal \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> (hml_srbb_inner_models p' \<chi>))\<close> |
  \<open>hml_srbb_models state (ImmConj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))\<close> |

  \<open>hml_srbb_inner_models state (Obs a \<phi>) =
    ((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)\<close> |
  \<open>hml_srbb_inner_models state (Conj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i))\<close> |
  \<open>hml_srbb_inner_models state (StableConj I \<psi>s) =
    ((\<nexists>p'. state \<mapsto> \<tau> p') \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))\<close> |
  \<open>hml_srbb_inner_models state (BranchConj a \<phi> I \<psi>s) =
    (((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models state \<phi>)
    \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models state (\<psi>s i)))\<close> |

  \<open>hml_srbb_conjunct_models state (Pos \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close> |
  \<open>hml_srbb_conjunct_models state (Neg \<chi>) =
    (\<nexists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>

sublocale lts_semantics \<open>step\<close> \<open>hml_srbb_models\<close> .
sublocale hml_srbb_inner: lts_semantics where models = hml_srbb_inner_models .
sublocale hml_srbb_conj: lts_semantics where models = hml_srbb_conjunct_models .

subsection \<open> Different Variants of Verum \<close>

lemma empty_conj_trivial[simp]:
  \<open>state \<Turnstile>SRBB ImmConj {} \<psi>s\<close>
  \<open>hml_srbb_inner_models state (Conj {} \<psi>s)\<close>
  \<open>hml_srbb_inner_models state (Obs \<tau> TT)\<close>
  by simp+

text \<open>\<open>\<And>{(\<tau>)\<top>}\<close> is trivially true. \<close>
lemma empty_branch_conj_tau:
  \<open>hml_srbb_inner_models state (BranchConj \<tau> TT {} \<psi>s)\<close>
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
  \<open>\<not> distinguishes TT p q\<close>
  by simp

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>},
then there must be at least one conjunct in this conjunction that distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>}.
\<close>
lemma srbb_dist_imm_conjunction_implies_dist_conjunct:
  assumes \<open>distinguishes (ImmConj I \<psi>s) p q\<close>
  shows \<open>\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
  using assms by auto

text \<open>
If there is one conjunct in that distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>}
and @{term \<open>p\<close>} satisfies all other conjuncts in a conjunction
then $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ (where $\psi s$ ranges over the previously mentioned
conjunctions) distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>}.
\<close>
lemma srbb_dist_conjunct_implies_dist_imm_conjunction:
  assumes \<open>i\<in>I\<close>
      and \<open>hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
      and \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
    shows \<open>distinguishes (ImmConj I \<psi>s) p q\<close>
  using assms by auto

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>},
then there must be at least one conjunct in this conjunction that distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>}.
\<close>
lemma srbb_dist_conjunction_implies_dist_conjunct:
  assumes \<open>hml_srbb_inner.distinguishes (Conj I \<psi>s) p q\<close>
  shows \<open>\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
  using assms by auto

text \<open>
In the following, we replicate @{term \<open>srbb_dist_conjunct_implies_dist_imm_conjunction\<close>} for simple conjunctions
in @{term \<open>hml_srbb_inner\<close>}.
\<close>
lemma srbb_dist_conjunct_implies_dist_conjunction:
  assumes \<open>i\<in>I\<close>
      and \<open>hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
      and \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
  shows \<open>hml_srbb_inner.distinguishes (Conj I \<psi>s) p q\<close>
  using assms by auto

text \<open>
We also replicate @{term \<open>srbb_dist_imm_conjunction_implies_dist_conjunct\<close>} for branching conjunctions
$(\alpha)\varphi\land\bigwedge\nolimits_{i \in I} {\psi s}(i)$.
Here, either the branching condition distinguishes @{term \<open>p\<close>} from @{term \<open>q\<close>} or there must be
a distinguishing conjunct.
\<close>
lemma srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch:
  assumes \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q\<close>
  shows \<open>(\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q)
       \<or> (hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q)\<close>
  using assms by force

text \<open>
In the following, we replicate @{term \<open>srbb_dist_conjunct_implies_dist_imm_conjunction\<close>} for branching conjunctions
in @{term \<open>hml_srbb_inner\<close>}.
\<close>
lemma srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction:
  assumes \<open>\<forall>i \<in> I. hml_srbb_conjunct_models p (\<psi>s i)\<close>
      and \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
      and \<open>(i\<in>I \<and> hml_srbb_conj.distinguishes (\<psi>s i) p q)
         \<or> (hml_srbb_inner.distinguishes (Obs \<alpha> \<phi>) p q)\<close>
  shows \<open>hml_srbb_inner.distinguishes (BranchConj \<alpha> \<phi> I \<psi>s) p q\<close>
  using assms by force

subsection \<open> HML$_\text{SRBB}$ Implication \<close>

abbreviation hml_srbb_impl
  :: \<open>('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close>  (infixr \<open>\<Rrightarrow>\<close> 70)
where
  \<open>hml_srbb_impl \<equiv> entails\<close>

abbreviation
  hml_srbb_impl_inner
  :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  (infix \<open>\<chi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.entails\<close>

abbreviation
  hml_srbb_impl_conjunct
  :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close>
  (infix \<open>\<psi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.entails\<close>

subsection \<open> HML$_\text{SRBB}$ Equivalence \<close>

text \<open>
We define HML$_\text{SRBB}$ formula equivalence to by appealing to HML$_\text{SRBB}$ implication.
A HML$_\text{SRBB}$ formula is equivalent to another formula if both imply each other.
\<close>

abbreviation
  hml_srbb_eq
  :: \<open>('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>srbb\<Rrightarrow>\<close> 70)
where
  \<open>(\<Lleftarrow>srbb\<Rrightarrow>) \<equiv> logical_eq\<close>

abbreviation
  hml_srbb_eq_inner
  :: \<open>('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>\<chi>\<Rrightarrow>\<close> 70)
where
  \<open>(\<Lleftarrow>\<chi>\<Rrightarrow>) \<equiv> hml_srbb_inner.logical_eq\<close>

abbreviation
  hml_srbb_eq_conjunct
  :: \<open>('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool\<close>
  (infix \<open>\<Lleftarrow>\<psi>\<Rrightarrow>\<close> 70)
  where
  \<open>(\<Lleftarrow>\<psi>\<Rrightarrow>) \<equiv> hml_srbb_conj.logical_eq\<close>

subsection \<open> Substitution \<close>

lemma srbb_internal_subst:
  assumes \<open>\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r\<close>
      and \<open>\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>l)\<close>
    shows \<open>\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)\<close>
  using assms by force

subsection \<open> Congruence \<close>

text \<open> This section provides means to derive new equivalences by extending both sides with a given prefix.  \<close>

text \<open> Prepending $\langle\varepsilon\rangle\dots$ preserves equivalence. \<close>
lemma internal_srbb_cong:
  assumes \<open>\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r\<close>
  shows \<open>(Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)\<close>
  using assms by auto

text \<open>If equivalent conjuncts are included in an otherwise identical conjunction, the equivalence is preserved.  \<close>
lemma immconj_cong:
  assumes \<open>\<psi>sl ` I = \<psi>sr ` I\<close>
      and \<open>\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s\<close>
  shows \<open>ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr\<close>
  using assms
  by (auto) (metis (mono_tags, lifting) image_iff)+

text \<open> Prepending $(\alpha)\dots$ preserves equivalence. \<close>
lemma obs_srbb_cong:
  assumes \<open>\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r\<close>
  shows \<open>(Obs \<alpha> \<phi>l) \<Lleftarrow>\<chi>\<Rrightarrow> (Obs \<alpha> \<phi>r)\<close>
  using assms by auto

subsection \<open> Known Equivalence Elements \<close>

text \<open>The formula $(\tau)\top$ is equivalent to $\bigwedge\{\}$. \<close>
lemma srbb_obs_\<tau>_is_\<chi>TT: \<open>Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s\<close>
  by simp

text \<open>The formula $(\alpha)\varphi$ is equivalent to $(\alpha)\varphi \land \bigwedge\{\}$. \<close>
lemma srbb_obs_is_empty_branch_conj: \<open>Obs \<alpha> \<phi> \<Lleftarrow>\<chi>\<Rrightarrow> BranchConj \<alpha> \<phi> {} \<psi>s\<close>
  by auto

text \<open> The formula $\top$ is equivalent to $\langle\varepsilon\rangle\bigwedge\{\}$.\<close>
lemma srbb_TT_is_\<chi>TT: \<open>TT \<Lleftarrow>srbb\<Rrightarrow> Internal (Conj {} \<psi>s)\<close>
  using LTS_Tau.refl by force

text \<open> The formula $\top$ is equivalent to $\bigwedge\{\}$.\<close>
lemma srbb_TT_is_empty_conj: \<open>TT \<Lleftarrow>srbb\<Rrightarrow> ImmConj {} \<psi>s\<close>
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

definition conjunctify_distinctions ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Pos \<chi>
    | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q)\<close>

lemma distinction_conjunctification:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p) q) p q\<close>
  unfolding conjunctify_distinctions_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Pos x
           | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) p q\<close>
      using assms q_I by auto
    then show ?thesis
      by (metis (mono_tags, lifting) ImmConj hml_srbb.simps(11) someI)
  qed
qed

lemma distinction_combination:
  fixes p q
  defines \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (distinguishes (\<Phi> q'') p' q'')\<close>
  shows
    \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. q' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close>
  proof clarify
    fix q' q''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close>
    thus \<open>hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p' q'') p' q''\<close>
      using distinction_conjunctification assms(3)
      by (metis mem_Collect_eq)
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close> by blast
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (ImmConj {q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}
                               (conjunctify_distinctions \<Phi> p')) p' q''\<close> by auto
  thus \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
    by (auto) (metis assms(2))+
qed

definition conjunctify_distinctions_dual ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions_dual \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Neg \<chi>
    | ImmConj I \<Psi> \<Rightarrow>
      (case \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
        Pos \<chi> \<Rightarrow> Neg \<chi> | Neg \<chi> \<Rightarrow> Pos \<chi>)\<close>

lemma dual_conjunct:
  assumes
    \<open>hml_srbb_conj.distinguishes \<psi> p q\<close>
  shows
    \<open>hml_srbb_conj.distinguishes (case \<psi> of
               hml_srbb_conjunct.Pos \<chi> \<Rightarrow> hml_srbb_conjunct.Neg \<chi>
               | hml_srbb_conjunct.Neg \<chi> \<Rightarrow> hml_srbb_conjunct.Pos \<chi>) q p\<close>
  using assms
  by (cases \<psi>, auto)

lemma distinction_conjunctification_dual:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes (conjunctify_distinctions_dual \<Phi> p q) p q\<close>
  unfolding conjunctify_distinctions_dual_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Neg x
           | ImmConj I \<Psi> \<Rightarrow>
               ( case \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
                  hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) q p\<close>
      using assms q_I by auto
    hence \<open>hml_srbb_conj.distinguishes (case \<Psi>
      (SOME i. i \<in> J \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
               hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x) p q\<close>
      by (metis (no_types, lifting) dual_conjunct someI_ex)
    then show ?thesis unfolding ImmConj by auto
  qed
qed

lemma distinction_conjunctification_two_way:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes ((if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q) p q\<close>
proof safe
  fix q
  assume \<open>q \<in> I\<close>
  then consider \<open>distinguishes (\<Phi> q) p q\<close> | \<open>distinguishes (\<Phi> q) q p\<close> using assms by blast
  thus \<open>hml_srbb_conj.distinguishes ((if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q) p q\<close>
  proof cases
    case 1
    then show ?thesis using distinction_conjunctification
      by (smt (verit) singleton_iff)
  next
    case 2
    then show ?thesis using distinction_conjunctification_dual singleton_iff
      unfolding distinguishes_def
      by (smt (verit, ccfv_threshold))
  qed
qed

end (* LTS_Tau *)

end
