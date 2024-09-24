text \<open>\newpage\<close>
section \<open> Stability-Respecting Branching Bisimilarity (HML$_\text{SRBB}$) \label{sect:hmlSRBB} \<close>
theory HML_SRBB
  imports Main HML
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

text \<open>
In the beginning, instead of defining the subset as a new data type,  we considered defining the
HML$_\text{SRBB}$ subset via a predicate on HML like \<open>is_srbb :: "('a,'s) hml \<Rightarrow> bool"\<close>.
For a concrete instance of this approach reference \<open>is_trace_formula\<close> in appendix \ref{appndx:weakTraces}.
We decided not to use this approach because we could not figure out how  define expressiveness prices (see section \ref{sect:ExpressivenessMeasure}) when using this option.
\<close>

subsection \<open> Semantics of HML$_\text{SRBB}$ Formulas \<close>

text \<open>
This section describes how semantic meaning is assigned to HML$_\text{SRBB}$ formulas in the context of a LTS.
We define what it means for a process @{term "p"} to satisfy a HML$_\text{SRBB}$ formula @{term "\<phi>"},
written as \<open>p \<Turnstile>SRBB \<phi>\<close>, by first translating this formula @{term "\<phi>"} into the corresponding HML formula
(via @{term "hml_srbb_to_hml"}) and then appealing to HML's models function.
This is in contrast to defining the function directly by inspecting the transitions possible from @{term "p"}.
Defining it via translation to HML allows (and forces) us to reuse the definitions and
properties of HML.
\<close>

subsubsection \<open> Mapping HML$_\text{SRBB}$ to HML \<close>

text \<open>
We ensure that HML$_\text{SRBB}$ is a subset of HML by mapping each constructor of
HML$_\text{SRBB}$ to a composition of constructors of HML.  This mapping is straight
forward when viewing above interpretation of the data constructors of HML$_\text{SRBB}$. The only
clause of note is the translation of the @{term "Obs"} data constructor of type @{term "hml_srbb_inner"}.
\<close>

context Inhabited_Tau_LTS
begin

primrec
  hml_srbb_to_hml
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml"
and
  hml_srbb_inner_to_hml
  :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml"
and
  hml_srbb_conjunct_to_hml_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_conjunct"
where
  "hml_srbb_to_hml TT =
    hml.TT" |
  "hml_srbb_to_hml (Internal \<chi>) =
    hml.Internal (hml_srbb_inner_to_hml \<chi>)" |
  "hml_srbb_to_hml (ImmConj I \<psi>s) =
    hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_inner_to_hml (Obs a \<phi>) =
    HML_soft_poss a (hml_srbb_to_hml \<phi>)" |
(*equivalent to? (if a = \<tau> then hml_srbb_to_hml \<phi> else hml.Obs a (hml_srbb_to_hml \<phi>))*)
  "hml_srbb_inner_to_hml (Conj I \<psi>s) =
    hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)" |

  "hml_srbb_inner_to_hml (StableConj I \<psi>s) =
    (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_inner_to_hml (BranchConj a \<phi> I \<psi>s) = 
     (hml_conjunct.Pos (HML_soft_poss a (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" |

  "hml_srbb_conjunct_to_hml_conjunct (Pos \<chi>) =
    hml_conjunct.Pos (hml.Internal (hml_srbb_inner_to_hml \<chi>))" |
  "hml_srbb_conjunct_to_hml_conjunct (Neg \<chi>) =
    hml_conjunct.Neg (hml.Internal (hml_srbb_inner_to_hml \<chi>))"

text \<open>
Given this translation, we may now note that this HML$_\text{SRBB}$ subset diverges significantly from the one
given in \cite{bisping2023lineartimebranchingtime}. Specifically, Bisping and Jansen allow for true observation
clauses $\langle \alpha \rangle$ under the non-terminal $\chi$ with the side condition that $\alpha \neq \tau$,
while we instead opted to allow for 'soft observations' $(\alpha)$ in the corresponding type @{term "hml_srbb_inner"},
without any constraint on $\alpha$.  We choose to do so, since we are unable to express the side
condition $\alpha \neq \tau$ at type level. This is rooted in the way in which we defined $\tau$ as
being a fixed but otherwise arbitrary inhabitant of the label type \<open>'a\<close> (\ref{sect:LTS}).
For an alternative definition of $\tau$ which allows for type level distinction of $\tau$ from all other
labels reference appendix \ref{appndx:LTSOptTau}. One may now wonder if this modification is valid or if it in any way impacts the results of this
project. While we do not not formally prove that this modification does not alter the meaning of
the HML$_\text{SRBB}$ subset, we may provide some evidence that the divergence is permitted:
\begin{enumerate}
  \item The proof that weak trace equivalence is characterized by a specific subset of our HML$_\text{SRBB}$
    (appendix \ref{appndx:weakTraces}) still works. If this had not been the case, our change would certainly have been problematic.
  \item \label{lbl:srbbArgument} One can argue that all occurrences of the 'soft' observation
    $(\alpha)\varphi$ are equivalent to some formula in \cite{bisping2023lineartimebranchingtime}'s
    dialect of HML$_\text{SRBB}$.
\end{enumerate}

The second one (\ref{lbl:srbbArgument}) may be justified by case analysis on the $\alpha$ in $(\alpha)\varphi$:
\begin{enumerate}
  \item If $\alpha \neq \tau$:\\
    By the definition of $(\alpha)\varphi$ in \ref{SoftPossDef} it follows that $(\alpha)\varphi = \langle \alpha \rangle \varphi$
    and since $\alpha \neq \tau$ we have exactly the observation in $\chi$ of \cite{bisping2023lineartimebranchingtime}.
  \item If $\alpha = \tau$:
    \begin{itemize}
      \item By the definition of $(\alpha)\varphi$ in \ref{SoftPossDef} it follows that $(\alpha)\varphi = (\tau) \varphi$.
      \item When closely inspecting the definitions of the data types @{term "hml_srbb"}, @{term "hml_srbb_inner"} and
        @{term "hml_srbb_conjunct"} as well as the corresponding translation functions, one can observe that
        the @{term "Obs"} in question must be preceeded by a @{term "hml.Internal"}, so we may inspect:
        $\langle\varepsilon\rangle(\tau)\varphi$
      \item From \ref{equivalenceProofs} we know $\langle \varepsilon \rangle (\tau) \varphi \Lleftarrow\Rrightarrow \langle\varepsilon\rangle\varphi$
      \item Next we do a case analysis on the $\varphi$ (in our encoding the type @{term "hml_srbb"}) in $\langle\varepsilon\rangle\varphi$:
        \begin{enumerate}
          \item $\varphi = \top$:\\
            Here, we know from \ref{equivalenceProofs} that $\langle\varepsilon\rangle\top \Lleftarrow\Rrightarrow \top$, which is in
            \cite{bisping2023lineartimebranchingtime}'s HML$_\text{SRBB}$.
          \item $\varphi = \langle \varepsilon \rangle \chi$:\\
            Once again, from \ref{equivalenceProofs} we know $\langle\varepsilon\rangle\langle\varepsilon\rangle\chi \Lleftarrow\Rrightarrow \langle\varepsilon\rangle\chi$,
            which is in \cite{bisping2023lineartimebranchingtime}'s HML$_\text{SRBB}$.
          \item $\varphi = \bigwedge\nolimits_{i \in I} {\psi s}(i)$:\\
            Here, we can observe that $\langle\varepsilon\rangle\bigwedge\nolimits_{i \in I} {\psi s}(i)$ is directly in
            \cite{bisping2023lineartimebranchingtime}'s HML$_\text{SRBB}$.
        \end{enumerate}
    \end{itemize}
\end{enumerate}
While this argument is not a proper proof (inductively moving this argument over the whole formula,
not just one observation is missing), it provides us with confidence that our adaptation of the
HML$_\text{SRBB}$ language does not impact the results of the project.
\<close>

subsubsection \<open>Models Relation for HML$_\text{SRBB}$ \<close>

text \<open>
We say that a process @{term "p"} satisfies a HML$_\text{SRBB}$ formula @{term "\<phi>"}, denoted as @{term "p \<Turnstile>SRBB \<phi>"}
if that process @{term "p"} models the result of translating the HML$_\text{SRBB}$ @{term "\<phi>"} formula into a HML formula.
\<close>

fun hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infixl "\<Turnstile>SRBB" 60)where
  "hml_srbb_models state formula = (state \<Turnstile> (hml_srbb_to_hml formula))"

fun hml_srbb_inner_models :: "'s \<Rightarrow>('a, 's) hml_srbb_inner \<Rightarrow> bool" where
  "hml_srbb_inner_models s \<chi> = (s \<Turnstile> (hml_srbb_inner_to_hml \<chi>))"

fun hml_srbb_conjunct_models :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" where
  "hml_srbb_conjunct_models s \<psi> = (hml_conjunct_models s (hml_srbb_conjunct_to_hml_conjunct \<psi>))"

primrec 
      hml_srbb_models' :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" 
  and hml_srbb_inner_models' :: "'s \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  and hml_srbb_conjunct_models' :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool" where
  "hml_srbb_models' state TT =
    True" |
  "hml_srbb_models' state (Internal \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> (hml_srbb_inner_models' p' \<chi>))" |
  "hml_srbb_models' state (ImmConj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models' state (\<psi>s i))" |

  "hml_srbb_inner_models' state (Obs a \<phi>) =
    ((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models' p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models' state \<phi>)" |
  "hml_srbb_inner_models' state (Conj I \<psi>s) =
    (\<forall>i\<in>I. hml_srbb_conjunct_models' state (\<psi>s i))" |
  "hml_srbb_inner_models' state (StableConj I \<psi>s) =
    ((\<nexists>p'. state \<mapsto> \<tau> p') \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models' state (\<psi>s i)))" |
  "hml_srbb_inner_models' state (BranchConj a \<phi> I \<psi>s) =
    (((\<exists>p'. state \<mapsto> a p' \<and> hml_srbb_models' p' \<phi>) \<or> a = \<tau> \<and> hml_srbb_models' state \<phi>)
    \<and> (\<forall>i\<in>I. hml_srbb_conjunct_models' state (\<psi>s i)))" |

  "hml_srbb_conjunct_models' state (Pos \<chi>) =
    (\<exists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models' p' \<chi>)" |
  "hml_srbb_conjunct_models' state (Neg \<chi>) =
    (\<nexists>p'. state \<Zsurj> p' \<and> hml_srbb_inner_models' p' \<chi>)"


lemma "(\<forall>s. hml_srbb_models s \<phi> = hml_srbb_models' s \<phi>)
     \<and> (\<forall>s. hml_srbb_inner_models s \<chi> = hml_srbb_inner_models' s \<chi>)
     \<and> (\<forall>s. hml_srbb_conjunct_models s \<psi> = hml_srbb_conjunct_models' s \<psi>)"
  apply (rule hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct )
  using left_right_distinct by fastforce+


sublocale lts_semantics \<open>step\<close> \<open>hml_srbb_models\<close> .
sublocale hml_srbb_inner: lts_semantics where models = hml_srbb_inner_models .
sublocale hml_srbb_conj: lts_semantics where models = hml_srbb_conjunct_models . 

subsection \<open> Different Variants of Verum \<close>

lemma empty_conj_trivial[simp]:
  "state \<Turnstile>SRBB TT"
  "state \<Turnstile>SRBB ImmConj {} \<psi>s"
  "hml_srbb_inner_models state (Conj {} \<psi>s)"
  "hml_srbb_inner_models state (Obs \<tau> TT)"
  by simp+

text \<open>\<open>\<And>{(\<tau>)\<top>}\<close> is trivially true. \<close>
lemma empty_branch_conj_tau:
  "hml_srbb_inner_models state (BranchConj \<tau> TT {} \<psi>s)"
  using left_right_distinct by auto

lemma stable_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close>
    \<open>i \<in> I \<close>
  shows \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms left_right_distinct by auto

lemma branching_conj_parts:
  assumes
    \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
    \<open>i \<in> I \<close>
  shows \<open>hml_srbb_conjunct_models p (\<Psi> i)\<close>
  using assms left_right_distinct by auto

lemma branching_conj_obs:
  assumes
    \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
  shows \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
  using assms left_right_distinct by auto

subsection \<open> Distinguishing Formulas \<close>

text \<open>
One may evaluate whether a HML$_\text{SRBB}$ formula distinguishes two processes by translating the formula
into a HML formula and then check if this formula distinguishes the two processes.
\<close>
lemma dist_srbb_eq_dist_hml:
  "distinguishes \<phi> p q = p << hml_srbb_to_hml \<phi> >> q"
  by simp

text \<open>Now, we take a look at some basic properties of the \<open>distinguishes\<close> predicate: \<close>

text \<open> \<open>\<top>\<close> can never distinguish two processes. This is due to the fact that every process
satisfies \<open>T\<close>. Therefore, the second part of the definition of \<open>distinguishes\<close> never holds. \<close>
lemma verum_never_distinguishes:
  "\<not> distinguishes TT p q"
  by simp

lemma dist_from_srbb_eq_dist_from_hml:
  "distinguishes_from \<phi> p Q = p << hml_srbb_to_hml \<phi> >>> Q"
  by simp

lemma dist_from_inner_srbb_eq_dist_from_hml:
  "hml_srbb_inner.distinguishes_from \<chi> p Q = p << hml_srbb_inner_to_hml \<chi> >>> Q"
  by auto

subsubsection \<open> Distinguishing Conjunctions \<close>

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
We also replicate @{term "srbb_dist_imm_conjunction_implies_dist_conjunct"} for stable conjunctions
$\neg\langle\tau\rangle\top\land\bigwedge\nolimits_{i \in I} {\psi s}(i)$.
Here, either the stability condition distinguishes @{term "p"} from @{term "q"} or there must be
a distinguishing conjunct.
\<close>
lemma srbb_dist_stable_conjunction_implies_dist_conjunct_or_stable:
  assumes "hml_srbb_inner.distinguishes (StableConj I \<psi>s) p q"
  shows "(\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q)
       \<or> (p << HML_not (hml.Obs \<tau> hml.TT) >> q)"
  using assms hml_and_and left_right_distinct by force

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for stable conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_or_stable_implies_dist_stable_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models p (\<psi>s i)"
      and "p \<Turnstile> (HML_not (hml.Obs \<tau> hml.TT))"
      and "(\<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q)
         \<or> (p << HML_not (hml.Obs \<tau> hml.TT) >> q)"
  shows "hml_srbb_inner.distinguishes (StableConj I \<psi>s) p q"
  using assms hml_and_and left_right_distinct by force

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
  using assms hml_and_and left_right_distinct by force

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
  using assms hml_and_and left_right_distinct by force


subsubsection \<open> Distinguishing Conjunction Thinning \<close>

(*
text \<open>
The following four lemmas lift the result
  that a conjunction which distinguishes
   a process $p$ from a set of processes $Q$ may be reduced (thinned) to have at most one conjunct per
   element of $Q$, while still being able to distinguish $p$ from $Q$
  (@{term "dist_conj_thinning"})
from unrestricted HML to HML$_\text{SRBB}$.
\<close>

lemma extract_converter:
  assumes "p <> (hml.Conj Q
                  (\<lambda>q. (f \<circ> \<psi>s) (SOME i. i \<in> I \<and>
                                  \<not>(hml_conjunct_models q ((f \<circ> \<psi>s) i)))))
           Q"
  shows "p <> (hml.Conj Q
                  (f \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and>
                                  \<not>(hml_conjunct_models q ((f \<circ> \<psi>s) i))))))
         Q"
  using assms and comp_apply
  by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)


lemma dist_immconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from (ImmConj I \<psi>s) p Q"
  shows "distinguishes_from (ImmConj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms 
  unfolding distinguishes_from_def
        and distinguishes_def
        and hml_srbb_models.simps
        and hml_srbb_to_hml.simps
        and distinguishing_conjunct_def
  using dist_conj_thinning distinguishes_from_hml_def 
proof -
  assume "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
  hence "p <> (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)) Q"
    by (simp add: LTS_Tau.distinguishes_hml_def distinguishes_from_hml_def)

  with dist_conj_thinning
  have "p <> (hml.Conj Q (\<lambda>q. (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))))) Q"
    by blast

  with extract_converter
  have "p <> (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)))))) Q"
    by auto

  then show "p \<Turnstile> hml.Conj Q
                (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))) \<and>
           (\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Conj Q
                   (hml_srbb_conjunct_to_hml_conjunct \<circ> (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q))))"
    unfolding distinguishes_from_hml_def and distinguishes_hml_def and hml_srbb_conjunct_models.simps and comp_apply
    by blast
qed


lemma dist_conj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q)))"
  assumes "distinguishes_from_inner (Conj I \<psi>s) p Q"
  shows "distinguishes_from_inner (Conj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms
  unfolding dist_from_inner_srbb_eq_dist_from_hml
            hml_srbb_inner_to_hml.simps
            distinguishing_conjunct_def
            o_apply
  using dist_conj_thinning[of _ _ "hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s"]
  unfolding o_apply 
  by auto 


lemma dist_stableconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Conj {} undefined)
           else if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                else \<psi>s (SOME i. i \<in> I))"
  (* These if-then-else's are necessary, as the distinction might come from the stability condition.
     If that is the case then the stability condition could be the only distinction from some or even all elements of Q.
     Due to the way that StableConj is translated (via two stacked conjunctions, c.f. the translate function),
     this can lead to the situation where I might be empty (i.e. there are no conjuncts apart from the stability
     condition) or there may be conjuncts via I, but some elements of Q model all of these (i.e. so they are
     distinguished from p only via the stability condition).  Since we want to pick a conjunct for each element in Q,
     we must describe what to do in these cases. *)
  assumes "distinguishes_from_inner (StableConj I \<psi>s) p Q"
  shows
    "distinguishes_from_inner (StableConj Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms 
  unfolding distinguishes_from_inner_def
        and distinguishes_inner_def
        and hml_srbb_inner_models.simps
        and hml_srbb_inner_to_hml.simps
proof -
  assume "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                       \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"

  then have "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                        \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
                 \<and> (\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
                 \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))))"
    unfolding hml_and_dist_disj hml_and_and by blast
  hence p_models_stable_conj:
    "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    and no_q_models_stable_conj:
    "\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    by auto

  show "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
            \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                    \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
  proof (rule conjI)
    from p_models_stable_conj and hml_and_and
    have "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
        \<and> hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by blast
    hence "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))"
      and "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    then have "p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)"
      unfolding hml_conjunct_models.simps by auto

    from \<open>hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))\<close>
    show "p \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
              \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and and hml_conjunct_models.simps
    proof (rule conjI)
      from \<open>p \<Turnstile> hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)\<close>
       and models_full_models_dist_subset'
      have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {} then hml_conjunct.Pos (hml.Internal (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> undefined)))
                else (if \<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))" by simp

      then have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {} then hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined))
                else (if \<exists>i\<in>I. \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i))
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i)))
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))"
        unfolding hml_models.simps(5)
              and comp_apply
              and hml_srbb_conjunct_to_hml_conjunct.simps
              and hml_srbb_inner_to_hml.simps.

      then show "p \<Turnstile> hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)"
        unfolding distinguishing_conjunct_def
              and hml_srbb_conjunct_models.simps
        by (smt (verit, ccfv_threshold) LTS_Tau.hml_models.simps(5) comp_apply)
    qed
  next
    from no_q_models_stable_conj
    have "\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    show "\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
                 \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and
            and de_Morgan_conj
    proof (rule ballI)
      fix q
      assume "q \<in> Q"
      with \<open>\<forall>q\<in>Q. \<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
                \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
      have "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
          \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))" by auto
      then show "\<not> hml_conjunct_models q (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))
               \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
        apply (rule disjE)
        using disjI1 apply auto[1]
        unfolding hml_conjunct_models.simps
              and hml_models.simps
      proof (rule disjI2)
        assume "\<not> (\<forall>i\<in>I. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i))"
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)" by auto
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s i))"
          using comp_apply by simp
        hence "\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q"
          using hml_srbb_conjunct_models.simps by simp
        then have "I \<noteq> {}" by blast

        from \<open>I \<noteq> {}\<close>
        have red_dist_conjunct: "distinguishing_conjunct I \<psi>s =
          (\<lambda>q. if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
               then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
               else \<psi>s (SOME i. i \<in> I))"
          unfolding distinguishing_conjunct_def
          by presburger

        from \<open>\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q\<close>
        have "\<not> hml_srbb_conjunct_models (\<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))) q"
          using someI_ex by (smt (verit))

        then have "\<not> hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct
                                        (if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                                         then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                                         else \<psi>s (SOME i. i \<in> I)))"
          unfolding hml_srbb_conjunct_models.simps
          using \<open>\<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q\<close> by simp

        then show "\<not> (\<forall>q'\<in>Q. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) q'))"
          using \<open>q \<in> Q\<close> and comp_apply and red_dist_conjunct by force
      qed
    qed
  qed
qed



lemma dist_branchconj_thinn:
  defines 
    "distinguishing_conjunct \<equiv> (\<lambda>I.\<lambda>\<psi>s.
       \<lambda>q. if I = {}
           then Pos (Conj {} undefined)
           else if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
                then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
                else \<psi>s (SOME i. i \<in> I))" (* c.f. dist_stableconj_thinn for an explanation of this function. *)
  assumes "distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q"
  shows
    "distinguishes_from_inner (BranchConj \<alpha> \<phi> Q (distinguishing_conjunct I \<psi>s)) p Q"
  using assms(2)
  unfolding distinguishes_from_inner_def
        and distinguishes_inner_def
        and hml_srbb_inner_models.simps
        and hml_srbb_inner_to_hml.simps
proof -
  assume "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) 
                    \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))
              \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                      \<and>hml hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
  with hml_and_dist_disj
  have "(p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                   \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))
            \<and> (\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
             \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))))"
    using hml_and_and by blast
  then have p_models_branch_conj:
    "p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
           \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
       and no_q_models_branch_conj:
    "\<forall>q\<in>Q. (\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
            \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))))"
    by auto

  show "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))
          \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                  \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
  proof (rule conjI)
    from p_models_branch_conj
    have "p \<Turnstile> (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))) 
                \<and>hml (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      by auto
    then have "hml_conjunct_models p (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
          and "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
      unfolding hml_and_and by auto

    from \<open>hml_conjunct_models p (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))\<close>
    show "p \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
              \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
      unfolding hml_and_and
    proof (rule conjI)
      from \<open>hml_conjunct_models p (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))\<close>
       and models_full_models_dist_subset'
      have "p \<Turnstile> hml.Conj Q
           (\<lambda>q. if I = {}
                then hml_srbb_conjunct_to_hml_conjunct (hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined))
                else (if \<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q
                     then (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q)
                     else (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) (SOME i. i \<in> I)))"
        unfolding hml_srbb_conjunct_to_hml_conjunct.simps
              and hml_srbb_inner_to_hml.simps
              and hml_srbb_conjunct_models.simps
              and comp_apply and hml_conjunct_models.simps by blast

      then have "p \<Turnstile> hml.Conj Q
          (hml_srbb_conjunct_to_hml_conjunct \<circ>
           (\<lambda>q. if I = {} then hml_srbb_conjunct.Pos (hml_srbb_inner.Conj {} undefined)
                else if \<exists>i\<in>I. \<not> hml_srbb_conjunct_models (\<psi>s i) q
                     then \<psi>s (SOME i. i \<in> I \<and> \<not> hml_srbb_conjunct_models (\<psi>s i) q) else \<psi>s (SOME i. i \<in> I)))"
        using comp_apply and o_def by (smt (verit) hml_models.simps(5))

      then show "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
        unfolding hml_conjunct_models.simps
              and distinguishing_conjunct_def.
    qed
  next
    show "\<forall>q\<in>Q. \<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                     \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
    proof (rule ballI)
      fix q
      assume "q \<in> Q"
      with no_q_models_branch_conj
      have "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
            \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        by auto
      then show "\<not> q \<Turnstile> hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
                     \<and>hml hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s))"
        unfolding hml_and_and and de_Morgan_conj
      proof (rule disjE)
        assume "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))"
        then show "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
               \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
          by (rule disjI1)
      next
        assume "\<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj I (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
        hence "\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)"
          unfolding hml_conjunct_models.simps and hml_models.simps by auto
        then have "I \<noteq> {}" by auto

        then have "distinguishing_conjunct I \<psi>s =
        (\<lambda>q. if \<exists>i \<in> I. \<not>(hml_srbb_conjunct_models (\<psi>s i) q)
             then \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))
             else \<psi>s (SOME i. i \<in> I))"
          using distinguishing_conjunct_def by auto

        with \<open>\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)\<close>

        have "distinguishing_conjunct I \<psi>s q = \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))"
          unfolding hml_srbb_conjunct_models.simps by auto

        show "\<not> hml_conjunct_models q (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)))
         \<or> \<not> hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s)))"
          unfolding hml_conjunct_models.simps and hml_models.simps
        proof (rule disjI2)
          from \<open>\<exists>i\<in>I. \<not> hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) i)\<close>
          have "\<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (\<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))))"
            using someI_ex by (metis (mono_tags, lifting) Inhabited_Tau_LTS.hml_srbb_conjunct_models.elims(1) Inhabited_Tau_LTS_axioms comp_eq_dest_lhs)
          then have "\<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (distinguishing_conjunct I \<psi>s q))"
            using \<open>distinguishing_conjunct I \<psi>s q = \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_srbb_conjunct_models (\<psi>s i) q))\<close> by simp
          then have "\<exists>q'\<in>Q. \<not>hml_conjunct_models q (hml_srbb_conjunct_to_hml_conjunct (distinguishing_conjunct I \<psi>s q'))" 
            using \<open>q \<in> Q\<close> by auto
          then have "\<exists>q'\<in>Q. \<not>hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) q')"
            unfolding comp_apply.
          then show "\<not> (\<forall>i\<in>Q. hml_conjunct_models q ((hml_srbb_conjunct_to_hml_conjunct \<circ> distinguishing_conjunct I \<psi>s) i))"
            by auto
        qed
      qed
    qed
  qed
qed

*)

subsection \<open> HML$_\text{SRBB}$ Implication \<close>

no_notation hml_entails (infixr "\<Rrightarrow>" 60)

abbreviation hml_srbb_impl
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"  (infixr "\<Rrightarrow>" 70)
where
  "hml_srbb_impl \<equiv> entails"

text \<open> One may also reduce HML$_\text{SRBB}$ implication to HML implication via the translation function. \<close>
lemma srbb_impl_to_hml_impl:
  fixes \<phi>l and \<phi>r :: "('a, 's) hml_srbb"
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "hml_entails (hml_srbb_to_hml \<phi>l) (hml_srbb_to_hml \<phi>r)"
  using assms by simp

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

lemma srbb_impl_conjunct_to_hml_impl:
  assumes "\<psi>l \<psi>\<Rrightarrow> \<psi>r"
  shows
    "hml_srbb_conjunct_to_hml_conjunct \<psi>l \<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r"
  using assms by simp

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


text \<open> We may establish that a HML$_\text{SRBB}$ formula is equivalent to another by translating both into
simple HML formulas and testing if those translated formulas are equivalent. \<close>
lemma srbb_eq_hml_eq:
  shows "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r = (hml_srbb_to_hml \<phi>l \<Lleftarrow>\<Rrightarrow> hml_srbb_to_hml \<phi>r)"
  by simp

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
  using assms by auto

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
  using \<epsilon>T_is_T by auto

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
  assume \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have \<open>\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>\<close>
    using assms(1,2) left_right_distinct by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using left_right_distinct \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms(3) using p'_spec by auto
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec(2) have other_conjuncts: \<open>\<forall>j\<in>I. i \<noteq> j \<longrightarrow> hml_srbb_conjunct_models p' (\<Psi> j)\<close>
    using assms stable_conj_parts fun_upd_apply by metis
  from p'_spec(2) have \<open>hml_srbb_conjunct_models p' (\<Psi>' i)\<close>
    using assms(1) stable_conj_parts by blast
  hence \<open>hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    unfolding assms(3) by auto
  with \<open>stable_state p'\<close> have \<open>hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable left_right_distinct by (auto, metis silent_reachable.simps)
  with \<open>stable_state p'\<close> have \<open>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using pre_\<epsilon> by auto
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
  assume \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>)\<close>
  then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close> by auto
  hence \<open>stable_state p'\<close> by auto
  from p'_spec have
    \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> (\<exists>p''. p' \<Zsurj> p'' \<and> hml_srbb_inner_models p'' \<chi>)\<close>
    using left_right_distinct by fastforce
  with \<open>stable_state p'\<close> have \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow> hml_srbb_inner_models p' \<chi>\<close>
    using stable_state_stable by blast
  hence pos_rewrite: \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>
      hml_srbb_conjunct_models p' (Neg (StableConj {left} (\<lambda>_. Neg \<chi>)))\<close>
    using left_right_distinct \<open>stable_state p'\<close> stable_state_stable by (auto, blast)
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>')\<close>
    unfolding assms using p'_spec
    by (auto, metis (no_types, lifting) hml_srbb_conjunct.exhaust hml_srbb_conjunct.simps(5,6)
        hml_srbb_conjunct_models.elims(2) pos_rewrite)
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
    using \<open>p \<Zsurj> p'\<close> by auto
next
  fix p
  assume \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>')\<close>
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
    using stable_state_stable left_right_distinct by (auto, metis silent_reachable.simps)
  with \<open>stable_state p'\<close> have pos_conjuncts:
      \<open>\<forall>\<chi> i. i\<in>I \<and> \<Psi> i = Pos \<chi> \<longrightarrow>hml_srbb_conjunct_models p' (Pos \<chi>)\<close>
    using pre_\<epsilon> by auto
  hence \<open>hml_srbb_inner_models p' (StableConj I \<Psi>)\<close>
    using p'_spec assms other_conjuncts 
    by (auto, metis other_conjuncts pos_conjuncts
              hml_srbb_conjunct.exhaust hml_srbb_conjunct_models.elims(2))
  thus \<open>p \<Turnstile>SRBB hml_srbb.Internal (StableConj I \<Psi>)\<close>
    using p'_spec(1) by auto
qed

end (* Inhabited_Tau_LTS *)

end
