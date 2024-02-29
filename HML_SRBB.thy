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

fun hml_srbb_models :: "'s \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool" (infix "\<Turnstile>SRBB" 60)where
  "hml_srbb_models state formula = (state \<Turnstile> (hml_srbb_to_hml formula))"

fun hml_srbb_inner_models :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_inner_models \<chi> s = (s \<Turnstile> (hml_srbb_inner_to_hml \<chi>))"

fun hml_srbb_conjunct_models :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_srbb_conjunct_models \<psi> s = (hml_conjunct_models s (hml_srbb_conjunct_to_hml_conjunct \<psi>))"


subsubsection \<open> Semantic Function for HML$_\text{SRBB}$ \<close>

text \<open>
We define the meaning of a HML$_\text{SRBB}$ formula @{term "\<phi>"}, written \<open>\<lbrakk>\<phi>\<rbrakk>\<close>), to be the set of all processes
that satisfy this formula @{term "\<phi>"}.
\<close>

abbreviation model_set :: "('a, 's) hml_srbb \<Rightarrow> 's set" where
  "model_set \<phi> \<equiv> {p. p \<Turnstile>SRBB \<phi>}"

abbreviation model_set_inner :: "('a, 's) hml_srbb_inner \<Rightarrow> 's set" where
  "model_set_inner \<chi> \<equiv> {p. hml_srbb_inner_models \<chi> p}"

abbreviation model_set_conjunct :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's set" where
  "model_set_conjunct \<psi> \<equiv> {p. hml_srbb_conjunct_models \<psi> p}"


subsection \<open> Different Variants of Verum \<close>

text \<open>The formula \<open>\<top>\<close> is equal to \<open>\<And>{}\<close>. \<close>
lemma empty_imm_conj:
  "(state \<Turnstile>SRBB TT) = (state \<Turnstile>SRBB ImmConj {} \<psi>s)"
  by simp

text \<open>The formula \<open>\<top>\<close> is equal to \<open>\<langle>\<epsilon>\<rangle>\<And>{}\<close>. \<close>
lemma empty_inner_conj:
  "(state \<Turnstile>SRBB TT) = (hml_srbb_inner_models (Conj {} \<psi>s) state)"
  by simp

text \<open>The formula \<open>\<top>\<close> is equal to \<open>(\<tau>)\<top>\<close>. \<close>
lemma tau_obs_triv:
  "(state \<Turnstile>SRBB TT) = (hml_srbb_inner_models (Obs \<tau> TT) state)"
  by simp

text \<open>The formula \<open>\<top>\<close> is equal to \<open>\<And>{(\<tau>)\<top>}\<close>. \<close>
lemma empty_branch_conj_tau:
  "(state \<Turnstile>SRBB TT) = (hml_srbb_inner_models (BranchConj \<tau> TT {} \<psi>s) state)"
  by (smt (verit, del_insts) Inhabited_Tau_LTS.hml_srbb_models.elims(1) Inhabited_Tau_LTS.tau_obs_triv Inhabited_Tau_LTS_axioms LTS_Tau.hml_conjunct_models.simps(1) LTS_Tau.hml_models.simps(1) LTS_Tau.hml_models.simps(5) LTS_Tau.tt_eq_empty_conj hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps(1) hml_srbb_inner_to_hml.simps(4) hml_srbb_to_hml.simps(1))


subsection \<open> Distinguishing Formulas \<close>

text \<open>
A formula \<open>\<phi>\<close> is said to 'distinguish' a process \<open>p\<close> from another process \<open>q\<close>,
if \<open>p\<close> satisfies \<open>\<phi>\<close>, while \<open>q\<close> does not.
\<close>
definition distinguishes :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "distinguishes \<phi> p q \<equiv> p \<Turnstile>SRBB \<phi> \<and> \<not>(q \<Turnstile>SRBB \<phi>)"

text \<open>
One may evaluate wheter a HML$_\text{SRBB}$ formula distinguishes two processes by translating the formula
into a HML formula and then check if this formula distinguishes the two processes.
\<close>
lemma dist_srbb_eq_dist_hml:
  "distinguishes \<phi> p q = p <> (hml_srbb_to_hml \<phi>) q"
  by (simp add: distinguishes_def distinguishes_hml_def)

text \<open>Now, we take a look at some basic properties of the \<open>distinguishes\<close> predicate: \<close>

text \<open> \<open>\<top>\<close> can never distinguish two processes. This is due to the fact that every process
satisfies \<open>T\<close>. Therefore, the second part of the definition of \<open>distinguishes\<close> never holds. \<close>
lemma verum_never_distinguishes:
  "\<not> distinguishes TT p q"
  by (simp add: distinguishes_def)

text \<open> A process can never be distinguished from itself, regardless of which formula you choose. \<close>
lemma no_self_distinguishing:
  "\<not> distinguishes \<phi> p p"
  by (simp add: distinguishes_def)

text \<open> These definitions need to be repeated for each mutually recursive data type: \<close>

definition
  distinguishes_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where
  "distinguishes_inner \<chi> p q
 \<equiv> hml_srbb_inner_models \<chi> p \<and> \<not>(hml_srbb_inner_models \<chi> q)"

lemma dist_inner_srbb_eq_dist_hml:
  "distinguishes_inner \<chi> p q = p <> (hml_srbb_inner_to_hml \<chi>) q"
  by (simp add: distinguishes_inner_def distinguishes_hml_def)


definition
  distinguishes_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool"
where
  "distinguishes_conjunct \<psi> p q
 \<equiv> hml_srbb_conjunct_models \<psi> p \<and> \<not>(hml_srbb_conjunct_models \<psi> q)"

lemma dist_conjunct_srbb_eq_dist_conjunct_hml:
  "distinguishes_conjunct \<psi> p q
 = distinguishes_conjunct_hml p (hml_srbb_conjunct_to_hml_conjunct \<psi>) q"
  by (simp add: distinguishes_conjunct_def distinguishes_conjunct_hml_def)

text \<open>
We lift this notion of distinguishing formulas to sets of processes on the right hand side.
We say that a formula @{term "\<phi>"} distinguishes a process @{term "p"} from a set of processes
@{term "Q"} if @{term "p"} satisfies the formula @{term "\<phi>"}, while every process in @{term "Q"} does not.
Once again we need this slightly stronger notion then the one that one would obtain by naively lifting
the distinguishing predicate (see @{term "distinguishes_from'"}, \ref{sect:hmlDist}).
\\\\
As with the previous definitions, we need to duplicate the definition of each mutually recursive type
@{term "hml_srbb_inner"} and @{term "hml_srbb_conjunct"}.
\<close>

definition distinguishes_from :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from \<phi> p Q \<equiv> p \<Turnstile>SRBB \<phi> \<and> (\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB \<phi>))"

lemma dist_from_srbb_eq_dist_from_hml:
  "distinguishes_from \<phi> p Q = p <> (hml_srbb_to_hml \<phi>) Q"
  by (simp add: distinguishes_from_def distinguishes_from_hml_def)

definition distinguishes_from' :: "('a, 's) hml_srbb \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool" where
  "distinguishes_from' \<phi> p Q \<equiv> \<forall>q \<in> Q. distinguishes \<phi> p q"

lemma distinguishes_from_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from \<phi> p Q = distinguishes_from' \<phi> p Q"
  using assms distinguishes_def distinguishes_from'_def distinguishes_from_def ex_in_conv by auto

lemma distinguishes_from_priming:
  assumes "distinguishes_from \<phi> p Q"
  shows "distinguishes_from' \<phi> p Q"
  using assms distinguishes_def distinguishes_from'_def distinguishes_from_def ex_in_conv by auto


definition
  distinguishes_from_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
where
  "distinguishes_from_inner \<chi> p Q
 \<equiv> hml_srbb_inner_models \<chi> p \<and> (\<forall>q \<in> Q. \<not>(hml_srbb_inner_models \<chi> q))"

lemma dist_from_inner_srbb_eq_dist_from_hml:
  "distinguishes_from_inner \<chi> p Q = p <> (hml_srbb_inner_to_hml \<chi>) Q"
  by (simp add: distinguishes_from_inner_def distinguishes_from_hml_def)

definition
  distinguishes_from_inner'
  :: "('a, 's) hml_srbb_inner \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
where
  "distinguishes_from_inner' \<chi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_inner \<chi> p q"

lemma distinguishes_from_inner_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from_inner \<phi> p Q = distinguishes_from_inner' \<phi> p Q"
  using assms distinguishes_inner_def distinguishes_from_inner'_def distinguishes_from_inner_def ex_in_conv by auto

lemma distinguishes_from_inner_priming:
  assumes "distinguishes_from_inner \<phi> p Q"
  shows "distinguishes_from_inner' \<phi> p Q"
  using assms distinguishes_inner_def distinguishes_from_inner'_def distinguishes_from_inner_def ex_in_conv by auto


definition
  distinguishes_from_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
where
  "distinguishes_from_conjunct \<psi> p Q
 \<equiv> hml_srbb_conjunct_models \<psi> p \<and> (\<forall>q \<in> Q. \<not>(hml_srbb_conjunct_models \<psi> q))"

lemma dist_from_conjunct_srbb_eq_dist_from_hml:
  "distinguishes_from_conjunct \<psi> p Q
 = distinguishes_conjunct_from_hml p (hml_srbb_conjunct_to_hml_conjunct \<psi>) Q"
  by (simp add: distinguishes_from_conjunct_def distinguishes_conjunct_from_hml_def)

definition
  distinguishes_from_conjunct'
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> 's \<Rightarrow> 's set \<Rightarrow> bool"
where
  "distinguishes_from_conjunct' \<psi> p Q \<equiv> \<forall>q \<in> Q. distinguishes_conjunct \<psi> p q"

lemma distinguishes_from_conjunct_prime:
  assumes "Q \<noteq> {}"
  shows "distinguishes_from_conjunct \<phi> p Q = distinguishes_from_conjunct' \<phi> p Q"
  using assms distinguishes_conjunct_def distinguishes_from_conjunct'_def distinguishes_from_conjunct_def ex_in_conv by auto

lemma distinguishes_from_conjunct_priming:
  assumes "distinguishes_from_conjunct \<phi> p Q"
  shows "distinguishes_from_conjunct' \<phi> p Q"
  using assms distinguishes_conjunct_def distinguishes_from_conjunct'_def distinguishes_from_conjunct_def ex_in_conv by auto


subsubsection \<open> Distinguishing Conjunctions \<close>

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term "p"} from @{term "q"},
then there must be at least one conjunct in this conjunction that distinguishes @{term "p"} from @{term "q"}.
\<close>
lemma srbb_dist_imm_conjunction_implies_dist_conjunct:
  assumes "distinguishes (ImmConj I \<psi>s) p q"
  shows "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
  using assms distinguishes_conjunct_def distinguishes_def by auto

text \<open>
If there is one conjunct in that distinguishes @{term "p"} from @{term "q"}
and @{term "p"} satisfies all other conjuncts in a conjunction
then $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ (where $\psi s$ ranges over the previously mentioned
conjunctions) distinguishes @{term "p"} from @{term "q"}.
\<close>
lemma srbb_dist_conjunct_implies_dist_imm_conjunction:
  assumes "i\<in>I"
      and "distinguishes_conjunct (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p"
    shows "distinguishes (ImmConj I \<psi>s) p q"
  using assms distinguishes_conjunct_def distinguishes_def by auto

text \<open>
If $\bigwedge\nolimits_{i \in I} {\psi s}(i)$ distinguishes @{term "p"} from @{term "q"},
then there must be at least one conjunct in this conjunction that distinguishes @{term "p"} from @{term "q"}.

This differs from @{term "srbb_dist_imm_conjunction_implies_dist_conjunct"} in that it addresses
simple conjunctions in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunction_implies_dist_conjunct:
  assumes "distinguishes_inner (Conj I \<psi>s) p q"
  shows "\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
  using assms distinguishes_conjunct_def distinguishes_inner_def by auto

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for simple conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_implies_dist_conjunction:
  assumes "i\<in>I"
      and "distinguishes_conjunct (\<psi>s i) p q"
      and "\<forall>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p"
  shows "distinguishes_inner (Conj I \<psi>s) p q"
  using assms distinguishes_conjunct_def distinguishes_inner_def by auto

text \<open>
We also replicate @{term "srbb_dist_imm_conjunction_implies_dist_conjunct"} for stable conjunctions
$\neg\langle\tau\rangle\top\land\bigwedge\nolimits_{i \in I} {\psi s}(i)$.
Here, either the stability condition distinguishes @{term "p"} from @{term "q"} or there must be
a distinguishing conjunct.
\<close>
lemma srbb_dist_stable_conjunction_implies_dist_conjunct_or_stable:
  assumes "distinguishes_inner (StableConj I \<psi>s) p q"
  shows "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q)
       \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  using assms
  unfolding distinguishes_inner_def
            distinguishes_hml_def
            distinguishes_conjunct_def
            hml_srbb_inner_models.simps
            hml_srbb_inner_to_hml.simps
            hml_and_and
            hml_conjunct_models.simps 
  by auto

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for stable conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_or_stable_implies_dist_stable_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
      and "p \<Turnstile> (HML_not (hml.Obs \<tau> hml.TT))"
      and "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q)
         \<or> (p <> (HML_not (hml.Obs \<tau> hml.TT)) q)"
  shows "distinguishes_inner (StableConj I \<psi>s) p q"
  using assms
  unfolding hml_not_not_models
            distinguishes_inner_def
            hml_srbb_inner_models.simps
            hml_srbb_inner_to_hml.simps
            hml_and_and
            hml_conjunct_models.simps
            distinguishes_hml_def 
  using distinguishes_conjunct_def by auto

text \<open>
We also replicate @{term "srbb_dist_imm_conjunction_implies_dist_conjunct"} for branching conjunctions
$(\alpha)\varphi\land\bigwedge\nolimits_{i \in I} {\psi s}(i)$.
Here, either the branching condition distinguishes @{term "p"} from @{term "q"} or there must be
a distinguishing conjunct.
\<close>
lemma srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch:
  assumes "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  shows "(\<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q)
       \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
  using assms
  unfolding distinguishes_inner_def
            hml_srbb_inner_models.simps
            hml_srbb_inner_to_hml.simps
            hml_and_and
            hml_conjunct_models.simps 
  using distinguishes_conjunct_def by fastforce

text \<open>
In the following, we replicate @{term "srbb_dist_conjunct_implies_dist_imm_conjunction"} for branching conjunctions
in @{term "hml_srbb_inner"}.
\<close>
lemma srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction:
  assumes "\<forall>i \<in> I. hml_srbb_conjunct_models (\<psi>s i) p"
      and "hml_srbb_inner_models (Obs \<alpha> \<phi>) p"
      and "(i\<in>I \<and> distinguishes_conjunct (\<psi>s i) p q)
         \<or> (distinguishes_inner (Obs \<alpha> \<phi>) p q)"
  shows "distinguishes_inner (BranchConj \<alpha> \<phi> I \<psi>s) p q"
  using assms
  unfolding distinguishes_inner_def
            hml_srbb_inner_models.simps
            hml_srbb_inner_to_hml.simps
            hml_and_and
            hml_conjunct_models.simps
  using distinguishes_conjunct_def by auto


subsubsection \<open> Distinguishing Conjunction Thinning \<close>

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

subsection \<open> HML$_\text{SRBB}$ Implication \<close>

text \<open>
As for our \<open>hml\<close> data type, we define what is means for one HML$_\text{SRBB}$ formula to imply another (denoted as \<open>\<phi>p \<Rrightarrow> \<phi>c\<close>) by
requiring that if the formula in the premise holds, the formula in the place of the conclusion must be satisfied as well.
\<close>

definition
  hml_srbb_impl
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"
  (infix "\<Rrightarrow>" 70)
where
  "\<phi>l \<Rrightarrow> \<phi>r \<equiv> \<forall>p. p \<Turnstile>SRBB \<phi>l \<longrightarrow> p \<Turnstile>SRBB \<phi>r"

text \<open> One may also reduce HML$_\text{SRBB}$ implication to HML implication via the translation function. \<close>
lemma srbb_impl_to_hml_impl:
  fixes \<phi>l and \<phi>r :: "('a, 's) hml_srbb"
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "hml_srbb_to_hml \<phi>l \<Rrightarrow> hml_srbb_to_hml \<phi>r"
  using assms
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_def)

text \<open>HML$_\text{SRBB}$ impliation is a pre-order. \<close>
lemma hml_srbb_impl_preord:
  shows "reflp (hml_srbb_impl) \<and> transp (hml_srbb_impl)"
  by (metis hml_srbb_impl_def reflpI transpI)

text \<open> Now, these definitions and lemmas need to be repeated for the other mutually recursive
data types.
\<close>

definition
  hml_srbb_impl_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  (infix "\<chi>\<Rrightarrow>" 70)
where
  "\<chi>l \<chi>\<Rrightarrow> \<chi>r \<equiv> \<forall>p. hml_srbb_inner_models \<chi>l p \<longrightarrow> hml_srbb_inner_models \<chi>r p"

lemma hml_srbb_impl_inner_preord:
  shows "reflp (hml_srbb_impl_inner) \<and> transp (hml_srbb_impl_inner)"
  by (metis hml_srbb_impl_inner_def reflpI transpI)

lemma srbb_impl_inner_to_hml_impl:
  assumes "\<chi>l \<chi>\<Rrightarrow> \<chi>r"
  shows "hml_srbb_inner_to_hml \<chi>l \<Rrightarrow> hml_srbb_inner_to_hml \<chi>r"
  using assms
  by (simp add: LTS_Tau.hml_impl_iffI hml_srbb_impl_inner_def)


definition
  hml_srbb_impl_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool"
  (infix "\<psi>\<Rrightarrow>" 70)
where
  "\<psi>l \<psi>\<Rrightarrow> \<psi>r
 \<equiv> \<forall>p. hml_srbb_conjunct_models \<psi>l p \<longrightarrow> hml_srbb_conjunct_models \<psi>r p"

lemma hml_srbb_impl_conjunct_preord:
  shows "reflp (hml_srbb_impl_conjunct) \<and> transp (hml_srbb_impl_conjunct)"
  by (metis hml_srbb_impl_conjunct_def reflpI transpI)

lemma srbb_impl_conjunct_to_hml_impl:
  assumes "\<psi>l \<psi>\<Rrightarrow> \<psi>r"
  shows
    "hml_srbb_conjunct_to_hml_conjunct \<psi>l \<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r"
  using assms
  by (simp add: hml_conjunct_impl_def hml_srbb_impl_conjunct_def)


subsection \<open> HML$_\text{SRBB}$ Equivalence \<close>

text \<open>
We define HML$_\text{SRBB}$ formula equivalence to by appealing to HML$_\text{SRBB}$ implication.
A HML$_\text{SRBB}$ formula is equivalent to another formula if both imply each other.
\<close>

definition
  hml_srbb_eq
  :: "('a, 's) hml_srbb \<Rightarrow> ('a, 's) hml_srbb \<Rightarrow> bool"
  (infix "\<Lleftarrow>srbb\<Rrightarrow>" 70)
where
  "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r \<equiv> \<phi>l \<Rrightarrow> \<phi>r \<and> \<phi>r \<Rrightarrow> \<phi>l"

text \<open> A HML$_\text{SRBB}$ formula is equivalent to another if
satisfaction of either formula implies the satisfaction of the other. \<close>
lemma hml_srbb_eq_iff:
  shows "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r = (\<forall>p. p \<Turnstile>SRBB \<phi>l \<longleftrightarrow> p \<Turnstile>SRBB \<phi>r)"
  using hml_srbb_eq_def hml_srbb_impl_def by blast

text \<open> We may establish that a HML$_\text{SRBB}$ formula is equivalent to another by translating both into
simple HML formulas and testing if those translated formulas are equivalent. \<close>
lemma srbb_eq_hml_eq:
  shows "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r = (hml_srbb_to_hml \<phi>l \<Lleftarrow>\<Rrightarrow> hml_srbb_to_hml \<phi>r)"
  by (simp add: hml_eq_equality hml_srbb_eq_iff)

text \<open> HML$_\text{SRBB}$ equivalence is an equivalence relation. \<close>
lemma hml_srbb_eq_equiv: "equivp (\<Lleftarrow>srbb\<Rrightarrow>)"
  by (smt (verit, ccfv_threshold) equivpI hml_srbb_eq_def hml_srbb_impl_preord reflp_on_def sympI transpE transpI)

text \<open> These definitions and lemmas are repeated for the other mutually recursive data types. \<close>

definition
  hml_srbb_eq_inner
  :: "('a, 's) hml_srbb_inner \<Rightarrow> ('a, 's) hml_srbb_inner \<Rightarrow> bool"
  (infix "\<Lleftarrow>\<chi>\<Rrightarrow>" 70)
where
  "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r \<equiv> \<chi>l \<chi>\<Rrightarrow> \<chi>r \<and> \<chi>r \<chi>\<Rrightarrow> \<chi>l"

lemma hml_srbb_eq_inner_iff:
  shows "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r
      = (\<forall>p. hml_srbb_inner_models \<chi>l p  \<longleftrightarrow> hml_srbb_inner_models \<chi>r p)"
  using hml_srbb_eq_inner_def hml_srbb_impl_inner_def by blast

lemma srbb_eq_inner_hml_eq:
  shows "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r = (hml_srbb_inner_to_hml \<chi>l \<Lleftarrow>\<Rrightarrow> hml_srbb_inner_to_hml \<chi>r)"
  by (simp add: hml_eq_equality hml_srbb_eq_inner_iff)

lemma hml_srbb_eq_inner_equiv: "equivp (\<Lleftarrow>\<chi>\<Rrightarrow>)"
  using hml_srbb_impl_inner_preord
  by (smt (verit, best) hml_srbb_eq_inner_def Inhabited_Tau_LTS_axioms equivpI reflpD reflpI symp_def transpE transpI)


definition
  hml_srbb_eq_conjunct
  :: "('a, 's) hml_srbb_conjunct \<Rightarrow> ('a, 's) hml_srbb_conjunct \<Rightarrow> bool"
  (infix "\<Lleftarrow>\<psi>\<Rrightarrow>" 70)
where
  "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r \<equiv> \<psi>l \<psi>\<Rrightarrow> \<psi>r \<and> \<psi>r \<psi>\<Rrightarrow> \<psi>l"

lemma hml_srbb_eq_conjunct_iff:
  shows "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r
      = (\<forall>p. hml_srbb_conjunct_models \<psi>l p  \<longleftrightarrow> hml_srbb_conjunct_models \<psi>r p)"
  using hml_srbb_eq_conjunct_def hml_srbb_impl_conjunct_def by blast

lemma srbb_eq_conjunct_hml_conjunct_eq:
  shows "\<psi>l \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>r
      = (hml_srbb_conjunct_to_hml_conjunct \<psi>l \<Lleftarrow>\<and>\<Rrightarrow> hml_srbb_conjunct_to_hml_conjunct \<psi>r)"
  using hml_conjunct_eq_def hml_conjunct_impl_def hml_srbb_eq_conjunct_iff by auto

lemma hml_srbb_eq_conjunct_equiv: "equivp (\<Lleftarrow>\<psi>\<Rrightarrow>)"
  using equivp_def hml_srbb_eq_conjunct_iff by fastforce


subsection \<open> Substitution \<close>

lemma srbb_internal_subst:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
      and "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>l)"
    shows "\<phi> \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  by (smt (verit) assms(1) assms(2) hml_impl_iffI hml_models.simps(3) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_def hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2) srbb_impl_inner_to_hml_impl)


subsection \<open> Congruence \<close>

text \<open> This section provides means to derive new equivalences by extending both sides with a given prefix.  \<close>

text \<open> Prepending $\langle\varepsilon\rangle\dots$ preserves equivalence. \<close>
lemma internal_srbb_cong:
  assumes "\<chi>l \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>r"
  shows "(Internal \<chi>l) \<Lleftarrow>srbb\<Rrightarrow> (Internal \<chi>r)"
  using assms
  by (smt (verit) hml_models.simps(3) hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_eq_inner_def hml_srbb_eq_def hml_srbb_impl_inner_def hml_srbb_impl_def hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2))

text \<open>If equivalent conjuncts are included in an otherwise identical conjunction, the equivalence is preserved.  \<close>
lemma immconj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  shows "ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
  using assms
proof -
  assume "\<psi>sl ` I = \<psi>sr ` I"
    and "\<psi>sl s \<Lleftarrow>\<psi>\<Rrightarrow> \<psi>sr s"
  then have "(\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p) \<and>
             (\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p)"
    unfolding hml_srbb_eq_conjunct_def and hml_srbb_impl_conjunct_def by auto
  then have "\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p"
        and "\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p" by auto

  show "ImmConj (I \<union> {s}) \<psi>sl \<Lleftarrow>srbb\<Rrightarrow> ImmConj (I \<union> {s}) \<psi>sr"
    unfolding hml_srbb_eq_def
          and hml_srbb_impl_def
          and hml_srbb_models.simps
          and hml_srbb_to_hml.simps
          and hml_models.simps
  proof (rule conjI)
    show "\<forall>p. (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)) \<longrightarrow>
              (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i))"
    proof (rule allI, rule impI)
      fix p
      assume "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)"
      then have "(hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s))
               \<and> (\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i))"
        by fastforce
      then have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)"
            and "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)" by auto

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)\<close>
       and \<open>\<forall>p. hml_srbb_conjunct_models (\<psi>sl s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sr s) p\<close>
      have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)" 
        by simp

      from \<open>\<psi>sl ` I = \<psi>sr ` I\<close> and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" 
        by (metis comp_apply image_iff)

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)\<close>
      show "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" 
        by fastforce
    qed
  next
    show "\<forall>p. (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)) \<longrightarrow>
              (\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i))"
    proof (rule allI, rule impI)
      fix p
      assume "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)"
      then have "(hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s))
               \<and> (\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i))"
        by fastforce
      then have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)"
            and "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)" by auto

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) s)\<close>
       and \<open>\<forall>p. hml_srbb_conjunct_models (\<psi>sr s) p \<longrightarrow> hml_srbb_conjunct_models (\<psi>sl s) p\<close>
      have "hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)" 
        by simp

      from \<open>\<psi>sl ` I = \<psi>sr ` I\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sr) i)\<close>
      have "\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)"
        by (smt (verit, ccfv_SIG) image_eq_imp_comp image_iff)

      from \<open>hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) s)\<close>
       and \<open>\<forall>i\<in>I. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)\<close>
      show "\<forall>i\<in>I \<union> {s}. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>sl) i)" 
        by fastforce
    qed
  qed
qed

text \<open> Prepending $(\alpha)\dots$ preserves equivalence. \<close>
lemma obs_srbb_cong:
  assumes "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<chi>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms 
  apply (cases "\<alpha> \<noteq> \<tau>")
  apply (smt (verit) hml_impl_iffI hml_models.simps(2) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_inner_def hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(1) srbb_impl_to_hml_impl)
  using hml_impl_iffI hml_models.simps(4) hml_srbb_eq_def hml_srbb_eq_inner_def hml_srbb_impl_inner_def hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(1) srbb_impl_to_hml_impl by auto

subsection \<open> Known Equivalence Elements \<close>

text \<open>The formula $(\tau)\top$ is equivalent to $\bigwedge\{\}$. \<close>
lemma srbb_obs_\<tau>_is_\<chi>TT: "Obs \<tau> TT \<Lleftarrow>\<chi>\<Rrightarrow> Conj {} \<psi>s"
  by (simp add: hml_srbb_eq_inner_def hml_srbb_impl_inner_def)

text \<open>The formula $(\alpha)\varphi$ is equivalent to $(\alpha)\varphi \land \bigwedge\{\}$. \<close>
lemma srbb_obs_is_empty_branch_conj: "Obs \<alpha> \<phi> \<Lleftarrow>\<chi>\<Rrightarrow> BranchConj \<alpha> \<phi> {} \<psi>s"
  unfolding srbb_eq_inner_hml_eq and hml_srbb_inner_to_hml.simps
proof -
  from T_is_empty_conj
  have "hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<Lleftarrow>\<Rrightarrow> hml.TT" 
    using hml_eq_equality by force
  have    "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))"
    using hml_eq_equality by blast
  then have "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos hml.TT)"
    using and_subst_right[OF pos_cong[OF \<open>hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s) \<Lleftarrow>\<Rrightarrow> hml.TT\<close>]] by auto
  then have "(hml_conjunct.Pos (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))
      \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s)))
  \<Lleftarrow>\<Rrightarrow>      (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))"
    using hml_and_right_tt 
    by (simp add: LTS_Tau.hml_eq_equality)
  then show "HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>) \<Lleftarrow>\<Rrightarrow>
    hml_conjunct.Pos
     (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>)) \<and>hml hml_conjunct.Pos (hml.Conj {} (hml_srbb_conjunct_to_hml_conjunct \<circ> \<psi>s))"
    by (meson LTS_Tau.hml_eq_equality)
qed

text \<open> The formula $\top$ is equivalent to $\langle\varepsilon\rangle\bigwedge\{\}$.\<close>
lemma srbb_TT_is_\<chi>TT: "TT \<Lleftarrow>srbb\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using \<epsilon>T_is_T hml_eq_def hml_impl_iffI hml_srbb_eq_def hml_srbb_impl_def by auto

text \<open> The formula $\top$ is equivalent to $\bigwedge\{\}$.\<close>
lemma srbb_TT_is_empty_conj: "TT \<Lleftarrow>srbb\<Rrightarrow> ImmConj {} \<psi>s"
  by (simp add: hml_srbb_eq_def hml_srbb_impl_def)


subsection \<open> Distinguishing Formulas and Equivalence \<close>

text \<open> If $\varphi$ is equivalent to $\varphi'$ and $\varphi$ distinguishes process @{term "p"} from
process @{term "q"}, the $\varphi'$ also distinguishes process @{term "p"} from process @{term "q"}. \<close>
lemma dist_equal_dist:
  assumes "\<phi>l \<Lleftarrow>srbb\<Rrightarrow> \<phi>r"
      and "distinguishes \<phi>l p q"
    shows "distinguishes \<phi>r p q"
  using assms
  by (simp add: distinguishes_def hml_srbb_eq_iff)


subsection \<open> HML$_\text{SRBB}$ Formula Set derived Pre-Order on Processes \<close>

text \<open> A set of HML$_\text{SRBB}$ formulas pre-order two processes @{term "p"} and @{term "q"} if
for all formulas in this set the fact that @{term "p"} satisfies a formula means that also
@{term "q"} must satisfy this formula. \<close>
definition hml_preordered :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_preordered \<phi>s p q \<equiv> \<forall>\<phi> \<in> \<phi>s. p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"

text \<open>
If a set of formulas pre-orders two processes @{term "p"} and @{term "q"}, then no formula in that set
may distinguish @{term "p"} from @{term "q"}.
\<close>
lemma "hml_preordered \<phi>s p q = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q))"
  by (simp add: distinguishes_def hml_preordered_def)

text \<open> A formula set derived pre-order is a pre-order. \<close>
lemma "reflp (hml_preordered \<phi>s) \<and> transp (hml_preordered \<phi>s)"
proof (rule conjI)
  show "reflp (hml_preordered \<phi>s)" 
    by (simp add: hml_preordered_def reflpI)
next
  show "transp (hml_preordered \<phi>s)" 
    by (smt (verit, best) hml_preordered_def transpI)
qed

subsection \<open>HML$_\text{SRBB}$ Formula Set derived Equivalence of Processes \<close>

text \<open> A set of HML$_\text{SRBB}$ formulas equates two processes @{term "p"} and @{term "q"} if
this set of formulas pre-orders these two processes in both directions. \<close>
definition hml_equivalent :: "(('a, 's) hml_srbb) set \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> bool" where
  "hml_equivalent \<phi>s p q \<equiv> hml_preordered \<phi>s p q \<and> hml_preordered \<phi>s q p"

text \<open>
If a set of formulas equates two processes @{term "p"} and @{term "q"}, then no formula in that set
may distinguish @{term "p"} from @{term "q"} nor the other way around.
\<close>
lemma "hml_equivalent \<phi>s p q
     = (\<forall>\<phi> \<in> \<phi>s. \<not>(distinguishes \<phi> p q) \<and> \<not>(distinguishes \<phi> q p))"
  using distinguishes_def hml_equivalent_def hml_preordered_def by auto

text \<open> A formula set derived equivalence is an equivalence. \<close>
lemma "equivp (hml_equivalent \<phi>s)"
proof (rule equivpI)
  show "reflp (hml_equivalent \<phi>s)" 
    by (simp add: hml_equivalent_def hml_preordered_def reflpI)
next
  show "symp (hml_equivalent \<phi>s)" 
    by (metis hml_equivalent_def sympI)
next
  show "transp (hml_equivalent \<phi>s)" 
    by (smt (verit) hml_equivalent_def hml_preordered_def transpI)
qed

end (* Inhabited_Tau_LTS *)

end
