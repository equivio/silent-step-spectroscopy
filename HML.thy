text \<open>\newpage\<close>
section \<open> Hennessy-Milner Logic (HML) \label{sect:HML}\<close>
theory HML
  imports LTS_Semantics
begin

text \<open>
In the context of this project, Hennessy-Milner Logic (HML) formulas are used to characterize different
notions of behavioural equivalence.
A particular equivalence $\sim_x$ is characterized by a subsets of the full HML language ($\mathrm{HML}_x$)
for which each element formula may only distinguish two processes if and only if those two processes are not
considered equivalent by the equivalence $\sim_x$. 
In this section, we define a dataype representing HML formulas (\ref{sect:hmlDatatype}) and
define the meaning of such formulas (\ref{sect:hmlSemantic}). 
Next, we define what it means of an HML formula to imply another formula (\ref{sect:hmlImpl}) and
introduce equivalence of HML formulas (\ref{sect:hmlEq}).
Finally, the notion of a formula distinguishing two processes is introduced in (\ref{sect:hmlDist}).
Sections \ref{sect:hmlSRBB} and \ref{sect:ExpressivenessMeasure} give insights into how sublanguages are defined in this project.
For a concrete example of how behavioural equivalences can be characterized by HML language subsets,
reference the corresponding proof for weak trace equivalence can be found in appendix \ref{appndx:weakTraces}.
\<close> 

subsection \<open> Representation of HML Formulas \label{sect:hmlDatatype} \<close>

text \<open>
The mutually recursive data types @{term "hml"} and @{term "hml_conjunct"} represent arbitrary HML formulas.

In particular:
\begin{itemize}
  \item in @{term "hml"}
  \begin{itemize}
    \item @{term "TT"} encodes \<open>\<top>\<close>
    \item \<open>(Obs \<alpha> \<phi>)\<close> encodes \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> and is to be read as '\<open>\<alpha>\<close> can be observed and then \<open>\<phi>\<close> holds'.
    \item \<open>(Internal \<phi>)\<close> encodes \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> and is to be read as 'after arbitrarily much internal behaviour \<open>\<phi>\<close> holds'.
    \item \<open>(Silent \<phi>)\<close> encodes \<open>(\<tau>)\<phi>\<close> and is to be read as '\<open>\<phi>\<close> holds after possibly no or exactly one internal step'.
    \item \<open>(Conj I \<psi>s)\<close> encodes $\bigwedge\nolimits_{i \in \mathrm{\texttt{I}}} {\psi s}(i)$ and is to be read as 'for all i in I the conjunct ${\psi s}(i)$ holds'.
  \end{itemize}
  \item in @{term "hml_conjunct"}
  \begin{itemize}
    \item \<open>(Pos \<phi>)\<close> encodes \<open>\<phi>\<close> when used as a conjunct and is to be read exactly as \<open>\<phi>\<close>.
    \item \<open>(Neg \<phi>)\<close> encodes \<open>\<not>\<phi>\<close> in position of a conjunct and is to be read as '\<open>\<phi>\<close> does not hold'.
  \end{itemize}
\end{itemize}
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

text \<open>
When a variable is of type @{term "hml"} then @{term "\<phi>"} is used in most cases.
In case a variable is of type @{term "hml_conjunct"} then @{term "\<psi>"} is used.
\\
\\
Note that in canonical definitions of HML @{term "TT"} is not usually part of the syntax, but is instead synonymous to \<open>\<And>{}\<close>.
We include @{term "TT"} in the definition to enable Isabelle to infer via syntax only
that the types @{term "hml"} and @{term "hml_srbb"} are non-empty.
Isabelle is unable to show that the types are non-empty if the @{term "TT"} data constructor is not
given due to the way we have chosen to formalize the conjunction.
This formalization allows for conjunctions of arbitrary - even of infinite - width and has been
taken from \cite{Pohlmann2021ReducingReactive} (appendix B).
This added expressiveness comes at the cost of making proofs regarding conjunctions more complex
and restricts the ways in which functions may be derived for these types (c.f. section \ref{sect:ExpressivenessMeasure}).

To illustrate how this ability to express conjunctions of infinite width may be used, we provide the 
example formula @{term "arbitrarily_many_\<alpha>s"}.  Even though we did not yet assign meaning to HML formulas
(\ref{sect:hmlSemantic}), we claim that this example formula may only be satisfied by a process from 
which any number of $\alpha$ steps may be observed. This formula is constructed by first defining
a function @{term "n_times_\<alpha>_then"} which - given an action $\alpha$ and a formula $\varphi$ - will produce
a formula with $n$ $\langle \alpha \rangle$ clauses followed by $\varphi$, i.e. $[\langle \alpha \rangle]^n \varphi$.
\footnote{The reader may excuse the abuse of notation. $[...]^n$ is supposed to read as repeated the part
in brackets $n$ times.}
Using this function we are now able to formalize $\bigwedge\nolimits_{i \in \mathbb{N}} [\langle \alpha \rangle]^i \top$:
We define the formula @{term "arbitrarily_many_\<alpha>s"} as being a conjunction which has the full
set of natural numbers $\mathbb{N}$ as index set and then using the function @{term "n_times_\<alpha>_then"}
as mapping from index to conjunct formula.  Note that \<open>Pos \<circ>\<close> is needed to satisfy the type checker.
For an example LTS where each process satisfies this formula consider $(\mathbb{N},\{()\}, \Delta(\mathbb{N}, ()))$,
where $\Delta(\mathbb{N}, ())$ stands for the diagonal relation on $\mathbb{N}$ where each element is
additionally labelled with $()$.
\<close>

fun n_times_\<alpha>_then :: "'act \<Rightarrow> ('act, 'i) hml \<Rightarrow> nat \<Rightarrow> ('act, 'i) hml" where
  "n_times_\<alpha>_then \<alpha> \<phi> 0 = \<phi>" |
  "n_times_\<alpha>_then \<alpha> \<phi> (Suc n) = Obs \<alpha> (n_times_\<alpha>_then \<alpha> \<phi> n)"

definition arbitrarily_many_\<alpha>s :: "'act \<Rightarrow> ('act, nat) hml" where
  "arbitrarily_many_\<alpha>s \<alpha> \<equiv> Conj \<nat> (Pos \<circ> (n_times_\<alpha>_then \<alpha> TT))"

text \<open>
Initially, we considered two alternative approaches of formalizing the conjunction (both would not
have required an index type \<open>'i\<close> and would not need the data constructor \<open>TT\<close>):
\begin{enumerate}
  \item \label{lbl:set_conj} \<open>Conj "'a hml set"\<close> 
  \item \label{lbl:cset_conj} \<open>Conj "'a hml cset"\<close> 
\end{enumerate}
Approach \ref{lbl:set_conj} is rejected by Isabelle, since \<open>set\<close> is not a bounded natural functor.
In particular, the \<open>set\<close> functor violates the boundedness condition of BNF \cite{HOLDatatypes}, which is that there must
be a fixed upper bound for the cardinality of the types resulting from the \<open>set\<close> functor. Such an
upper bound can not exist due to Cantor's theorem. \footnote{We would like to thank Robin Cogan for
helping us figure this out as well as helping a lot with the initial formalization of HML as well as
HML$_\text{SRBB}$.}

Approach \ref{lbl:cset_conj} does not present this issue and is accepted by Isabelle. Pohlmann \cite{Pohlmann2021ReducingReactive}
shows that it can be employed fruitfully.  We ultimately decided against it and for the formalization
via an additional index type, since we were able to overcome the technical challenges presented by
the more general formalization.
\<close>

subsection \<open> Semantics of HML Formulas \label{sect:hmlSemantic}\<close>

context LTS_Tau
begin

text \<open>
We define what it means for a process @{term "p"} to satisfy a formula @{term "\<phi>"}, written as
\<open>p \<Turnstile> \<phi>\<close>, by inspecting the transitions available at process @{term "p"}.
\<close>

primrec
      hml_models          :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> bool" (infixl "\<Turnstile>" 50)
  and hml_conjunct_models :: "'s \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> bool"
where
  "_ \<Turnstile> TT = True" |
  "p \<Turnstile> Obs a \<phi> = (\<exists>p'. p \<mapsto> a p' \<and> p' \<Turnstile> \<phi>)" |
  "p \<Turnstile> Internal \<phi> = (\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> \<phi>)" |
  "p \<Turnstile> Silent \<phi> = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> p' \<Turnstile> \<phi>) \<or> p \<Turnstile> \<phi>)" |
  "p \<Turnstile> Conj I \<psi>s = (\<forall>i \<in> I. hml_conjunct_models p (\<psi>s i))" |

  "(hml_conjunct_models p (Pos \<phi>)) = (p \<Turnstile> \<phi>)" |
  "(hml_conjunct_models p (Neg \<phi>)) = (\<not>(p \<Turnstile> \<phi>))"

interpretation hml: lts_semantics where models = hml_models
  by unfold_locales
interpretation hml_conj: lts_semantics where models = hml_conjunct_models
  by unfold_locales

abbreviation hml_entails (infixr "\<Rrightarrow>" 60) where \<open>hml_entails \<equiv> hml.entails\<close>
abbreviation hml_logical_eq (infix "\<Lleftarrow>\<Rrightarrow>" 60) where \<open>hml_logical_eq \<equiv> hml.logical_eq\<close>

abbreviation hml_conj_entails (infixr "\<and>\<Rrightarrow>" 60) where \<open>hml_conj_entails \<equiv> hml_conj.entails\<close>
abbreviation hml_conj_logical_eq (infix "\<Lleftarrow>\<and>\<Rrightarrow>" 60) where \<open>hml_conj_logical_eq \<equiv> hml_conj.logical_eq\<close>

declare lts_semantics.entails_def[simp]
declare lts_semantics.eq_equality[simp]

abbreviation hml_distinguishes :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's \<Rightarrow> bool" ("_ <<_>> _" [70, 70, 70] 80) where
  \<open>p <<\<phi>>> q \<equiv> hml.distinguishes \<phi> p q\<close>
abbreviation hml_distinguishes_from :: "'s \<Rightarrow> ('a, 's) hml \<Rightarrow> 's set \<Rightarrow> bool" ("_ <<_>>> _" [70, 70, 70] 80) where
  \<open>p <<\<phi>>>> Q \<equiv> hml.distinguishes_from \<phi> p Q\<close>

abbreviation hml_conj_distinguishes where \<open>hml_conj_distinguishes \<equiv> hml_conj.distinguishes\<close>

declare lts_semantics.distinguishes_def[simp]
declare lts_semantics.distinguishes_from_def[simp]

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> Given this semantics, one may note that the @{term "Silent"} data constructor representing \<open>(\<tau>)\<phi>\<close>
is redundant.  It does not add to the expressiveness of the HML language and could safely be turned
into an abbreviation for \<open>\<And>{\<not>(\<And>{\<not>\<langle>\<tau>\<rangle>\<phi>, \<not>\<phi>})}\<close>: \<close>
lemma "state \<Turnstile> Silent \<phi>
     = (state \<Turnstile> (Conj {left}
                       (\<lambda>i. if i = left
                            then Neg (Conj {left, right}
                                           (\<lambda>j. if j = left
                                                then Neg (Obs \<tau> \<phi>)
                                                else if j = right
                                                then Neg \<phi>
                                                else undefined))
                            else undefined)))"
  using Inhabited_LTS_axioms Inhabited_LTS_def
        hml_conjunct_models.simps(2)
        hml_models.simps(2)
        hml_models.simps(4)
        hml_models.simps(5)
        insert_iff singletonD
  by fastforce

text \<open> We choose to still include @{term "Silent"} to stay close to \cite{bisping2023lineartimebranchingtime}
and \cite{FOKKINK2019104435}. \<close>

text \<open>
Similarly, one may wonder why we define the set of HML formulas with two mutually recursive data types,
instead of simply having just one data type by either:
\begin{itemize}
  \item inlining the \<open>hml_conjunct\<close> data type into the only place where it occurs (the conjunction), 
    viz: \<open>Conj "'i set" "'i \<Rightarrow> (('a,'i) hml + ('a,'i) hml)"\<close>, or
  \item adding a data constructor for negation (e.g. \<open>Not "('a,'i) hml"\<close>) and then in the conjunction
    simply mapping to the \<open>hml\<close> data type, i.e. \<open>Conj "'i set" "i \<Rightarrow> ('a, 'i) hml"\<close>
    (c.f. \cite{Pohlmann2021ReducingReactive}).
\end{itemize}
Once again, we choose to go for a mutually recursive definition to stay close to \cite{bisping2023lineartimebranchingtime}.
\<close>

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin

text \<open>
While @{term "T"} and \<open>\<And>{}\<close> differ syntactically, they mean exactly the same thing.
Every process will satisfy both of these formulas.
\<close>
lemma tt_eq_empty_conj: "(state \<Turnstile> TT) = (state \<Turnstile> Conj {} \<psi>)"
  by simp

text \<open> \<open>\<And>{\<phi>}\<close> (i.e. the single element conjunction) is satisfied if and only if \<open>\<phi>\<close> is satisfied. \<close>
lemma conj_\<phi>_is_\<phi>:
  "(state \<Turnstile> \<phi>)
 = (state \<Turnstile> Conj {state} (\<lambda>i. if i = state then (Pos \<phi>) else (Pos TT)))"
  by simp

lemma opt_\<tau>_is_or: "(p \<Turnstile> (Silent \<phi>)) = ((p \<Turnstile> (Obs \<tau> \<phi>)) \<or> (p \<Turnstile> \<phi>))"
  by simp


subsection \<open>HML Meta Syntax\<close>

subsubsection \<open> Soft Poss  \label{SoftPossDef}\<close>

text \<open>
@{term "(HML_soft_poss \<alpha> \<phi>)"} represents \<open>(\<alpha>)\<phi>\<close>,
which is to be interpeted as \<open>\<langle>\<alpha>\<rangle>\<phi>\<close>, if \<open>\<alpha> \<noteq> \<tau>\<close> and as \<open>(\<tau>)\<phi>\<close> otherwise.
\<close>
abbreviation HML_soft_poss :: "'a \<Rightarrow> ('a, 'i) hml \<Rightarrow> ('a, 'i) hml" where
  "HML_soft_poss \<alpha> \<phi> \<equiv> if \<alpha> = \<tau> then Silent \<phi> else Obs \<alpha> \<phi>"

text \<open>
\<open>(\<alpha>)\<phi>\<close> is satisfied if either \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> is satisfied (note that here \<open>\<alpha>\<close> may be equal to \<open>\<tau>\<close>) or
if \<open>\<alpha> = \<tau>\<close> and \<open>\<phi>\<close> is already satisfied.
\<close>
lemma soft_poss_to_or[simp]:
  "(p \<Turnstile> HML_soft_poss \<alpha> \<phi>) \<longleftrightarrow> (p \<Turnstile> Obs \<alpha> \<phi>) \<or> (\<alpha> = \<tau> \<and> (p \<Turnstile> \<phi>))"
  by auto

end (* context LTS_Tau *)

subsubsection \<open> Binary Conjunction\<close>

context Inhabited_LTS
begin

text \<open>
Binary conjunction (\<open>\<and>\<close>) is reduced to a conjunction over sets,
whereby the LTS needs to be inhabited so that at least two indices are available.
\<close>
abbreviation
  HML_and :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct
              \<Rightarrow> ('a, 's) hml"
  (infixl "\<and>hml" 80) where

  "left_conjunct \<and>hml right_conjunct \<equiv> 
   Conj {left, right} (\<lambda>i. if i = left
                           then left_conjunct
                           else if i = right
                                then right_conjunct
                                else Pos TT)"

end (* context Inhabited_LTS *)

context Inhabited_Tau_LTS
begin

text \<open> The lemma @{term "hml_and_and"} lifts satisfaction of a HML conjunction from HML to High Order Logic (HOL). \<close>
lemma hml_and_and[simp]:
  "(p \<Turnstile> (\<psi>l \<and>hml \<psi>r))
 = (hml_conjunct_models p \<psi>l \<and> hml_conjunct_models p \<psi>r)"
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_conjunct_models.simps(1) hml_models.simps(1) hml_models.simps(5) by force


end (* Inhabited_Tau_LTS *)

subsubsection \<open> Negation\<close>

context Inhabited_Tau_LTS
begin

text \<open>The abbreviation @{term "(HML_not \<phi>)"} represents \<open>\<not>\<phi>\<close> and is realized via a one element conjunction. \<close>
abbreviation HML_not :: "('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "HML_not \<phi> \<equiv> Conj {left} (\<lambda>i. if i = left then (Neg \<phi>) else (Pos TT))"


text \<open> The formula \<open>\<not>\<not>\<phi>\<close> is satisfied if and only if \<open>\<phi>\<close> is satisfied. \<close>
lemma hml_not_not:
  shows "(state \<Turnstile> \<phi>)
       \<longleftrightarrow> (state \<Turnstile> HML_not (HML_not \<phi>))"
  by simp

text \<open>
@{term "(HML_not \<phi>)"} is satisfied if and only if \<open>\<phi>\<close> is not satisfied.
This lifts the negation from HML to HOL.
\<close>
lemma hml_not_not_models[simp]:
  shows "state \<Turnstile> HML_not \<phi> == \<not> (state \<Turnstile> \<phi>)"
  by simp

subsubsection \<open> Falsum\<close>

abbreviation HML_falsum :: "('a, 's) hml" ("\<bottom>\<bottom>") where
  "\<bottom>\<bottom> \<equiv> HML_not TT"

text \<open> No process satisfies falsum.\<close>
lemma never_models_falsum[simp]:
  shows "\<not> (state \<Turnstile> \<bottom>\<bottom>)"
  by simp

subsubsection \<open> Binary Disjunction\<close>

text \<open> The formula @{term "(\<phi> \<or>hml \<phi>')"} is realized by using binary conjunction and negation. \<close>

definition HML_or :: "('a, 's) hml \<Rightarrow> ('a, 's) hml \<Rightarrow> ('a, 's) hml" ("_ \<or>hml _" 70) where
  "\<phi>l \<or>hml \<phi>r \<equiv> HML_not (Neg \<phi>l \<and>hml Neg \<phi>r)"

lemma hml_or_or[simp]: "(p \<Turnstile> (\<phi>l \<or>hml \<phi>r)) = ((p \<Turnstile> \<phi>l) \<or> (p \<Turnstile> \<phi>r))"
  unfolding HML_or_def 
  using Inhabited_LTS_axioms Inhabited_LTS_def hml_conjunct_models.simps(2) hml_models.simps(1) hml_models.simps(5) by force

end (* context Inhabited_Tau_LTS *)


context LTS_Tau
begin

subsection \<open> Pre-Order \label{sect:hmlImpl}\<close>

subsubsection \<open> Pre-Substitution \<close>

text \<open>
The following lemmas provide means to manipulate a HML implication
by substituting other HML implications into it. This substitution may only occur on the right hand side of the implication.
A notable exception is @{term "neg_pre_subst"}, i.e. when substituting into a negation where one may only
substitute on the left hand side of the implication.
The lemmas differ in the choice of context, i.e. what formula is substituted into.
\<close>

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<langle>\<alpha>\<rangle>\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<langle>\<alpha>\<rangle>\<phi>''\<close>. \<close>
lemma obs_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<langle>\<epsilon>\<rangle>\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<langle>\<epsilon>\<rangle>\<phi>''\<close>. \<close>
lemma internal_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Internal \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<tau>)\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> (\<tau>)\<phi>''\<close>. \<close>
lemma silent_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Silent \<phi>l)"
  shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms by force

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<And>{\<phi>', ...}\<close> follows \<open>\<phi> \<Rrightarrow> \<And>{\<phi>'', ...}\<close>
as long the remainder of the conjunction is unchanged. \<close>
lemma conj_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>l else \<psi>s i))"
  shows "\<phi> \<Rrightarrow> (Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos \<phi>r else \<psi>s i))"
  using assms by fastforce

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> \<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> \<phi>''\<close>.
This simply lifts HML implication into the @{term "hml_conjunct"} data type.\<close>
lemma pos_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Pos \<phi>l)" 
  shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)" 
  using assms by simp

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<not>\<phi>' \<Rrightarrow> \<phi>\<close> follows \<open>\<not>\<phi>'' \<Rrightarrow> \<phi>\<close>.
Note that the substitution here occurs on the left hand side.\<close>
lemma neg_pre_subst: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<and>\<Rrightarrow> \<psi>" 
  shows "(Neg \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<alpha>)\<phi>'\<close> follows \<open>\<phi> \<Rrightarrow> (\<alpha>)\<phi>''\<close>. \<close>
lemma soft_pos_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (HML_soft_poss \<alpha> \<phi>l)"
  shows "\<phi> \<Rrightarrow> (HML_soft_poss \<alpha> \<phi>r)"
  using assms obs_pre_subst silent_pre_subst by presburger

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<phi>' \<and> \<phi>o)\<close> follows \<open>\<phi> \<Rrightarrow> (\<phi>'' \<and> \<phi>o)\<close>. \<close>
lemma hml_and_left_pre_subst:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (\<phi>l \<and>hml \<phi>o)"
  shows "\<phi> \<Rrightarrow> (\<phi>r \<and>hml \<phi>o)"
  using assms by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<phi> \<Rrightarrow> (\<phi>o \<and> \<phi>')\<close> follows \<open>\<phi> \<Rrightarrow> (\<phi>o \<and> \<phi>'')\<close>. \<close>
lemma hml_and_right_pre_subst:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
    and "\<phi> \<Rrightarrow> (\<phi>o \<and>hml \<phi>l)"
  shows "\<phi> \<Rrightarrow> (\<phi>o \<and>hml \<phi>r)"
  using assms by auto

text \<open> From \<open>\<phi>' \<Rrightarrow> \<phi>''\<close> and \<open>\<not>\<phi>' \<Rrightarrow> \<phi>\<close> follows \<open>\<not>\<phi>'' \<Rrightarrow> \<phi>\<close>.
Note that the substitution here occurs on the left hand side.\<close>
lemma not_pre_subst:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
    and "HML_not \<phi>l \<Rrightarrow> \<phi>"
  shows "HML_not \<phi>r \<Rrightarrow> \<phi>"
  using assms by auto

end (* Inhabited_Tau_LTS *)


subsubsection \<open> Pre-Congruence\<close>

text \<open>
The following lemmas provide means to manipulate a HML implication
by wrapping both sides of the implication in the same HML formula context.

The lemmas differ in the choice of context, i.e. how both sides are extended.
\<close>

context LTS_Tau
begin

text \<open> Prepending an observation (\<open>\<langle>\<alpha>\<rangle>...\<close>) preserves implication. \<close>
lemma obs_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms by auto

text \<open> Prepending an epsilon (\<open>\<langle>\<epsilon>\<rangle>...\<close>) preserves implication. \<close>
lemma internal_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Rrightarrow> (Internal \<phi>r)"
  using assms by auto

text \<open> Prepending an silent observation (\<open>(\<tau>)...\<close>) preserves implication. \<close>
lemma silent_pre_cong: 
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Rrightarrow> (Silent \<phi>r)"
  using assms by auto

text \<open>
Wrapping both sides of an implication in the same conjunction
will preserve the implication.
\<close>
lemma conj_pre_cong: 
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<psi>sl l \<and>\<Rrightarrow> \<psi>sr r" 
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms
  by (force simp add: image_iff)

text \<open>
Wrapping a set of implying conjuncts in the same conjunction
will preserve the implications.
\<close>
lemma conj_pre_congs:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i \<in> I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i"
  shows "(Conj (I \<union> I') \<psi>sl) \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms 
  by (auto, metis UnCI image_iff)

text \<open> We lift HML implication to HML conjunct implication. \<close>
lemma pos_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Pos \<phi>l \<and>\<Rrightarrow> Pos \<phi>r"
  using assms
  by simp

text \<open> Turning both sides of an implication into a negated conjunct will invert the implication direction.
Note that \<open>\<phi>l\<close> and \<open>\<phi>r\<close> switch sides in the conclusion.\<close>
lemma neg_pre_cong:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
  shows "Neg \<phi>r \<and>\<Rrightarrow> Neg \<phi>l"
  using assms by auto

text \<open> Prepending a soft observation (\<open>(\<alpha>)...\<close>) preserves implication. \<close>
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
  by simp

text \<open> Prepending a conjunct (\<open>\<psi> \<and> ...\<close>) preserves implication. \<close>
lemma hml_and_right_pre_cong:
  assumes "\<psi>l \<and>\<Rrightarrow> \<psi>r"
  shows "\<psi> \<and>hml \<psi>l \<Rrightarrow> \<psi> \<and>hml \<psi>r"
  using assms and conj_pre_congs 
  by simp

text \<open> Prepending a negation (\<open>\<not>...\<close>) inverts implication. \<close>
lemma not_pre_cong:
  shows "\<phi>l \<Rrightarrow> \<phi>r
       = HML_not \<phi>r \<Rrightarrow> HML_not \<phi>l"
  by auto

end (* Inhabited_Tau_LTS *)


subsubsection \<open> Known Pre-Order Elements\<close>

context LTS_Tau
begin

text \<open> If \<open>\<phi>\<close> is satisfied, then also \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> must be satisfied. \<close>
lemma pre_\<epsilon>:
  shows "\<phi> \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable.refl by fastforce

text \<open> If \<open>\<phi>\<close> is satisfied, then also \<open>(\<tau>)\<phi>\<close> must be satisfied. \<close>
lemma pre_\<tau>:
  shows "\<phi> \<Rrightarrow> (Silent \<phi>)"
  by fastforce

text \<open> If \<open>\<langle>\<epsilon>\<rangle>\<langle>\<tau>\<rangle>\<phi>\<close> is satisfied, then also \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close> must be satisfied. \<close>
lemma \<epsilon>_eats_\<tau>:
  shows "(Internal (Obs \<tau> \<phi>)) \<Rrightarrow> (Internal \<phi>)"
  using silent_reachable_append_\<tau> by fastforce

text \<open>If \<open>\<And>{\<psi>, ...}\<close> is satisfied, then also \<open>\<And>{...}\<close> is satisfied.
Conjunctions can be omitted, but the slimmed-down conjunction will still be satisfied. \<close>
lemma drop_conjunct:
  shows "Conj (I \<union> {s}) \<psi>s \<Rrightarrow> Conj (I - {s}) \<psi>s"
  using Un_Diff_cancel2 by auto

subsection \<open> Equivalence \label{sect:hmlEq} \<close>

subsubsection \<open> Substitution \<close>

text \<open>
The following lemmas provide means to manipulate a HML equivalence
by substituting other HML equivalence into it. While one may substitute on both sides of the equivalence, only substitutions on the left hand side
are shown. If one needs a substitution on the other side, one can use @{term "hml_eq_equiv"}.
The lemmas differ in the choice of context, i.e. what formula is substituted into.
\<close>

lemma obs_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Obs \<alpha> \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms obs_pre_cong by simp

lemma internal_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Internal \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms by simp

lemma silent_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Silent \<phi>r) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms silent_pre_cong by simp

lemma conj_subst:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>l else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  shows "(Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi>r else \<psi>s i)) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using assms by force

lemma pos_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Pos \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms pos_pre_cong by simp

lemma neg_subst:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  shows "(Neg \<phi>r) \<Lleftarrow>\<and>\<Rrightarrow> \<psi>"
  using assms by simp

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma and_subst_right:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>l)"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>r)"
  using assms by simp

lemma and_subst_left:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi>l \<and>hml \<psi>)"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> (\<psi>r \<and>hml \<psi>)"
  using assms by simp

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin


subsubsection \<open> Congruence \<close>

text \<open>
The lemmas in this subsection all follow a similar form:
  Given that two formulas (\<open>\<phi>l\<close> and \<open>\<phi>r\<close>) are equivalent,
  then these two formulas wrapped in the same context are also equivalent.
Also in this case, the lemmas differ in the choice of context.
\<close>

text \<open> Prepending an observation (\<open>\<langle>\<alpha>\<rangle>...\<close>) preserves equivalence. \<close>
lemma obs_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Obs \<alpha> \<phi>l) \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms by simp

text \<open> Prepending an epsilon (\<open>\<langle>\<epsilon>\<rangle>...\<close>) preserves equivalence. \<close>
lemma internal_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Internal \<phi>l) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>r)"
  using assms by simp

text \<open> Prepending a silent observation (\<open>(\<tau>)...\<close>) preserves equivalence. \<close>
lemma silent_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Silent \<phi>l) \<Lleftarrow>\<Rrightarrow> (Silent \<phi>r)"
  using assms by simp

text \<open>
Wrapping two equivalent conjunction formulas in otherwise the same conjunction
will result in two equivalent conjunctions.
\<close>
lemma conj_cong:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "(\<psi>sl l) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr r)"
  shows "(Conj (I \<union> {l}) \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> {r}) \<psi>sr)"
  using assms by (auto simp add: conj_pre_cong) (metis (mono_tags, lifting) image_iff)+

text \<open>
Wrapping two sets of equivalent conjunction formulas in otherwise the same conjunction
will result in two equivalent conjunctions.
\<close>
lemma conj_congs:
  assumes "\<forall>i \<in> I. \<psi>sl i = \<psi>sr i"
      and "\<forall>i \<in> I'. (\<psi>sl i) \<Lleftarrow>\<and>\<Rrightarrow> (\<psi>sr i)"
  shows "(Conj (I \<union> I') \<psi>sl) \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms 
  using conj_pre_congs
  by (metis image_cong lts_semantics.logical_eq_def)

text \<open> Two equivalent formulas are also equivalent when used as conjuncts. \<close>
lemma pos_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Pos \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>r)"
  using assms
  by simp

text \<open>Two equivalent formulas are also equivalent when negated. \<close>
lemma neg_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "(Neg \<phi>l) \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
  using assms
  by simp

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma and_cong_right:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
  shows "(\<psi> \<and>hml \<psi>l) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml \<psi>r)"
  using assms by auto

lemma and_cong_left:
  assumes "\<psi>l \<Lleftarrow>\<and>\<Rrightarrow> \<psi>r"
  shows "(\<psi>l \<and>hml \<psi>) \<Lleftarrow>\<Rrightarrow> (\<psi>r \<and>hml \<psi>)"
  using assms by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin

subsubsection \<open> Known Equivalence Elements \label{equivalenceProofs} \<close>

text \<open>The formula \<open>\<langle>\<epsilon>\<rangle>(\<tau>)\<phi>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close>. \<close>
lemma \<epsilon>\<tau>_is_\<tau>: "(Internal (Silent \<phi>)) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  using silent_reachable_append_\<tau> by auto

text \<open>The formula \<open>\<langle>\<epsilon>\<rangle>\<langle>\<epsilon>\<rangle>\<phi>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close>. \<close>
lemma \<epsilon>\<epsilon>_is_\<epsilon>: "(Internal (Internal \<phi>)) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
  using silent_reachable_trans pre_\<epsilon> by auto 

thm LTS_Tau.hml_models.simps(1)
thm hml_models.simps(1)

text \<open> The formula \<open>\<langle>\<epsilon>\<rangle>\<top>\<close> is equivalent to \<open>\<top>\<close>. \<close>
lemma \<epsilon>T_is_T: "(Internal TT) \<Lleftarrow>\<Rrightarrow> TT"
  using pre_\<epsilon> silent_reachable.refl by fastforce

fun n_\<epsilon>\<tau>s_then :: "nat \<Rightarrow> ('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "n_\<epsilon>\<tau>s_then 0 cont = cont" |
  "n_\<epsilon>\<tau>s_then (Suc n) cont = (Internal (Silent (n_\<epsilon>\<tau>s_then n cont)))"

text \<open>$[\langle \epsilon \rangle (\tau)]^n \langle \epsilon \rangle \varphi$ is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<phi>\<close>.\<close>
lemma \<epsilon>\<tau>_stack_reduces: "n_\<epsilon>\<tau>s_then n (Internal \<phi>) \<Lleftarrow>\<Rrightarrow> (Internal \<phi>)"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    unfolding lts_semantics.logical_eq_def
  proof (safe)
    assume
      \<open>n_\<epsilon>\<tau>s_then n (Internal \<phi>) \<Rrightarrow> Internal \<phi>\<close>
      \<open>Internal \<phi> \<Rrightarrow> n_\<epsilon>\<tau>s_then n (Internal \<phi>)\<close>
    thus \<open>n_\<epsilon>\<tau>s_then (Suc n) (Internal \<phi>) \<Rrightarrow> Internal \<phi>\<close>
      using  \<epsilon>\<epsilon>_is_\<epsilon> \<epsilon>\<tau>_is_\<tau> internal_pre_subst by fastforce
  next
    assume
      \<open>n_\<epsilon>\<tau>s_then n (Internal \<phi>) \<Rrightarrow> Internal \<phi>\<close>
      \<open>Internal \<phi> \<Rrightarrow> n_\<epsilon>\<tau>s_then n (Internal \<phi>)\<close>
    thus \<open>Internal \<phi> \<Rrightarrow> n_\<epsilon>\<tau>s_then (Suc n) (Internal \<phi>)\<close>
      using silent_reachable.refl by fastforce
  qed
qed

text \<open> Wrapping two equivalent formulas into n \<open>\<langle>\<epsilon>\<rangle>(\<tau>)\<close> prefixes yields two equivalent formulas. \<close>
lemma n_\<epsilon>\<tau>s_then_cong:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
  shows "n_\<epsilon>\<tau>s_then n \<phi>l \<Lleftarrow>\<Rrightarrow> n_\<epsilon>\<tau>s_then n \<phi>r"
  using assms
  by (induct n) (simp add: internal_cong silent_cong)+

text \<open> The formula $[\langle \epsilon \rangle (\tau)]^n \top$ is equivalent to \<open>\<top>\<close>. \<close>
lemma "n_\<epsilon>\<tau>s_then n TT \<Lleftarrow>\<Rrightarrow> TT"
  using n_\<epsilon>\<tau>s_then_cong \<epsilon>\<tau>_stack_reduces \<epsilon>T_is_T equivp_def lts_semantics.eq_equiv by metis

text \<open> The formula \<open>\<top>\<close> is equivalent to \<open>\<And>{}\<close>. \<close>
lemma T_is_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Conj {} \<psi>s"
  using tt_eq_empty_conj
  by force

text \<open> The formula \<open>\<top>\<close> is equivalent to \<open>\<langle>\<epsilon>\<rangle>\<And>{}\<close>. \<close>
lemma T_is_\<epsilon>_empty_conj: "TT \<Lleftarrow>\<Rrightarrow> Internal (Conj {} \<psi>s)"
  using \<epsilon>T_is_T by force

lemma soft_\<tau>_is_silent:
  assumes "\<alpha> = \<tau>"
  shows "Silent \<phi> \<Lleftarrow>\<Rrightarrow> HML_soft_poss \<alpha> \<phi>"
  using assms by simp

lemma soft_non_\<alpha>_is_obs:
  assumes "\<alpha> \<noteq> \<tau>"
  shows "Obs \<alpha> \<phi> \<Lleftarrow>\<Rrightarrow> HML_soft_poss \<alpha> \<phi>"
  using assms by auto

end

context Inhabited_Tau_LTS
begin

text \<open> The formula \<open>\<phi>l \<and> \<phi>r\<close> is equivalent to \<open>\<phi>r \<and> \<phi>l\<close>. \<close>
lemma hml_and_commutative: "(\<phi>l \<and>hml \<phi>r) \<Lleftarrow>\<Rrightarrow> (\<phi>r \<and>hml \<phi>l)"
  using Inhabited_LTS_axioms Inhabited_LTS_def by fastforce


text \<open>The formula \<open>\<top> \<and> \<phi>\<close> is equivalent to \<open>\<phi>\<close>. \<close>
lemma hml_and_left_tt: "(Pos TT \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using Inhabited_LTS_axioms Inhabited_LTS_def by fastforce

text \<open> The formula \<open>\<phi> \<and> \<top>\<close> is equivalent to \<open>\<phi>\<close>. \<close>
lemma hml_and_right_tt: "(Pos \<phi> \<and>hml Pos TT) \<Lleftarrow>\<Rrightarrow> \<phi>"
  using hml_and_commutative hml_and_left_tt by simp

text \<open> The formula \<open>\<phi> \<and> \<phi>\<close> is equivalent to \<open>\<phi>\<close>. \<close>
lemma hml_and_same_no_and: "(Pos \<phi> \<and>hml Pos \<phi>) \<Lleftarrow>\<Rrightarrow> \<phi>"
  by simp

text \<open> The formula \<open>\<And>({\<psi>} \<union> \<Psi>)\<close> is equivalent to \<open>\<psi> \<and> \<And>\<Psi>\<close>. \<close>
lemma conj_extract_conjunct:
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then \<psi> else \<psi>s i) \<Lleftarrow>\<Rrightarrow> (\<psi> \<and>hml Pos (Conj I \<psi>s))"
  using assms hml_and_and by auto

text \<open> The formula \<open>\<And>({\<top>} \<union> \<Psi>)\<close> is equivalent to \<open>\<And>\<Psi>\<close>. \<close>
lemma
  assumes "s \<notin> I"
  shows "Conj (I \<union> {s}) (\<lambda>i. if i = s then Pos TT else \<psi>s i) \<Lleftarrow>\<Rrightarrow> Conj I \<psi>s"
  using assms conj_extract_conjunct hml_and_left_tt by force

text \<open> The formula \<open>(\<tau>)\<phi>\<close> is equivalent to \<open>\<langle>\<tau>\<rangle>\<phi> \<or> \<phi>\<close>. \<close>
lemma silent_is_or: "(Silent \<phi>) \<Lleftarrow>\<Rrightarrow> ((Obs \<tau> \<phi>) \<or>hml \<phi>)"
  by simp

text \<open>The formula \<open>\<phi>\<close> is equivalent to \<open>\<not>\<not>\<phi>\<close>. \<close>
lemma hml_not_not_eq: "\<phi> \<Lleftarrow>\<Rrightarrow> HML_not (HML_not \<phi>)"
  using hml_not_not by auto

text \<open>The formula \<open>\<phi> \<and> \<not>\<phi>\<close> is equivalent to \<open>\<bottom>\<close>. \<close>
lemma hml_absurdity:
  shows "(Pos \<phi> \<and>hml Neg \<phi>) \<Lleftarrow>\<Rrightarrow> \<bottom>\<bottom>"
  using never_models_falsum left_right_distinct by auto

text \<open> The formula \<open>\<phi> \<or> \<not>\<phi>\<close> is equivalent to \<open>\<top>\<close>. \<close>
lemma hml_tertium_non_datur:
  shows "TT \<Lleftarrow>\<Rrightarrow> (\<phi> \<or>hml HML_not \<phi>)"
  using hml_absurdity hml_not_not_eq by simp

subsection \<open> HML Equivalence and HML Pre-Order \<close>

text \<open>
These lemmas provide means to substitute HML equivalences and implications into each other,
thereby providing further support for equational reasoning on HML formulas.
Note that this always yields a HML implication.
\<close>

subsubsection \<open> Observations \<close>

lemma obs_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Obs \<alpha> \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Obs \<alpha> \<phi>r) \<Rrightarrow> \<phi>"
  using assms obs_pre_cong by simp

lemma obs_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)" 
  using assms obs_pre_subst by simp

lemma obs_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Obs \<alpha> \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Obs \<alpha> \<phi>r)"
  using assms obs_pre_subst by force

subsubsection \<open> Internal Behaviour \<close>

lemma internal_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Internal \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Internal \<phi>r) \<Rrightarrow> \<phi>"
  using assms internal_pre_cong by simp

lemma internal_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Internal \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms internal_pre_subst by simp

lemma internal_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Internal \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Internal \<phi>r)"
  using assms internal_pre_subst by force

subsubsection \<open> Silent Step\<close>

lemma silent_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Silent \<phi>l) \<Rrightarrow> \<phi>"
    shows "(Silent \<phi>r) \<Rrightarrow> \<phi>"
  using assms by simp

lemma silent_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> (Silent \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms silent_pre_subst by simp

lemma silent_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Silent \<phi>l)"
    shows "\<phi> \<Rrightarrow> (Silent \<phi>r)"
  using assms silent_pre_subst by force

subsubsection \<open> Conjunctions\<close>

lemma conjunction_left_impl_subst_equal:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<Lleftarrow>\<and>\<Rrightarrow> \<psi>sr i"
      and "(Conj (I \<union> I') \<psi>sl) \<Rrightarrow> \<phi>"
    shows "(Conj (I \<union> I') \<psi>sr) \<Rrightarrow> \<phi>"
  using assms conj_pre_congs unfolding lts_semantics.entails_def lts_semantics.logical_eq_def
  by metis

lemma conjunction_right_impl_subst_equal:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<Lleftarrow>\<and>\<Rrightarrow> \<psi>sr i"
      and "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sl)"
    shows "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms conj_pre_congs unfolding lts_semantics.entails_def lts_semantics.logical_eq_def
  by metis
 
lemma conjunction_equal_subst_impl:
  assumes "\<psi>sl ` I = \<psi>sr ` I"
      and "\<forall>i\<in>I'. \<psi>sl i \<and>\<Rrightarrow> \<psi>sr i"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> (Conj (I \<union> I') \<psi>sl)"
    shows "\<phi> \<Rrightarrow> (Conj (I \<union> I') \<psi>sr)"
  using assms conj_pre_congs unfolding lts_semantics.entails_def lts_semantics.logical_eq_def
  by metis

subsubsection \<open> Positive Conjunct \<close>

lemma conjunct_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Pos \<phi>l) \<and>\<Rrightarrow> \<psi>"
    shows "(Pos \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms pos_pre_cong by auto

lemma conjunct_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Pos \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)" 
  using assms pos_pre_subst by auto

lemma conjunct_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<Lleftarrow>\<and>\<Rrightarrow> (Pos \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Pos \<phi>r)"
  using assms by (simp add: pos_pre_subst)

subsubsection \<open> Negative Conjunct \<close>

lemma neg_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "(Neg \<phi>l) \<and>\<Rrightarrow> \<psi>"
    shows "(Neg \<phi>r) \<and>\<Rrightarrow> \<psi>"
  using assms neg_pre_subst by auto

lemma neg_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<psi> \<and>\<Rrightarrow> (Neg \<phi>l)"
    shows "\<psi> \<and>\<Rrightarrow> (Neg \<phi>r)" 
  using assms by auto

lemma neg_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<psi> \<Lleftarrow>\<and>\<Rrightarrow> (Neg \<phi>r)"
    shows "\<psi> \<and>\<Rrightarrow> (Neg \<phi>l)"
  using assms by auto

subsubsection \<open> Negation \<close>

lemma not_left_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "HML_not \<phi>l \<Rrightarrow> \<phi>"
    shows "HML_not \<phi>r \<Rrightarrow> \<phi>"
  using assms by auto

lemma not_right_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<Rrightarrow> \<phi>r"
      and "\<phi> \<Rrightarrow> HML_not \<phi>l"
    shows "\<phi> \<Rrightarrow> HML_not \<phi>r"
  using assms by auto

lemma not_equal_subst_impl:
  assumes "\<phi>l \<Rrightarrow> \<phi>r"
      and "\<phi> \<Lleftarrow>\<Rrightarrow> HML_not \<phi>r"
    shows "\<phi> \<Rrightarrow> HML_not \<phi>l"
  using assms by auto

subsubsection \<open> Binary Conjunction \<close>

lemma and_lr_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi> \<and>hml \<phi>l \<Rrightarrow> \<phi>'"
    shows "\<phi> \<and>hml \<phi>r \<Rrightarrow> \<phi>'"
  using assms by auto

lemma and_ll_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>l \<and>hml \<phi> \<Rrightarrow> \<phi>'"
    shows "\<phi>r \<and>hml \<phi> \<Rrightarrow> \<phi>'"
  using assms by auto

lemma and_rr_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>l"
    shows "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>r"
  using assms by auto

lemma and_rl_impl_subst_equal:
  assumes "\<phi>l \<Lleftarrow>\<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Rrightarrow> \<phi>l \<and>hml \<phi>"
    shows "\<phi>' \<Rrightarrow> \<phi>r \<and>hml \<phi>"
  using assms by auto

lemma and_left_equal_subst_impl:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Lleftarrow>\<Rrightarrow> \<phi>l \<and>hml \<phi>"
    shows "\<phi>' \<Rrightarrow> \<phi>r \<and>hml \<phi>"
  using assms by simp

lemma and_right_equal_subst_impl:
  assumes "\<phi>l \<and>\<Rrightarrow> \<phi>r"
      and "\<phi>' \<Lleftarrow>\<Rrightarrow> \<phi> \<and>hml \<phi>l"
    shows "\<phi>' \<Rrightarrow> \<phi> \<and>hml \<phi>r"
  using assms by simp

subsubsection \<open> Verum and Falsum\<close>

text \<open> If we can show that verum entails the satisfaction of a formula, the formula must be equivalent
to verum. \<close>
lemma follows_verum_equals_verum:
  assumes "TT \<Rrightarrow> \<phi>"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> TT"
  using assms 
  by simp

text \<open> If the satisfaction of a formula entails that falsum must be satisfied, this means that this formula
can never be satisfied. \<close>
lemma entails_falsum_equals_falsum:
  assumes "\<phi> \<Rrightarrow> \<bottom>\<bottom>"
  shows "\<phi> \<Lleftarrow>\<Rrightarrow> \<bottom>\<bottom>"
  using assms 
  by simp
end (* Inhabited_Tau_LTS *)

subsection \<open> Distinguishing Formulas \label{sect:hmlDist} \<close>
subsubsection \<open> Fundamentals \<close>
context LTS_Tau
begin

lemma vertum_cant_distinguish:
  shows "\<not> (p << TT >> q)"
  by auto


end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

text \<open> If a formula \<open>\<phi>\<close> distinguishes the processes \<open>p\<close> and \<open>q\<close> then the inverted formula
\<open>\<not>\<phi>\<close> will distinguish both processes, but in inverted order. \<close>
lemma inverted_distinguishes:
  shows "(p << \<phi> >> q) = (q << HML_not \<phi> >> p)"
  by auto

end (* Inhabited_Tau_LTS *)

context LTS_Tau
begin

text \<open> If a conjunction distinguishes a processes \<open>p\<close> from another process \<open>q\<close> then there must be
at least one conjunct in this conjunction that on its own distinguishes \<open>p\<close> from \<open>q\<close>. \<close>

lemma dist_conjunction_implies_dist_conjunct:
  fixes q :: 's
  assumes "p << Conj I \<psi>s >> q"
  shows "\<exists>i\<in>I. hml_conj_distinguishes (\<psi>s i) p q"
  using assms by auto

text \<open> Inversely, If there is a conjunct that distinguishes \<open>p\<close> from \<open>q\<close>, then a conjunction containing
this conjunct will itself distinguish \<open>p\<close> from \<open>q\<close>, provided that \<open>p\<close> satisfies all other conjuncts
as well.\<close>

lemma dist_conjunct_implies_dist_conjunction:
  fixes q :: 's
  assumes "i\<in>I"
      and "hml_conj_distinguishes (\<psi>s i) p q" 
      and "\<forall>i\<in>I. hml_conjunct_models p (\<psi>s i)"
  shows "p << Conj I \<psi>s >> q"
  using assms by auto

subsubsection \<open> Distinguishing Conjunction Thinning \<close>

text \<open>
This subsection provides proofs regarding conjunctions that distinguish a process \<open>p\<close> from a set of
processes \<open>Q\<close>. In particular, the property of distinguishing conjunction thinning is proven.
This property states that if a conjunction distinguishes \<open>p\<close> from \<open>Q\<close> with some arbitrary index set
\<open>I\<close>, then one can construct another conjunction with the index set \<open>Q\<close> (with one conjunct per
process to be distinguished from) that also distinguished \<open>p\<close> from \<open>Q\<close>. 
Intuitively, this proposition should hold, since for the conjunction to distinguish from \<open>Q\<close> it must
contain at least one conjunct for each element \<open>q\<close> of \<open>Q\<close> that is not satisfied by \<open>q\<close>.
One may now constructed the 'thinned' conjunction with index set \<open>Q\<close> by picking for each \<open>q\<close> in \<open>Q\<close>
a conjunct that \<open>q\<close> does not satisfy, thereby guaranteeing that all elements of \<open>Q\<close> cannot satisfy
this new conjunction. The process \<open>p\<close> must still satisfy this new conjunction, since all conjuncts originate from the old
conjunction which \<open>p\<close> satisfies and thereby all conjuncts hold for \<open>p\<close>. In other words: 
As no new conjunctions are constructed, there is no opportunity for \<open>p\<close> not to satisfy the new conjunction.\<close>

text \<open>The following proof is one for an underspecified variant of distinguishing conjunction thinning.
It is underspecified in the sense that we do not know anything about the new set of conjuncts.
For purposes of the silent step spectroscopy, this is problematic as we may want to relate the
expressiveness price of the new distinguishing conjunction to the old distinguishing conjunction.
The proof diverges from the proof sketch given above in that the new conjunction simply copies the
old conjunction in each new conjunct.
\<close>
lemma
  fixes Q :: "'s set"
  assumes "p << Conj I \<psi>s >>> Q"
  shows "\<exists>\<psi>s'. p << Conj Q \<psi>s' >>> Q"
  using assms
  unfolding lts_semantics.distinguishes_from_def
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
  assumes "p << Conj I \<psi>s >>> Q"
  shows "p << Conj Q (\<lambda>q. \<psi>s (SOME i. i \<in> I \<and> \<not>(hml_conjunct_models q (\<psi>s i)))) >>> Q"
  using assms
  unfolding lts_semantics.distinguishes_from_def
  using tfl_some by (simp, smt (verit, ccfv_SIG) someI)


text \<open> The following three lemmas prove that the first condition of a distinguishing conjunction
(so that the distinguished process \<open>p\<close> satisfies the conjunction) holds for a somewhat more complex strategy of picking conjuncts. 
These become necessary when one wants to lift the distinguishing conjunction thinning lemma to @{term "hml_srbb"}.
Further information on the background can be found in the section \ref{sect:hmlSRBB}.
\\\\
The strategy for picking the conjuncts -- defined as @{term "distinguishing_conjunct"} in each lemma head --
is robust against original conjunctions with empty index sets or that do not contain distinguishing
conjuncts for some elements of \<open>Q\<close>. While these cases are impossible for normal distinguishing 
conjunctions in HML (how can an empty conjunction distinguish anything: A distinguishing conjunction
must have a subformula that actually distinguishes), in our formalisation of HML$_\text{SRBB}$ these cases
are relevant and in particular, it is important that well defined conjuncts be present in such cases.
So the strategy works as follows: If $I$ is empty, just pick \<open>\<top>\<close> (encoded in different ways).
If there is no distinguishing conjunct, just pick any conjunct for the original conjunction.
Otherwise pick a distinguishing conjunct.
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
  apply (cases \<open>I \<noteq> {}\<close>)
  using distinguishing_conjunct_def empty_subsetI image_eqI image_is_empty image_subsetI subset_antisym tfl_some 
  by (smt (verit) UnI1 some_in_eq, auto)

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
  using assms(2) unfolding hml_models.simps
  apply (cases \<open>I \<noteq> {}\<close>)
  using dist_conjunct_image_subset_all_conjuncts
    and distinguishing_conjunct_def
    and some_in_eq some_eq_ex 
  by (smt (verit), auto)

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
  assumes "p << Conj I \<psi>s >> q"
  shows "I \<noteq> {}"
  using assms by auto

end (* LTS_Tau *)

context Inhabited_Tau_LTS
begin

lemma hml_and_dist_disj:
  "p << \<psi>l \<and>hml \<psi>r >> q = (p \<Turnstile> (\<psi>l \<and>hml \<psi>r) \<and> (\<not>hml_conjunct_models q \<psi>l \<or> \<not>hml_conjunct_models q \<psi>r))"
  using left_right_distinct by fastforce

end (* Inhabited_Tau_LTS *)

end
