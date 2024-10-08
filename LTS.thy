text \<open>\newpage\<close>
section \<open>LTS \label{sect:LTS}\<close>
theory LTS
  imports Main
begin

subsection \<open>Labelled Transition Systems\<close>

text \<open>
The locale @{term "LTS"} represents a labelled transition system consisting of a set of states $\mathcal{P}$, 
a set of actions $\Sigma$, and a transition relation $\mapsto \subseteq \mathcal{P}\times\Sigma\times\mathcal{P}$ (cf. \cite[defintion 1]{bisping2023lineartimebranchingtime}). 
We formalize the sets of states and actions by the type variables \<open>'s\<close> and \<open>'a\<close>. An LTS is then determined by the transition relation @{term "step"}. 
Due to technical limitations we use the notation \<open>p \<mapsto>\<alpha> p'\<close> which has same meaing as $p \xrightarrow{\alpha} p'$ has in \cite{bisping2023lineartimebranchingtime}.

\<close>

locale LTS =
  fixes step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
begin

text \<open>One may lift @{term "step"} to sets of states, written as \<open>P \<mapsto>S \<alpha> Q\<close>. We define \<open>P \<mapsto>S \<alpha> Q\<close> to be true if and only if for all states \<open>q\<close> in \<open>Q\<close> there exists
a state \<open>p\<close> in \<open>P\<close> such that \<open>p \<mapsto> \<alpha> q\<close> and for all \<open>p\<close> in \<open>P\<close> and for all \<open>q\<close>, if \<open>p \<mapsto> \<alpha> q\<close> then \<open>q\<close> is in \<open>Q\<close>.\<close>
abbreviation step_setp ("_ \<mapsto>S _ _" [70,70,70] 80) where
  "P \<mapsto>S \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto> \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto> \<alpha> q \<longrightarrow> q \<in> Q)"

text \<open>The set of possible \<open>\<alpha>\<close>-steps for a set of states \<open>P\<close> are all \<open>q\<close> such that there is a state \<open>p\<close> in \<open>P\<close> with \<open>p \<mapsto> \<alpha> q\<close>.\<close>
definition step_set :: "'s set \<Rightarrow> 'a \<Rightarrow> 's set" where
  "step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto> \<alpha> q }"

text \<open>The set of possible \<open>\<alpha>\<close>-steps for a set of states \<open>P\<close> is an instance of @{term "step"} lifted to sets of steps.\<close>
lemma step_set_is_step_set: "P \<mapsto>S \<alpha> (step_set P \<alpha>)"
  using step_set_def by force

text \<open>For a set of states \<open>P\<close> and an action \<open>\<alpha>\<close> there exists exactly one \<open>Q\<close> such that \<open>P \<mapsto>S \<alpha> Q\<close>.\<close>
lemma exactly_one_step_set: "\<exists>!Q. P \<mapsto>S \<alpha> Q"
proof -
  from step_set_is_step_set
  have "P \<mapsto>S \<alpha> (step_set P \<alpha>)"
    and "\<And>Q. P \<mapsto>S \<alpha> Q \<Longrightarrow> Q = (step_set P \<alpha>)"
    by fastforce+
  then show "\<exists>!Q. P \<mapsto>S \<alpha> Q"
    by blast
qed

text \<open>The lifted @{term "step"} (\<open>P \<mapsto>S \<alpha> Q\<close>) is therefore this set \<open>Q\<close>.\<close>
lemma step_set_eq:
  assumes "P \<mapsto>S \<alpha> Q"
  shows "Q = step_set P \<alpha>"
  using assms step_set_is_step_set exactly_one_step_set by fastforce

end (*<*) (* locale LTS *) (*>*)

subsection \<open>Labelled Transition Systems with Silent Steps\<close>

text \<open>We formalize labelled transition systems with silent steps as an extension of ordinary labelled transition systems
with a fixed silent action \<open>\<tau>\<close>.\<close>

locale LTS_Tau =
  LTS step
    for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
    fixes \<tau> :: 'a
begin

text \<open>The paper introduces a transition $p \xrightarrow{(\alpha)}p'$ if $p \xrightarrow{\alpha} p'$, or if $\alpha = \tau$ and $p = p'$ (cf. \cite[defintion 2]{bisping2023lineartimebranchingtime}). 
We define @{term "soft_step"} analagously and provide the notation \<open>p \<mapsto>a \<alpha> p'\<close>.\<close>
abbreviation soft_step ("_ \<mapsto>a _ _" [70,70,70] 80) where
  "p \<mapsto>a \<alpha> q \<equiv> p \<mapsto>\<alpha> q \<or> (\<alpha> = \<tau> \<and> p = q)" 

text \<open>A state \<open>p\<close> is @{term "silent_reachable"}, represented by the symbol \<open>\<Zsurj>\<close>, from another state \<open>p'\<close> iff there exists a path of \<open>\<tau>\<close>-transitions.
from \<open>p'\<close> to \<open>p\<close>.\<close>
inductive silent_reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>" 80)
  where
    refl: "p \<Zsurj> p" |
    step: "p \<Zsurj> p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj> p''"

text \<open>If \<open>p'\<close> is silent reachable from \<open>p\<close> and there is a \<open>\<tau>\<close>-transition from \<open>p'\<close> to \<open>p''\<close> then \<open>p''\<close> is silent reachable from \<open>p\<close>.\<close>
lemma silent_reachable_append_\<tau>: "p \<Zsurj> p' \<Longrightarrow> p' \<mapsto> \<tau> p'' \<Longrightarrow> p \<Zsurj> p''"
proof (induct rule: silent_reachable.induct)
  case (refl p)
  then show ?case using silent_reachable.intros by blast
next
  case (step p p' p'')
  then show ?case using silent_reachable.intros by blast
qed

text \<open>The relation @{term "silent_reachable"} is transitive.\<close>
lemma silent_reachable_trans:
  assumes
    \<open>p \<Zsurj> p'\<close>
    \<open>p' \<Zsurj> p''\<close>
  shows
    \<open>p \<Zsurj> p''\<close>
using assms silent_reachable.intros(2)
  by (induct, blast+)

text \<open>The relation @{term "silent_reachable_loopless"} is a variation of @{term "silent_reachable"} that does not use self-loops.\<close>
inductive silent_reachable_loopless :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>L" 80)
  where
    "p \<Zsurj>L p" |
    "p \<Zsurj>L p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj>L p''" and "p \<noteq> p'"

text \<open>If a state \<open>p'\<close> is @{term "silent_reachable"} from \<open>p\<close> it is also @{term "silent_reachable_loopless"}.\<close>
lemma silent_reachable_impl_loopless:
  assumes "p \<Zsurj> p'"
  shows "p \<Zsurj>L p'"
  using assms
proof(induct rule: silent_reachable.induct)
  case (refl p)
  thus ?case by (rule silent_reachable_loopless.intros(1))
next
  case (step p p' p'')
  thus ?case proof(cases "p = p'")
    case True
    thus ?thesis using "step.hyps"(3) by auto
  next
    case False
    thus ?thesis using "step.hyps" silent_reachable_loopless.intros(2) by blast
  qed
qed

lemma tau_chain_reachabilty:
  assumes \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
  shows \<open>\<forall>j < length pp. \<forall>i \<le> j. pp!i \<Zsurj> pp!j\<close>
proof safe
  fix j i
  assume \<open>j < length pp\<close> \<open>i \<le> j\<close>
  thus \<open>pp!i \<Zsurj> pp!j\<close>
  proof (induct j)
    case 0
    then show ?case
      using silent_reachable.refl by blast
  next
    case (Suc j)
    then show ?case
    proof (induct i)
      case 0
      then show ?case using assms silent_reachable_append_\<tau>
        by (metis Suc_lessD Suc_lessE bot_nat_0.extremum diff_Suc_1)
    next
      case (Suc i)
      then show ?case using silent_reachable.refl assms silent_reachable_append_\<tau>
        by (metis Suc_lessD Suc_lessE  diff_Suc_1 le_SucE)
    qed
  qed
qed

text \<open>In the following, we define @{term "weak_step"} as a new notion of transition relation between states. A state \<open>p\<close> can reach
\<open>p'\<close> by performing an \<open>\<alpha>\<close>-transition, possibly proceeded and followed by any number of \<open>\<tau>\<close>-transitions.\<close>
definition weak_step ("_ \<Zsurj>\<mapsto>\<Zsurj> _ _" [70, 70, 70] 80) where
  "p  \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p' \<equiv> if \<alpha> = \<tau> 
                    then p \<Zsurj> p'
                    else \<exists>p1 p2. p \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p'"

lemma silent_prepend_weak_step: "p \<Zsurj> p' \<Longrightarrow> p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'' \<Longrightarrow> p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
proof (cases "\<alpha> = \<tau>")
  case True
  assume "p \<Zsurj> p'"
     and "p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
     and "\<alpha> = \<tau>"
  hence "p' \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" by auto
  then have "p' \<Zsurj> p''" unfolding weak_step_def by auto
  with \<open>p \<Zsurj> p'\<close>
  have "p \<Zsurj> p''" using silent_reachable_trans 
    by blast
  then have "p \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" unfolding weak_step_def by auto
  with \<open>\<alpha> = \<tau>\<close>
  show "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''" by auto
next
  case False
  assume "p \<Zsurj> p'"
    and "p' \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''"
    and "\<alpha> \<noteq> \<tau>"
  then have "\<exists>p1 p2. p' \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> p''" 
    using weak_step_def by auto
  then obtain p1 and p2 where "p' \<Zsurj> p1" and "p1 \<mapsto> \<alpha> p2" and "p2 \<Zsurj> p''" by auto

  from \<open>p \<Zsurj> p'\<close> and \<open>p' \<Zsurj> p1\<close>
  have "p \<Zsurj> p1" by (rule silent_reachable_trans)

  with \<open>p1 \<mapsto> \<alpha> p2\<close> and \<open>p2 \<Zsurj> p''\<close> and \<open>\<alpha> \<noteq> \<tau>\<close>
  show "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p''" 
    using weak_step_def by auto
qed

text \<open>A sequence of @{term "weak_step"}'s from one state \<open>p\<close> to another \<open>p'\<close> is called a @{term "weak_step_sequence"}
That means that \<open>p'\<close> can be reached from \<open>p\<close> with that sequence of steps.\<close>
inductive weak_step_sequence :: "'s \<Rightarrow> 'a list \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Zsurj>\<mapsto>\<Zsurj>$ _ _" [70,70,70] 80) where
  "p \<Zsurj>\<mapsto>\<Zsurj>$ [] p'" if "p \<Zsurj> p'" |
  "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha>#rt) p''" if "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> p'" "p' \<Zsurj>\<mapsto>\<Zsurj>$ rt p''"

lemma weak_step_sequence_trans:
  assumes "p \<Zsurj>\<mapsto>\<Zsurj>$ tr_1 p'" and "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr_2 p''"
  shows "p \<Zsurj>\<mapsto>\<Zsurj>$ (tr_1 @ tr_2) p''"
  using assms weak_step_sequence.intros(2)
proof induct
  case (1 p p')
  then show ?case
    by (metis LTS_Tau.weak_step_sequence.simps append_Nil silent_prepend_weak_step silent_reachable_trans)
next
  case (2 p \<alpha> p' rt p'')
  then show ?case by fastforce
qed

text \<open>The weak traces of a state or all possible sequences of weak transitions that can be performed.
In the context of labelled transition systems, weak traces capture the observable behaviour of a state.\<close>
abbreviation weak_traces :: "'s \<Rightarrow> 'a list set"
  where "weak_traces p \<equiv> {tr. \<exists>p'. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p'}"

text \<open>The empty trace is in @{term "weak_traces"} for all states.\<close>
lemma empty_trace_allways_weak_trace:
  shows "[] \<in> weak_traces p"
  using silent_reachable.intros(1) weak_step_sequence.intros(1) by fastforce

text \<open>Since @{term "weak_step"}'s can be proceeded and followed by any number \<open>\<tau>\<close>-transitions and the empty
@{term "weak_step_sequence"} also allows \<open>\<tau>\<close>-transitions, \<open>\<tau>\<close> can be prepended to a weak trace of a state.\<close>
lemma prepend_\<tau>_weak_trace:
  assumes "tr \<in> weak_traces p"
  shows "(\<tau> # tr) \<in> weak_traces p"
  using silent_reachable.intros(1)
    and weak_step_def
    and assms
    and mem_Collect_eq
    and weak_step_sequence.intros(2)
  by fastforce

text \<open>If state \<open>p'\<close> is reachable from state \<open>p\<close> via a sequence of \<open>\<tau>\<close>-transitions and there exists a weak trace \<open>tr\<close> starting from \<open>p'\<close>,
then \<open>tr\<close> is also a weak trace starting from \<open>p\<close>.\<close>
lemma silent_prepend_weak_traces:
  assumes "p \<Zsurj> p'"
      and "tr \<in> weak_traces p'"
    shows "tr \<in> weak_traces p"
  using assms
proof-
  assume "p \<Zsurj> p'"
     and "tr \<in> weak_traces p'"
  hence "\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then obtain p'' where "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  
  from \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close>
    and \<open>p \<Zsurj> p'\<close>
  have "p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" 
    by (metis append_self_conv2 weak_step_sequence.intros(1) weak_step_sequence_trans)

  hence "\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then show "tr \<in> weak_traces p" 
    by blast
qed

text \<open>If there is an \<open>\<alpha>\<close>-transition from \<open>p\<close> to \<open>p'\<close>, and \<open>p'\<close> has a weak trace \<open>tr\<close>, then the sequence \<open>(\<alpha> # tr)\<close> 
is a valid (weak) trace of \<open>p\<close>.\<close>
lemma step_prepend_weak_traces:
  assumes "p \<mapsto> \<alpha> p'"
      and "tr \<in> weak_traces p'"
    shows "(\<alpha> # tr) \<in> weak_traces p"
  using assms
proof -
  from \<open>tr \<in> weak_traces p'\<close>
  have "\<exists>p''. p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  then obtain p'' where "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" by auto
  with \<open>p \<mapsto> \<alpha> p'\<close>
  have "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''" 
    by (metis LTS_Tau.silent_reachable.intros(1) LTS_Tau.silent_reachable_append_\<tau> LTS_Tau.weak_step_def LTS_Tau.weak_step_sequence.intros(2))
  then have "\<exists>p''. p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tr) p''" by auto
  then show "(\<alpha> # tr) \<in> weak_traces p" by auto
qed

text \<open>One of the behavioural pre-orders/equivalences that we talk about is trace pre-order/equivalence.
This is the modal characterization for one state is weakly trace pre-ordered to the other, @{term "weakly_trace_preordered"}
denoted by \<open>\<lesssim>WT\<close>, and two states are weakly trace equivalent, @{term "weakly_trace_equivalent"} denoted \<open>\<simeq>WT\<close>.\<close>
definition weakly_trace_preordered (infix "\<lesssim>WT" 60) where
  "p \<lesssim>WT q \<equiv> weak_traces p \<subseteq> weak_traces q"

definition weakly_trace_equivalent (infix "\<simeq>WT" 60) where
"p \<simeq>WT q \<equiv> p \<lesssim>WT q \<and> q \<lesssim>WT p"

text \<open>Just like @{term"step_setp"}, one can lift @{term "silent_reachable"} to sets of states.\<close>
abbreviation silent_reachable_setp (infix "\<Zsurj>S" 80) where
  "P \<Zsurj>S P' \<equiv> ((\<forall>p' \<in> P'. \<exists>p \<in> P. p \<Zsurj> p') \<and> (\<forall>p \<in> P. \<forall>p'. p \<Zsurj> p' \<longrightarrow> p' \<in> P'))"

definition silent_reachable_set :: "'s set \<Rightarrow> 's set" where
  "silent_reachable_set P \<equiv> { q . \<exists>p \<in> P. p \<Zsurj> q }"

lemma sreachable_set_is_sreachable: "P \<Zsurj>S (silent_reachable_set P)"
  using silent_reachable_set_def by auto

lemma exactly_one_sreachable_set: "\<exists>!Q. P \<Zsurj>S Q"
proof -
  from sreachable_set_is_sreachable
  have "P \<Zsurj>S (silent_reachable_set P)".

  have "\<And>Q. P \<Zsurj>S Q \<Longrightarrow> Q = (silent_reachable_set P)"
  proof -
    fix Q
    assume "P \<Zsurj>S Q"

    with sreachable_set_is_sreachable
    have "\<forall>q \<in> Q. q \<in> (silent_reachable_set P)" 
      by meson

    from \<open>P \<Zsurj>S Q\<close>
     and sreachable_set_is_sreachable
    have "\<forall>q \<in> (silent_reachable_set P). q \<in> Q"
      by meson

    from \<open>\<forall>q \<in> Q. q \<in> (silent_reachable_set P)\<close>
     and \<open>\<forall>q \<in> (silent_reachable_set P). q \<in> Q\<close>
    show "Q = (silent_reachable_set P)" by auto
  qed

  with \<open>P \<Zsurj>S (silent_reachable_set P)\<close> 
  show "\<exists>!Q. P \<Zsurj>S Q" 
    by blast
qed


lemma sreachable_set_eq:
  assumes "P \<Zsurj>S Q"
  shows "Q = silent_reachable_set P"
  using exactly_one_sreachable_set sreachable_set_is_sreachable assms by fastforce

text \<open>We likewise lift @{term "soft_step"} to sets of states.\<close>
abbreviation soft_step_setp ("_ \<mapsto>aS _ _" [70,70,70] 80) where
  "P \<mapsto>aS \<alpha> Q \<equiv> (\<forall>q \<in> Q. \<exists>p \<in> P. p \<mapsto>a \<alpha> q) \<and> (\<forall>p \<in> P. \<forall>q. p \<mapsto>a \<alpha> q \<longrightarrow> q \<in> Q)"

definition soft_step_set :: "'s set \<Rightarrow> 'a \<Rightarrow> 's set" where
  "soft_step_set P \<alpha> \<equiv> { q . \<exists>p \<in> P. p \<mapsto>a \<alpha> q }"

lemma soft_step_set_is_soft_step_set:
  "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)"
  using soft_step_set_def by auto

lemma exactly_one_soft_step_set:
  "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
proof -
  from soft_step_set_is_soft_step_set
  have "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)"
    and "\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)"
    by fastforce+
  show "\<exists>!Q. P \<mapsto>aS \<alpha> Q"
  proof
    from \<open>P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)\<close>
    show "P \<mapsto>aS \<alpha> (soft_step_set P \<alpha>)".
  next
    from \<open>\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)\<close>
    show "\<And>Q. P \<mapsto>aS \<alpha> Q \<Longrightarrow> Q = (soft_step_set P \<alpha>)".
  qed
qed  

lemma soft_step_set_eq:
  assumes "P \<mapsto>aS \<alpha> Q"
  shows "Q = soft_step_set P \<alpha>"
  using exactly_one_soft_step_set soft_step_set_is_soft_step_set assms 
  by fastforce

abbreviation \<open>stable_state p \<equiv> \<forall>p'. \<not>(p \<mapsto> \<tau> p')\<close>

lemma stable_state_stable:
  assumes \<open>stable_state p\<close> \<open>p \<Zsurj> p'\<close>
  shows \<open>p = p'\<close>
  using assms(2,1) by (cases, blast+)

definition stability_respecting :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stability_respecting R \<equiv> \<forall> p q. R p q \<and> stable_state p \<longrightarrow>
    (\<exists>q'. q \<Zsurj> q' \<and> R p q' \<and> stable_state q')\<close>

end (* locale LTS_Tau *)

end (* theory LTS *)
