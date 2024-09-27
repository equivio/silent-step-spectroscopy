section \<open>Weak Traces \label{appndx:weakTraces}\<close>
theory Weak_Traces
  imports Main HML_SRBB Expressiveness_Price
begin

text \<open>The inductive @{term "is_trace_formula"} represents the modal-logical characterization of weak traces HML$_{WT}$.
In particular:
\begin{itemize}
  \item $\top \in$ HML$_{WT}$ encoded by  @{term "is_trace_formula"} \<open>TT\<close>, @{term "is_trace_formula"} @{term "(ImmConj I \<psi>s)"} if \<open>I = {}\<close> and @{term "is_trace_formula"} @{term "(Conj I \<psi>s)"} if \<open>I = {}.\<close>.
  \item \<open>\<langle>\<epsilon>\<rangle>\<chi>\<close> $\in$ HML$_{WT}$ if \<open>\<phi>\<close> $\in$ HML$_{WT}$ encoded by @{term "is_trace_formula"} @{term "(Internal \<chi>)"} if @{term "is_trace_formula"} \<open>\<chi>\<close>.
  \item \<open>(\<alpha>)\<phi>\<close> $\in$ HML$_{WT}$ if \<open>\<phi>\<close> $\in$ HML$_{WT}$ encoded by @{term "is_trace_formula"} @{term "(Obs \<alpha> \<phi>)"} if @{term "is_trace_formula"} \<open>\<phi>\<close>.
  \item \<open>\<And>{(\<alpha>)\<phi>} \<union> \<Psi>\<close> $\in$ HML$_{WT}$ if \<open>\<phi>\<close> $\in$ HML$_{WT}$ and \<open>\<Psi> = {}\<close> encoded by @{term "is_trace_formula"} @{term "(BranchConj \<alpha> \<phi> I \<psi>s)"} if @{term "is_trace_formula"} \<open>\<phi>\<close> and \<open>I = {}\<close>.
\end{itemize}\<close>

inductive
      is_trace_formula :: "('act, 'i) hml_srbb \<Rightarrow> bool"
  and is_trace_formula_inner :: "('act, 'i) hml_srbb_inner \<Rightarrow> bool" where
  "is_trace_formula TT" |
  "is_trace_formula (Internal \<chi>)" if "is_trace_formula_inner \<chi>" |
  "is_trace_formula (ImmConj I \<psi>s)" if "I = {}" |

  "is_trace_formula_inner (Obs \<alpha> \<phi>)" if "is_trace_formula \<phi>" |
  "is_trace_formula_inner (Conj I \<psi>s)" if "I = {}"

text \<open>We define a function that translates a (weak) trace \<open>tr\<close> to a formula \<open>\<phi>\<close> such that a state \<open>p\<close> models \<open>\<phi>\<close>, \<open>p \<Turnstile> \<phi>\<close> if and only if \<open>tr\<close> is a (weak) trace of \<open>p\<close>.\<close>
fun wtrace_to_srbb :: "'act list \<Rightarrow> ('act, 'i) hml_srbb"
  and wtrace_to_inner :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_inner"
  and wtrace_to_conjunct :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_conjunct" where
  "wtrace_to_srbb [] = TT" |
  "wtrace_to_srbb tr = (Internal (wtrace_to_inner tr))" |

  "wtrace_to_inner [] = (Conj {} (\<lambda>_. undefined))" | \<comment> \<open> Should never happen\<close>
  "wtrace_to_inner (\<alpha> # tr) = (Obs \<alpha> (wtrace_to_srbb tr))" |

  "wtrace_to_conjunct tr = Pos (wtrace_to_inner tr)" \<comment> \<open>Should never happen\<close>

text \<open>@{term "wtrace_to_srbb trace"} is in our modal-logical characterization of weak traces.\<close>
lemma trace_to_srbb_is_trace_formula:
  "is_trace_formula (wtrace_to_srbb trace)"
  apply (induct trace)
  using is_trace_formula_is_trace_formula_inner.intros
    and is_trace_formula.simps
    and is_trace_formula_is_trace_formula_inner.intros(4)
    and wtrace_to_inner.simps(2)
    and wtrace_to_srbb.simps(2)
  by fastforce+

text \<open>The following three lemmas show that the modal-logical characterization of HML$_{WT}$ corresponds to the sublanguage of HML$_\text{SRBB}$, obtain by the energy coordinates \<open>(\<infinity>, 0, 0, 0, 0, 0, 0, 0)\<close>.\<close>

lemma trace_formula_to_expressiveness:
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_inner"
  shows  "(is_trace_formula \<phi>       \<longrightarrow> (\<phi> \<in> \<O>       (E \<infinity> 0 0 0 0 0 0 0)))
        \<and> (is_trace_formula_inner \<chi> \<longrightarrow> (\<chi> \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)))"
  by (rule is_trace_formula_is_trace_formula_inner.induct) (simp add: Sup_enat_def \<O>_def \<O>_inner_def)+

lemma expressiveness_to_trace_formula:
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_inner"
  shows "(\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0) \<longrightarrow> is_trace_formula \<phi>)
       \<and> (\<chi> \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0) \<longrightarrow> is_trace_formula_inner \<chi>) 
       \<and> True"
proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
  case TT
  then show ?case
    using is_trace_formula_is_trace_formula_inner.intros(1) by blast
next
  case (Internal x)
  then show ?case
    by (simp add: \<O>_inner_def \<O>_def is_trace_formula_is_trace_formula_inner.intros(2))
next
  case (ImmConj x1 x2)
  then show ?case
    using \<O>_def is_trace_formula_is_trace_formula_inner.intros(3)
    by(auto simp add: \<O>_def)
next
  case (Obs x1 x2)
  then show ?case by (simp add: \<O>_def \<O>_inner_def is_trace_formula_is_trace_formula_inner.intros(4))
next
  case (Conj I \<psi>s)
  show ?case
  proof (rule impI)
    assume "Conj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)"
    hence "I = {}"
      unfolding \<O>_inner_def
      by (metis bot.extremum_uniqueI bot_enat_def energy.sel(3) expr_pr_inner.simps inst_conj_depth_inner.simps(2) le_iff_add leq_components mem_Collect_eq not_one_le_zero)
    then show "is_trace_formula_inner (Conj I \<psi>s)" 
      by (simp add: is_trace_formula_is_trace_formula_inner.intros(5))
  qed
next
  case (StableConj I \<psi>s)
  show ?case
  proof (rule impI)
    assume "StableConj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)"
    have "StableConj I \<psi>s \<notin> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)" 
      by (simp add: \<O>_inner_def)
    with \<open>StableConj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)\<close>
    show "is_trace_formula_inner (StableConj I \<psi>s)" by contradiction
  qed
next
  case (BranchConj \<alpha> \<phi> I \<psi>s)
  have \<open>expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) \<ge> E 0 1 1 0 0 0 0 0\<close>
    by simp
  hence \<open>BranchConj \<alpha> \<phi> I \<psi>s \<notin> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)\<close>
    unfolding \<O>_inner_def by simp
  thus ?case by blast
next
  case (Pos x)
  then show ?case by auto
next
  case (Neg x)
  then show ?case by auto
qed

lemma modal_depth_only_is_trace_form: 
  "(is_trace_formula \<phi>) = (\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0))"
  using expressiveness_to_trace_formula trace_formula_to_expressiveness by blast

context Inhabited_Tau_LTS
begin                 

text \<open>If a formula \<open>\<phi>\<close> is in HML$_{WT}$ and a state \<open>p\<close> models \<open>\<phi>\<close>, then there exists a weak trace \<open>tr\<close> of \<open>p\<close> such that @{term "wtrace_to_srbb tr"} is equivalent to \<open>\<phi>\<close>.\<close>
lemma trace_formula_implies_trace:
  fixes \<psi> ::"('a, 's) hml_srbb_conjunct"
  shows
       trace_case: "is_trace_formula \<phi> \<Longrightarrow> p \<Turnstile>SRBB \<phi> \<Longrightarrow> (\<exists>tr \<in> weak_traces p. wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> \<phi>)"
    and conj_case: "is_trace_formula_inner \<chi> \<Longrightarrow> hml_srbb_inner_models q \<chi> \<Longrightarrow> (\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>)"
    and            True
proof (induction \<phi> and \<chi> and \<psi> arbitrary: p and q)
  case TT
  then have "[] \<in> weak_traces p" 
    using weak_step_sequence.intros(1) silent_reachable.intros(1) by fastforce
  moreover have "wtrace_to_srbb [] \<Lleftarrow>srbb\<Rrightarrow> TT"
    unfolding wtrace_to_srbb.simps
    by (simp add: equivp_reflp)
  ultimately show ?case by auto
next
  case (Internal \<chi>)

  from \<open>is_trace_formula (Internal \<chi>)\<close>
  have "is_trace_formula_inner \<chi>" 
    using is_trace_formula.cases by auto

  from \<open>p \<Turnstile>SRBB Internal \<chi>\<close>
  have "\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>"
    unfolding hml_srbb_models.simps.
  then obtain p' where "p \<Zsurj> p'" and "hml_srbb_inner_models p' \<chi>" by auto
  hence "hml_srbb_inner_models p' \<chi>" by auto
  with \<open>is_trace_formula_inner \<chi>\<close>
  have "\<exists>tr\<in>weak_traces p'. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>"
    using Internal.IH by blast
  then obtain tr where tr_spec:
    "tr \<in> weak_traces p'" "wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> \<chi>" by auto
  with \<open>p \<Zsurj> p'\<close> have "tr \<in> weak_traces p"
    using silent_prepend_weak_traces by auto

  moreover
  have "wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> Internal \<chi>"
  proof (cases tr)
    case Nil
    thus ?thesis
      using srbb_TT_is_\<chi>TT tr_spec by auto
  next
    case (Cons a tr)
    thus ?thesis
      using tr_spec internal_srbb_cong by auto
  qed

  ultimately show ?case by auto
next
  case (ImmConj I \<psi>s)

  from \<open>is_trace_formula (ImmConj I \<psi>s)\<close>
  have "I = {}" 
    by (simp add: is_trace_formula.simps)

  have "[] \<in> weak_traces p" 
    using silent_reachable.intros(1) weak_step_sequence.intros(1) by auto

  from srbb_TT_is_empty_conj
   and \<open>I = {}\<close>
  have "wtrace_to_srbb [] \<Lleftarrow>srbb\<Rrightarrow> ImmConj I \<psi>s"
    unfolding wtrace_to_srbb.simps by auto

  from \<open>[] \<in> weak_traces p\<close>
   and \<open>wtrace_to_srbb [] \<Lleftarrow>srbb\<Rrightarrow> ImmConj I \<psi>s\<close>
  show "\<exists>tr\<in>weak_traces p. wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> ImmConj I \<psi>s" by auto
next
  case (Obs \<alpha> \<phi>)
  assume IH: "\<And>p1. is_trace_formula \<phi> \<Longrightarrow> p1 \<Turnstile>SRBB \<phi> \<Longrightarrow> \<exists>tr\<in>weak_traces p1. wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> \<phi>"
     and "is_trace_formula_inner (Obs \<alpha> \<phi>)"
     and "hml_srbb_inner_models q (Obs \<alpha> \<phi>)"
  then show "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
  proof (cases "\<alpha> = \<tau>")
    case True

    with \<open>hml_srbb_inner_models q (Obs \<alpha> \<phi>)\<close> have \<open>q \<Turnstile>SRBB \<phi>\<close>
      using Obs.prems(1) silent_reachable.step empty_conj_trivial(1)
      by (metis (no_types, lifting) hml_srbb_inner.distinct(1) hml_srbb_inner.inject(1)
          hml_srbb_inner_models.simps(1) hml_srbb_models.simps(1,2) is_trace_formula.cases
          is_trace_formula_inner.cases)

    moreover have "is_trace_formula \<phi>" 
      using \<open>is_trace_formula_inner (Obs \<alpha> \<phi>)\<close> is_trace_formula_inner.cases by auto

    ultimately show "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      using Obs.IH
      by (metis \<open>\<alpha> = \<tau>\<close> obs_srbb_cong prepend_\<tau>_weak_trace wtrace_to_inner.simps(2))
  next
    case False

    from \<open>is_trace_formula_inner (Obs \<alpha> \<phi>)\<close>
    have "is_trace_formula \<phi>" 
      by (simp add: is_trace_formula_inner.simps)

    from \<open>hml_srbb_inner_models q (Obs \<alpha> \<phi>)\<close> and \<open>\<alpha> \<noteq> \<tau>\<close>
    have "\<exists>q'. q \<mapsto> \<alpha> q' \<and> q' \<Turnstile>SRBB \<phi>" by simp
    then obtain q' where "q \<mapsto> \<alpha> q'" and "q' \<Turnstile>SRBB \<phi>" by auto

    from \<open>is_trace_formula \<phi>\<close>
     and \<open>q' \<Turnstile>SRBB \<phi>\<close>
     and IH
    have "\<exists>tr' \<in> weak_traces q'. wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>" by auto
    then obtain tr' where "tr' \<in> weak_traces q'" and "wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>" by auto

    from \<open>q \<mapsto> \<alpha> q'\<close>
     and \<open>tr' \<in> weak_traces q'\<close>
    have "(\<alpha> # tr') \<in> weak_traces q"
      using step_prepend_weak_traces by auto

    from \<open>wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>\<close>
    have "Obs \<alpha> (wtrace_to_srbb tr') \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      using obs_srbb_cong by auto
    then have "wtrace_to_inner (\<alpha> # tr') \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      unfolding wtrace_to_inner.simps.

    with \<open>(\<alpha> # tr') \<in> weak_traces q\<close>
    show "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>" by blast
  qed
next
  case (Conj I \<psi>s)
  assume "is_trace_formula_inner (Conj I \<psi>s)"
     and "hml_srbb_inner_models q (Conj I \<psi>s)"

  from \<open>is_trace_formula_inner (Conj I \<psi>s)\<close>
  have "I = {}" 
    by (simp add: is_trace_formula_inner.simps)

  have "[] \<in> weak_traces q" by (rule empty_trace_allways_weak_trace)

  have "(Conj {} (\<lambda>_. undefined)) \<Lleftarrow>\<chi>\<Rrightarrow> (Conj {} \<psi>s)"
    using srbb_obs_\<tau>_is_\<chi>TT by simp
  then have "(Conj {} (\<lambda>_. undefined)) \<Lleftarrow>\<chi>\<Rrightarrow> (Conj I \<psi>s)"
    using \<open>I = {}\<close> by auto
  then have "wtrace_to_inner [] \<Lleftarrow>\<chi>\<Rrightarrow> Conj I \<psi>s"
    unfolding wtrace_to_inner.simps.

  from \<open>[] \<in> weak_traces q\<close>
   and \<open>wtrace_to_inner [] \<Lleftarrow>\<chi>\<Rrightarrow> Conj I \<psi>s\<close>
  show ?case by auto
next
  case (StableConj I \<psi>s)
  have "\<not>is_trace_formula_inner (StableConj I \<psi>s)" 
    by (simp add: is_trace_formula_inner.simps)
  with \<open>is_trace_formula_inner (StableConj I \<psi>s)\<close>
  show ?case by contradiction
next
  case (BranchConj \<alpha> \<phi> I \<psi>s)
  assume IH: "\<And>p1. is_trace_formula \<phi> \<Longrightarrow> p1 \<Turnstile>SRBB \<phi> \<Longrightarrow> \<exists>tr\<in>weak_traces p1. wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> \<phi>"
  from \<open>is_trace_formula_inner (BranchConj \<alpha> \<phi> I \<psi>s)\<close>
  have "is_trace_formula \<phi> \<and> I = {}" 
    by (simp add: is_trace_formula_inner.simps)
  hence "is_trace_formula \<phi>" and "I = {}" by auto
  from \<open>hml_srbb_inner_models q (BranchConj \<alpha> \<phi> I \<psi>s)\<close>
   and \<open>I = {}\<close>
  have "hml_srbb_inner_models q (Obs \<alpha> \<phi>)"
    using srbb_obs_is_empty_branch_conj
    by auto

  have "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
  proof (cases "\<alpha> = \<tau>")
    assume "\<alpha> = \<tau>"

    from \<open>hml_srbb_inner_models q (Obs \<alpha> \<phi>)\<close>
    show "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      using BranchConj.prems(1) is_trace_formula_inner.simps by fastforce
  next
    assume "\<alpha> \<noteq> \<tau>"

    from \<open>hml_srbb_inner_models q (Obs \<alpha> \<phi>)\<close>
     and \<open>\<alpha> \<noteq> \<tau>\<close>
    have "\<exists>q'. q \<mapsto> \<alpha> q' \<and> q' \<Turnstile>SRBB \<phi>" by auto
    then obtain q' where "q \<mapsto> \<alpha> q'" and "q' \<Turnstile>SRBB \<phi>" by auto

    from \<open>is_trace_formula \<phi>\<close>
     and \<open>q' \<Turnstile>SRBB \<phi>\<close>
     and IH
    have "\<exists>tr' \<in> weak_traces q'. wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>" by auto
    then obtain tr' where "tr' \<in> weak_traces q'" and "wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>" by auto

    from \<open>q \<mapsto> \<alpha> q'\<close>
     and \<open>tr' \<in> weak_traces q'\<close>
    have "(\<alpha> # tr') \<in> weak_traces q"
      using step_prepend_weak_traces by auto

    from \<open>wtrace_to_srbb tr' \<Lleftarrow>srbb\<Rrightarrow> \<phi>\<close>
    have "Obs \<alpha> (wtrace_to_srbb tr') \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      using obs_srbb_cong by auto
    then have "wtrace_to_inner (\<alpha> # tr') \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>"
      unfolding wtrace_to_inner.simps.

    with \<open>(\<alpha> # tr') \<in> weak_traces q\<close>
    show "\<exists>tr \<in> weak_traces q. wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>" by blast
  qed
  then obtain tr where "tr \<in> weak_traces q" and "wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>" by auto

  from \<open>wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> Obs \<alpha> \<phi>\<close>
   and \<open>I = {}\<close>
  have "wtrace_to_inner tr \<Lleftarrow>\<chi>\<Rrightarrow> (BranchConj \<alpha> \<phi> I \<psi>s)"
    using srbb_obs_is_empty_branch_conj by simp
  with \<open>tr \<in> weak_traces q\<close>
  show ?case by blast
next
  case (Pos \<chi>)
  then show ?case by auto
next
  case (Neg \<chi>)
  then show ?case by auto
qed

text \<open>\<open>t\<close> is a weak trace of a state \<open>p\<close> if and only if \<open>p\<close> models the formula obtained from @{term "wtrace_to_srbb t"}.\<close>
lemma trace_equals_trace_to_formula: 
  "t \<in> weak_traces p = (p \<Turnstile>SRBB (wtrace_to_srbb t))"
proof
  assume "t \<in> weak_traces p"
  show "p \<Turnstile>SRBB (wtrace_to_srbb t)"
    using \<open>t \<in> weak_traces p\<close>
  proof(induction t arbitrary: p)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons a tail)
    from Cons obtain p'' p' where "p \<Zsurj>\<mapsto>\<Zsurj> a p''" "p'' \<Zsurj>\<mapsto>\<Zsurj>$ tail p'" using weak_step_sequence.simps 
      by (smt (verit, best) list.discI list.inject mem_Collect_eq) 
    with Cons(1) have IS: "p'' \<Turnstile>SRBB wtrace_to_srbb tail"
      by blast
    from Cons have goal_eq: "wtrace_to_srbb (a # tail) = (Internal (Obs a (wtrace_to_srbb tail)))"
      by simp
    show ?case
      by (smt (verit) Cons.IH IS Inhabited_Tau_LTS.hml_srbb_inner_models.simps(1) Inhabited_Tau_LTS_axioms LTS_Tau.silent_reachable_trans \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> empty_trace_allways_weak_trace goal_eq hml_srbb_models.simps(2) weak_step_def wtrace_to_srbb.elims)
  qed
next
  assume "p \<Turnstile>SRBB wtrace_to_srbb t"
  then show "t \<in> weak_traces p"
  proof(induction t arbitrary: p)
    case Nil
    then show ?case
      using weak_step_sequence.intros(1) silent_reachable.intros(1) by auto
  next
    case (Cons a tail)
    hence "p \<Turnstile>SRBB (Internal (Obs a (wtrace_to_srbb tail)))"
      by simp
    show ?case 
      using Cons.IH \<open>p \<Turnstile>SRBB hml_srbb.Internal (hml_srbb_inner.Obs a (wtrace_to_srbb tail))\<close> prepend_\<tau>_weak_trace silent_prepend_weak_traces step_prepend_weak_traces by fastforce
  qed
qed

text \<open>If a state \<open>p\<close> weakly trace-pre-orders another state \<open>q\<close>, \<open>\<phi>\<close> is in our modal-logical characterization HML$_{WT}$, and \<open>p\<close> models \<open>\<phi>\<close> then \<open>q\<close> models \<open>\<phi>\<close>.\<close>
lemma aux:
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<chi> :: "('a, 's) hml_srbb_inner"
  fixes \<psi> :: "('a, 's) hml_srbb_conjunct"
  shows "p \<lesssim>WT q \<Longrightarrow> is_trace_formula \<phi> \<Longrightarrow> p \<Turnstile>SRBB \<phi> \<Longrightarrow> q \<Turnstile>SRBB \<phi>"
proof -
  assume \<phi>_trace: "is_trace_formula \<phi>" and p_sat_srbb: "p \<Turnstile>SRBB \<phi>" and assms: "p \<lesssim>WT q"
  show "q \<Turnstile>SRBB \<phi>"
  proof-
    from assms have p_trace_implies_q_trace: "\<forall>tr p'. (p \<Zsurj>\<mapsto>\<Zsurj>$ tr p') \<longrightarrow> (\<exists>q'. q \<Zsurj>\<mapsto>\<Zsurj>$ tr q')" 
      unfolding weakly_trace_preordered_def by auto
    from p_sat_srbb trace_formula_implies_trace obtain tr p' where 
      "(p \<Zsurj>\<mapsto>\<Zsurj>$ tr p')" "wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> \<phi>"
      using \<phi>_trace by blast
    with p_trace_implies_q_trace obtain q' where "q \<Zsurj>\<mapsto>\<Zsurj>$ tr q'" 
      by blast
    with trace_equals_trace_to_formula show ?thesis 
      using \<open>wtrace_to_srbb tr \<Lleftarrow>srbb\<Rrightarrow> \<phi>\<close> by auto
  qed
qed 

text \<open>These are the main lemmas of this theory. They establish that the colloquial, relational notion of of weak trace pre-order/equivalence 
has the same distinctive power as the one derived from the coordinate (\<open>\<infinity>, 0, 0, 0, 0, 0, 0, 0\<close>).
\\\\
A state \<open>p\<close> weakly trace-pre-orders a state \<open>q\<close> iff and only if it also pre-orders \<open>q\<close> with respect to the coordinate (\<open>\<infinity>, 0, 0, 0, 0, 0, 0, 0\<close>).\<close>
lemma expr_preorder_characterizes_relational_preorder_traces:
  "(p \<lesssim>WT q) = (p \<preceq> (E \<infinity> 0 0 0 0 0 0 0) q)"
  unfolding expr_preord_def preordered_def
proof
  assume "p \<lesssim>WT q"
  thus "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"
    using aux expressiveness_to_trace_formula weakly_trace_preordered_def
    by blast+ 
next
  assume \<phi>_eneg: "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"
  thus "p \<lesssim>WT q"
    unfolding weakly_trace_preordered_def
    using trace_equals_trace_to_formula trace_formula_to_expressiveness trace_to_srbb_is_trace_formula
    by fastforce
qed

text \<open>Two states \<open>p\<close> and \<open>q\<close> are weakly trace equivalent if and only if they they are equivalent with respect to the coordinate (\<open>\<infinity>, 0, 0, 0, 0, 0, 0, 0\<close>).\<close>
lemma "(p \<simeq>WT q) = (p \<sim> (E \<infinity> 0 0 0 0 0 0 0) q)"
  using expr_preorder_characterizes_relational_preorder_traces
  unfolding weakly_trace_equivalent_def expr_equiv_def \<O>_def expr_preord_def
  by simp

end

end