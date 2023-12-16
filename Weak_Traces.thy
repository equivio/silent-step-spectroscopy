theory Weak_Traces
  imports Main HML_SRBB Expressiveness_Price
begin

inductive
      is_trace_formula :: "('act, 'i) hml_srbb \<Rightarrow> bool"
  and is_trace_formula_conjunction :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> bool" where
  "is_trace_formula TT" |
  "is_trace_formula (Internal \<chi>)" if "is_trace_formula_conjunction \<chi>" |
  "is_trace_formula_conjunction (Obs \<alpha> \<phi>)" if "is_trace_formula \<phi>"

primrec \<phi>_wtraces :: "('act, 'i) hml_srbb \<Rightarrow> 'act list set"
  and \<chi>_wtraces :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> 'act list set"
  and \<psi>_wtraces :: "('act, 'i) hml_srbb_conjunct \<Rightarrow> 'act list set" where
  "\<phi>_wtraces TT = {[]}" |
  "\<phi>_wtraces (Internal \<chi>) = \<chi>_wtraces \<chi>" |
  "\<phi>_wtraces (ImmConj I \<psi>s) = \<Union>((\<psi>_wtraces \<circ> \<psi>s) ` I)" |

  "\<chi>_wtraces (Obs \<alpha> \<phi>) = (\<lambda>tr. \<alpha> # tr) ` (\<phi>_wtraces \<phi>)" |
  "\<chi>_wtraces (Conj I \<psi>s) = \<Union>((\<psi>_wtraces \<circ> \<psi>s) ` I)" |
  "\<chi>_wtraces (StableConj I \<psi>s) = \<Union>((\<psi>_wtraces \<circ> \<psi>s) ` I)" |
  "\<chi>_wtraces (BranchConj \<alpha> \<phi> I \<psi>s) = (\<lambda>tr. \<alpha> # tr) ` (\<phi>_wtraces \<phi>) \<union> \<Union>((\<psi>_wtraces \<circ> \<psi>s) ` I)" |

  "\<psi>_wtraces (Pos \<chi>) = \<chi>_wtraces \<chi>" |
  "\<psi>_wtraces (Neg \<chi>) = \<chi>_wtraces \<chi>" \<comment> \<open> This case is problematic! Actually, I want to reject all those traces... \<close>

lemma 
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_conjunction"
  shows "(is_trace_formula \<phi> \<longrightarrow> (\<exists>tr. \<phi>_wtraces \<phi> = {tr}))
       \<and> (is_trace_formula_conjunction \<chi> \<longrightarrow> (\<exists>tr. \<chi>_wtraces \<chi> = {tr}))"
  apply (induct rule: is_trace_formula_is_trace_formula_conjunction.induct)
  by fastforce+

fun wtrace_to_\<phi> :: "'act list \<Rightarrow> ('act, 'i) hml_srbb"
  and wtrace_to_\<chi> :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_conjunction"
  and wtrace_to_\<psi> :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_conjunct" where
  "wtrace_to_\<phi> [] = TT" |
  "wtrace_to_\<phi> tr = (Internal (wtrace_to_\<chi> tr))" |

  "wtrace_to_\<chi> [] = (Conj {} (\<lambda>_. undefined))" | \<comment> \<open> Should never happen\<close>
  "wtrace_to_\<chi> (\<alpha> # tr) = (Obs \<alpha> (wtrace_to_\<phi> tr))" |

  "wtrace_to_\<psi> tr = Pos (wtrace_to_\<chi> tr)" \<comment> \<open>Should never happen\<close>

lemma "is_trace_formula (wtrace_to_\<phi> trace)"
  apply (induct trace)
  using is_trace_formula_is_trace_formula_conjunction.intros
  by fastforce+

lemma trace_formula_to_expressiveness:
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_conjunction"
  shows  "(is_trace_formula \<phi>             \<longrightarrow> (\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0)))
        \<and> (is_trace_formula_conjunction \<chi> \<longrightarrow> (\<chi> \<in> \<O>_\<chi> (E \<infinity> 0 0 0 0 0 0 0)))"
  apply (rule is_trace_formula_is_trace_formula_conjunction.induct)
  by (simp add: \<O>_def \<O>_\<chi>_def leq_not_eneg)+

lemma expressiveness_to_trace_formula:
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_conjunction"
  shows "(\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0) \<longrightarrow> is_trace_formula \<phi>)
       \<and> (\<chi> \<in> \<O>_\<chi> (E \<infinity> 0 0 0 0 0 0 0) \<longrightarrow> is_trace_formula_conjunction \<chi>) 
       \<and> True"
  apply (rule hml_srbb_hml_srbb_conjunction_hml_srbb_conjunct.induct)
  using is_trace_formula_is_trace_formula_conjunction.intros(1) apply blast
  apply (simp add: \<O>_\<chi>_def \<O>_def is_trace_formula_is_trace_formula_conjunction.intros(2))
  apply (simp add: \<O>_def leq_not_eneg)
  by (simp add: \<O>_\<chi>_def \<O>_def is_trace_formula_is_trace_formula_conjunction.intros(3) leq_not_eneg)+

lemma modal_depth_only_is_trace_form: 
  "(is_trace_formula \<phi>) = (\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0))"
  using expressiveness_to_trace_formula trace_formula_to_expressiveness by blast

context Inhabited_Tau_LTS
begin

lemma trace_formula_implies_trace:
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<psi> ::"('a, 's) hml_srbb_conjunct"
  shows trace_case: "is_trace_formula \<phi> \<Longrightarrow> \<phi> \<Turnstile>SRBB p \<Longrightarrow> (\<exists>tr \<in> weak_traces p. wtrace_to_\<phi> tr = \<phi>)" and
conj_case: "is_trace_formula_conjunction \<chi> \<Longrightarrow> hml_srbb_conjunction_models \<chi> q \<Longrightarrow> (\<exists>tr \<in> weak_traces q. wtrace_to_\<chi> tr = \<chi>)"
and True
proof(induction \<phi> and \<chi> and \<psi> arbitrary: p and q)
  case TT
  then show ?case 
    using weak_step_sequence.intros(1) by fastforce 
next
  case (Internal \<chi>r)
  assume IH: "(\<And>q. is_trace_formula_conjunction \<chi>r \<Longrightarrow>
                 hml_srbb_conjunction_models \<chi>r q \<Longrightarrow> \<exists>tr\<in>weak_traces q. wtrace_to_\<chi> tr = \<chi>r)"
and is_trace_internal :"is_trace_formula (hml_srbb.Internal \<chi>r)"
and internal_satisfied: "hml_srbb.Internal \<chi>r \<Turnstile>SRBB p"
  from internal_satisfied have "((hml_srbb_to_hml (hml_srbb.Internal \<chi>r)) \<Turnstile> p)"
    by simp
  then obtain p' where wtrace_to_p': "p \<Zsurj> p'" and p'_models_\<chi>r: "hml_srbb_conjunction_models \<chi>r p'" 
    by auto
  from is_trace_internal have "is_trace_formula_conjunction \<chi>r"
    using is_trace_formula.cases by auto
  with p'_models_\<chi>r IH obtain tail where tail_in_traces_p': "tail \<in> weak_traces p'" "wtrace_to_\<chi> tail = \<chi>r"
    by blast
  from tail_in_traces_p' obtain p'' where "p' \<Zsurj>\<mapsto>\<Zsurj>$ tail p''"
    by blast
  then show ?case
  proof(cases tail)
    case Nil
    hence False
      using \<open>is_trace_formula_conjunction \<chi>r\<close> is_trace_formula_conjunction.simps tail_in_traces_p'(2) by force
    then show ?thesis by blast
  next
    case (Cons a list)
    then obtain q' where q'_properties:"p' \<Zsurj>\<mapsto>\<Zsurj> a q' \<and> q' \<Zsurj>\<mapsto>\<Zsurj>$ list p''"
      using \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tail p''\<close> weak_step_sequence.cases 
      by (metis list.discI list.inject)
    hence "p \<Zsurj>\<mapsto>\<Zsurj> a q'" using wtrace_to_p' silent_reachable_trans weak_step_def
      by metis
    with q'_properties have "p \<Zsurj>\<mapsto>\<Zsurj>$ tail p''" 
      using Cons weak_step_sequence.intros(2) by blast
    then show ?thesis
      using Cons tail_in_traces_p'(2) by auto 
  qed
next
  case (ImmConj x1 x2)
  then have False
    using is_trace_formula.cases by auto
  then show ?case by blast
next
  case (Obs x1 x2)
  then show ?case sorry
next
  case (Conj x1 x2)
  hence False
    using is_trace_formula_conjunction.cases by blast
  then show ?case by blast 
next
  case (StableConj x1 x2)
  hence False 
    using is_trace_formula_conjunction.cases by blast
  then show ?case by by blast
next
  case (BranchConj x1 x2 x3 x4)
  hence False 
    by (simp add: is_trace_formula_conjunction.simps)
  then show ?case by blast
next
  case (Pos x)
  then show ?case 
    by blast 
next
  case (Neg x)
  then show ?case by blast
qed

lemma aux:
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<chi> :: "('a, 's) hml_srbb_conjunction"
  fixes \<psi> :: "('a, 's) hml_srbb_conjunct"
  assumes "p \<lesssim>WT q"
  shows "(is_trace_formula \<phi> \<longrightarrow> (\<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q))
      \<and> (is_trace_formula_conjunction \<chi> \<longrightarrow> (hml_srbb_conjunction_models \<chi> p \<longrightarrow> hml_srbb_conjunction_models \<chi> q))
      \<and> (\<lambda>x. True) \<psi>"
  sorry

lemma "(p \<lesssim>WT q) = (p \<preceq> (E \<infinity> 0 0 0 0 0 0 0) q)"
  unfolding expr_preord_def hml_preordered_def
proof
  assume "p \<lesssim>WT q"
  show "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). \<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q"
  proof
    fix \<phi>:: "('a, 's) hml_srbb"
    assume "\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0)"
    hence "is_trace_formula \<phi>" using expressiveness_to_trace_formula by blast
    thus "\<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q" 
      using aux \<open>p \<lesssim>WT q\<close> weakly_trace_preordered_def by blast
  qed
next
  assume \<phi>_eneg: "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). \<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q"
  show "p \<lesssim>WT q"
  proof-
    from \<phi>_eneg have "\<forall>\<phi>. is_trace_formula \<phi> \<longrightarrow> \<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q"
      using expressiveness_to_trace_formula modal_depth_only_is_trace_form by blast
    then show ?thesis unfolding weakly_trace_preordered_def using trace_formula_implies_trace
      sorry
  qed
qed

lemma "p \<Zsurj>\<mapsto>\<Zsurj>$ t p' \<Longrightarrow> \<exists>\<phi>. is_trace_formula \<phi> \<and> \<phi> \<Turnstile>SRBB p \<and> wtrace_to_\<phi> t = \<phi>"
proof (induction t arbitrary: p)
  case Nil
  then show ?case 
    using is_trace_formula_is_trace_formula_conjunction.intros(1) by force
next
  case (Cons \<alpha> tail)

  assume IH: "\<And>p1. p1 \<Zsurj>\<mapsto>\<Zsurj>$ tail p' \<Longrightarrow> \<exists>\<phi>. is_trace_formula \<phi> \<and> \<phi> \<Turnstile>SRBB p1 \<and> wtrace_to_\<phi> tail = \<phi>"
    and "p \<Zsurj>\<mapsto>\<Zsurj>$ (\<alpha> # tail) p'"
  hence "\<exists>m. p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m \<and> m \<Zsurj>\<mapsto>\<Zsurj>$ tail p'" 
    using weak_step_sequence.cases by fastforce
  then obtain m where "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m" and "m \<Zsurj>\<mapsto>\<Zsurj>$ tail p'" 
    by blast
  then have "\<exists>\<phi>. is_trace_formula \<phi> \<and> \<phi> \<Turnstile>SRBB m \<and> wtrace_to_\<phi> tail = \<phi>" using IH
    by blast
  then obtain \<phi>_tail where "is_trace_formula \<phi>_tail"
                  and "\<phi>_tail \<Turnstile>SRBB m"
                  and "wtrace_to_\<phi> tail = \<phi>_tail" by blast
  define \<phi> where "\<phi> \<equiv> (Internal (Obs \<alpha> \<phi>_tail))"

  have "is_trace_formula \<phi>"
    using \<open>is_trace_formula \<phi>_tail\<close>
      and is_trace_formula_is_trace_formula_conjunction.intros
      and \<phi>_def
    by force

  have "wtrace_to_\<phi> (\<alpha> # tail) = \<phi>"
    using \<open>wtrace_to_\<phi> tail = \<phi>_tail\<close>
      and \<phi>_def by force

  have "\<phi> \<Turnstile>SRBB p"
    using \<open>p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m\<close>
      and \<open>\<phi>_tail \<Turnstile>SRBB m\<close>
    unfolding \<phi>_def
      and hml_srbb_models.simps
      and hml_srbb_to_hml.simps
    unfolding hml_models.simps
      and hml_srbb_conjunction_to_hml.simps
  proof -
    assume "p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m"
       and "hml_srbb_to_hml \<phi>_tail \<Turnstile> m"

    show "\<exists>p'. p \<Zsurj> p' \<and> (\<exists>p'a. p' \<mapsto> \<alpha> p'a \<and> ((hml_srbb_to_hml \<phi>_tail) \<Turnstile> p'a))"
    proof (cases \<open>\<alpha> = \<tau>\<close>)
      case True
      hence "\<alpha> = \<tau>".

      from \<open>p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m\<close> and \<open>\<alpha> = \<tau>\<close>
      have "p \<Zsurj> m" 
        using weak_step_def by auto

      then show ?thesis sorry
    next
      case False
      hence "\<alpha> \<noteq> \<tau>".

      from \<open>p \<Zsurj>\<mapsto>\<Zsurj> \<alpha> m\<close> and \<open>\<alpha> \<noteq> \<tau>\<close>
      have "\<exists>p1 p2. p \<Zsurj> p1 \<and> p1 \<mapsto> \<alpha> p2 \<and> p2 \<Zsurj> m"
        using weak_step_def by auto
      then obtain ml and mr where "p \<Zsurj> ml" and "ml \<mapsto> \<alpha> mr" and "mr \<Zsurj> m"
        by blast

      from \<open>hml_srbb_to_hml \<phi>_tail \<Turnstile> m\<close>
       and \<open>mr \<Zsurj> m\<close>
       and \<open>is_trace_formula \<phi>_tail\<close>
      have "hml_srbb_to_hml \<phi>_tail \<Turnstile> mr" sorry

      then show ?thesis 
        using \<open>ml \<mapsto> \<alpha> mr\<close> \<open>p \<Zsurj> ml\<close> by blast
    qed
  qed

  then show ?case
    using \<open>is_trace_formula \<phi>\<close>
      and \<open>\<phi> \<Turnstile>SRBB p\<close>
      and \<open>wtrace_to_\<phi> (\<alpha> # tail) = \<phi>\<close>
    by blast
qed

end

end