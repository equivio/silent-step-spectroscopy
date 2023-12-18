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

lemma trace_to_\<phi>_is_trace_formula:
  "is_trace_formula (wtrace_to_\<phi> trace)"
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

fun remove_\<tau>_from_wtrace :: "'a list \<Rightarrow> 'a list"
  where
"remove_\<tau>_from_wtrace [] = []" |
"remove_\<tau>_from_wtrace (\<alpha>#tr) = (if \<alpha> = \<tau> then remove_\<tau>_from_wtrace tr 
                                          else (\<alpha> # remove_\<tau>_from_wtrace tr))"

(*TODO: cleanup*)
lemma removed_\<tau>_in_wtraces:
  assumes "t \<in> weak_traces p"
  shows "remove_\<tau>_from_wtrace t \<in> weak_traces p"
  using assms
proof(induction t arbitrary: p)
  case Nil
  then show ?case 
    using LTS_Tau.weak_step_sequence.intros(1) by fastforce 
next
  case (Cons a tr)
  from this(2) obtain p' p'' where "p \<Zsurj>\<mapsto>\<Zsurj> a p'" "p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''" 
    using weak_step_sequence.cases     
    by blast
  with Cons have IS: "remove_\<tau>_from_wtrace tr \<in> weak_traces p'"
    by blast
  then show ?case
  proof(cases \<open>a = \<tau>\<close>)
    case True
    hence eq: "remove_\<tau>_from_wtrace (a # tr) = remove_\<tau>_from_wtrace tr"
      by simp
    from \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p'\<close> have "p \<Zsurj> p'"
      by (simp add: LTS_Tau.weak_step_def True)
    with IS show ?thesis 
      proof(cases tr)
        case Nil
        with \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> have "p' = p''"
          using LTS_Tau.weak_step_sequence.cases by fastforce
        then show ?thesis
          using weak_step_sequence.intros(1) eq local.Nil by fastforce 
      next
        case (Cons b tail)
        with \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> obtain q where "p' \<Zsurj>\<mapsto>\<Zsurj> b q" "q \<Zsurj>\<mapsto>\<Zsurj>$ tail p''"
          using weak_step_sequence.cases by force
        with \<open>p \<Zsurj> p'\<close> have "p \<Zsurj>\<mapsto>\<Zsurj> b q"
          by (metis (no_types, lifting) LTS_Tau.silent_reachable_trans weak_step_def)
        with \<open>q \<Zsurj>\<mapsto>\<Zsurj>$ tail p''\<close> have "(b#tail) \<in> weak_traces p" 
          using weak_step_sequence.intros(2) by fastforce
        then show ?thesis
          using Cons.IH eq local.Cons by auto
      qed
  next
    case False
    with \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p'\<close> \<open>p' \<Zsurj>\<mapsto>\<Zsurj>$ tr p''\<close> show ?thesis
      using IS weak_step_sequence.intros(2) by fastforce
  qed
  qed

lemma trace_formula_implies_trace:
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
  from Internal(3) obtain p' where wtrace_to_p': "p \<Zsurj> p'" and p'_models_\<chi>r: "hml_srbb_conjunction_models \<chi>r p'" 
    by auto
  from Internal(2) have "is_trace_formula_conjunction \<chi>r"
    using is_trace_formula.cases by auto
  with p'_models_\<chi>r IH obtain tail p'' where tail_in_traces_p': "tail \<in> weak_traces p'" "wtrace_to_\<chi> tail = \<chi>r" "p' \<Zsurj>\<mapsto>\<Zsurj>$ tail p''"
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
  case (Obs \<alpha> \<phi>r)
  assume IH: "(\<And>p. is_trace_formula \<phi>r \<Longrightarrow> \<phi>r \<Turnstile>SRBB p \<Longrightarrow> \<exists>tr\<in>weak_traces p. wtrace_to_\<phi> tr = \<phi>r)"
and obs_is_trace:"is_trace_formula_conjunction (hml_srbb_conjunction.Obs \<alpha> \<phi>r)"
and obs_models_q: "hml_srbb_conjunction_models (hml_srbb_conjunction.Obs \<alpha> \<phi>r) q"
  from obs_is_trace have \<phi>r_is_trace: "is_trace_formula \<phi>r"
    using is_trace_formula_conjunction.cases by auto
  from obs_models_q have hml_models: "hml_srbb_conjunction_to_hml (Obs \<alpha> \<phi>r) \<Turnstile> q"
    by simp
  then show ?case
  proof(cases \<open>\<alpha> = \<tau>\<close>)
    case True
    with hml_models have "hml.Silent (hml_srbb_to_hml \<phi>r) \<Turnstile> q" 
      using hml_srbb_conjunction_to_hml.simps 
      by force
    then obtain q' where "(q \<mapsto> \<tau> q' \<and> (\<phi>r \<Turnstile>SRBB q')) \<or> (\<phi>r \<Turnstile>SRBB q)"
      using hml_models.simps(4)
      by fastforce
    then show ?thesis 
    proof
      assume assm: "q \<mapsto> \<tau> q' \<and> \<phi>r \<Turnstile>SRBB q'"
      with IH \<phi>r_is_trace  obtain tail where "tail\<in>weak_traces q'" "wtrace_to_\<phi> tail = \<phi>r"
        by blast
      with assm show ?thesis
        using LTS_Tau.weak_step_sequence.intros(2) True silent_reachable.intros weak_step_def 
        by fastforce
    next
      assume "\<phi>r \<Turnstile>SRBB q"
      with IH \<phi>r_is_trace show ?thesis 
        using LTS_Tau.weak_step_sequence.intros(2) True silent_reachable.intros(1) weak_step_def 
        by fastforce
    qed
  next
    case False
    hence "hml.Obs \<alpha> (hml_srbb_to_hml \<phi>r) \<Turnstile> q" 
      using hml_srbb_conjunction_to_hml.simps hml_models by presburger
    then obtain q' where \<alpha>_step: "q \<mapsto> \<alpha> q'" and \<phi>r_models_q': "(\<phi>r \<Turnstile>SRBB q')"
      by auto
    with IH \<phi>r_is_trace obtain tail where tail_in_wt_q': "tail \<in>weak_traces q'" "wtrace_to_\<phi> tail = \<phi>r"
      by blast
    from \<alpha>_step have "q \<Zsurj>\<mapsto>\<Zsurj> \<alpha> q'" 
      unfolding weak_step_def using silent_reachable.simps by metis
    hence wt_q_to_q': "q \<Zsurj>\<mapsto>\<Zsurj>$ [\<alpha>] q'" 
      using weak_step_sequence.simps unfolding weak_step_def using silent_reachable.simps
      by (smt (verit, best))
    with tail_in_wt_q' have "(\<alpha>#tail) \<in> weak_traces q" using weak_step_sequence_trans
      by fastforce
    then show ?thesis 
      using tail_in_wt_q'(2) by fastforce
  qed
next
  case (Conj x1 x2)
  hence False
    using is_trace_formula_conjunction.cases by blast
  then show ?case by blast 
next
  case (StableConj x1 x2)
  hence False 
    using is_trace_formula_conjunction.cases by blast
  then show ?case by blast
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

lemma trace_equals_trace_to_formula: 
  "t \<in> weak_traces p = ((wtrace_to_\<phi> t) \<Turnstile>SRBB p)"
proof
  assume "t \<in> weak_traces p"
  show "((wtrace_to_\<phi> t) \<Turnstile>SRBB p)"
    using \<open>t \<in> weak_traces p\<close>
  proof(induction t arbitrary: p)
    case Nil
    then show ?case 
      by simp
  next
    case (Cons a tail)
    from Cons obtain p'' p' where "p \<Zsurj>\<mapsto>\<Zsurj> a p''" "p'' \<Zsurj>\<mapsto>\<Zsurj>$ tail p'" using weak_step_sequence.simps 
      by (smt (verit, best) list.discI list.inject mem_Collect_eq) 
    with Cons(1) have IS: "wtrace_to_\<phi> tail \<Turnstile>SRBB p''"
      by blast
    hence IS_2: "((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p'')" by simp
    from Cons have goal_eq: "wtrace_to_\<phi> (a # tail) = (Internal (Obs a (wtrace_to_\<phi> tail)))"
      by simp
    show ?case
    proof(cases \<open>a = \<tau>\<close>)
      case True
      with goal_eq have "(wtrace_to_\<phi> (a # tail) \<Turnstile>SRBB p) = 
(hml.Internal (hml.Silent (hml_srbb_to_hml (wtrace_to_\<phi> tail))) \<Turnstile> p)"
        by force
      also have "... = 
(\<exists>p'. p \<Zsurj> p' \<and> (((\<exists>p''. p' \<mapsto> \<tau> p'' \<and> ((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p'')) \<or> 
((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p'))))"
        by force
      with \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> True IS_2 show ?thesis 
        using weak_step_def by auto
    next
      case False
      hence "wtrace_to_\<phi> (a#tail) = 
(Internal (Obs a (wtrace_to_\<phi> tail)))"
        by simp
      hence converted_srbb_sat:  "(wtrace_to_\<phi> (a # tail) \<Turnstile>SRBB p) =
(\<exists>p'. p \<Zsurj> p' \<and> ((\<exists>p''. p' \<mapsto> a p'' \<and> wtrace_to_\<phi> tail \<Turnstile>SRBB p'')))"
        by (simp add: False)
      with IS_2 False \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> show ?thesis 
        by (smt (verit, best) LTS_Tau.hml_models.simps(1) LTS_Tau.hml_models.simps(3) 
LTS_Tau.silent_reachable_trans hml_srbb_models.elims(3) hml_srbb_to_hml.simps(1) 
hml_srbb_to_hml.simps(2) weak_step_def wtrace_to_\<phi>.elims) 
    qed
  qed
next
  assume "wtrace_to_\<phi> t \<Turnstile>SRBB p"
  then show "t \<in> weak_traces p"
  proof(induction t arbitrary: p)
    case Nil
    then show ?case
      using weak_step_sequence.intros(1) by fastforce
  next
    case (Cons a tail)
    hence "(Internal (Obs a (wtrace_to_\<phi> tail))) \<Turnstile>SRBB p"
      by simp
    hence 1: "((hml_srbb_to_hml (Internal (Obs a (wtrace_to_\<phi> tail)))) \<Turnstile> p)"
      by simp
    show ?case
      proof(cases \<open>a = \<tau>\<close>)
        case True
        with 1 have "(hml.Internal (hml.Silent (hml_srbb_to_hml (wtrace_to_\<phi> tail)))) \<Turnstile> p"
          by simp
        then obtain p' p'' where "(p \<Zsurj> p' \<and> (p' \<mapsto> \<tau> p'' \<and> 
((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p'')) \<or> 
(p \<Zsurj> p' \<and> ((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p')))" 
          by fastforce
        then show ?thesis
        proof
          assume assms: "(p \<Zsurj> p') \<and> p' \<mapsto> \<tau> p'' \<and> (hml_srbb_to_hml (wtrace_to_\<phi> tail) \<Turnstile> p'')"
          with Cons have "tail \<in> weak_traces p''"
            using hml_srbb_models.simps by blast
          from assms have "p \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" 
            using weak_step_def LTS_Tau.silent_reachable_trans silent_reachable.intros 
            by metis
          with True \<open>tail \<in> weak_traces p''\<close> show ?thesis 
            using weak_step_sequence.intros(2) by fastforce
        next
          assume assms: "p \<Zsurj> p' \<and> (hml_srbb_to_hml (wtrace_to_\<phi> tail) \<Turnstile> p')"
          show "a # tail \<in> weak_traces p"
          proof-
            from assms Cons have "tail \<in> weak_traces p'" 
              by auto
            from assms have "p \<Zsurj>\<mapsto>\<Zsurj> \<tau> p'"
              using weak_step_def by fastforce
            with \<open>tail \<in> weak_traces p'\<close> have "(\<tau> # tail) \<in> weak_traces p" 
              using weak_step_sequence.intros(2) by fastforce
            with True show "a # tail \<in> weak_traces p" by simp
          qed
        qed
      next
        case False
        with Cons(2) have "wtrace_to_\<phi> ((a # tail)) \<Turnstile>SRBB p"
        using remove_\<tau>_from_wtrace.simps(2)
        by auto
      hence restructure: "(Internal (Obs a (wtrace_to_\<phi> tail))) \<Turnstile>SRBB p" 
        by force
      have "((wtrace_to_\<phi> tail) \<Turnstile>SRBB p )= 
((hml_srbb_to_hml (wtrace_to_\<phi> tail)) \<Turnstile> p)"
        by simp
        with Cons(2) restructure obtain p' p'' where 
"p \<Zsurj> p'" "p' \<mapsto> a p''" "((hml_srbb_to_hml (wtrace_to_\<phi> tail))) \<Turnstile> p''" 
          using False by auto
from this(1, 2) have "p \<Zsurj>\<mapsto>\<Zsurj> a p''" unfolding weak_step_def using silent_reachable.intros 
      by (metis silent_reachable_trans)
    from \<open>((hml_srbb_to_hml (wtrace_to_\<phi> tail))) \<Turnstile> p''\<close> 
    have "wtrace_to_\<phi> tail \<Turnstile>SRBB p''"
      by simp
    with \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> show "(a#tail) \<in> weak_traces p" 
      using weak_step_sequence.intros(2) 
      using Cons.IH by fastforce
  qed
qed
qed

lemma aux:
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<chi> :: "('a, 's) hml_srbb_conjunction"
  fixes \<psi> :: "('a, 's) hml_srbb_conjunct"
  assumes "p \<lesssim>WT q"
  shows "(is_trace_formula \<phi> \<Longrightarrow> (\<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q))"
proof
  assume \<phi>_trace: "is_trace_formula \<phi>" and p_sat_\<phi>: "\<phi> \<Turnstile>SRBB p"
  show "\<phi> \<Turnstile>SRBB q"
  proof-
    from assms have p_trace_implies_q_trace: "\<forall>tr p'. (p \<Zsurj>\<mapsto>\<Zsurj>$ tr p') \<longrightarrow> (\<exists>q'. q \<Zsurj>\<mapsto>\<Zsurj>$ tr q')" 
      unfolding weakly_trace_preordered_def by auto
    from p_sat_\<phi> trace_formula_implies_trace obtain tr p' where 
      "(p \<Zsurj>\<mapsto>\<Zsurj>$ tr p')" "wtrace_to_\<phi> tr = \<phi>"
      using \<phi>_trace by blast
    with p_trace_implies_q_trace obtain q' where "q \<Zsurj>\<mapsto>\<Zsurj>$ tr q'" 
      by blast
    with trace_equals_trace_to_formula show ?thesis 
      using \<open>wtrace_to_\<phi> tr = \<phi>\<close> by blast
  qed
qed

lemma "(p \<lesssim>WT q) = (p \<preceq> (E \<infinity> 0 0 0 0 0 0 0) q)"
  unfolding expr_preord_def hml_preordered_def
proof
  assume assm: "p \<lesssim>WT q"
  show "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). \<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q"
    using assm aux expressiveness_to_trace_formula weakly_trace_preordered_def
    by blast+
next
  assume \<phi>_eneg: "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). \<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q"
  show "p \<lesssim>WT q"
    unfolding weakly_trace_preordered_def
    using \<phi>_eneg trace_equals_trace_to_formula trace_formula_to_expressiveness trace_to_\<phi>_is_trace_formula
    by (simp, blast+)
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