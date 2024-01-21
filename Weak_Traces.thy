theory Weak_Traces
  imports Main HML_SRBB Expressiveness_Price
begin

inductive
      is_trace_formula :: "('act, 'i) hml_srbb \<Rightarrow> bool"
  and is_trace_formula_inner :: "('act, 'i) hml_srbb_inner \<Rightarrow> bool" where
  "is_trace_formula TT" |
  "is_trace_formula (Internal \<chi>)" if "is_trace_formula_inner \<chi>" |
  "is_trace_formula (ImmConj I \<psi>s)" if "I = {}" |

  "is_trace_formula_inner (Obs \<alpha> \<phi>)" if "is_trace_formula \<phi>" |
  "is_trace_formula_inner (Conj I \<psi>s)" if "I = {}" |
  "is_trace_formula_inner (BranchConj \<alpha> \<phi> I \<psi>s)" if "I = {}" and "is_trace_formula \<phi>"


fun wtrace_to_srbb :: "'act list \<Rightarrow> ('act, 'i) hml_srbb"
  and wtrace_to_inner :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_inner"
  and wtrace_to_conjunct :: "'act list \<Rightarrow> ('act, 'i) hml_srbb_conjunct" where
  "wtrace_to_srbb [] = TT" |
  "wtrace_to_srbb tr = (Internal (wtrace_to_inner tr))" |

  "wtrace_to_inner [] = (Conj {} (\<lambda>_. undefined))" | \<comment> \<open> Should never happen\<close>
  "wtrace_to_inner (\<alpha> # tr) = (Obs \<alpha> (wtrace_to_srbb tr))" |

  "wtrace_to_conjunct tr = Pos (wtrace_to_inner tr)" \<comment> \<open>Should never happen\<close>

lemma trace_to_srbb_is_trace_formula:
  "is_trace_formula (wtrace_to_srbb trace)"
  apply (induct trace)
  using is_trace_formula_is_trace_formula_inner.intros
    and is_trace_formula.simps
    and is_trace_formula_is_trace_formula_inner.intros(4)
    and wtrace_to_inner.simps(2)
    and wtrace_to_srbb.simps(2)
  by fastforce+

lemma trace_formula_to_expressiveness:
  fixes \<phi> :: "('act, 'i) hml_srbb"
  fixes \<chi> :: "('act, 'i) hml_srbb_inner"
  shows  "(is_trace_formula \<phi>       \<longrightarrow> (\<phi> \<in> \<O>       (E \<infinity> 0 0 0 0 0 0 0)))
        \<and> (is_trace_formula_inner \<chi> \<longrightarrow> (\<chi> \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)))"
  apply (rule is_trace_formula_is_trace_formula_inner.induct)
  by (simp add: Sup_enat_def \<O>_def \<O>_inner_def leq_not_eneg)+


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
  then show ?case apply (simp add: \<O>_def leq_not_eneg)
  using \<O>_def leq_not_eneg is_trace_formula_is_trace_formula_inner.intros(3) by blast
next
  case (Obs x1 x2)
  then show ?case by (simp add: \<O>_def \<O>_inner_def is_trace_formula_is_trace_formula_inner.intros(4) leq_not_eneg)
next
  case (Conj I \<psi>s)
  show ?case
  proof (rule impI)
    assume "Conj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)"
    hence "I = {}" 
      by (metis \<O>_inner_def add_eq_0_iff_both_eq_0 bot.extremum_uniqueI bot_enat_def energy.distinct(1) energy.sel(3) expr_pr_inner.simps inst_conj_depth_inner.simps(2) leq_not_eneg mem_Collect_eq zero_one_enat_neq(2))
    then show "is_trace_formula_inner (Conj I \<psi>s)" 
      by (simp add: is_trace_formula_is_trace_formula_inner.intros(5))
  qed
next
  case (StableConj I \<psi>s)
  show ?case
  proof (rule impI)
    assume "StableConj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)"
    have "StableConj I \<psi>s \<notin> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)" 
      by (simp add: \<O>_inner_def leq_not_eneg)
    with \<open>StableConj I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)\<close>
    show "is_trace_formula_inner (StableConj I \<psi>s)" by contradiction
  qed
next
  case (BranchConj \<alpha> \<phi> I \<psi>s)
  show ?case
  proof (rule impI)
    assume "BranchConj \<alpha> \<phi> I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)"
    hence "I = {}" 
      by (metis \<O>_inner_def add_eq_0_iff_both_eq_0 bot.extremum_uniqueI bot_enat_def branch_conj_depth_inner.simps(4) energy.distinct(1) energy.sel(2) expr_pr_inner.simps leq_not_eneg mem_Collect_eq zero_one_enat_neq(2))
    from \<open>BranchConj \<alpha> \<phi> I \<psi>s \<in> \<O>_inner (E \<infinity> 0 0 0 0 0 0 0)\<close>
    have "expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) \<le> E \<infinity> 0 0 0 0 0 0 0" unfolding \<O>_inner_def by auto
    with \<open>I = {}\<close>
    have "expressiveness_price \<phi> \<le> E \<infinity> 0 0 0 0 0 0 0" unfolding expr_pr_inner.simps 
      by (smt (verit) bot.extremum_uniqueI bot_enat_def branch_conj_depth_inner.simps(4) ccpo_Sup_singleton enat_ord_simps(6) energy.distinct(1) energy.sel(1) energy.sel(2) energy.sel(3) energy.sel(4) energy.sel(5) energy.sel(6) energy.sel(7) energy.sel(8) expressiveness_price.elims image_empty imm_conj_depth_inner.simps(4) insert_is_Un inst_conj_depth_inner.simps(4) leq_not_eneg less_numeral_extra(3) max_neg_conj_depth_inner.simps(4) max_pos_conj_depth_inner.simps(4) neg_depth_inner.simps(4) somwhere_larger_eq st_conj_depth_inner.simps(4))
    then have "\<phi> \<in> \<O> (E \<infinity> 0 0 0 0 0 0 0)" unfolding \<O>_def by auto
    with \<open>I = {}\<close>
    show "is_trace_formula_inner (BranchConj \<alpha> \<phi> I \<psi>s)" 
      by (simp add: BranchConj.hyps(1) is_trace_formula_is_trace_formula_inner.intros(6))
  qed
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

lemma trace_formula_implies_trace:
  fixes \<psi> ::"('a, 's) hml_srbb_conjunct"
  shows
       trace_case: "is_trace_formula \<phi> \<Longrightarrow> p \<Turnstile>SRBB \<phi> \<Longrightarrow> (\<exists>tr \<in> weak_traces p. wtrace_to_srbb tr = \<phi>)"
    and conj_case: "is_trace_formula_inner \<chi> \<Longrightarrow> hml_srbb_inner_models \<chi> q \<Longrightarrow> (\<exists>tr \<in> weak_traces q. wtrace_to_inner tr = \<chi>)"
    and            True
    apply (induction \<phi> and \<chi> and \<psi> arbitrary: p and q)
  oops
  (*using weak_step_sequence.intros(1) apply fastforce
  prefer 2 using is_trace_formula.cases apply blast
  prefer 3 prefer 4 prefer 6 prefer 7
  using is_trace_formula_inner.cases apply blast+
  prefer 3 apply (simp add: is_trace_formula_inner.simps)
proof-
  case (Internal \<chi>r)
  assume IH: "(\<And>q. is_trace_formula_inner \<chi>r \<Longrightarrow>
                 hml_srbb_inner_models \<chi>r q \<Longrightarrow> \<exists>tr\<in>weak_traces q. wtrace_to_inner tr = \<chi>r)"
and is_trace_internal :"is_trace_formula (hml_srbb.Internal \<chi>r)"
and internal_satisfied: "p \<Turnstile>SRBB hml_srbb.Internal \<chi>r"
  from Internal(3) obtain p' where wtrace_to_p': "p \<Zsurj> p'" and p'_models_innerr: "hml_srbb_inner_models \<chi>r p'" 
    by auto
  from Internal(2) have "is_trace_formula_inner \<chi>r"
    using is_trace_formula.cases by auto
  with p'_models_innerr IH obtain tail p'' where tail_in_traces_p': "tail \<in> weak_traces p'" "wtrace_to_inner tail = \<chi>r" "p' \<Zsurj>\<mapsto>\<Zsurj>$ tail p''"
    by blast
  then show ?case
  proof(cases tail)
    case Nil
    hence False
      using \<open>is_trace_formula_inner \<chi>r\<close> is_trace_formula_inner.simps tail_in_traces_p'(2) by force
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
  case (Obs \<alpha> \<phi>r)
  assume IH: "(\<And>p. is_trace_formula \<phi>r \<Longrightarrow> p \<Turnstile>SRBB \<phi>r \<Longrightarrow> \<exists>tr\<in>weak_traces p. wtrace_to_srbb tr = \<phi>r)"
and obs_is_trace:"is_trace_formula_inner (hml_srbb_inner.Obs \<alpha> \<phi>r)"
and obs_models_q: "hml_srbb_inner_models (hml_srbb_inner.Obs \<alpha> \<phi>r) q"
  from obs_is_trace have \<phi>r_is_trace: "is_trace_formula \<phi>r"
    using is_trace_formula_inner.cases by auto
  from obs_models_q have hml_models: "q \<Turnstile> hml_srbb_inner_to_hml (Obs \<alpha> \<phi>r)"
    by simp
  then show ?case
  proof(cases \<open>\<alpha> = \<tau>\<close>)
    case True
    with hml_models have "q \<Turnstile> hml.Silent (hml_srbb_to_hml \<phi>r)" 
      using hml_srbb_inner_to_hml.simps 
      by force
    then obtain q' where "(q \<mapsto> \<tau> q' \<and> (q' \<Turnstile>SRBB \<phi>r)) \<or> (q \<Turnstile>SRBB \<phi>r)"
      using hml_models.simps(4)
      by fastforce
    then show ?thesis 
    proof
      assume assm: "q \<mapsto> \<tau> q' \<and> q' \<Turnstile>SRBB \<phi>r"
      with IH \<phi>r_is_trace  obtain tail where "tail\<in>weak_traces q'" "wtrace_to_srbb tail = \<phi>r"
        by blast
      with assm show ?thesis
        using LTS_Tau.weak_step_sequence.intros(2) True silent_reachable.intros weak_step_def 
        by fastforce
    next
      assume "q \<Turnstile>SRBB \<phi>r"
      with IH \<phi>r_is_trace show ?thesis 
        using LTS_Tau.weak_step_sequence.intros(2) True silent_reachable.intros(1) weak_step_def 
        by fastforce
    qed
  next
    case False
    hence "q \<Turnstile> hml.Obs \<alpha> (hml_srbb_to_hml \<phi>r)" 
      using hml_srbb_inner_to_hml.simps hml_models by presburger
    then obtain q' where \<alpha>_step: "q \<mapsto> \<alpha> q'" and \<phi>r_models_q': "q' \<Turnstile>SRBB \<phi>r"
      by auto
    with IH \<phi>r_is_trace obtain tail where tail_in_wt_q': "tail \<in>weak_traces q'" "wtrace_to_srbb tail = \<phi>r"
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
qed *)

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
    hence IS_2: "p'' \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail))" by simp
    from Cons have goal_eq: "wtrace_to_srbb (a # tail) = (Internal (Obs a (wtrace_to_srbb tail)))"
      by simp
    show ?case
    proof(cases \<open>a = \<tau>\<close>)
      case True
      with goal_eq have "p \<Turnstile>SRBB (wtrace_to_srbb (a # tail)) = 
(p \<Turnstile> hml.Internal (hml.Silent (hml_srbb_to_hml (wtrace_to_srbb tail))))"
        by force
      also have "... = 
(\<exists>p'. p \<Zsurj> p' \<and> (((\<exists>p''. p' \<mapsto> \<tau> p'' \<and> (p'' \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail)))) \<or> 
(p' \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail))))))"
        by force
      with \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> True IS_2 show ?thesis 
        using weak_step_def by auto
    next
      case False
      hence "wtrace_to_srbb (a#tail) = 
(Internal (Obs a (wtrace_to_srbb tail)))"
        by simp
      hence converted_srbb_sat:  "(p \<Turnstile>SRBB wtrace_to_srbb (a # tail)) =
(\<exists>p'. p \<Zsurj> p' \<and> ((\<exists>p''. p' \<mapsto> a p'' \<and> p'' \<Turnstile>SRBB wtrace_to_srbb tail)))"
        by (simp add: False)
      with IS_2 False \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> show ?thesis 
        by (smt (verit, best) LTS_Tau.hml_models.simps(1) LTS_Tau.hml_models.simps(3) 
LTS_Tau.silent_reachable_trans hml_srbb_models.elims(3) hml_srbb_to_hml.simps(1) 
hml_srbb_to_hml.simps(2) weak_step_def wtrace_to_srbb.elims) 
    qed
  qed
next
  assume "p \<Turnstile>SRBB wtrace_to_srbb t"
  then show "t \<in> weak_traces p"
  proof(induction t arbitrary: p)
    case Nil
    then show ?case
      using weak_step_sequence.intros(1) by fastforce
  next
    case (Cons a tail)
    hence "p \<Turnstile>SRBB (Internal (Obs a (wtrace_to_srbb tail)))"
      by simp
    hence 1: "p \<Turnstile> (hml_srbb_to_hml (Internal (Obs a (wtrace_to_srbb tail))))"
      by simp
    show ?case
      proof(cases \<open>a = \<tau>\<close>)
        case True
        with 1 have "p \<Turnstile> (hml.Internal (hml.Silent (hml_srbb_to_hml (wtrace_to_srbb tail))))"
          by simp
        then obtain p' p'' where "(p \<Zsurj> p' \<and> (p' \<mapsto> \<tau> p'' \<and> 
(p'' \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail)))) \<or> 
(p \<Zsurj> p' \<and> (p' \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail)))))" 
          by fastforce
        then show ?thesis
        proof
          assume assms: "(p \<Zsurj> p') \<and> p' \<mapsto> \<tau> p'' \<and> (p'' \<Turnstile> hml_srbb_to_hml (wtrace_to_srbb tail))"
          with Cons have "tail \<in> weak_traces p''"
            using hml_srbb_models.simps by blast
          from assms have "p \<Zsurj>\<mapsto>\<Zsurj> \<tau> p''" 
            using weak_step_def LTS_Tau.silent_reachable_trans silent_reachable.intros 
            by metis
          with True \<open>tail \<in> weak_traces p''\<close> show ?thesis 
            using weak_step_sequence.intros(2) by fastforce
        next
          assume assms: "p \<Zsurj> p' \<and> (p' \<Turnstile> hml_srbb_to_hml (wtrace_to_srbb tail))"
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
        with Cons(2) have "p \<Turnstile>SRBB wtrace_to_srbb ((a # tail))"
        by auto
      hence restructure: "p \<Turnstile>SRBB (Internal (Obs a (wtrace_to_srbb tail)))" 
        by force
      have "(p \<Turnstile>SRBB (wtrace_to_srbb tail))= 
(p \<Turnstile> (hml_srbb_to_hml (wtrace_to_srbb tail)))"
        by simp
        with Cons(2) restructure obtain p' p'' where 
"p \<Zsurj> p'" "p' \<mapsto> a p''" "p'' \<Turnstile> ((hml_srbb_to_hml (wtrace_to_srbb tail)))" 
          using False by auto
from this(1, 2) have "p \<Zsurj>\<mapsto>\<Zsurj> a p''" unfolding weak_step_def using silent_reachable.intros 
      by (metis silent_reachable_trans)
    from \<open>p'' \<Turnstile> ((hml_srbb_to_hml (wtrace_to_srbb tail)))\<close> 
    have "p'' \<Turnstile>SRBB wtrace_to_srbb tail"
      by simp
    with \<open>p \<Zsurj>\<mapsto>\<Zsurj> a p''\<close> show "(a#tail) \<in> weak_traces p" 
      using weak_step_sequence.intros(2) 
      using Cons.IH by fastforce
  qed
qed
qed

lemma aux:
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<chi> :: "('a, 's) hml_srbb_inner"
  fixes \<psi> :: "('a, 's) hml_srbb_conjunct"
  shows "p \<lesssim>WT q \<Longrightarrow> is_trace_formula \<phi> \<Longrightarrow> p \<Turnstile>SRBB \<phi> \<Longrightarrow> q \<Turnstile>SRBB \<phi>"
  oops
(*proof -
  assume \<phi>_trace: "is_trace_formula \<phi>" and p_sat_srbb: "p \<Turnstile>SRBB \<phi>" and assms: "p \<lesssim>WT q"
  show "q \<Turnstile>SRBB \<phi>"
  proof-
    from assms have p_trace_implies_q_trace: "\<forall>tr p'. (p \<Zsurj>\<mapsto>\<Zsurj>$ tr p') \<longrightarrow> (\<exists>q'. q \<Zsurj>\<mapsto>\<Zsurj>$ tr q')" 
      unfolding weakly_trace_preordered_def by auto
    from p_sat_srbb trace_formula_implies_trace obtain tr p' where 
      "(p \<Zsurj>\<mapsto>\<Zsurj>$ tr p')" "wtrace_to_srbb tr = \<phi>"
      using \<phi>_trace by blast
    with p_trace_implies_q_trace obtain q' where "q \<Zsurj>\<mapsto>\<Zsurj>$ tr q'" 
      by blast
    with trace_equals_trace_to_formula show ?thesis 
      using \<open>wtrace_to_srbb tr = \<phi>\<close> by blast
  qed
qed *)

lemma expr_preorder_characterizes_relational_preorder_traces: "(p \<lesssim>WT q) = (p \<preceq> (E \<infinity> 0 0 0 0 0 0 0) q)"
  unfolding expr_preord_def hml_preordered_def
proof
  assume "p \<lesssim>WT q"
  then show "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"
    oops
    (* using aux expressiveness_to_trace_formula weakly_trace_preordered_def
    by blast+ 
next
  assume \<phi>_eneg: "\<forall>\<phi>\<in>\<O> (E \<infinity> 0 0 0 0 0 0 0). p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>"
  show "p \<lesssim>WT q"
    unfolding weakly_trace_preordered_def
    using \<phi>_eneg trace_equals_trace_to_formula trace_formula_to_expressiveness trace_to_srbb_is_trace_formula
    by (simp, blast+)
qed *)

lemma "(p \<simeq>WT q) = (p \<sim> (E \<infinity> 0 0 0 0 0 0 0) q)"
  unfolding weakly_trace_equivalent_def expr_equiv_def \<O>_def hml_equivalent_def hml_preordered_def
  oops
  (* using expr_preorder_characterizes_relational_preorder_traces
  by (simp add: \<O>_def expr_preord_def hml_preordered_def) *)
end

end