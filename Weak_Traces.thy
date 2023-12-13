theory Weak_Traces
  imports Main HML_SRBB Expressiveness_Price
begin

inductive
      is_trace_formula :: "('act, 'i) hml_srbb \<Rightarrow> bool"
  and is_trace_formula_conjunction :: "('act, 'i) hml_srbb_conjunction \<Rightarrow> bool" where
  "is_trace_formula TT" |
  "is_trace_formula (Internal \<chi>)" if "is_trace_formula_conjunction \<chi>" |
  "is_trace_formula_conjunction (Obs \<alpha> \<phi>)" if "is_trace_formula \<phi>"

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

lemma
  fixes \<phi> :: "('a, 's) hml_srbb"
  fixes \<chi> :: "('a, 's) hml_srbb_conjunction"
  fixes \<psi> :: "('a, 's) hml_srbb_conjunct"
  shows "(is_trace_formula \<phi> \<longrightarrow> (\<phi> \<Turnstile>SRBB p \<longrightarrow> \<phi> \<Turnstile>SRBB q))
      \<and> (is_trace_formula_conjunction \<chi> \<longrightarrow> (hml_srbb_conjunction_models \<chi> p \<longrightarrow> hml_srbb_conjunction_models \<chi> q))
      \<and> (\<lambda>x. True) \<psi>"
  sorry

lemma "(p \<lesssim>WT q) = (p \<preceq> (E \<infinity> 0 0 0 0 0 0 0) q)"
  sorry

end

end