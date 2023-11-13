theory Hennessy_Milner_Logic
imports Behavioral_Equivalences
begin

datatype ('a, 'i) hml_formula =
HML_true
| HML_conj \<open>'i set\<close> \<open>'i \<Rightarrow> ('a,'i) hml_psi\<close>  (\<open>AND _ _\<close>)
| HML_poss \<open>'a\<close> \<open>('a,'i) hml_formula\<close>            (\<open>\<langle>_\<rangle>_\<close> [60] 60)
| HML_tau \<open>('a, 'i) hml_formula\<close>
| HML_eps \<open>('a, 'i) hml_formula\<close>

and ('a, 'i) hml_psi = 
HML_neg \<open>('a,'i) hml_formula\<close>                  (\<open>~_\<close> [20] 60)
| HML_phi \<open>('a, 'i) hml_formula\<close>

context lts_tau
begin

function satisfies :: \<open>'s \<Rightarrow> ('a,'s) hml_formula \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<close> 50) 
and psi_sat :: \<open>'s \<Rightarrow> ('a,'s) hml_psi \<Rightarrow> bool\<close> (infix \<open>\<TTurnstile>\<close> 50)
where
\<open>(_ \<Turnstile> HML_true) = True\<close> |
  \<open>(p \<Turnstile> \<langle>\<alpha>\<rangle>\<phi>) = (\<exists>p'. p \<mapsto> \<alpha> p' \<and> p' \<Turnstile> \<phi>)\<close>|
  \<open>(p \<Turnstile> AND I \<Phi>) = (\<forall>i \<in> I. p \<TTurnstile> (\<Phi> i))\<close> |
\<open>p \<Turnstile> HML_tau \<phi> = (\<exists>p'. p \<mapsto> \<tau> p' \<and> p' \<Turnstile> \<phi>)\<close> |
\<open>p \<Turnstile> HML_eps \<phi> = (\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> \<phi>)\<close> |
\<open>psi_sat p (HML_neg \<phi>) = (\<not> (p \<Turnstile> \<phi>))\<close> |
\<open>psi_sat p (HML_phi \<phi>) = (p \<Turnstile> \<phi>)\<close>
  using hml_formula.exhaust hml_psi.exhaust
  by (metis sumE surj_pair, blast+)

inductive_set wf_rel_formula :: "(('s \<times> ('a, 's) hml_formula) + ('s \<times> ('a, 's) hml_psi)) rel" where
"(Inl (p, \<phi>), Inl (p', HML_poss \<alpha> \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_tau \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inl (p', HML_eps \<phi>)) \<in> wf_rel_formula" |
"\<phi> = \<Phi> i \<and> i \<in> I \<Longrightarrow> (Inr (p, \<phi>), Inl (p, HML_conj I \<Phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_neg \<phi>)) \<in> wf_rel_formula" |
"(Inl (p, \<phi>), Inr (p, HML_phi \<phi>)) \<in> wf_rel_formula" 

lemma wf_rel_formula_wf: "wf wf_rel_formula"
  unfolding wf_def
proof safe
  fix P p x
  assume  A1 :"\<forall>x. (\<forall>y. (y, x) \<in> wf_rel_formula \<longrightarrow> P y) \<longrightarrow> P x"
  then show "P x"
  proof(cases x)
    case (Inl a)
    then obtain p \<phi> where "x = Inl (p, \<phi>)"
      by fastforce
    then have "P x = P (Inl (p, \<phi>))" by simp
    from A1 have A2:
"\<forall>p \<phi>. (\<forall>p' \<phi>'.
(Inl (p',\<phi>'), Inl (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inl (p', \<phi>'))) \<and> 
(\<forall>p' \<phi>'. (Inr (p',\<phi>'), Inl (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inr (p', \<phi>'))) 
\<longrightarrow> P (Inl (p, \<phi>))"
    using surj_pair
    by (metis obj_sumE)
  from A1 have A3:
"\<forall>p \<phi>. (\<forall>p' \<phi>'.
(Inl (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inl (p', \<phi>'))) \<and> 
(\<forall>p' \<phi>'. (Inr (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inr (p', \<phi>'))) 
\<longrightarrow> P (Inr (p, \<phi>))"
    using surj_pair
    by (metis obj_sumE)
  with A2 have "P (Inl (p, \<phi>))"
  proof(induct \<phi> arbitrary: p)
    case HML_true
    with wf_rel_formula.cases have "P (Inl (p, HML_true))" 
      by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml_formula.distinct(1) hml_formula.distinct(3) hml_formula.distinct(5) hml_formula.distinct(7))
    with HML_true(1) show ?case by simp
  next
    case (HML_conj x1 x2)
    then show ?case sorry
  next
    case (HML_poss \<alpha> \<psi>)
    with wf_rel_formula.cases hml_formula.distinct(4, 10, 15, 17) hml_formula.inject range_eqI
    show "P (Inl (p, HML_poss \<alpha> \<psi>))" 
      by (smt (verit) Inr_not_Inl snd_conv sum.sel(1))
  next
    case (HML_tau \<phi>)
    with wf_rel_formula.cases hml_formula.distinct hml_formula.inject show ?case
      by (smt (verit) Inl_inject Inr_not_Inl Pair_inject)
  next
    case (HML_eps \<phi>)
    with wf_rel_formula.cases hml_formula.distinct hml_formula.inject show ?case 
      by (smt (verit) Inl_inject Inr_not_Inl Pair_inject)
  next
    case (HML_neg \<psi>)
    with wf_rel_formula.cases hml_psi.distinct hml_psi.inject
    show ?thesis sorry
  next
    case (HML_phi \<psi>)
    then show ?thesis sorry
  qed
  next
    case (Inr b)
    from A1 have A3:"\<forall>p \<phi>. (\<forall>p' \<phi>'.(Inl (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inl (p', \<phi>'))) \<and> (\<forall>p' \<phi>'. (Inr (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inr (p', \<phi>'))) \<longrightarrow> P (Inr (p, \<phi>))"
    using surj_pair
    by (metis obj_sumE)
    then show ?thesis sorry
  qed
(*TODO: cases von assume betrachten, je nachdem ob x und y mit Inl/Inr constructed sind.*)
  hence A2 :"\<forall>p \<phi>. (\<forall>p' \<phi>'.(Inl (p',\<phi>'), Inl (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inl (p', \<phi>'))) \<and> (\<forall>p' \<phi>'. (Inr (p',\<phi>'), Inl (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inr (p', \<phi>'))) \<longrightarrow> P (Inl (p, \<phi>))"
    using surj_pair
    by (metis obj_sumE)
  from A1 have A3:"\<forall>p \<phi>. (\<forall>p' \<phi>'.(Inl (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inl (p', \<phi>'))) \<and> (\<forall>p' \<phi>'. (Inr (p',\<phi>'), Inr (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (Inr (p', \<phi>'))) \<longrightarrow> P (Inr (p, \<phi>))"
    using surj_pair
    by (metis obj_sumE)
  from A2 have A2: "P (Inl (p, \<phi>))" sorry
  from A3 have A3: "P (Inr (q, \<psi>))" sorry
  from A2 A3 show ?thesis
hence "\<forall>p \<phi>. (\<forall>p' \<phi>'. ((p',\<phi>'), (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (case_sum (\<lambda>(p', \<phi>'). P (p', \<phi>')) (\<lambda>(p', \<phi>'). P (p', \<phi>')) (Inl (p', \<phi>')))) \<longrightarrow>
                 P (case_sum (\<lambda>(p', \<phi>'). P (p', \<phi>')) (\<lambda>(p', \<phi>'). P (p', \<phi>')) (Inl (p, \<phi>)))"
  hence "\<forall>p \<phi>. (\<forall>p' \<phi>'. ((p',\<phi>'), (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (case_sum (\<lambda>(p', \<phi>'). P (p', \<phi>')) (\<lambda>(p', \<phi>'). P (p', \<phi>')) (Inl (p, \<phi>')))) \<longrightarrow> P (case_sum (\<lambda>(p', \<phi>'). P (p', \<phi>')) (\<lambda>(p', \<phi>'). P (p', \<phi>')) (Inl (p, \<phi>)))"
  hence "\<forall>p \<phi>. (\<forall>p' \<phi>'. ((p',\<phi>'), (p,\<phi>)) \<in> wf_rel_formula \<longrightarrow> P (p',\<phi>')) \<longrightarrow> P (p, \<phi>)"
  sorry
qed

termination
  using wf_rel_formula_wf wf_rel_formula.intros
  by (simp add: "termination")

end
end