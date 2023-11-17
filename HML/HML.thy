theory HML
  imports Main "HOL-Library.Countable_Set_Type" "../LTS"
begin

datatype 
  'act hml =
    Obs 'act "'act hml" |
    Silent "'act hml" |
    Internal "'act hml" |
    Conj "'act hml_conjunct cset"
and
  'act hml_conjunct =
    Pos "'act hml" |
    Neg "'act hml"

abbreviation "TT \<equiv> Conj cempty"

context LTS_Tau
begin

function
      hml_models     :: "'a hml          \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
  and hml_neg_models :: "'a hml_conjunct \<Rightarrow> 's \<Rightarrow> bool"
where
  "((Obs a \<phi>)    \<Turnstile> p) = (\<exists>p'. p \<mapsto> a p' \<and> (\<phi> \<Turnstile> p'))" |
  "((Silent \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<Zsurj> p' \<and> (\<phi> \<Turnstile> p'))" |
  "((Internal \<phi>) \<Turnstile> p) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (\<phi> \<Turnstile> p')) \<or> (\<phi> \<Turnstile> p))" |
  "((Conj \<psi>s)    \<Turnstile> p) = (\<forall>\<psi>. cin \<psi> \<psi>s \<longrightarrow> (hml_neg_models \<psi> p))" |

  "(hml_neg_models (Pos \<phi>) p) = (\<phi> \<Turnstile> p)" |
  "(hml_neg_models (Neg \<phi>) p) = (\<not>(\<phi> \<Turnstile> p))"
  by (metis hml.exhaust hml_conjunct.exhaust sumE surj_pair, auto)

inductive_set hml_models_wf_arg_space :: "('a hml \<times> 's, 'a hml_conjunct \<times> 's) sum rel" where
                "(Inl (\<phi>, x), Inl (Obs    a \<phi>, p)) \<in> hml_models_wf_arg_space" |
                "(Inl (\<phi>, x), Inl (Silent   \<phi>, p)) \<in> hml_models_wf_arg_space" |
                "(Inl (\<phi>, x), Inl (Internal \<phi>, p)) \<in> hml_models_wf_arg_space" |
  "cin \<psi> \<psi>s \<Longrightarrow> (Inr (\<psi>, p), Inl (Conj    \<psi>s, p)) \<in> hml_models_wf_arg_space" |
                "(Inl (\<phi>, p), Inr (Pos      \<phi>, p)) \<in> hml_models_wf_arg_space" |
                "(Inl (\<phi>, p), Inr (Neg      \<phi>, p)) \<in> hml_models_wf_arg_space"

lemma wf_hml_models_wf_arg_space: "wf hml_models_wf_arg_space"
  unfolding wf_def
proof safe
  fix P \<phi>sOr\<psi>s
  assume "\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x"

  then show "P \<phi>sOr\<psi>s"
  proof (induct \<phi>sOr\<psi>s)
    fix \<phi>s :: "'a hml \<times> 's"
    obtain \<phi> and sl where "\<phi>s = (\<phi>, sl)" by fastforce

    fix \<psi>s :: "'a hml_conjunct \<times> 's"
    obtain \<psi> and sr where "\<psi>s = (\<psi>, sr)" by fastforce

    show "P (Inl \<phi>s)" and "P (Inr \<psi>s)"
      unfolding \<open>\<phi>s = (\<phi>, sl)\<close> and \<open>\<psi>s = (\<psi>, sr)\<close>
      using \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close>
    proof (induct \<phi> and \<psi> arbitrary: sl and sr)
      case (Obs x1 x2)
      then show ?case
        by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml.distinct(1) hml.distinct(3) hml.distinct(5) hml.inject(1) hml_models_wf_arg_space.cases)
    next
      case (Silent x)
      then show ?case
        by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml.distinct(1) hml.distinct(7) hml.distinct(9) hml.inject(2) hml_models_wf_arg_space.cases)
    next
      case (Internal x)
      then show ?case
        by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml.distinct(11) hml.distinct(3) hml.distinct(7) hml.inject(3) hml_models_wf_arg_space.cases)
    next
      case (Conj x)
      then show ?case
        by (smt (verit) Inl_inject Inr_not_Inl Pair_inject hml.distinct(11) hml.distinct(5) hml.distinct(9) hml.inject(4) hml_models_wf_arg_space.cases cin.rep_eq)
    next
      case (Pos x)
      then show ?case
        by (smt (verit) Inr_inject Inr_not_Inl Pair_inject hml_conjunct.distinct(1) hml_conjunct.inject(1) hml_models_wf_arg_space.cases)
    next
      case (Neg x)
      then show ?case
        by (smt (verit) Inr_inject Inr_not_Inl Pair_inject hml_conjunct.distinct(1) hml_conjunct.inject(2) hml_models_wf_arg_space.cases)
    qed
  qed
qed

termination
  using wf_hml_models_wf_arg_space
  by (standard) (simp add: hml_models_wf_arg_space.intros)+

lemma TT_admits_all_states:
  fixes p::'s
  shows "TT \<Turnstile> p"
  by simp

end

end
