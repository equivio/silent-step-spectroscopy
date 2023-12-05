theory HML
  imports Main "./LTS"
begin

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


context Inhabited_LTS
begin

abbreviation HML_and :: "('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml_conjunct \<Rightarrow> ('a, 's) hml" ("_ \<and>hml _" 70) where
  "HML_and left right \<equiv> Conj {l, r} (\<lambda>i. if i = l
                                          then left
                                          else if i = r
                                               then right
                                               else Pos TT)"

end (* context Inhabited_LTS *)


context LTS_Tau
begin

abbreviation HML_soft_poss :: "'a \<Rightarrow> ('a, 'i) hml \<Rightarrow> ('a, 'i) hml" where
  "HML_soft_poss \<alpha> \<phi> \<equiv> if \<alpha> = \<tau> then Silent \<phi> else Obs \<alpha> \<phi>"

function
      hml_models          :: "('a, 's) hml     \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
  and hml_conjunct_models :: "('a, 's) hml_conjunct \<Rightarrow> 's \<Rightarrow> bool"
where
  "(TT           \<Turnstile> _) = True" |
  "((Obs a \<phi>)    \<Turnstile> p) = (\<exists>p'. p \<mapsto> a p' \<and> (\<phi> \<Turnstile> p'))" |
  "((Internal \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<Zsurj> p' \<and> (\<phi> \<Turnstile> p'))" |
  "((Silent \<phi>) \<Turnstile> p) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (\<phi> \<Turnstile> p')) \<or> (\<phi> \<Turnstile> p))" |
  "((Conj I \<psi>s)  \<Turnstile> p) = (\<forall>i \<in> I. hml_conjunct_models (\<psi>s i) p)" |

  "(hml_conjunct_models (Pos \<phi>) p) = (\<phi> \<Turnstile> p)" |
  "(hml_conjunct_models (Neg \<phi>) p) = (\<not>(\<phi> \<Turnstile> p))"
  by (metis hml.exhaust hml_conjunct.exhaust sumE surj_pair, auto)
            
inductive_set hml_models_wf_arg_space :: "(('a, 's) hml \<times> 's, ('a, 's) hml_conjunct \<times> 's) sum rel" where
                          "(Inl (\<phi>, x), Inl (Obs    a \<phi>, p)) \<in> hml_models_wf_arg_space" |
                          "(Inl (\<phi>, x), Inl (Silent   \<phi>, p)) \<in> hml_models_wf_arg_space" |
                          "(Inl (\<phi>, x), Inl (Internal \<phi>, p)) \<in> hml_models_wf_arg_space" |
  "i \<in> I \<Longrightarrow> \<psi> = \<psi>s i \<Longrightarrow> (Inr (\<psi>, p), Inl (Conj  I \<psi>s, p)) \<in> hml_models_wf_arg_space" |
                          "(Inl (\<phi>, p), Inr (Pos      \<phi>, p)) \<in> hml_models_wf_arg_space" |
                          "(Inl (\<phi>, p), Inr (Neg      \<phi>, p)) \<in> hml_models_wf_arg_space"

lemma wf_hml_models_wf_arg_space: "wf hml_models_wf_arg_space"
  unfolding wf_def
proof safe
  fix P \<phi>sOr\<psi>s
  assume "\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x"

  then show "P \<phi>sOr\<psi>s"
  proof (induct \<phi>sOr\<psi>s)
    fix \<phi>s :: "('a, 's) hml \<times> 's"
    obtain \<phi> and sl where "\<phi>s = (\<phi>, sl)" by fastforce

    fix \<psi>s :: "('a, 's) hml_conjunct \<times> 's"
    obtain \<psi> and sr where "\<psi>s = (\<psi>, sr)" by fastforce

    show "P (Inl \<phi>s)" and "P (Inr \<psi>s)"
      unfolding \<open>\<phi>s = (\<phi>, sl)\<close> and \<open>\<psi>s = (\<psi>, sr)\<close>
      using \<open>\<forall>x. (\<forall>y. (y, x) \<in> hml_models_wf_arg_space \<longrightarrow> P y) \<longrightarrow> P x\<close>
    proof (induct \<phi> and \<psi> arbitrary: sl and sr)
      case TT
      then show ?case
        by (smt (verit) hml.distinct(1) hml.distinct(3) hml.distinct(5) hml.distinct(7) Inl_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (Obs a \<phi>)
      then show ?case
        by (smt (verit) hml.distinct(11) hml.distinct(13) hml.distinct(9) hml.inject(1) Inl_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (Internal \<phi>)
      then show ?case
        by (smt (verit) hml.distinct(15) hml.distinct(17) hml.distinct(9) hml.inject(2) Inl_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (Silent \<phi>)
      then show ?case
        by (smt (verit) hml.distinct(11) hml.distinct(15) hml.distinct(19) hml.inject(3) Inl_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (Conj I \<psi>s)
      then show ?case
        by (smt (verit) hml.distinct(13) hml.distinct(17) hml.distinct(19) hml.inject(4) Inl_inject Pair_inject hml_models_wf_arg_space.simps range_eqI sum.distinct(1))
    next
      case (Pos \<phi>)
      then show ?case
        by (smt (verit) hml_conjunct.distinct(1) hml_conjunct.inject(1) Inr_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    next
      case (Neg \<phi>)
      then show ?case
        by (smt (verit) hml_conjunct.distinct(2) hml_conjunct.inject(2) Inr_inject Pair_inject hml_models_wf_arg_space.simps sum.distinct(1))
    qed
  qed
qed

termination
  using wf_hml_models_wf_arg_space
  by (standard) (simp add: hml_models_wf_arg_space.intros)+

lemma "(TT \<Turnstile> state) = (Conj {} \<psi> \<Turnstile> state)"
  by simp

end (* context LTS_Tau *)


context Inhabited_Tau_LTS
begin

abbreviation HML_not :: "('a, 's) hml \<Rightarrow> ('a, 's) hml" where
  "HML_not \<phi> \<equiv> Conj {l} (\<lambda>i. if i = l then (Neg \<phi>) else (Pos TT))"

lemma "(\<phi> \<Turnstile> state) = (Conj {l}
                            (\<lambda>i. if i = l
                                 then (Pos \<phi>)
                                 else (Pos TT)) \<Turnstile> state)"
  by simp

lemma "(\<phi> \<Turnstile> state) = (HML_not (HML_not \<phi>) \<Turnstile> state)"
  by simp

end (* context Inhabited_Tau_LTS *)


end
