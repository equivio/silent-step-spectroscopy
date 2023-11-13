theory HML
  imports Main "../LTS"
begin

datatype 
  ('act, 'i) HML =
    HML_true |
    HML_poss 'act "('act, 'i) HML" |
    HML_silent "('act, 'i) HML" |
    HML_internal "('act, 'i) HML" |
    HML_conj "'i set" "'i \<Rightarrow>  (('act, 'i) HML, ('act, 'i) HML) sum"


context LTS_Tau
begin

\<comment> \<open>
fun hml_semantic :: "('a, 's) HML \<Rightarrow> 's set" ("\<lbrakk>_\<rbrakk>HML" 60) where
  "\<lbrakk>HML_true\<rbrakk>HML = {}" (* How to get the set of all processes? 's set? *)
\<close>

function hml_models     :: "('a, 's) HML     \<Rightarrow> 's \<Rightarrow> bool" ("_ \<Turnstile> _" 60) 
where
  "(HML_true         \<Turnstile> _) = True" |
  "((HML_poss a \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<mapsto> a p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_silent \<phi>)   \<Turnstile> p) = (\<exists>p'. p \<Zsurj> p' \<and> (\<phi> \<Turnstile> p'))" |
  "((HML_internal \<phi>) \<Turnstile> p) = ((\<exists>p'. p \<mapsto> \<tau> p' \<and> (\<phi> \<Turnstile> p')) \<or> (\<phi> \<Turnstile> p))" |
  "((HML_conj I \<psi>s)  \<Turnstile> p) = (\<forall>i \<in> I. (\<lambda>x. case x of Inl tr \<Rightarrow> (tr \<Turnstile> p) | Inr fl \<Rightarrow> \<not>(fl \<Turnstile> p)) (\<psi>s i))" 
                 apply (metis HML.exhaust surj_pair)
                apply simp
               apply simp
              apply fastforce
             apply blast
            apply simp
           apply fastforce
          apply fastforce
         apply force
        apply fastforce
       apply fastforce
      apply simp
     apply fastforce
    apply force
   apply simp
  by fastforce

inductive_set hml_models_wf_argument_space :: "(('a, 's) HML  \<times> 's) rel" where
                             "((\<phi>, x), HML_poss   a \<phi>, p) \<in> hml_models_wf_argument_space" |
                             "((\<phi>, x), HML_silent   \<phi>, p) \<in> hml_models_wf_argument_space" |
                             "((\<phi>, x), HML_internal \<phi>, p) \<in> hml_models_wf_argument_space" |
  "x \<in> I \<Longrightarrow> \<psi>s x = Inl \<phi> \<Longrightarrow> ((\<phi>, p), HML_conj  I \<psi>s, p) \<in> hml_models_wf_argument_space" |
  "x \<in> I \<Longrightarrow> \<psi>s x = Inr \<phi> \<Longrightarrow> ((\<phi>, p), HML_conj  I \<psi>s, p) \<in> hml_models_wf_argument_space"

lemma wf_hml_models_wf_argument_space: "wf hml_models_wf_argument_space"
  unfolding wf_def
proof safe
  fix P \<phi> s
  assume "\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s"
  hence "\<forall>\<phi> s. (\<forall>\<phi>' s'. ((\<phi>' s'), (\<phi>, s)) \<in> hml_models_wf_argument_space \<longrightarrow> P (\<phi>' s')) \<longrightarrow> P (\<phi>, s)" sledgehammer
    by meson 
  show "P (\<phi>, s)"
  proof (induct \<phi> arbitrary: s)
    case HML_true
    then show ?case
      by (metis (no_types, lifting) HML.distinct(1) HML.distinct(3) HML.distinct(5) HML.distinct(7) \<open>\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s\<close> case_prodI2 case_prod_curry hml_models_wf_argument_space.simps)
  next
    case (HML_poss x1 \<phi>)
    then show ?case
      by (smt (verit) HML.distinct(11) HML.distinct(13) HML.distinct(9) HML.inject(1) \<open>\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s\<close> case_prodE' case_prod_conv hml_models_wf_argument_space.simps hml_models_wf_argument_space_def mem_Collect_eq)
  next
    case (HML_silent \<phi>)
    then show ?case
      by (smt (verit) HML.distinct(15) HML.distinct(17) HML.distinct(9) HML.inject(2) LTS_Tau.hml_models_wf_argument_space_def \<open>\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s\<close> case_prodE' case_prod_conv hml_models_wf_argument_space.simps mem_Collect_eq)
  next
    case (HML_internal \<phi>)
    then show ?case
      by (smt (verit) HML.distinct(11) HML.distinct(15) HML.distinct(19) HML.inject(3) \<open>\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s\<close> case_prodE' hml_models_wf_argument_space.simps hml_models_wf_argument_space_def mem_Collect_eq split_conv)
  next
    case (HML_conj x1 x2)
    then show ?case
      by (smt (verit) HML.distinct(13) HML.distinct(17) HML.distinct(19) HML.inject(4) LTS_Tau.hml_models_wf_argument_space_def \<open>\<forall>\<phi>s. (\<forall>\<phi>'s'. (\<phi>'s', \<phi>s) \<in> hml_models_wf_argument_space \<longrightarrow> P \<phi>'s') \<longrightarrow> P \<phi>s\<close> case_prodE' case_prod_conv hml_models_wf_argument_space.simps mem_Collect_eq range_eqI setl.intros sum_set_simps(1) sum_set_simps(4))
  qed
qed

termination
  unfolding wf_def
proof 
  from wf_hml_models_wf_argument_space show "wf hml_models_wf_argument_space".
  show "\<And>a \<phi> p x. ((\<phi>, x), HML_poss a \<phi>, p) \<in> hml_models_wf_argument_space"
    by (simp add: hml_models_wf_argument_space.intros(1))
  show "\<And>\<phi> p x. ((\<phi>, x), HML_silent \<phi>, p) \<in> hml_models_wf_argument_space"
    by (simp add: LTS_Tau.hml_models_wf_argument_space.simps)
  show "\<And>\<phi> p x. ((\<phi>, x), HML_internal \<phi>, p) \<in> hml_models_wf_argument_space"
    by (simp add: hml_models_wf_argument_space.intros(3))
  show "\<And>\<phi> p. ((\<phi>, p), HML_internal \<phi>, p) \<in> hml_models_wf_argument_space"
    by (simp add: hml_models_wf_argument_space.intros(3))
  show "\<And>I \<psi>s p x a. x \<in> I \<Longrightarrow> \<psi>s x = Inl a \<Longrightarrow> ((a, p), HML_conj I \<psi>s, p) \<in> hml_models_wf_argument_space"
    by (simp add: hml_models_wf_argument_space.intros(4))
  show "\<And>I \<psi>s p x b. x \<in> I \<Longrightarrow> \<psi>s x = Inr b \<Longrightarrow> ((b, p), HML_conj I \<psi>s, p) \<in> hml_models_wf_argument_space"
    by (simp add: hml_models_wf_argument_space.intros(5))
qed

end

end