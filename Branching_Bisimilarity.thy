theory Branching_Bisimilarity
  imports HML_SRBB Expressiveness_Price
begin

context Inhabited_Tau_LTS
begin

definition branching_simulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>branching_simulation R \<equiv> \<forall>p \<alpha> p' q. R p q \<longrightarrow> p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q''))\<close>

definition branching_simulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_simulated p q \<equiv> \<exists>R. branching_simulation R \<and> R p q\<close>

definition branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_bisimulated p q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> R p q\<close>


definition directed_branching_bisimulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>directed_branching_bisimulation R \<equiv> \<forall>p \<alpha> p' p'' q. R p q \<longrightarrow> p \<Zsurj> p' \<longrightarrow> p' \<mapsto> \<alpha> p'' \<longrightarrow>
    (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p' q' \<and> R p'' q'' \<and>  R q'' p'')\<close>

lemma branching_bisim_directable:
  \<open>branching_bisimulated p q = (\<exists>R. directed_branching_bisimulation R \<and> R p q)\<close>
  sorry

lemma branching_simulation_stuttering:
  assumes
    \<open>branching_simulated p q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>branching_simulated p' q\<close> using assms(2,1)
proof (induct)
  case (refl p)
  then show ?case .
next
  case (step p p' p'')
  then show ?case sorry
qed

definition stability_respecting :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stability_respecting R \<equiv> \<forall> p q. R p q \<and> stable_state p \<longrightarrow>
    (\<exists>q'. q \<Zsurj> q' \<and> R p q' \<and> stable_state q')\<close>

definition sr_branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>sr_branching_bisimulated p q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> stability_respecting R \<and> R p q\<close>

lemma sr_branching_bisimulation_stuttering:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>sr_branching_bisimulated p' q\<close> using assms(2,1)
proof (induct)
  case (refl p)
  then show ?case .
next
  case (step p p' p'')
  then show ?case sorry
qed

lemma sr_branching_bisimulation_sim:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>p \<Zsurj> p'\<close> \<open>p' \<mapsto>a \<alpha> p''\<close>
  shows
    \<open>\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto>a \<alpha> q'' \<and> sr_branching_bisimulated p' q' \<and> sr_branching_bisimulated p'' q''\<close>
  sorry

lemma sr_branching_bisimulation_stabilizes:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>stable_state p\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> sr_branching_bisimulated p q' \<and> stable_state q'\<close>
proof -
  from assms obtain R where
    R_spec: \<open>branching_simulation R\<close> \<open>symp R\<close> \<open>stability_respecting R\<close> \<open>R p q\<close>
    unfolding sr_branching_bisimulated_def by blast
  then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>stable_state q'\<close>
    using assms(2) unfolding stability_respecting_def by blast
  moreover have \<open>sr_branching_bisimulated p q'\<close>
    by (metis assms(1) calculation(1) sr_branching_bisimulated_def sr_branching_bisimulation_stuttering sympD)
  ultimately show ?thesis by blast
qed

lemma sr_branching_bisimulated_sym:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
  shows
    \<open>sr_branching_bisimulated q p\<close>
  using assms unfolding sr_branching_bisimulated_def by (meson sympD)


lemma sr_branching_bisim_stronger:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
  shows
    \<open>branching_bisimulated p q\<close>
  sorry

definition conjunctify_distinctions ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Pos \<chi>
    | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q)\<close>

lemma distinction_conjunctification:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p) q) p q\<close>
  unfolding conjunctify_distinctions_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Pos x
           | ImmConj I \<Psi> \<Rightarrow> \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) p q))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) p q\<close>
      using assms q_I by auto
    then show ?thesis
      by (metis (mono_tags, lifting) ImmConj hml_srbb.simps(11) someI)
  qed
qed

lemma distinction_combination:
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in>I. \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (distinguishes (\<Phi> q'') p' q'')\<close>
  shows
    \<open>\<forall>q'\<in>I. hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi> p'))) p q'\<close>
  using assms distinction_conjunctification
  unfolding hml_srbb_conj.distinguishes_def distinguishes_def
  sorry(*
  apply auto
          apply (metis assms(2) distinction_conjunctification hml_srbb_conj.distinguishes_def hml_srbb_conjunct_models.elims(2) mem_Collect_eq)
         defer
  defer
  apply (metis mem_Collect_eq)
  apply (metis singleton_iff)
  apply (metis mem_Collect_eq)
  apply (metis singleton_iff)
  apply (metis mem_Collect_eq)
    apply (metis singleton_iff)*)

lemma modal_stability_respecting:
  \<open>stability_respecting (preordered UNIV)\<close>
  unfolding stability_respecting_def
proof safe
  fix p q
  assume p_stability:
    \<open>preordered UNIV p q\<close>
    \<open>stable_state p\<close>
  have \<open>\<not>(\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> stable_state q')\<close>
  proof safe
    assume \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> stable_state q'\<close>
    hence  \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> stable_state q' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p q')\<close> by auto
    then obtain \<Phi> where
      \<open>\<forall>q'\<in>(silent_reachable_set {q}). stable_state q' \<longrightarrow> distinguishes (\<Phi> q') p q'\<close>
      using singleton_iff sreachable_set_is_sreachable by metis
    then have
      \<open>\<forall>q'\<in>(silent_reachable_set {q}). stable_state q' \<longrightarrow>
         hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p q') p q'\<close>
      using singleton_iff distinction_conjunctification by metis
    hence \<open>hml_srbb_inner.distinguishes_from
       (StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'}) (conjunctify_distinctions \<Phi> p))
       p (silent_reachable_set {q})\<close>
      using left_right_distinct by (auto simp add: p_stability(2))
    hence
      \<open>distinguishes
        (Internal (StableConj (silent_reachable_set {q} \<inter> {q'. stable_state q'})
                (conjunctify_distinctions \<Phi> p)))
        p q\<close>
      unfolding silent_reachable_set_def
      using left_right_distinct silent_reachable.refl by auto
    thus False
      using p_stability(1) preordered_no_distinction by blast
  qed
  thus \<open>\<exists>q'. q \<Zsurj> q' \<and> preordered UNIV p q' \<and> stable_state q'\<close>
    by blast
qed

lemma modal_sym: \<open>symp (preordered UNIV)\<close>
proof-
  have \<open>\<nexists> p q. preordered UNIV p q \<and> \<not>preordered UNIV q p\<close>
  proof safe
    fix p q
    assume contradiction:
      \<open>preordered UNIV p q\<close>
      \<open>\<not>preordered UNIV q p\<close>
    then obtain \<phi> where \<phi>_distinguishes: \<open>distinguishes \<phi> q p\<close> by auto
    thus False
    proof (cases \<phi>)
      case TT
      then show ?thesis using \<phi>_distinguishes by auto
    next
      case (Internal \<chi>)
      hence \<open>distinguishes (ImmConj {left} (\<lambda>i. Neg \<chi>)) p q\<close>
        using \<phi>_distinguishes by simp
      then show ?thesis using contradiction preordered_no_distinction by blast
    next
      case (ImmConj I \<Psi>)
      then obtain i where i_def: \<open>i \<in> I\<close> \<open>hml_srbb_conj.distinguishes (\<Psi> i) q p\<close>
        using \<phi>_distinguishes srbb_dist_imm_conjunction_implies_dist_conjunct by auto
      then show ?thesis
      proof (cases \<open>\<Psi> i\<close>)
        case (Pos \<chi>)
        hence \<open>distinguishes (ImmConj {left} (\<lambda>i. Neg \<chi>)) p q\<close> using i_def by simp
        thus ?thesis using contradiction preordered_no_distinction by blast
      next
        case (Neg \<chi>)
        hence \<open>distinguishes (Internal \<chi>) p q\<close> using i_def by simp
        thus ?thesis using contradiction preordered_no_distinction by blast
      qed
    qed
  qed
  thus ?thesis unfolding symp_def by blast
qed

lemma modal_branching_sim: \<open>branching_simulation (preordered UNIV)\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (preordered UNIV) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(preordered UNIV) p' q) \<and>
      (\<forall>q' q''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> preordered UNIV p' q'')\<close>
  proof clarify
    fix p \<alpha> p' q
    assume contradiction:
      \<open>preordered UNIV p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> preordered UNIV p' q''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> preordered UNIV p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>. distinguishes \<phi> p q') \<or>
      (\<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q''))\<close>
      using preordered_no_distinction
      by (metis equivpI equivp_def lts_semantics.preordered_preord modal_sym)
    hence \<open>\<forall>q''. \<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      by auto
    hence \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'') \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      by blast
    then obtain \<Phi>\<alpha> where \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'') \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close> by metis
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}. \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close>
      by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}. distinguishes (\<Phi>\<eta> q') p q'\<close> by moura
    with distinction_conjunctification obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}. hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q'\<close> by blast
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination[OF this distinctions_\<alpha>] have obs_dist:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}. hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p'))) p q'\<close> .
    with distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using left_right_distinct unfolding distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def
      apply auto
      apply (metis LTS_Tau.refl UNIV_I contradiction(1) hml_srbb_models.elims(1) preordered_def)
      apply (metis Inhabited_Tau_LTS.hml_srbb_models.elims(1) Inhabited_Tau_LTS_axioms LTS_Tau.refl UNIV_I contradiction(1) preordered_def)
      by (metis Inhabited_Tau_LTS.hml_srbb_models.elims(1) Inhabited_Tau_LTS_axioms LTS_Tau.refl UNIV_I contradiction(1) preordered_def)
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
      using obs_dist distinctions_\<eta> left_right_distinct unfolding distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def
      by (auto, blast+)
    qed
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''. q \<Zsurj> q''' \<and> q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def
      using left_right_distinct silent_reachable.refl by (auto, blast)
    thus False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding branching_simulation_def by blast
qed

thm hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct

lemma logic_sr_branching_bisim_invariant:
  assumes
    \<open>sr_branching_bisimulated p0 q0\<close>
    \<open>p0 \<Turnstile>SRBB \<phi>\<close>
  shows \<open>q0 \<Turnstile>SRBB \<phi>\<close>
proof-
  have \<open>\<And>\<phi> \<chi> \<psi>.
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
    (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
  proof-
    fix \<phi> \<chi> \<psi>
    show
      \<open>(\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
      (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
      (\<forall>p q. sr_branching_bisimulated p q \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case by simp
    next
      case (Internal \<chi>)
      show ?case
      proof safe
        fix p q
        assume \<open>sr_branching_bisimulated p q\<close> \<open>p \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close>
        then obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        hence \<open>sr_branching_bisimulated p' q\<close> using \<open>sr_branching_bisimulated p q\<close>
          using sr_branching_bisimulation_stuttering by blast
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close> using Internal \<open>hml_srbb_inner_models p' \<chi>\<close> by blast
        thus \<open>q \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> by auto
      qed
    next
      case (ImmConj I \<Psi>)
      then show ?case by auto
    next
      case (Obs \<alpha> \<phi>)
      then show ?case
      proof (safe)
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' where \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>sr_branching_bisimulated p' q''\<close>
          using sr_branching_bisimulation_sim[OF \<open>sr_branching_bisimulated p q\<close>] silent_reachable.refl
          by blast
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using \<open>p' \<Turnstile>SRBB \<phi>\<close> Obs by blast
        hence \<open>hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q' \<mapsto>a \<alpha> q''\<close> by auto 
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (Conj I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Conj I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> by auto
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q (\<Psi> i)\<close>
          using Conj \<open>sr_branching_bisimulated p q\<close> by blast
        hence \<open>hml_srbb_inner_models q (hml_srbb_inner.Conj I \<Psi>)\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Conj I \<Psi>)\<close>
          using silent_reachable.refl by blast
      qed
    next
      case (StableConj I \<Psi>) show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
          using stable_conj_parts by blast
        from \<open>hml_srbb_inner_models p (StableConj I \<Psi>)\<close> have \<open>stable_state p\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>stable_state q'\<close> \<open>sr_branching_bisimulated p q'\<close>
          using \<open>sr_branching_bisimulated p q\<close> sr_branching_bisimulation_stabilizes by blast
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> StableConj by blast
        hence \<open>hml_srbb_inner_models q' (StableConj I \<Psi>)\<close> using \<open>stable_state q'\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (StableConj I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (BranchConj \<alpha> \<phi> I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
              \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
          using branching_conj_parts branching_conj_obs by blast+
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' where q'_q''_spec:
          \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close>
          \<open>sr_branching_bisimulated p q'\<close> \<open>sr_branching_bisimulated p' q''\<close>
          using sr_branching_bisimulation_sim[OF \<open>sr_branching_bisimulated p q\<close>]
            silent_reachable.refl[of p]
          by blast
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using BranchConj.hyps \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        hence \<open>hml_srbb_inner_models q' (Obs \<alpha> \<phi>)\<close> using q'_q''_spec by auto
        moreover have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using BranchConj.hyps \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> q'_q''_spec by blast
        ultimately show \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by auto
      qed
    next
      case (Pos \<chi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_conjunct_models p (Pos \<chi>)\<close>
        then obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        hence \<open>sr_branching_bisimulated p' q\<close>
          using sr_branching_bisimulation_stuttering \<open>sr_branching_bisimulated p q\<close> by blast
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using \<open>hml_srbb_inner_models p' \<chi>\<close> Pos by blast
        thus \<open>hml_srbb_conjunct_models q (Pos \<chi>)\<close> by auto
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof safe
        fix p q
        assume
          \<open>sr_branching_bisimulated p q\<close>
          \<open>hml_srbb_conjunct_models p (Neg \<chi>)\<close>
        hence \<open>\<forall>p'. p \<Zsurj> p' \<longrightarrow> \<not>hml_srbb_inner_models p' \<chi>\<close> by simp
        moreover have
          \<open>(\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>) \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>
          using Neg sr_branching_bisimulated_sym[OF \<open>sr_branching_bisimulated p q\<close>]
            sr_branching_bisimulation_stuttering by blast
        ultimately have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>hml_srbb_inner_models q' \<chi>\<close> by blast
        thus \<open>hml_srbb_conjunct_models q (Neg \<chi>)\<close> by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma sr_branching_bisim_is_hmlsrbb: \<open>sr_branching_bisimulated p q = preordered UNIV p q\<close>
  using modal_stability_respecting modal_sym modal_branching_sim logic_sr_branching_bisim_invariant
  unfolding sr_branching_bisimulated_def by auto

theorem \<open>sr_branching_bisimulated p q = (p \<preceq> (E \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity>) q)\<close>
  using sr_branching_bisim_is_hmlsrbb \<O>_sup
  unfolding expr_preord_def by auto

end

end