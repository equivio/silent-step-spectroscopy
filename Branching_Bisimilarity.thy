section \<open>Branching Bisimilarity\<close>

theory Branching_Bisimilarity
  imports HML_SRBB Expressiveness_Price
begin

context Inhabited_Tau_LTS
begin

definition branching_simulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>branching_simulation R \<equiv> \<forall>p \<alpha> p' q. R p q \<longrightarrow> p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q''))\<close>

lemma branching_simulation_intro:
  assumes
    \<open>\<And>p \<alpha> p' q. R p q \<Longrightarrow> p \<mapsto> \<alpha> p' \<Longrightarrow>
      ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q''))\<close>
  shows
    \<open>branching_simulation R\<close>
  using assms unfolding branching_simulation_def by simp

lemma silence_retains_branching_sim:
assumes 
  \<open>branching_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<Zsurj> p'\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<Zsurj> q'\<close>
  using assms(3,2)
proof (induct arbitrary: q)
  case (refl p)
  then show ?case
    using silent_reachable.refl by blast
next
  case (step p p' p'')
  then obtain q' where \<open>R p' q'\<close> \<open>q \<Zsurj> q'\<close>
    using \<open>branching_simulation R\<close> silent_reachable.refl silent_reachable_append_\<tau> 
    unfolding branching_simulation_def by blast
  then obtain q'' where \<open>R p'' q''\<close> \<open>q' \<Zsurj> q''\<close> using step by blast
  then show ?case
    using \<open>q \<Zsurj> q'\<close> silent_reachable_trans by blast
qed

definition branching_simulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_simulated p q \<equiv> \<exists>R. branching_simulation R \<and> R p q\<close>

definition branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> where
  \<open>branching_bisimulated p q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> R p q\<close>

definition stability_respecting :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>stability_respecting R \<equiv> \<forall> p q. R p q \<and> stable_state p \<longrightarrow>
    (\<exists>q'. q \<Zsurj> q' \<and> R p q' \<and> stable_state q')\<close>

definition sr_branching_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>~SRBB\<close> 40) where
  \<open>p ~SRBB q \<equiv> \<exists>R. branching_simulation R \<and> symp R \<and> stability_respecting R \<and> R p q\<close>

lemma branching_bisimilarity_branching_sim: \<open>branching_simulation sr_branching_bisimulated\<close>
  unfolding sr_branching_bisimulated_def branching_simulation_def by blast

lemma branching_bisimilarity_stability: \<open>stability_respecting sr_branching_bisimulated\<close>
  unfolding sr_branching_bisimulated_def stability_respecting_def by blast

lemma sr_branching_bisimulation_silently_retained:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> sr_branching_bisimulated p' q'\<close> using assms(2,1)
  using branching_bisimilarity_branching_sim silence_retains_branching_sim by blast

lemma sr_branching_bisimulation_sim:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
    \<open>p \<Zsurj> p'\<close> \<open>p' \<mapsto>a \<alpha> p''\<close>
  shows
    \<open>\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto>a \<alpha> q'' \<and> sr_branching_bisimulated p' q' \<and> sr_branching_bisimulated p'' q''\<close>
proof -
  obtain q' where \<open>q \<Zsurj> q'\<close> \<open>sr_branching_bisimulated p' q'\<close>
    using assms sr_branching_bisimulation_silently_retained by blast
  thus ?thesis
    using assms(3) branching_bisimilarity_branching_sim silent_reachable_trans
    unfolding branching_simulation_def
    by blast
qed

lemma sr_branching_bisimulated_sym:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
  shows
    \<open>sr_branching_bisimulated q p\<close>
  using assms unfolding sr_branching_bisimulated_def by (meson sympD)

lemma sr_branching_bisimulated_symp:
  shows \<open>symp (~SRBB)\<close>
  using sr_branching_bisimulated_sym symp_on_def by blast
 
lemma sr_branching_bisimulated_reflp:
  shows \<open>reflp (~SRBB)\<close>
    unfolding sr_branching_bisimulated_def stability_respecting_def reflp_def
    using silence_retains_branching_sim silent_reachable.refl
    by (smt (verit) DEADID.rel_symp branching_simulation_intro)

lemma establish_sr_branching_bisim:
  assumes
    \<open>\<forall>\<alpha> p'. p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> p' ~SRBB q) \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> p ~SRBB q' \<and> p' ~SRBB q''))\<close>
    \<open>\<forall>\<alpha> q'. q \<mapsto> \<alpha> q' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> p ~SRBB q') \<or> (\<exists>p' p''. p \<Zsurj> p' \<and> p' \<mapsto> \<alpha> p'' \<and> p' ~SRBB q \<and> p'' ~SRBB q'))\<close>
    \<open>stable_state p \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> p ~SRBB q' \<and> stable_state q')\<close>
    \<open>stable_state q \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> p' ~SRBB q \<and> stable_state p')\<close>
  shows \<open>p ~SRBB q\<close>
proof -
  define R where \<open>R \<equiv> \<lambda>pp qq. pp ~SRBB qq \<or> (pp = p \<and> qq = q) \<or> (pp = q \<and> qq = p)\<close>
  hence
    R_cases: \<open>\<And>pp qq. R pp qq \<Longrightarrow> pp ~SRBB qq \<or> (pp = p \<and> qq = q) \<or> (pp = q \<and> qq = p)\<close> and
    bisim_extension: \<open>\<forall>pp qq. pp ~SRBB qq \<longrightarrow> R pp qq\<close> by blast+
  have \<open>symp R\<close>
    unfolding symp_def R_def sr_branching_bisimulated_def
    by blast
  moreover have \<open>stability_respecting R\<close>
    unfolding stability_respecting_def
  proof safe
    fix pp qq
    assume \<open>R pp qq\<close> \<open>stable_state pp\<close>
    then consider \<open>pp ~SRBB qq\<close> | \<open>pp = p \<and> qq = q\<close> | \<open>pp = q \<and> qq = p\<close>
      using R_cases by blast
    thus \<open>\<exists>q'. qq \<Zsurj> q' \<and> R pp q' \<and> stable_state q'\<close>
    proof cases
      case 1
      then show ?thesis
        using branching_bisimilarity_stability \<open>stable_state pp\<close> bisim_extension
        unfolding stability_respecting_def
        by blast
    next
      case 2
      then show ?thesis
        using assms(3) \<open>stable_state pp\<close> unfolding R_def by blast
    next
      case 3
      then show ?thesis
        using assms(4) \<open>stable_state pp\<close> \<open>symp R\<close> unfolding R_def
        by (meson sr_branching_bisimulated_sym)
    qed
  qed
  moreover have \<open>branching_simulation R\<close> unfolding branching_simulation_def
  proof clarify
    fix pp \<alpha> p' qq
    assume bc: \<open>R pp qq\<close> \<open>pp \<mapsto> \<alpha> p'\<close> \<open>\<nexists>q' q''. qq \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R pp q' \<and> R p' q''\<close>
    then consider \<open>pp ~SRBB qq\<close> | \<open>pp = p \<and> qq = q\<close> | \<open>pp = q \<and> qq = p\<close>
      using R_cases by blast
    thus \<open>\<alpha> = \<tau> \<and> R p' qq\<close>
    proof cases
      case 1
      then show ?thesis
        by (smt (verit, del_insts) bc bisim_extension
            branching_bisimilarity_branching_sim branching_simulation_def)
    next
      case 2
      then show ?thesis
        using bc assms(1) bisim_extension by blast
    next
      case 3
      then show ?thesis 
        using bc assms(2) bisim_extension sr_branching_bisimulated_sym by metis
    qed
  qed
  moreover have \<open>R p q\<close> unfolding R_def by blast
  ultimately show ?thesis
    unfolding sr_branching_bisimulated_def by blast
qed

lemma sr_branching_bisimulation_stuttering:
  assumes
    \<open>pp \<noteq> []\<close>
    \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
    \<open>hd pp ~SRBB last pp\<close>
    \<open>i < length pp\<close>
  shows
    \<open>hd pp ~SRBB pp!i\<close>
proof -
  have chain_reachable: \<open>\<forall>j < length pp. \<forall>i \<le> j. pp!i \<Zsurj> pp!j\<close>
    using tau_chain_reachabilty assms(2) .
  hence chain_hd_last:
    \<open>\<forall>i < length pp. hd pp \<Zsurj> pp!i\<close>
    \<open>\<forall>i < length pp.  pp!i \<Zsurj> last pp\<close>
    by (auto simp add: assms(1) hd_conv_nth last_conv_nth)
  define R where \<open>R \<equiv> \<lambda>p q. (p = hd pp \<and> (\<exists>i < length pp. pp!i = q)) \<or> ((q = hd pp \<and> (\<exists>i < length pp. pp!i = p))) \<or> p ~SRBB q\<close>
  have later_hd_sim: \<open>\<And>i p' \<alpha>. i < length pp \<Longrightarrow> pp!i \<mapsto> \<alpha> p'
    \<Longrightarrow> (hd pp) \<Zsurj> (pp!i) \<and> (pp!i) \<mapsto> \<alpha> p' \<and> R (pp!i) (pp!i) \<and> R p' p'\<close>
    using chain_hd_last sr_branching_bisimulated_reflp
    unfolding R_def
    by (simp add: reflp_def)
  have hd_later_sim: \<open>\<And>i p' \<alpha>. i < length pp - 1 \<Longrightarrow> (hd pp) \<mapsto> \<alpha> p'
    \<Longrightarrow> (\<exists>q' q''. (pp!i) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q'')\<close>
  proof -
    fix i p' \<alpha>
    assume case_assm: \<open>i < length pp - 1\<close> \<open>(hd pp) \<mapsto> \<alpha> p'\<close>
    hence \<open>(\<alpha> = \<tau> \<and> p' ~SRBB (last pp)) \<or> (\<exists>q' q''. (last pp) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> (hd pp) ~SRBB q' \<and> p' ~SRBB q'')\<close>
      using \<open>hd pp ~SRBB last pp\<close> branching_bisimilarity_branching_sim branching_simulation_def
      by auto
    thus \<open>(\<exists>q' q''. (pp!i) \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q'')\<close>
    proof
      assume tau_null_step: \<open>\<alpha> = \<tau> \<and> p' ~SRBB last pp\<close>
      have \<open>pp ! i \<Zsurj> (pp!(length pp - 2))\<close>
        using case_assm(1) chain_reachable by force
      moreover have \<open>pp!(length pp - 2) \<mapsto> \<alpha> (last pp)\<close>
        using assms(1,2) case_assm(1) last_conv_nth tau_null_step
        by (metis Nat.lessE Suc_1 Suc_diff_Suc less_Suc_eq zero_less_Suc zero_less_diff)
      moreover have \<open>R (hd pp) (pp!(length pp - 2)) \<and> R p' (last pp)\<close>
        unfolding R_def
        by (metis assms(1) diff_less length_greater_0_conv less_2_cases_iff tau_null_step)
      ultimately show \<open>\<exists>q' q''. pp ! i \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close> by blast
    next
      assume \<open>\<exists>q' q''. last pp \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> hd pp ~SRBB q' \<and> p' ~SRBB q''\<close>
      hence \<open>\<exists>q' q''. last pp \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close>
        unfolding R_def by blast
      moreover have \<open>i < length pp\<close> using case_assm by auto
      ultimately show \<open>\<exists>q' q''. pp ! i \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R (hd pp) q' \<and> R p' q''\<close> 
        using chain_hd_last silent_reachable_trans by blast
    qed
  qed
  have \<open>branching_simulation R\<close>
  proof (rule branching_simulation_intro)
    fix p \<alpha> p' q
    assume challenge: \<open>R p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
    from this(1) consider
      \<open>(p = hd pp \<and> (\<exists>i < length pp. pp!i = q))\<close> |
      \<open>(q = hd pp \<and> (\<exists>i < length pp. pp!i = p))\<close> |
      \<open> p ~SRBB q\<close> unfolding R_def by blast
    thus \<open>\<alpha> = \<tau> \<and> R p' q \<or> (\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> R p q' \<and> R p' q'')\<close>
    proof cases
      case 1
      then obtain i where i_spec: \<open>i < length pp\<close> \<open>pp ! i = q\<close> by blast
      from 1 have \<open>p = hd pp\<close> ..
      show ?thesis
      proof (cases \<open>i = length pp - 1\<close>)
        case True
        then have \<open>q = last pp\<close> using i_spec assms(1)
          by (simp add: last_conv_nth)
        then show ?thesis using challenge(2) assms(3) branching_bisimilarity_branching_sim
          unfolding R_def branching_simulation_def \<open>p = hd pp\<close>
          by metis
      next
        case False
        hence \<open>i < length pp - 1\<close> using i_spec by auto
        then show ?thesis using \<open>p = hd pp\<close> i_spec hd_later_sim challenge(2) by blast
      qed
    next
      case 2
      then show ?thesis
        using later_hd_sim challenge(2) by blast
    next
      case 3
      then show ?thesis
        using challenge(2) branching_bisimilarity_branching_sim
        unfolding branching_simulation_def R_def by metis
    qed
  qed
  moreover have \<open>symp R\<close>
    using sr_branching_bisimulated_sym
    unfolding R_def sr_branching_bisimulated_def
    by (smt (verit, best) sympI)
  moreover have \<open>stability_respecting R\<close>
    using assms(3) stable_state_stable sr_branching_bisimulated_sym
      branching_bisimilarity_stability
    unfolding R_def stability_respecting_def
    by (metis chain_hd_last)
  moreover have \<open>\<And>i. i < length pp \<Longrightarrow> R (hd pp) (pp!i)\<close> unfolding R_def by auto
  ultimately show ?thesis
    using assms(4) sr_branching_bisimulated_def by blast
qed

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
    using sr_branching_bisimulation_stuttering
     assms(1) calculation(1) sr_branching_bisimulated_def sympD
    by (metis LTS_Tau.silent_reachable.cases assms(2) silence_retains_branching_sim)
  ultimately show ?thesis by blast
qed

lemma sr_branching_bisim_stronger:
  assumes
    \<open>sr_branching_bisimulated p q\<close>
  shows
    \<open>branching_bisimulated p q\<close>
  using assms unfolding sr_branching_bisimulated_def branching_bisimulated_def by auto

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
  fixes p q
  defines \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (distinguishes (\<Phi> q'') p' q'')\<close>
  shows
    \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. q' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close>
  proof clarify
    fix q' q''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close>
    thus \<open>hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p' q'') p' q''\<close>
      using distinction_conjunctification assms(3)
      by (metis mem_Collect_eq)
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''\<in>{q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q'') p' q''\<close> by blast
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (ImmConj {q''. \<exists>q1'\<in>Q\<alpha>. q1' \<mapsto>a \<alpha> q''}
                               (conjunctify_distinctions \<Phi> p')) p' q''\<close> by auto
  thus \<open>\<forall>q'\<in>Q\<alpha>.
      hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                   (conjunctify_distinctions \<Phi> p'))) p q'\<close>
    by (auto) (metis assms(2))+
qed

lemma distinction_combination_eta:
  fixes p q
  defines \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and>  (\<nexists>\<phi>. \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes \<phi> p q')}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi> q''') p' q'''\<close>
  shows
    \<open>\<forall>q'\<in> Q\<alpha>. hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
      {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} (conjunctify_distinctions \<Phi> p')))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''\<in>{q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
      hml_srbb_conj.distinguishes ((conjunctify_distinctions \<Phi> p') q''') p' q'''\<close>
  proof clarify
    fix q' q'' q'''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
    thus \<open>hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p' q''') p' q'''\<close>
       using assms(3)  distinction_conjunctification by blast
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (Internal (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} (conjunctify_distinctions \<Phi> p')))  p' q''\<close>
    using silent_reachable.refl unfolding Q\<alpha>_def by fastforce
  thus \<open>\<forall>q'\<in> Q\<alpha>.
     hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
        {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} (conjunctify_distinctions \<Phi> p')))) p q'\<close>
    using assms(2) by (auto) (metis silent_reachable.refl)+
qed

definition conjunctify_distinctions_dual ::
  \<open>('s \<Rightarrow> ('a, 's) hml_srbb) \<Rightarrow> 's \<Rightarrow> ('s \<Rightarrow> ('a, 's) hml_srbb_conjunct)\<close> where
  \<open>conjunctify_distinctions_dual \<Phi> p \<equiv> \<lambda>q.
    case (\<Phi> q) of
      TT \<Rightarrow> undefined
    | Internal \<chi> \<Rightarrow> Neg \<chi>
    | ImmConj I \<Psi> \<Rightarrow> 
      (case \<Psi> (SOME i. i\<in>I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
        Pos \<chi> \<Rightarrow> Neg \<chi> | Neg \<chi> \<Rightarrow> Pos \<chi>)\<close>

lemma dual_conjunct:
  assumes
    \<open>hml_srbb_conj.distinguishes \<psi> p q\<close>
  shows
    \<open>hml_srbb_conj.distinguishes (case \<psi> of
               hml_srbb_conjunct.Pos \<chi> \<Rightarrow> hml_srbb_conjunct.Neg \<chi>
               | hml_srbb_conjunct.Neg \<chi> \<Rightarrow> hml_srbb_conjunct.Pos \<chi>) q p\<close>
  using assms
  by (simp, smt (verit, ccfv_SIG) LTS_Tau.hml_conjunct_models.simps(2)
      hml_conjunct_models.simps(1) hml_srbb_conjunct.exhaust hml_srbb_conjunct.simps(5)
      hml_srbb_conjunct.simps(6) hml_srbb_conjunct_to_hml_conjunct.simps(1) hml_srbb_conjunct_to_hml_conjunct.simps(2))

(*
lemma distinction_conjunctification_two_way:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes (conjunctify_distinctions \<Phi> p q) p q\<close>
  unfolding conjunctify_distinctions_def
proof *)

lemma distinction_conjunctification_dual:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes (conjunctify_distinctions_dual \<Phi> p q) p q\<close>
  unfolding conjunctify_distinctions_dual_def
proof
  fix q
  assume q_I: \<open>q\<in>I\<close>
  show \<open>hml_srbb_conj.distinguishes
          (case \<Phi> q of hml_srbb.Internal x \<Rightarrow> hml_srbb_conjunct.Neg x
           | ImmConj I \<Psi> \<Rightarrow>
               ( case \<Psi> (SOME i. i \<in> I \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
                  hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x))
          p q\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis using assms q_I by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis using assms q_I by auto
  next
    case (ImmConj J \<Psi>)
    then have \<open>\<exists>i \<in> J. hml_srbb_conj.distinguishes (\<Psi> i) q p\<close>
      using assms q_I by auto
    hence \<open>hml_srbb_conj.distinguishes (case \<Psi>
      (SOME i. i \<in> J \<and> hml_srbb_conj.distinguishes (\<Psi> i) q p) of
               hml_srbb_conjunct.Pos x \<Rightarrow> hml_srbb_conjunct.Neg x
               | hml_srbb_conjunct.Neg x \<Rightarrow> hml_srbb_conjunct.Pos x) p q\<close> 
      by (metis (no_types, lifting) dual_conjunct someI_ex)
    then show ?thesis unfolding ImmConj by auto
  qed
qed

lemma distinction_conjunctification_two_way:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
  shows
    \<open>\<forall>q\<in>I. hml_srbb_conj.distinguishes ((if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q) p q\<close>
proof safe
  fix q
  assume \<open>q \<in> I\<close>
  then consider \<open>distinguishes (\<Phi> q) p q\<close> | \<open>distinguishes (\<Phi> q) q p\<close> using assms by blast
  thus \<open>hml_srbb_conj.distinguishes ((if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q) p q\<close>
  proof cases
    case 1
    then show ?thesis using distinction_conjunctification
      by (smt (verit) singleton_iff)
  next
    case 2
    then show ?thesis using distinction_conjunctification_dual singleton_iff
      unfolding distinguishes_def
      by (smt (verit, ccfv_threshold))
  qed
qed

lemma distinction_conjunctification_two_way_price:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q \<or> distinguishes (\<Phi> q) q p\<close>
    \<open>\<forall>q\<in>I. \<Phi> q \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  shows
    \<open>\<forall>q\<in>I. 
      (if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q 
      \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
proof
  fix q
  assume \<open>q \<in> I\<close>
  show \<open>(if distinguishes (\<Phi> q) p q then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p q \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  proof (cases \<open>\<Phi> q\<close>)
    case TT
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      by fastforce
  next
    case (Internal \<chi>)
    then show ?thesis
      using assms \<open>q \<in> I\<close>
      unfolding conjunctify_distinctions_def conjunctify_distinctions_dual_def \<O>_def \<O>_conjunct_def
      by fastforce
  next
    case (ImmConj J \<Psi>)
    hence \<open>J = {}\<close>
      using assms \<open>q \<in> I\<close> unfolding \<O>_def
      by (simp, metis iadd_is_0 immediate_conjunction_depth.simps(3) zero_one_enat_neq(1))
    then show ?thesis
      using assms \<open>q \<in> I\<close> ImmConj by fastforce
  qed
qed

lemma distinction_combination_eta_two_way:
  fixes p q
  defines \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and>  (\<nexists>\<phi>. \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p))}\<close>
  assumes
    \<open>p \<mapsto>a \<alpha> p'\<close>
    \<open>\<forall>q'\<in> Q\<alpha>.
      \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi> q''') p' q''' \<or> distinguishes (\<Phi> q''') q''' p'\<close>
  shows
    \<open>\<forall>q'\<in> Q\<alpha>. hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
      {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (\<lambda>q'''. (if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q''')))) p q'\<close>
proof -
  have \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'''\<in>{q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
      hml_srbb_conj.distinguishes ((if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q''') p' q'''\<close>
  proof clarify
    fix q' q'' q'''
    assume \<open>q' \<in> Q\<alpha>\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
    thus \<open>hml_srbb_conj.distinguishes
        ((if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q''') p' q''' \<close>
      using assms(3) distinction_conjunctification_two_way by blast
  qed
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
    \<longrightarrow> hml_srbb_inner.distinguishes (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (\<lambda>q'''. (if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q'''))  p' q'''\<close>
    by auto (smt (verit))+
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q'''
    \<longrightarrow> distinguishes (Internal (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (\<lambda>q'''. (if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q''')))  p' q'''\<close>
    unfolding Q\<alpha>_def apply simp sledgehammer
  hence \<open>\<forall>q'\<in> Q\<alpha>. \<forall>q''. q' \<mapsto>a \<alpha> q''
    \<longrightarrow> distinguishes (Internal (Conj {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
      (\<lambda>q'''. (if distinguishes (\<Phi> q''') p' q''' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi> p' q''')))  p' q''\<close>
    using silent_reachable.refl 
    oops
  thus \<open>\<forall>q'\<in> Q\<alpha>.
     hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj
        {q'''. \<exists>q'\<in> Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} (conjunctify_distinctions \<Phi> p')))) p q'\<close>
    using assms(2) by (auto) (metis silent_reachable.refl)+
qed

lemma distinction_conjunctification_price:
  assumes
    \<open>\<forall>q\<in>I. distinguishes (\<Phi> q) p q\<close>
    \<open>\<forall>q\<in>I. \<Phi> q \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  shows
    \<open>\<forall>q\<in>I. ((conjunctify_distinctions \<Phi> p) q) \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
  using assms distinction_conjunctification_two_way_price
  by (smt (verit, best))

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
    define Q\<alpha> where \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q')}\<close>
    assume contradiction:
      \<open>preordered UNIV p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> \<not> preordered UNIV p q' \<or> \<not> preordered UNIV p' q''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> preordered UNIV p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>. distinguishes \<phi> p q') \<or>
      (\<forall>q''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q''))\<close>
      using preordered_no_distinction
      by (metis equivpI equivp_def lts_semantics.preordered_preord modal_sym)
    hence \<open>\<forall>q''. \<forall>q'\<in>Q\<alpha>.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      unfolding Q\<alpha>_def by auto
    hence \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>. distinguishes \<phi> p' q'')\<close>
      unfolding Q\<alpha>_def by blast
    then obtain \<Phi>\<alpha> where
      \<open>\<forall>q''. (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close> by metis
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> distinguishes (\<Phi>\<alpha> q'') p' q''\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}
        \<longrightarrow> distinguishes (\<Phi>\<eta> q') p q'\<close> unfolding mem_Collect_eq by moura
    with distinction_conjunctification obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')}. hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q'\<close>
      by blast
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination[OF this] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>.
        hml_srbb_inner.distinguishes (Obs \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                                                     (conjunctify_distinctions \<Phi>\<alpha> p'))) p q'\<close>
      unfolding Q\<alpha>_def by blast
    with distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''}
                   (conjunctify_distinctions \<Phi>\<alpha> p'))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using left_right_distinct contradiction(1) silent_reachable.refl
      unfolding Q\<alpha>_def distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def preordered_def
      by simp force
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta> left_right_distinct unfolding distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by (auto) blast+
    qed
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha> (ImmConj {q''. \<exists>q'''\<in>Q\<alpha>. q''' \<mapsto>a \<alpha> q''} (conjunctify_distinctions \<Phi>\<alpha> p')) {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>. distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using left_right_distinct silent_reachable.refl by (auto) blast+
    thus False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding branching_simulation_def by blast
qed

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
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close> using Internal \<open>hml_srbb_inner_models p' \<chi>\<close>
          by (meson LTS_Tau.silent_reachable_trans \<open>p ~SRBB q\<close> sr_branching_bisimulation_silently_retained)
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
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using Pos \<open>p ~SRBB q\<close> sr_branching_bisimulation_silently_retained
          by (meson  silent_reachable_trans)
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
            sr_branching_bisimulation_silently_retained
          by (meson silent_reachable_trans)
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

lemma sr_branching_bisimulated_transitive:
  assumes
    \<open>p ~SRBB q\<close>
    \<open>q ~SRBB r\<close>
  shows
    \<open>p ~SRBB r\<close>
  using assms unfolding sr_branching_bisim_is_hmlsrbb by simp

lemma sr_branching_bisimulated_equivalence: \<open>equivp (~SRBB)\<close>
proof (rule equivpI)
  show \<open>symp (~SRBB)\<close> using sr_branching_bisimulated_symp .
  show \<open>reflp (~SRBB)\<close> using sr_branching_bisimulated_reflp .
  show \<open>transp (~SRBB)\<close>
    unfolding transp_def using sr_branching_bisimulated_transitive by blast
qed

lemma sr_branching_bisimulation_stuttering_all:
  assumes
    \<open>pp \<noteq> []\<close>
    \<open>\<forall>i < length pp - 1.  pp!i \<mapsto> \<tau> pp!(Suc i)\<close>
    \<open>hd pp ~SRBB last pp\<close>
    \<open>i \<le> j\<close> \<open>j < length pp\<close>
  shows
    \<open>pp!i ~SRBB pp!j\<close>
  using assms equivp_def sr_branching_bisimulated_equivalence equivp_def order_le_less_trans
    sr_branching_bisimulation_stuttering
  by metis

theorem \<open>(p ~SRBB q) = (p \<preceq> (E \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity> \<infinity>) q)\<close>
  using sr_branching_bisim_is_hmlsrbb \<O>_sup
  unfolding expr_preord_def by auto

section \<open>Eta Bisimilarity\<close>

\<comment>\<open>Following Def 2.1 in Divide and congruence\<close>
definition eta_simulation :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>eta_simulation R \<equiv> \<forall>p \<alpha> p' q. R p q \<longrightarrow> p \<mapsto> \<alpha> p' \<longrightarrow>
    ((\<alpha> = \<tau> \<and> R p' q) \<or> (\<exists>q' q'' q'''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> q'' \<Zsurj> q'''  \<and> R p q' \<and> R p' q'''))\<close>

definition eta_bisimulated :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>~\<eta>\<close> 40) where
  \<open>p ~\<eta> q \<equiv> \<exists>R. eta_simulation R \<and> symp R \<and> R p q\<close>

lemma branching_sim_eta_sim:
  assumes \<open>branching_simulation R\<close>
  shows \<open>eta_simulation R\<close>
  using assms silent_reachable.refl unfolding branching_simulation_def eta_simulation_def by blast

lemma eta_bisim_sim:
  shows \<open>eta_simulation (~\<eta>)\<close>
  unfolding eta_bisimulated_def eta_simulation_def by blast

lemma eta_bisim_sym:
  assumes \<open>p ~\<eta> q\<close>
  shows \<open>q ~\<eta> p\<close>
  using assms unfolding eta_bisimulated_def
  by (meson sympD)

(*TODO move up to derive branching sim prop*)
lemma silence_retains_eta_sim:
assumes 
  \<open>eta_simulation R\<close>
  \<open>R p q\<close>
  \<open>p \<Zsurj> p'\<close>
shows \<open>\<exists>q'. R p' q' \<and> q \<Zsurj> q'\<close>
  using assms(3,2)
proof (induct arbitrary: q)
  case (refl p)
  then show ?case
    using silent_reachable.refl by blast
next
  case (step p p' p'')
  then obtain q' where \<open>R p' q'\<close> \<open>q \<Zsurj> q'\<close>
    using \<open>eta_simulation R\<close> silent_reachable.refl silent_reachable_append_\<tau> silent_reachable_trans
    unfolding eta_simulation_def by blast
  then obtain q'' where \<open>R p'' q''\<close> \<open>q' \<Zsurj> q''\<close> using step by blast
  then show ?case
    using \<open>q \<Zsurj> q'\<close> silent_reachable_trans by blast
qed

lemma eta_bisimulated_silently_retained:
  assumes
    \<open>p ~\<eta> q\<close>
    \<open>p \<Zsurj> p'\<close>
  shows
    \<open>\<exists>q'. q \<Zsurj> q' \<and> p' ~\<eta> q'\<close> using assms(2,1)
  using silence_retains_eta_sim unfolding eta_bisimulated_def by blast

lemma logic_eta_bisim_invariant:
  assumes
    \<open>p0 ~\<eta> q0\<close>
    \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
    \<open>p0 \<Turnstile>SRBB \<phi>\<close>
  shows \<open>q0 \<Turnstile>SRBB \<phi>\<close>
proof -
  have \<open>\<And>\<phi> \<chi> \<psi>.
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
    (\<forall>p q. p ~\<eta> q \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
  proof-
    fix \<phi> \<chi> \<psi>
    show
      \<open>(\<forall>p q. p ~\<eta> q \<longrightarrow> \<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> p \<Turnstile>SRBB \<phi> \<longrightarrow> q \<Turnstile>SRBB \<phi>) \<and>
      (\<forall>p q. p ~\<eta> q \<longrightarrow> \<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> hml_srbb_inner_models p \<chi> \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)) \<and>
      (\<forall>p q. p ~\<eta> q \<longrightarrow> \<psi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<longrightarrow> hml_srbb_conjunct_models p \<psi> \<longrightarrow> hml_srbb_conjunct_models q \<psi>)\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
      case TT
      then show ?case by simp
    next
      case (Internal \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close> \<open>p \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> \<open>Internal \<chi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
        then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        have \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          using case_assms(3) unfolding \<O>_inner_def \<O>_def by auto
        hence \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>\<close>
          using Internal case_assms(1) p'_spec eta_bisimulated_silently_retained
          by (meson  silent_reachable_trans)
        thus \<open>q \<Turnstile>SRBB hml_srbb.Internal \<chi>\<close> by auto
      qed
    next
      case (ImmConj I \<Psi>)
      then show ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (Obs \<alpha> \<phi>)
      then show ?case
      proof (safe)
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Obs \<alpha> \<phi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> unfolding \<O>_inner_def \<O>_def by auto
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>  \<open>p' ~\<eta> q'''\<close>
          using \<open>p ~\<eta> q\<close> eta_bisim_sim unfolding eta_simulation_def
          using silent_reachable.refl by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close> using \<open>p' \<Turnstile>SRBB \<phi>\<close> Obs \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by blast
        hence \<open>hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close> back_step by auto
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Obs \<alpha> \<phi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by blast
      qed
    next
      case (Conj I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Conj I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (Conj I \<Psi>)\<close>
        hence conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) le_zero_eq sup_bot_left sup_ge1)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> by auto
        hence \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q (\<Psi> i)\<close>
          using Conj \<open>p ~\<eta> q\<close> conj_price by blast
        hence \<open>hml_srbb_inner_models q (hml_srbb_inner.Conj I \<Psi>)\<close> by simp
        thus \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (hml_srbb_inner.Conj I \<Psi>)\<close>
          using silent_reachable.refl by blast
      qed
    next
      case (StableConj I \<Psi>)
      thus ?case unfolding \<O>_inner_def \<O>_def by auto
    next
      case (BranchConj \<alpha> \<phi> I \<Psi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>BranchConj \<alpha> \<phi> I \<Psi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_inner_models p (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
        hence \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> unfolding \<O>_inner_def \<O>_def
          by (simp, metis le_zero_eq sup_ge1)
        hence no_imm_conj: \<open>\<nexists>I \<Psi>. \<phi> = ImmConj I \<Psi> \<and> I \<noteq> {}\<close> unfolding \<O>_def by force
        have back_step: \<open>\<forall>p0 p1. p1 \<Turnstile>SRBB \<phi> \<longrightarrow> p0 \<Zsurj> p1 \<longrightarrow> p0 \<Turnstile>SRBB \<phi>\<close>
        proof (cases \<phi>)
          case TT
          then show ?thesis by auto
        next
          case (Internal _)
          then show ?thesis
            using silent_reachable_trans by auto
        next
          case (ImmConj _ _)
          then show ?thesis using no_imm_conj by auto
        qed
        from case_assms have conj_price: \<open>\<forall>i\<in>I. \<Psi> i \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_conjunct_def \<O>_inner_def
          by (simp, metis SUP_bot_conv(1) le_zero_eq sup_bot_left sup_ge1)
        from case_assms have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close>
              \<open>hml_srbb_inner_models p (Obs \<alpha> \<phi>)\<close>
          using branching_conj_parts branching_conj_obs by blast+
        then obtain p' where \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto
        then obtain q' q'' q''' where q'_q''_spec:
          \<open>q \<Zsurj> q'\<close> \<open>q' \<mapsto>a \<alpha> q''\<close> \<open>q'' \<Zsurj> q'''\<close>
          \<open>p ~\<eta> q'\<close> \<open>p' ~\<eta> q'''\<close>
          using eta_bisim_sim \<open>p ~\<eta> q\<close> silent_reachable.refl
          unfolding eta_simulation_def by blast
        hence \<open>q''' \<Turnstile>SRBB \<phi>\<close>
          using BranchConj.hyps \<open>p' \<Turnstile>SRBB \<phi>\<close> \<open>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by auto
        hence \<open>q'' \<Turnstile>SRBB \<phi>\<close> using back_step q'_q''_spec by blast
        hence \<open>hml_srbb_inner_models q' (Obs \<alpha> \<phi>)\<close> using q'_q''_spec by auto
        moreover have \<open>\<forall>i\<in>I. hml_srbb_conjunct_models q' (\<Psi> i)\<close>
          using BranchConj.hyps \<open>\<forall>i\<in>I. hml_srbb_conjunct_models p (\<Psi> i)\<close> q'_q''_spec conj_price
          by blast
        ultimately show \<open>\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' (BranchConj \<alpha> \<phi> I \<Psi>)\<close>
          using \<open>q \<Zsurj> q'\<close> by auto
      qed
    next
      case (Pos \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Pos \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_conjunct_models p (Pos \<chi>)\<close>
        hence \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_inner_def \<O>_conjunct_def by simp
        from case_assms obtain p' where \<open>p \<Zsurj> p'\<close> \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        then obtain q' where \<open>q \<Zsurj> q'\<close> \<open>hml_srbb_inner_models q' \<chi>\<close>
          using Pos \<open>p ~\<eta> q\<close> \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          by (meson eta_bisimulated_silently_retained silent_reachable_trans)
        thus \<open>hml_srbb_conjunct_models q (Pos \<chi>)\<close> by auto
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof safe
        fix p q
        assume case_assms:
          \<open>p ~\<eta> q\<close>
          \<open>Neg \<chi> \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          \<open>hml_srbb_conjunct_models p (Neg \<chi>)\<close>
        hence \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
          unfolding \<O>_inner_def \<O>_conjunct_def by simp
        from case_assms have \<open>\<forall>p'. p \<Zsurj> p' \<longrightarrow> \<not>hml_srbb_inner_models p' \<chi>\<close> by simp
        moreover have
          \<open>(\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>) \<longrightarrow> (\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>)\<close>
          using Neg eta_bisim_sym[OF \<open>p ~\<eta> q\<close>] eta_bisimulated_silently_retained 
            silent_reachable_trans \<open>\<chi> \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> by blast
        ultimately have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>hml_srbb_inner_models q' \<chi>\<close> by blast
        thus \<open>hml_srbb_conjunct_models q (Neg \<chi>)\<close> by simp
      qed
    qed
  qed
  thus ?thesis using assms by blast
qed

lemma modal_eta_sim_eq: \<open>eta_simulation (equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)))\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p' q) \<and>
      (\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow>
    \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q' \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q''')\<close>
  proof clarify
    fix p \<alpha> p' q
    define Q\<alpha> where \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p))}\<close>
    assume contradiction:
      \<open>equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow>
      \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q' \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q'''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p) \<or>
      (\<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p'))\<close>
      unfolding equivalent_no_distinction
      by (metis silent_reachable.cases silent_reachable.refl)
    hence \<open>\<forall>q'' q''' . \<forall>q'\<in>Q\<alpha>.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      unfolding Q\<alpha>_def using silent_reachable.refl by fastforce
    hence \<open>\<forall>q'' q'''. q'' \<Zsurj> q''' \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      unfolding Q\<alpha>_def by blast
    hence \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'' \<and>  q'' \<Zsurj> q''')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''' \<or> distinguishes \<phi> q''' p')\<close>
      by blast
    then obtain \<Phi>\<alpha> where \<Phi>\<alpha>_def:
      \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)) \<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q''')
        \<longrightarrow> (\<Phi>\<alpha> q''') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> (distinguishes (\<Phi>\<alpha> q''') p' q''' \<or> distinguishes (\<Phi>\<alpha> q''') q''' p')\<close> by metis 
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q'' q'''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi>\<alpha> q''') p' q''' \<or> distinguishes (\<Phi>\<alpha> q''') q''' p'\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}
        \<longrightarrow> (distinguishes (\<Phi>\<eta> q') p q' \<or> distinguishes (\<Phi>\<eta> q') q' p) \<and> (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      unfolding mem_Collect_eq by moura
    hence
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        (distinguishes (\<Phi>\<eta> q') p q' \<or> distinguishes (\<Phi>\<eta> q') q' p)\<close>
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
         (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      by blast+
    from distinction_conjunctification_two_way[OF this(1)] distinction_conjunctification_two_way_price[OF this]
      have \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        hml_srbb_conj.distinguishes ((if distinguishes (\<Phi>\<eta> q') p q' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi>\<eta> p q') p q' \<and>
         (if distinguishes (\<Phi>\<eta> q') p q' then conjunctify_distinctions else conjunctify_distinctions_dual) \<Phi>\<eta> p q' \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
        by blast
    then obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q' \<or> distinguishes \<phi> q' p)}.
        hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q' \<and> \<Psi>\<eta> q' \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      by auto
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination_eta[OF this] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>.
        hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                                                     (conjunctify_distinctions \<Phi>\<alpha> p')))) p q'\<close>
      unfolding Q\<alpha>_def by blast
    have \<open>Q\<alpha> \<noteq> {}\<close>
      using Q\<alpha>_def contradiction(1) silent_reachable.refl by fastforce
    hence conjunct_prices: \<open>\<forall>q'''\<in>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
          (conjunctify_distinctions \<Phi>\<alpha> p' q''') \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_price[of \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}\<close>]
      using Q\<alpha>_def \<Phi>\<alpha>_def by auto
    have \<open>(Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
          (conjunctify_distinctions \<Phi>\<alpha> p')) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
    proof (cases \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} = {}\<close>)
      case True
      then show ?thesis
        unfolding \<O>_inner_def \<O>_conjunct_def
        by (auto simp add: True bot_enat_def)
    next
      case False
      then show ?thesis
        using conjunct_prices
        unfolding \<O>_inner_def \<O>_conjunct_def by force
    qed
    hence obs_price: \<open>(Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
         (conjunctify_distinctions \<Phi>\<alpha> p')))) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_price distinctions_\<alpha> unfolding \<O>_inner_def \<O>_def by simp
    from obs_dist distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using left_right_distinct contradiction(1) silent_reachable.refl
      unfolding Q\<alpha>_def by force
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta> left_right_distinct
        unfolding distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by (auto) blast+
    qed
    moreover have branch_price: \<open>(BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)
      \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinctions_\<eta> obs_price
      unfolding Q\<alpha>_def \<O>_inner_def \<O>_def \<O>_conjunct_def \<Phi>\<alpha>_def
      by (simp, metis (mono_tags, lifting) SUP_bot_conv(2) bot_enat_def sup_bot_left)
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using left_right_distinct silent_reachable.refl by (auto) blast+
    moreover have \<open>(Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>))
      \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using branch_price
      unfolding Q\<alpha>_def \<O>_def \<O>_conjunct_def
      by (metis (no_types, lifting) \<O>_inner_def expr_internal_eq mem_Collect_eq)
    ultimately show False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding eta_simulation_def by blast
qed


lemma modal_eta_sim: \<open>eta_simulation (preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)))\<close>
proof -
  have \<open>\<nexists>p \<alpha> p' q. (preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p q \<and> p \<mapsto> \<alpha> p' \<and>
      (\<alpha> \<noteq> \<tau> \<or> \<not>(preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>))) p' q) \<and>
      (\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow>
    \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q' \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q''')\<close>
  proof clarify
    fix p \<alpha> p' q
    define Q\<alpha> where \<open>Q\<alpha> \<equiv> {q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes \<phi> p q')}\<close>
    assume contradiction:
      \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close> \<open>p \<mapsto> \<alpha> p'\<close>
      \<open>\<forall>q' q'' q'''. q \<Zsurj> q' \<longrightarrow> q' \<mapsto> \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow>
      \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q' \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q'''\<close>
      \<open>\<alpha> \<noteq> \<tau> \<or> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q\<close>
    hence distinctions: \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow>
      (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q') \<or>
      (\<forall>q'' q'''. q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q'''))\<close>
      unfolding preordered_no_distinction
      by (metis silent_reachable.cases silent_reachable.refl)
    hence \<open>\<forall>q'' q''' . \<forall>q'\<in>Q\<alpha>.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''')\<close>
      unfolding Q\<alpha>_def using silent_reachable.refl by fastforce
    hence \<open>\<forall>q'' q'''. q'' \<Zsurj> q''' \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''')\<close>
      unfolding Q\<alpha>_def by blast
    hence \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'' \<and>  q'' \<Zsurj> q''')
        \<longrightarrow> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p' q''')\<close>
      by blast
    then obtain \<Phi>\<alpha> where \<Phi>\<alpha>_def:
      \<open>\<forall>q'''. (\<exists>q' q''. q \<Zsurj> q' \<and> (\<nexists>\<phi>. \<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes \<phi> p q') \<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q''')
        \<longrightarrow> (\<Phi>\<alpha> q''') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes (\<Phi>\<alpha> q''') p' q'''\<close> by metis 
    hence distinctions_\<alpha>: \<open>\<forall>q'\<in>Q\<alpha>. \<forall>q'' q'''.
        q' \<mapsto>a \<alpha> q'' \<longrightarrow> q'' \<Zsurj> q''' \<longrightarrow> distinguishes (\<Phi>\<alpha> q''') p' q'''\<close>
      unfolding Q\<alpha>_def by blast
    from distinctions obtain \<Phi>\<eta> where
      \<open>\<forall>q'. q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')}
        \<longrightarrow> distinguishes (\<Phi>\<eta> q') p q' \<and> (\<Phi>\<eta> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close> unfolding mem_Collect_eq by moura
    with distinction_conjunctification distinction_conjunctification_price
    obtain \<Psi>\<eta> where distinctions_\<eta>:
      \<open>\<forall>q'\<in>{q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')}.
        hml_srbb_conj.distinguishes (\<Psi>\<eta> q') p q' \<and> (\<Psi>\<eta> q') \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      by (smt (verit, del_insts))
    have \<open>p \<mapsto>a \<alpha> p'\<close> using \<open>p \<mapsto> \<alpha> p'\<close> by auto
    from distinction_combination_eta[OF this] distinctions_\<alpha> have obs_dist:
      \<open>\<forall>q'\<in>Q\<alpha>.
        hml_srbb_inner.distinguishes (Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                                                     (conjunctify_distinctions \<Phi>\<alpha> p')))) p q'\<close>
      unfolding Q\<alpha>_def by blast
    have \<open>Q\<alpha> \<noteq> {}\<close>
      using Q\<alpha>_def contradiction(1) silent_reachable.refl by fastforce
    hence conjunct_prices: \<open>\<forall>q'''\<in>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}.
          (conjunctify_distinctions \<Phi>\<alpha> p' q''') \<in> \<O>_conjunct (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_price[of \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}\<close>]
      using Q\<alpha>_def \<Phi>\<alpha>_def by auto
    have \<open>(Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''}
          (conjunctify_distinctions \<Phi>\<alpha> p')) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
    proof (cases \<open>{q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} = {}\<close>)
      case True
      then show ?thesis
        unfolding \<O>_inner_def \<O>_conjunct_def
        by (auto simp add: True bot_enat_def)
    next
      case False
      then show ?thesis
        using conjunct_prices
        unfolding \<O>_inner_def \<O>_conjunct_def by force
    qed
    hence obs_price: \<open>(Obs \<alpha> (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
         (conjunctify_distinctions \<Phi>\<alpha> p')))) \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinction_conjunctification_price distinctions_\<alpha> unfolding \<O>_inner_def \<O>_def by simp
    from obs_dist distinctions_\<eta> have
      \<open>hml_srbb_inner_models p (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      using left_right_distinct contradiction(1) silent_reachable.refl
      unfolding Q\<alpha>_def by force
    moreover have \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> hml_srbb_inner_models q'
        (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
    proof safe
      fix q'
      assume contradiction: \<open>q \<Zsurj> q'\<close>
        \<open>hml_srbb_inner_models q' (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)\<close>
      thus \<open>False\<close>
        using obs_dist distinctions_\<eta> left_right_distinct
        unfolding distinguishes_def hml_srbb_conj.distinguishes_def hml_srbb_inner.distinguishes_def Q\<alpha>_def
        by (auto) blast+
    qed
    moreover have branch_price: \<open>(BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)
      \<in> \<O>_inner (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using distinctions_\<eta> obs_price
      unfolding Q\<alpha>_def \<O>_inner_def \<O>_def \<O>_conjunct_def \<Phi>\<alpha>_def
      by (simp, metis (mono_tags, lifting) SUP_bot_conv(2) bot_enat_def sup_bot_left)
    ultimately have \<open>distinguishes (Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>)) p q\<close>
      unfolding distinguishes_def Q\<alpha>_def
      using left_right_distinct silent_reachable.refl by (auto) blast+
    moreover have \<open>(Internal (BranchConj \<alpha>
          (Internal (Conj {q'''. \<exists>q'\<in>Q\<alpha>. \<exists>q''. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Zsurj> q'''} 
                   (conjunctify_distinctions \<Phi>\<alpha> p')))
          {q'. q \<Zsurj> q' \<and> (\<exists>\<phi>\<in>\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> p q')} \<Psi>\<eta>))
      \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)\<close>
      using branch_price
      unfolding Q\<alpha>_def \<O>_def \<O>_conjunct_def
      by (metis (no_types, lifting) \<O>_inner_def expr_internal_eq mem_Collect_eq)
    ultimately show False using contradiction(1) preordered_no_distinction by blast
  qed
  thus ?thesis
    unfolding eta_simulation_def by blast
qed

definition coupled :: \<open>('s \<Rightarrow> 's \<Rightarrow> bool) \<Rightarrow> bool\<close> where
  \<open>coupled R \<equiv> \<forall>p q. R p q \<longrightarrow> (\<exists>q'. q \<Zsurj> q' \<and> R q' p)\<close>

lemma coupled_eta:
  \<open>coupled (preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)))\<close>
  unfolding coupled_def
  sorry
(*
proof (rule allI)+
  fix p q
  have \<open>(\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) q' p)
    \<longrightarrow> \<not>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close>
  proof safe
    assume contra:
      \<open>\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) q' p\<close>
      \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close>
    hence \<open>\<forall>q' \<in> silent_reachable_set {q}.
      \<exists>\<phi> \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>). distinguishes \<phi> q' p\<close>
      using sreachable_set_is_sreachable by force
    then obtain \<Phi> where
      \<open>\<forall>q' \<in> silent_reachable_set {q}.
        (\<Phi> q') \<in> \<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) \<and> distinguishes (\<Phi> q') q' p\<close>
      by metis
    hence \<open>\<forall>q'\<in>silent_reachable_set {q}. distinguishes (\<Phi> q') q' p\<close> by blast
    with distinction_conjunctification_dual have
      \<open>\<forall>q' \<in> silent_reachable_set {q}.
       hml_srbb_conj.distinguishes (conjunctify_distinctions_dual \<Phi> p q') q' p\<close>
    then have \<open>hml_srbb_inner.distinguishes (Conj (silent_reachable_set {q})
                   (conjunctify_distinctions_dual \<Phi> p)) q p\<close>
      apply simp oops
      
  thus \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q \<longrightarrow>
           (\<exists>q'. q \<Zsurj> q' \<and> preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) q' p)\<close> by blast
qed
*)

lemma
  \<open>eta_simulation (equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)))\<close>
  unfolding eta_simulation_def
proof clarify
  fix p \<alpha> p' q
  assume step:
    \<open>equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close>
    \<open>p \<mapsto> \<alpha> p'\<close>
    \<open>\<nexists>q' q'' q'''.
          q \<Zsurj> q' \<and>
          q' \<mapsto> \<alpha> q'' \<and>
          q'' \<Zsurj> q''' \<and>
          equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q' \<and>
          equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q'''\<close>
  hence mutual_preorder:
    \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p q\<close>
    \<open>preordered (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) q p\<close>
    by auto
  show \<open>\<alpha> = \<tau> \<and> equivalent (\<O> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>)) p' q\<close>
  
    

  


theorem \<open>(p ~\<eta> q) = (p \<preceq> (E \<infinity> \<infinity> \<infinity> 0 0 \<infinity> \<infinity> \<infinity>) q)\<close>
  oops


end

end
