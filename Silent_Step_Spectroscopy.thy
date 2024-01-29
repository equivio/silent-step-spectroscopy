theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

lemma expr_internal_eq:
  shows "expressiveness_price (Internal \<chi>) = expr_pr_inner \<chi>"
proof-
  have expr_internal: "expressiveness_price (Internal \<chi>) = E (modal_depth_srbb (Internal \<chi>))
                              (branching_conjunction_depth (Internal \<chi>))
                              (instable_conjunction_depth  (Internal \<chi>))
                              (stable_conjunction_depth    (Internal \<chi>))
                              (immediate_conjunction_depth (Internal \<chi>))
                              (max_positive_conjunct_depth (Internal \<chi>))
                              (max_negative_conjunct_depth (Internal \<chi>))
                              (negation_depth              (Internal \<chi>))"
            using expressiveness_price.simps by blast
          have "modal_depth_srbb (Internal \<chi>) = modal_depth_srbb_inner \<chi>"
            "(branching_conjunction_depth (Internal \<chi>)) = branch_conj_depth_inner \<chi>"
            "(instable_conjunction_depth  (Internal \<chi>)) = inst_conj_depth_inner \<chi>"
            "(stable_conjunction_depth    (Internal \<chi>)) = st_conj_depth_inner \<chi>"
            "(immediate_conjunction_depth (Internal \<chi>)) = imm_conj_depth_inner \<chi>"
            "max_positive_conjunct_depth (Internal \<chi>) = max_pos_conj_depth_inner \<chi>"
            "max_negative_conjunct_depth (Internal \<chi>) = max_neg_conj_depth_inner \<chi>"
            "negation_depth (Internal \<chi>) = neg_depth_inner \<chi>"
            by simp+
          with expr_internal show ?thesis
            by auto
        qed

lemma expr_pos:
  assumes "expr_pr_inner \<chi> \<le> (min1_6 e)"
  shows "expr_pr_conjunct (Pos \<chi>) \<le> e"
proof-
  have expr_internal: "expr_pr_conjunct (Pos \<chi>) = E (modal_depth_srbb_conjunct (Pos \<chi>))
                              (branch_conj_depth_conjunct (Pos \<chi>))
                              (inst_conj_depth_conjunct  (Pos \<chi>))
                              (st_conj_depth_conjunct    (Pos \<chi>))
                              (imm_conj_depth_conjunct (Pos \<chi>))
                              (max_pos_conj_depth_conjunct (Pos \<chi>))
                              (max_neg_conj_depth_conjunct (Pos \<chi>))
                              (neg_depth_conjunct            (Pos \<chi>))"
            using expr_pr_conjunct.simps by blast
          have pos_upd: "(modal_depth_srbb_conjunct (Pos \<chi>)) = modal_depth_srbb_inner \<chi>"
            "(branch_conj_depth_conjunct (Pos \<chi>)) = branch_conj_depth_inner \<chi>"
            "(inst_conj_depth_conjunct  (Pos \<chi>)) = inst_conj_depth_inner \<chi>"
            "(st_conj_depth_conjunct    (Pos \<chi>)) = st_conj_depth_inner \<chi>"
            "(imm_conj_depth_conjunct (Pos \<chi>)) = imm_conj_depth_inner \<chi>"
            "(max_pos_conj_depth_conjunct (Pos \<chi>)) = modal_depth_srbb_inner \<chi>"
            "(max_neg_conj_depth_conjunct (Pos \<chi>)) = max_neg_conj_depth_inner \<chi>"
            "(neg_depth_conjunct            (Pos \<chi>)) = neg_depth_inner \<chi>"
            by simp+
          have "expr_pr_inner \<chi> \<le> (min1_6 e)"
            using assms 
            by blast
          obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
            by (metis antysim assms eneg_leq energy.exhaust_sel expr_pr_inner.simps min_eneg(1))
          hence "min1_6 e = (E (min e1 e6) e2 e3 e4 e5 e6 e7 e8)"  
            by (simp add: min1_6_def)
          hence "modal_depth_srbb_inner \<chi> \<le> (min e1 e6)"
            using \<open> expr_pr_inner \<chi> \<le> (min1_6 e)\<close> expr_pr_inner.simps 
            by (simp add: leq_not_eneg)
          hence "modal_depth_srbb_inner \<chi> \<le> e6"
            using min.boundedE by blast
          thus "expr_pr_conjunct (Pos \<chi>) \<le> e"
            using expr_internal pos_upd \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close>
            using \<open> expr_pr_inner \<chi> \<le> min1_6 e\<close> \<open>min1_6 e = E (min e1 e6) e2 e3 e4 e5 e6 e7 e8\<close> leq_not_eneg by force
        qed

lemma expr_neg:
  assumes "expr_pr_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))"
  shows "expr_pr_conjunct (Neg \<chi>) \<le> e"
proof-
  have expr_neg: "expr_pr_conjunct (Neg \<chi>) =
  E (modal_depth_srbb_conjunct (Neg \<chi>))
                                (branch_conj_depth_conjunct (Neg \<chi>))
                                (inst_conj_depth_conjunct (Neg \<chi>))
                                (st_conj_depth_conjunct (Neg \<chi>))
                                (imm_conj_depth_conjunct (Neg \<chi>))
                                (max_pos_conj_depth_conjunct (Neg \<chi>))
                                (max_neg_conj_depth_conjunct (Neg \<chi>))
                                (neg_depth_conjunct (Neg \<chi>))"
              using expr_pr_conjunct.simps by blast
  
            have neg_ups: "modal_depth_srbb_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>" 
                          "(branch_conj_depth_conjunct (Neg \<chi>)) = branch_conj_depth_inner \<chi>"
                          "inst_conj_depth_conjunct (Neg \<chi>) = inst_conj_depth_inner \<chi>" 
                          "st_conj_depth_conjunct (Neg \<chi>) = st_conj_depth_inner \<chi>"
                          "imm_conj_depth_conjunct (Neg \<chi>) = imm_conj_depth_inner \<chi>"
                          "max_pos_conj_depth_conjunct (Neg \<chi>) = max_pos_conj_depth_inner \<chi>"
                          "max_neg_conj_depth_conjunct (Neg \<chi>) = modal_depth_srbb_inner \<chi>"
                          "neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>" 
              by simp+

          have "expr_pr_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))"
            using assms
            by blast
          obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
            by (metis antysim assms eneg_leq energy.exhaust_sel expr_pr_inner.simps min_eneg(2) minus_energy_def)
          hence "(e - (E 0 0 0 0 0 0 0 1)) = (E e1 e2 e3 e4 e5 e6 e7 (e8-1)) \<or> 
                  ((e - (E 0 0 0 0 0 0 0 1)) = eneg)"
            using minus_energy_def
            by simp
          then show ?thesis
          proof(rule disjE)
            assume "e - E 0 0 0 0 0 0 0 1 = eneg"
            hence "e = (E 0 0 0 0 0 0 0 0)"
              using assms
              using antysim eneg_leq min_eneg(2) by fastforce
            then show ?thesis 
              using \<open>e - E 0 0 0 0 0 0 0 1 = eneg\<close> assms 
              by (metis antysim eneg_leq energy.distinct(1) expr_pr_inner.simps min_eneg(2))
          next
            assume "e - E 0 0 0 0 0 0 0 1 = E e1 e2 e3 e4 e5 e6 e7 (e8 - 1)"
            hence "(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))"
            using min1_7_def
            by simp
            hence "modal_depth_srbb_inner \<chi> \<le> (min e1 e7)"
              using expr_pr_inner.simps
              using \<open>expr_pr_inner \<chi> \<le> min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> leq_not_eneg by auto
            
            have "neg_depth_inner \<chi> \<le> (e8-1)"
              using \<open>(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))\<close>
                    \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>expr_pr_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1))\<close>
              using leq_not_eneg by force
            hence "neg_depth_conjunct (Neg \<chi>) \<le> e8"
              using \<open>neg_depth_conjunct (Neg \<chi>) = 1 + neg_depth_inner \<chi>\<close>
              by (metis \<open>e - E 0 0 0 0 0 0 0 1 = E e1 e2 e3 e4 e5 e6 e7 (e8 - 1)\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> add_diff_cancel_enat enat_add_left_cancel_le energy.sel(8) energy.simps(3) le_iff_add leq_not_eneg minus_energy_def)
          thus "expr_pr_conjunct (Neg \<chi>) \<le> e"
            using expr_neg \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>modal_depth_srbb_inner \<chi> \<le> (min e1 e7)\<close>
            using \<open>expr_pr_inner \<chi> \<le> min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> \<open>(min1_7 (e - E 0 0 0 0 0 0 0 1)) = (E (min e1 e7) e2 e3 e4 e5 e6 e7 (e8-1))\<close> leq_not_eneg 
            by (simp add: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> neg_ups(7))
        qed
      qed

lemma expr_obs:
  assumes "expressiveness_price \<phi> \<le> (e - E 1 0 0 0 0 0 0 0)"
  shows "expr_pr_inner (Obs \<alpha> \<phi>) \<le> e"
proof-
  have expr_pr_obs: "expr_pr_inner (Obs \<alpha> \<phi>) = 
                  (E (modal_depth_srbb_inner (Obs \<alpha> \<phi>))
                 (branch_conj_depth_inner (Obs \<alpha> \<phi>))
                 (inst_conj_depth_inner (Obs \<alpha> \<phi>))
                 (st_conj_depth_inner (Obs \<alpha> \<phi>))
                 (imm_conj_depth_inner (Obs \<alpha> \<phi>))
                 (max_pos_conj_depth_inner (Obs \<alpha> \<phi>))
                 (max_neg_conj_depth_inner (Obs \<alpha> \<phi>))
                 (neg_depth_inner (Obs \<alpha> \<phi>)))"
    using expr_pr_inner.simps by blast
  have obs_upds: "modal_depth_srbb_inner (Obs \<alpha> \<phi>) = 1 + modal_depth_srbb \<phi>" 
  "branch_conj_depth_inner (Obs \<alpha> \<phi>) = branching_conjunction_depth \<phi>"
  "inst_conj_depth_inner (Obs \<alpha> \<phi>) = instable_conjunction_depth \<phi>"
  "st_conj_depth_inner (Obs \<alpha> \<phi>) = stable_conjunction_depth \<phi>"
  "imm_conj_depth_inner (Obs \<alpha> \<phi>) = immediate_conjunction_depth \<phi>"
  "max_pos_conj_depth_inner (Obs \<alpha> \<phi>) = max_positive_conjunct_depth \<phi>"
  "max_neg_conj_depth_inner (Obs \<alpha> \<phi>) = max_negative_conjunct_depth \<phi>"
  "neg_depth_inner (Obs \<alpha> \<phi>) = negation_depth \<phi>"
    by simp+

  obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
    by (metis antysim assms eneg_leq energy.exhaust_sel gets_smaller srbb_price_never_neg)
  hence "(e - (E 1 0 0 0 0 0 0 0)) = (E (e1-1) e2 e3 e4 e5 e6 e7 e8) \<or> 
                  ((e - (E 1 0 0 0 0 0 0 0)) = eneg)"
            using minus_energy_def
            by simp
  then show ?thesis
  proof(rule disjE)
  assume "e - E 1 0 0 0 0 0 0 0 = eneg"
  hence "e = (E 0 0 0 0 0 0 0 0)"
    using assms
    using antysim eneg_leq min_eneg(2) by fastforce
  then show ?thesis 
    using \<open>e - E 1 0 0 0 0 0 0 0 = eneg\<close> assms 
    using eneg_leq order_class.order_eq_iff by auto
next
  assume "e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8"
  hence "modal_depth_srbb \<phi> \<le> (e1 - 1)"
    using assms leq_not_eneg by force
  hence "modal_depth_srbb_inner (Obs \<alpha> \<phi>) \<le> e1"
    using obs_upds
    by (metis \<open>e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> add_diff_assoc_enat add_diff_cancel_enat add_mono_thms_linordered_semiring(1) enat.simps(3) energy.distinct(1) energy.sel(1) le_numeral_extra(4) leq_not_eneg minus_energy_def one_enat_def)
  then show ?thesis
    using expr_pr_obs obs_upds 
    using \<open>e - E 1 0 0 0 0 0 0 0 = E (e1 - 1) e2 e3 e4 e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> assms leq_not_eneg by fastforce 
qed
qed

lemma expr_st_conj: 
  assumes "I \<noteq> {}" "\<forall>q \<in> I. expr_pr_conjunct (\<psi>s q) \<le> (e - (E 0 0 0 1 0 0 0 0))"
  shows "expr_pr_inner (StableConj I \<psi>s) \<le> e" 
proof-
  have st_conj_upds: "modal_depth_srbb_inner (StableConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)"
"branch_conj_depth_inner (StableConj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"inst_conj_depth_inner (StableConj I \<psi>s) = Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"st_conj_depth_inner (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"imm_conj_depth_inner (StableConj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"max_pos_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"max_neg_conj_depth_inner (StableConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"neg_depth_inner (StableConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)"
    by force+

  obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
    using antysim assms eneg_leq energy.exhaust_sel gets_smaller \<psi>_price_never_neg
    by (metis ex_in_conv)
  hence "(e - (E 0 0 0 1 0 0 0 0)) = (E e1 e2 e3 (e4-1) e5 e6 e7 e8) \<or> 
                  ((e - (E 0 0 0 1 0 0 0 0)) = eneg)"
            using minus_energy_def
            by simp
  then show ?thesis
  proof(rule disjE)
  assume "e - E 0 0 0 1 0 0 0 0 = eneg"
  hence "e = (E 0 0 0 0 0 0 0 0)"
    using assms
    using antysim eneg_leq min_eneg(2) by fastforce
  then show ?thesis 
    using \<open>e - E 0 0 0 1 0 0 0 0 = eneg\<close> assms 
    using eneg_leq order_class.order_eq_iff by auto
next
  assume assm: "e - E 0 0 0 1 0 0 0 0 = E e1 e2 e3 (e4-1) e5 e6 e7 e8"
  hence "\<forall>i \<in> I. modal_depth_srbb_conjunct (\<psi>s i) \<le> e1"
"\<forall>i \<in> I. branch_conj_depth_conjunct (\<psi>s i) \<le> e2"
"\<forall>i \<in> I. inst_conj_depth_conjunct (\<psi>s i) \<le> e3"
"\<forall>i \<in> I. st_conj_depth_conjunct (\<psi>s i) \<le> (e4 - 1)"
"\<forall>i \<in> I. imm_conj_depth_conjunct (\<psi>s i) \<le> e5"
"\<forall>i \<in> I. max_pos_conj_depth_conjunct (\<psi>s i) \<le> e6"
"\<forall>i \<in> I. max_neg_conj_depth_conjunct (\<psi>s i) \<le> e7"
"\<forall>i \<in> I. neg_depth_conjunct (\<psi>s i) \<le> e8"
    using assms leq_not_eneg by force+
  hence sups: "Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1"
"Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2"
"Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e3"
"Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e4 - 1)"
"Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e5"
"Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6"
"Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7"
"Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8"
    by (simp add: Sup_le_iff)+
  hence "st_conj_depth_inner (StableConj I \<psi>s) \<le> e4"
    using \<open>e - E 0 0 0 1 0 0 0 0 = E e1 e2 e3 (e4 - 1) e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>st_conj_depth_inner (StableConj I \<psi>s) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    by (metis add_diff_cancel_enat enat_add_left_cancel_le energy.sel(4) energy.simps(3) le_iff_add leq_not_eneg minus_energy_def)
  then show ?thesis
    using st_conj_upds sups 
    by (simp add: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> leq_not_eneg)
qed
qed

lemma expr_imm_conj: 
  assumes "I \<noteq> {}" "expr_pr_inner (Conj I \<psi>) \<le> (e - E 0 0 0 0 1 0 0 0)"
  shows "expressiveness_price (ImmConj I \<psi>s) \<le> e"
proof-
  have conj_upds: "modal_depth_srbb_inner (Conj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)"
  "branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "inst_conj_depth_inner (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "max_pos_conj_depth_inner (Conj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "max_neg_conj_depth_inner (Conj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)"
    using assms  
    by force+

  have imm_conj_upds:  "modal_depth_srbb (ImmConj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)"
"branching_conjunction_depth (ImmConj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"instable_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"stable_conjunction_depth (ImmConj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"immediate_conjunction_depth (ImmConj I \<psi>s) = 1 + Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"max_positive_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"max_negative_conjunct_depth (ImmConj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)"
"negation_depth (ImmConj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)"
    using assms
    by force+

  obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8" 
    using antysim assms eneg_leq energy.exhaust_sel gets_smaller \<psi>_price_never_neg
    by (metis \<chi>_price_never_neg)

  hence "Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1"
  "Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2"
  "1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e3"
  "Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e4"
  "Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e5-1)"
  "Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6"
  "Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7"
  "Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8" using assms conj_upds sorry

  thus "expressiveness_price (ImmConj I \<psi>s) \<le> e" using imm_conj_upds sorry
qed

lemma expr_conj: 
  assumes "I \<noteq> {}" "\<forall>q \<in> I. expr_pr_conjunct (\<psi>s q) \<le> (e - E 0 0 1 0 0 0 0 0)"
  shows "expr_pr_inner (Conj I \<psi>s) \<le> e"
proof-
  have conj_upds: "modal_depth_srbb_inner (Conj I \<psi>s) = Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I)"
  "branch_conj_depth_inner (Conj I \<psi>s) = Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "inst_conj_depth_inner (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "st_conj_depth_inner (Conj I \<psi>s) = Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "imm_conj_depth_inner (Conj I \<psi>s) = Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "max_pos_conj_depth_inner (Conj I \<psi>s) = Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "max_neg_conj_depth_inner (Conj I \<psi>s) = Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I)"
  "neg_depth_inner (Conj I \<psi>s) = Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I)"
    using assms  
    by force+

  obtain e1 e2 e3 e4 e5 e6 e7 e8 where "e = E e1 e2 e3 e4 e5 e6 e7 e8"
    using antysim assms eneg_leq energy.exhaust_sel gets_smaller \<psi>_price_never_neg
    by (metis ex_in_conv)
  hence "(e - (E 0 0 1 0 0 0 0 0)) = (E e1 e2 (e3-1) e4 e5 e6 e7 e8) \<or> 
                  ((e - (E 0 0 1 0 0 0 0 0)) = eneg)"
            using minus_energy_def
            by simp
  then show ?thesis
  proof(rule disjE)
  assume "e - E 0 0 1 0 0 0 0 0 = eneg"
  hence "e = (E 0 0 0 0 0 0 0 0)"
    using assms
    using antysim eneg_leq min_eneg(2) by fastforce
  then show ?thesis 
    using \<open>e - E 0 0 1 0 0 0 0 0 = eneg\<close> assms 
    using eneg_leq order_class.order_eq_iff by auto
next
  assume assm: "e - E 0 0 1 0 0 0 0 0 = E e1 e2 (e3-1) e4 e5 e6 e7 e8"
  hence "\<forall>i \<in> I. modal_depth_srbb_conjunct (\<psi>s i) \<le> e1"
"\<forall>i \<in> I. branch_conj_depth_conjunct (\<psi>s i) \<le> e2"
"\<forall>i \<in> I. inst_conj_depth_conjunct (\<psi>s i) \<le> (e3-1)"
"\<forall>i \<in> I. st_conj_depth_conjunct (\<psi>s i) \<le> e4"
"\<forall>i \<in> I. imm_conj_depth_conjunct (\<psi>s i) \<le> e5"
"\<forall>i \<in> I. max_pos_conj_depth_conjunct (\<psi>s i) \<le> e6"
"\<forall>i \<in> I. max_neg_conj_depth_conjunct (\<psi>s i) \<le> e7"
"\<forall>i \<in> I. neg_depth_conjunct (\<psi>s i) \<le> e8"
    using assms leq_not_eneg by force+
  hence sups: "Sup ((modal_depth_srbb_conjunct \<circ> \<psi>s) ` I) \<le> e1"
"Sup ((branch_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e2"
"Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> (e3-1)"
"Sup ((st_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e4"
"Sup ((imm_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e5"
"Sup ((max_pos_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e6"
"Sup ((max_neg_conj_depth_conjunct \<circ> \<psi>s) ` I) \<le> e7"
"Sup ((neg_depth_conjunct \<circ> \<psi>s) ` I) \<le> e8"
    by (simp add: Sup_le_iff)+
  hence "inst_conj_depth_inner (Conj I \<psi>s) \<le> e3" 
    using \<open>e - E 0 0 1 0 0 0 0 0 = E e1 e2 (e3-1) e4 e5 e6 e7 e8\<close> \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> \<open>inst_conj_depth_inner (Conj I \<psi>s) = 1 + Sup ((inst_conj_depth_conjunct \<circ> \<psi>s) ` I)\<close>
    sorry

  then show ?thesis
    using conj_upds sups 
    by (simp add: \<open>e = E e1 e2 e3 e4 e5 e6 e7 e8\<close> leq_not_eneg)
qed
qed

lemma winning_budget_implies_strategy_formula:
  fixes g e
  assumes "in_wina e g"
  shows
    "(\<exists>p Q. g = Attacker_Immediate p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Delayed p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p q. g = Attacker_Clause p q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e)"
    "(\<exists>p Q. g = Defender_Conj p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p Q. g =  Defender_Stable_Conj p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p \<alpha> p' Q Qa. g = Defender_Branch p \<alpha> p' Q Qa) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Branch p Q) \<Longrightarrow> \<exists>p Q. (g = Attacker_Branch p Q \<and> (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e- E 1 0 0 0 0 0 0 0) \<phi> \<and> expressiveness_price \<phi> \<le> (e- E 1 0 0 0 0 0 0 0)))"

using assms proof(induction rule: in_wina.induct)
  case (1 g e)
  {
    case 1
    then show ?case 
      using "1.hyps" by force
  next
    case 2
    then show ?case 
      using "1.hyps" by force
  next
    case 3
    then show ?case 
      using "1.hyps" by force
  next
    case 4
    from 4 obtain p Q where G: "g = Defender_Conj p Q"
    by auto
    from assms have A: "in_wina e (Defender_Conj p Q)"
    using "1" G in_wina.intros(1) by blast 
    have "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)"
      using "1" A by blast
    hence "(\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)" by auto
    hence "\<forall>g'. spectroscopy_moves g g' = None" by blast
    hence A1: "\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' = None"
      using \<open>g = Defender_Conj p Q\<close> by blast
    have "\<forall>q\<in>Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = None"
      using A1 by blast
    hence "Q = {}" using local.conj_s_answer 
      by simp
    hence "\<exists>\<Phi>.\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"
      by (simp add: emptyE)
    from this obtain \<Phi> where "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)" by auto
     hence Strat: "strategy_formula_inner (Defender_Conj p Q) e (Conj {} \<Phi>)"
       using \<open>Q = {}\<close> conj by blast
     then have  "modal_depth_srbb_inner (Conj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)"
                "branch_conj_depth_inner (Conj Q \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                "inst_conj_depth_inner (Conj Q \<Phi>) = 0"
                "st_conj_depth_inner (Conj Q \<Phi>) = Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                "imm_conj_depth_inner (Conj Q \<Phi>) = Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                "max_pos_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                "max_neg_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                "neg_depth_inner (Conj Q \<Phi>) = Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q)"
     using modal_depth_srbb_inner.simps(3) branch_conj_depth_inner.simps st_conj_depth_inner.simps
      inst_conj_depth_inner.simps imm_conj_depth_inner.simps max_pos_conj_depth_inner.simps
      max_neg_conj_depth_inner.simps neg_depth_inner.simps \<open>Q = {}\<close>
     by auto+
      hence "modal_depth_srbb_inner (Conj Q \<Phi>) = 0"
          "branch_conj_depth_inner (Conj Q \<Phi>) = 0"
          "inst_conj_depth_inner (Conj Q \<Phi>) = 0"
          "st_conj_depth_inner (Conj Q \<Phi>) = 0"
          "imm_conj_depth_inner (Conj Q \<Phi>) = 0"
          "max_pos_conj_depth_inner (Conj Q \<Phi>) = 0"
          "max_neg_conj_depth_inner (Conj Q \<Phi>) = 0"
          "neg_depth_inner (Conj Q \<Phi>) = 0"

      using \<open>Q = {}\<close> image_empty comp_apply
      by (simp add: bot_enat_def)+
       hence "expr_pr_inner (Conj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)"
      using expr_pr_inner.simps \<open>Q = {}\<close>
      by force
    have "(e - (E 0 0 0 0 0 0 0 0)) = e"
      by (simp add: "1" leq_not_eneg minus_energy_def)
    have Win_a: "\<forall>q \<in> Q. in_wina e (Attacker_Clause p q)"  by (metis A1 local.conj_answer option.discI)
    have NotWin_a: "\<forall>q \<in> Q. \<not>(in_wina eneg (Attacker_Clause p q))"
      by (simp add: defender_win_level_not_in_wina)
    have B: "\<not>(in_wina eneg (Defender_Conj p Q))"
      by (simp add: defender_win_level_not_in_wina)
    from A B have "e \<noteq> eneg" by auto
    hence price: "expr_pr_inner (Conj Q \<Phi>) \<le> e"
      using \<open>expr_pr_inner (hml_srbb_inner.Conj Q \<Phi>) = E 0 0 0 0 0 0 0 0\<close> minus_energy_def
      using \<open>e - E 0 0 0 0 0 0 0 0 = e\<close> by presburger
    with Strat price have "(\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
      using G \<open>Q = {}\<close> by blast
    hence "\<exists>\<Phi>.\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"
      by (simp add: \<open>Q = {}\<close>)
    from this obtain \<Phi> where "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)" by auto
     hence Strat: "strategy_formula (Defender_Conj p Q) e (ImmConj {} \<Phi>)"
       using \<open>Q = {}\<close> imm_conj by blast
     then have "modal_depth_srbb (ImmConj  {}  \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ>  \<Phi>) ` {})"
               "branching_conjunction_depth (ImmConj {}  \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ>  \<Phi>) ` {})" 
               "instable_conjunction_depth (ImmConj {}  \<Phi>) =
                  (if {} = {}
                    then 0
                   else 1 + Sup ((inst_conj_depth_conjunct \<circ>  \<Phi>) ` {}))"
                "stable_conjunction_depth (ImmConj {} \<Phi>) = Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                "immediate_conjunction_depth (ImmConj {}  \<Phi>) =
                  (if {} = {}
                    then 0
                   else 1 + Sup ((imm_conj_depth_conjunct \<circ>  \<Phi>) ` {}))"
                "max_positive_conjunct_depth (ImmConj {} \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                "max_negative_conjunct_depth (ImmConj {} \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                "negation_depth (ImmConj {}  \<Phi>) = Sup ((neg_depth_conjunct \<circ>  \<Phi>) ` {})"
     using modal_depth_srbb_inner.simps(3) branch_conj_depth_inner.simps st_conj_depth_inner.simps
      inst_conj_depth_inner.simps imm_conj_depth_inner.simps max_pos_conj_depth_inner.simps
      max_neg_conj_depth_inner.simps neg_depth_inner.simps \<open>Q = {}\<close>
     by auto+
      hence   "modal_depth_srbb (ImmConj  {}  \<Phi>) = 0"
               "branching_conjunction_depth (ImmConj {}  \<Phi>) = 0" 
               "instable_conjunction_depth (ImmConj {}  \<Phi>) = 0"
                "stable_conjunction_depth (ImmConj {} \<Phi>) = 0"
                "immediate_conjunction_depth (ImmConj {}  \<Phi>) = 0"
                "max_positive_conjunct_depth (ImmConj {} \<Phi>) = 0"
                "max_negative_conjunct_depth (ImmConj {} \<Phi>) = 0"
                "negation_depth (ImmConj {}  \<Phi>) = 0"
      using \<open>Q = {}\<close> image_empty comp_apply
      by (simp add: bot_enat_def)+
      hence "expressiveness_price (ImmConj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)"
      using expr_pr_inner.simps \<open>Q = {}\<close>
      by force
      have "(e - (E 0 0 0 0 0 0 0 0)) = e"
      by (simp add: "1" leq_not_eneg minus_energy_def)
      from A B have "e \<noteq> eneg" by auto
      hence price: "expressiveness_price (ImmConj Q \<Phi>) \<le> e"
        using \<open>expressiveness_price (ImmConj Q \<Phi>) = E 0 0 0 0 0 0 0 0\<close> minus_energy_def
        using \<open>e - E 0 0 0 0 0 0 0 0 = e\<close> by presburger
    then show ?case
      using G Strat \<open>Q = {}\<close> \<open>\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e\<close> by blast
  next
    case 5
    then obtain p Q where "g = Defender_Stable_Conj p Q" by blast
    hence "\<forall>q\<in>Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) = None"
      using "1" by blast
    hence "Q = {}" using local.conj_s_answer 
      by simp
    hence "spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p Q) \<noteq> None"
      by simp
    hence False 
      using "1" \<open>g = Defender_Stable_Conj p Q\<close> by blast
    then show ?case by blast
  next
    case 6
    from 6 obtain p \<alpha> p' Q Qa  where G: "g =  Defender_Branch p \<alpha> p' Q Qa"
      by auto
    have "p'=p' \<and> Qa \<mapsto>aS \<alpha>(soft_step_set Qa \<alpha>)"
      by (simp add: soft_step_set_is_soft_step_set)
    hence A: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
      by simp
    from 1 have "(\<forall>g'. \<not> spectroscopy_moves g g' \<noteq> None)" by simp
    hence "False" using A using G by blast 
    thus ?case by simp
  next
    case 7
    then show ?case 
      using "1.hyps" by force
  }
next
  case (2 g e)
  {
    case 1 
    then obtain p Q where "g =  Attacker_Immediate p Q" by blast
    hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g')))"
      using energy_game.in_wina_Ga energy_game_axioms "2" 
      by blast
    then obtain g' where move: "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Immediate p Q) g') e) g') \<and>
    ((\<exists>p Q. g' = Defender_Conj p Q) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)) \<and> 
    ((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e))" 
      using in_wina.cases 1 "2" 
      by (metis \<open>g = Attacker_Immediate p Q\<close>)     
      from move have move_cases: "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
        using spectroscopy_moves.simps
        by (smt (verit) spectroscopy_defender.elims(1))
      have IH: "((\<exists>p' Q'. g' = Defender_Conj p Q) \<longrightarrow> 
                  ((\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
                        expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e)))"
        using \<open>g = Attacker_Immediate p Q\<close> move
        by force

      have IH_att_del: "((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow> (\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
                          expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e))"
        using "2" move 
        using \<open>g = Attacker_Immediate p Q\<close> 
        by fastforce
      show ?case using move_cases
      proof(rule disjE)
        assume "\<exists>p' Q'. g' = Attacker_Delayed p' Q'"
        then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
        have "(the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e) = (id e)"
          by (smt (verit, ccfv_threshold) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay g'_att_del move option.exhaust_sel option.inject)
        have "p' = p"
          by (metis \<open>g' = Attacker_Delayed p' Q'\<close> move spectroscopy_moves.simps(1))
        have "(in_wina e (Attacker_Delayed p Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> move update_gets_smaller win_a_upwards_closure 
          by blast
        from IH_att_del g'_att_del have "(\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
          expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e)"
          using \<open>in_wina e (Attacker_Delayed p Q')\<close> 
          using \<open>p' = p\<close> 
          using \<open>g = Attacker_Immediate p Q\<close> move by blast
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
          using \<open>p' = p\<close> \<open>weight (Attacker_Immediate p Q) (Attacker_Delayed p' Q') e = id e\<close> g'_att_del by auto
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))) \<and> (in_wina e (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))"
          using g'_att_del
          by (smt (verit) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay \<open>in_wina e (Attacker_Delayed p Q')\<close> move)

        hence "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
        have "expressiveness_price (Internal \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)\<close>
          by auto
        then show ?case 
          using \<open>strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)\<close>
          using \<open>g = Attacker_Immediate p Q\<close> by blast
    next
      assume "\<exists>p' Q'. g' = Defender_Conj p' Q'"
      then obtain p' Q' where g'_def_conj: "g' = Defender_Conj p' Q'" by blast
      from g'_def_conj show ?case
        proof(cases "Q = {} \<and> Q' = {}")
          case True
          hence "p = p'"
            by (metis \<open>g' = Defender_Conj p' Q'\<close> move spectroscopy_moves.simps(4))
          with True have 
              "(the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')) e) = id e"
            by simp
          have "(in_wina e (Defender_Conj p Q))"
            using True \<open>g' = Defender_Conj p' Q'\<close> \<open>p = p'\<close> move by auto
          with IH g'_def_conj have IH_case: "(\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
            expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e)"
            using \<open>g' = Defender_Conj p' Q'\<close>
            using \<open>g = Attacker_Immediate p Q\<close> move by force
        have "(in_wina e (Defender_Conj p Q'))"
          using \<open>g' = Defender_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
          by blast

      (* here Q=Q'={} holds and (Defender_Conj p Q') is a leaf *)



(*
        hence "(\<exists>\<phi>. strategy_formula (Defender_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
          using \<open>in_wina e (Defender_Conj p Q')\<close> IH_case 
          using \<open>p = p'\<close> \<open>weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e = id e\<close> g'_def_conj by auto
         then obtain \<phi> where "(strategy_formula (Defender_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
            by blast
  
          hence "strategy_formula (Attacker_Immediate p Q) e \<phi>"
            using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj True
            by (metis \<open>in_wina e (Defender_Conj p Q')\<close> local.finishing_or_early_conj)
          have "expressiveness_price \<phi> \<le> e"
            using \<open>strategy_formula (Defender_Conj p Q') e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close> by blast
          then show ?thesis
            using \<open>strategy_formula (Attacker_Immediate p Q) e \<phi>\<close> 
            using \<open>g = Attacker_Immediate p Q\<close> by blast
*)      
          thus ?thesis sorry
        next
          case False
          hence "p = p'" "Q = Q'"
            using \<open>g' = Defender_Conj p' Q'\<close> move spectroscopy_moves.simps
             apply (metis (mono_tags, lifting))
            using \<open>g' = Defender_Conj p' Q'\<close> move spectroscopy_moves.simps False
            by (smt (verit, best))
          with False have 
              "(the (spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')) e) 
                = e - (E 0 0 0 0 1 0 0 0)"
            by simp
          have "(in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q'))"
            using \<open>g' = Defender_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
            using \<open>weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e = e - E 0 0 0 0 1 0 0 0\<close> by force

          with IH g'_def_conj have IH_case: "(\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
            expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e)"
            using \<open>g = Attacker_Immediate p Q\<close> move by auto
          hence "(\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expr_pr_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            using \<open>in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q')\<close> IH_case 
            using \<open>Q = Q'\<close> \<open>p = p'\<close> \<open>weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e = e - E 0 0 0 0 1 0 0 0\<close> g'_def_conj by auto
          then obtain \<phi> where S: "(strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expr_pr_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            by blast
          hence "\<exists>\<psi>. \<phi>= Conj Q \<psi>" using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj
            by (smt (verit) \<open>Q = Q'\<close> \<open>p = p'\<close> g'_def_conj move spectroscopy_defender.simps(4) spectroscopy_defender.simps(6) spectroscopy_moves.simps(60) spectroscopy_moves.simps(70) spectroscopy_position.inject(6) strategy_formula_inner.simps)
          then obtain \<psi> where "\<phi>= Conj Q \<psi>" by auto
          hence "strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) (ImmConj Q \<psi>)" using S strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj strategy_formula_strategy_formula_inner_strategy_formula_conjunct.imm_conj
            by (smt (verit) \<open>Q = Q'\<close> \<open>p = p'\<close> g'_def_conj hml_srbb_inner.inject(2) move spectroscopy_defender.simps(4) spectroscopy_defender.simps(6) spectroscopy_moves.simps(60) spectroscopy_moves.simps(70) strategy_formula_inner.cases) 
          hence SI: "strategy_formula (Attacker_Immediate p Q) e (ImmConj Q \<psi>)"
            using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj False \<open>Q = Q'\<close>
            by (metis (no_types, lifting) \<open>in_wina (e - E 0 0 0 0 1 0 0 0) (Defender_Conj p Q')\<close> local.finishing_or_early_conj)

          have "expr_pr_inner (Conj Q \<psi>) \<le> (e - (E 0 0 0 0 1 0 0 0))" using S \<open>\<phi> = Conj Q \<psi>\<close> by simp
          
          hence "expressiveness_price (ImmConj Q \<psi>) \<le> e" using expr_imm_conj False \<open>Q = Q'\<close>
            by metis

          thus ?thesis using SI
            using \<open>g = Attacker_Immediate p Q\<close> by blast
        qed
      qed
  next
    case 2
    then obtain p Q where g_att_del: "g = Attacker_Delayed p Q" by blast
    hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Delayed p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Delayed p Q) g') e) g')))"
      using energy_game_axioms 2 "2.IH" by blast
    then obtain g' where move: "((spectroscopy_moves (Attacker_Delayed p Q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Delayed p Q) g') e) g')" 
      and IH: "((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
                   (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                         expr_pr_inner \<phi> \<le> weight g g' e))"
      "(\<exists>p' Q'. g' = (Attacker_Immediate p' Q')) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and>
                               expressiveness_price \<phi> \<le> weight g g' e)"
      "(\<exists>p Q. g' = (Defender_Conj p Q)) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                               expr_pr_inner \<phi> \<le> weight g g' e)"
      "(\<exists>p Q. g' = (Defender_Stable_Conj p Q)) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                               expr_pr_inner \<phi> \<le> weight g g' e)"
      "(\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                               expr_pr_inner \<phi> \<le> weight g g' e)"
      using in_wina.cases 2 "2.IH" \<open>g = Attacker_Delayed p Q\<close>
      by metis
    hence move_cases: "(\<exists>p Q. g' = Attacker_Delayed p Q) \<or> (\<exists>p' Q'. g' = (Attacker_Immediate p' Q')) \<or> 
      (\<exists>p Q. g' = (Defender_Conj p Q)) \<or> (\<exists>p Q. g' = (Defender_Stable_Conj p Q)) \<or> (\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
      by (metis spectroscopy_defender.cases spectroscopy_moves.simps(53) spectroscopy_moves.simps(59))

    then consider (Att_Del) "(\<exists>p Q. g' = Attacker_Delayed p Q)" | (Att_Imm) "(\<exists>p' Q'. g' = (Attacker_Immediate p' Q'))" |
                  (Def_Conj) "(\<exists>p Q. g' = (Defender_Conj p Q))" | (Def_St_Conj) "(\<exists>p Q. g' = (Defender_Stable_Conj p Q))" |
                  (Def_Branch) "(\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
      by blast
    then show ?case proof(cases)
      case Att_Del
      assume "\<exists>p Q. g' = Attacker_Delayed p Q"
      then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" and
                          IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                          expr_pr_inner \<phi> \<le> weight g g' e)" using IH by blast

      show "\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e"
      proof-
        have "Q' = Q" "p \<noteq> p'" "p \<mapsto> \<tau> p'"
          using move g'_att_del Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.procrastination
          by metis+
        hence "(the (spectroscopy_moves (Attacker_Delayed p Q) g') e) = id e"
          using g'_att_del \<open>Q' = Q\<close> \<open>p \<noteq> p'\<close> \<open>p \<mapsto> \<tau> p'\<close>
          by simp
        have "(in_wina (id e) (Attacker_Delayed p' Q'))"
          using g'_att_del \<open>Q' = Q\<close> \<open>p \<noteq> p'\<close> \<open>p \<mapsto> \<tau> p'\<close> "2.IH" \<open>g = Attacker_Delayed p Q\<close> id_apply in_wina.intros(2)
          using \<open>weight (Attacker_Delayed p Q) g' e = id e\<close> move by presburger

        have "(weight g g' e) = e"
          using g'_att_del g_att_del
          using \<open>weight (Attacker_Delayed p Q) g' e = id e\<close> by fastforce

        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
          using IH g'_att_del   
          by auto 

        hence "(\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) 
         = (Some id) \<and> in_wina e (Attacker_Delayed p' Q)
          \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>)"
          using \<open>(in_wina (id e) (Attacker_Delayed p' Q'))\<close> g'_att_del \<open>Q' = Q\<close> \<open>p \<noteq> p'\<close> \<open>p \<mapsto> \<tau> p'\<close> local.procrastination
          move
          by (metis Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.procrastination \<open>weight g g' e = e\<close> g_att_del)
         hence "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
          using \<open>Q' = Q\<close> \<open>in_wina (id e) (Attacker_Delayed p' Q')\<close> \<open>strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close> \<open>weight (Attacker_Delayed p Q) g' e = id e\<close> \<open>weight g g' e = e\<close> g_att_del local.procrastination strategy_formula_strategy_formula_inner_strategy_formula_conjunct.procrastination
          by blast

        have "expr_pr_inner \<chi> \<le> e"
          using \<open>strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close> by blast

        then show ?thesis 
          using \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close> g_att_del by blast
      qed
    next
      case Att_Imm
(* Needs to be updated according to the changed definition of observation *)

      assume "\<exists>p' Q'. g' = Attacker_Immediate p' Q'"
      then obtain p' Q' where g'_att_imm: "g' = Attacker_Immediate p' Q'" and
                          IH: "(\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and>
                          expressiveness_price \<phi> \<le> weight g g' e)" using IH by blast 
      have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') \<noteq> None" using move \<open>g' = Attacker_Immediate p' Q'\<close>
        by simp
      hence "(\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q')" using spectroscopy_moves.simps(3) by metis 
      then obtain \<alpha> where \<alpha>_prop: "p \<mapsto>a \<alpha> p'" "Q \<mapsto>aS \<alpha> Q'" by blast
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')) e) = (e - (E 1 0 0 0 0 0 0 0))"
        by fastforce
      hence "(in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q'))"
        using g'_att_imm \<open>p \<mapsto>a \<alpha> p'\<close> \<open>Q \<mapsto>aS \<alpha> Q'\<close> "2.IH" \<open>g = Attacker_Delayed p Q\<close> id_apply in_wina.intros(2) move
        by presburger

      have "(weight g g' e) = (e - (E 1 0 0 0 0 0 0 0))"
        using g'_att_imm g_att_del
        using \<open>weight (Attacker_Delayed p Q) (Attacker_Immediate p' Q') e = e - E 1 0 0 0 0 0 0 0\<close> by blast

      then obtain \<phi> where \<phi>_prop: "(strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
        using IH g'_att_imm
        by auto 
      hence "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
       = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')"
        using \<open>\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q'\<close> \<open>in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q')\<close> by auto 
      hence "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
       = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')" by blast
      hence "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
         = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
          \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
          \<and> p \<mapsto>a\<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'"
        using \<alpha>_prop(1) \<alpha>_prop(2) \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and> in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q')\<close> \<phi>_prop by blast
      hence "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)"
        using local.observation 
        by presburger
      have "expr_pr_inner (Obs \<alpha> \<phi>) \<le> e" using expr_obs \<phi>_prop 
        by auto
      then show ?thesis using \<open>strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)\<close>
        using g_att_del by blast
    next
      case Def_Conj
      assume "\<exists>p Q. g' = Defender_Conj p Q"
      then obtain p' Q' where g'_def_conj: "g' = Defender_Conj p' Q'" and
                          IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)" 
        using IH by blast
      have "p = p'" "Q = Q'" 
        using \<open>g' = Defender_Conj p' Q'\<close> local.late_inst_conj move by presburger+
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')) e) = (id e)"
        by fastforce
      hence "(in_wina e (Defender_Conj p' Q'))" using id_apply
        using \<open>g' = Defender_Conj p' Q'\<close> move by auto
      have "(weight g g' e) = e" 
        using \<open>g' = Defender_Conj p' Q'\<close> \<open>weight (Attacker_Delayed p Q) (Defender_Conj p' Q') e = id e\<close> g_att_del by force
      
      then obtain \<chi> where \<chi>_prop: "(strategy_formula_inner (Defender_Conj p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using IH g'_def_conj
        by auto 

      hence "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q') 
       = (Some id) \<and> in_wina e (Defender_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Conj p' Q') e \<chi>"
        by (simp add: \<open>Q = Q'\<close> \<open>in_wina e (Defender_Conj p' Q')\<close> \<open>p = p'\<close>)

      then show ?thesis using \<chi>_prop 
        using \<open>Q = Q'\<close> \<open>in_wina e (Defender_Conj p' Q')\<close> \<open>p = p'\<close> full_spec_game.late_conj full_spec_game_axioms g_att_del by fastforce
    next
      case Def_St_Conj
      assume "\<exists>p Q. g' = Defender_Stable_Conj p Q"
      then obtain p' Q' where "g' = Defender_Stable_Conj p' Q'" and
        IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)"
        using IH by blast

      hence "(p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p''))"
        using local.late_stbl_conj \<open>g' = Defender_Stable_Conj p' Q'\<close> g_att_del move
        by meson

      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')) e) = (id e)"
        by auto

      hence "(in_wina e (Defender_Stable_Conj p' Q'))" using id_apply
        using \<open>g' = Defender_Stable_Conj p' Q'\<close> move by auto

      have "(weight g g' e) = e" 
        using \<open>g' = Defender_Stable_Conj p' Q'\<close> \<open>weight (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') e = id e\<close> g_att_del by force
        
      then obtain \<chi> where \<chi>_prop: "(strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using IH \<open>g' = Defender_Stable_Conj p' Q'\<close>
        by auto 
      hence expr: "expr_pr_inner \<chi> \<le> e" by blast

      from \<chi>_prop have "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') 
       = (Some id) \<and> in_wina e (Defender_Stable_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>"
        using \<open>g' = Defender_Stable_Conj p' Q'\<close> \<open>in_wina e (Defender_Stable_Conj p' Q')\<close> local.late_stbl_conj move
        by meson

      hence "strategy_formula_inner g e \<chi>"
        using g_att_del local.stable 
        by (metis (no_types, lifting) local.late_stbl_conj option.distinct(1))
      
      then show ?thesis using expr g_att_del 
        by blast

    next
      case Def_Branch
      then obtain p' \<alpha> p'' Q' Q\<alpha> where g'_def_br: "g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>" and
        IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)"
        using IH by blast

      hence "(p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p'' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q)"
        using local.br_conj move by metis
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) e) = (id e)"
        by auto

      hence "(in_wina e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))" using id_apply
        using g'_def_br move by auto

      have "(weight g g' e) = e" 
        using g'_def_br g_att_del \<open>weight (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e = id e\<close> by fastforce
        
      then obtain \<chi> where \<chi>_prop: "(strategy_formula_inner (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using IH g'_def_br
        by auto 
      hence expr: "expr_pr_inner \<chi> \<le> e" by blast

      from \<chi>_prop have "\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) 
       = (Some id) \<and> in_wina e (Defender_Branch p \<alpha> p' Q' Q\<alpha>)
        \<and> strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi>"
        using g'_def_br \<open>in_wina e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)\<close> local.branch move
        by (metis local.br_conj)

      hence "strategy_formula_inner g e \<chi>"
        using g_att_del local.stable 
        using branch by presburger
      
      then show ?thesis using expr g_att_del 
        by blast
    qed

  next

    case 3
    then obtain p q where "g = Attacker_Clause p q" by blast
    hence "(\<exists>g'. (((spectroscopy_moves (Attacker_Clause p q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Clause p q) g') e) g')))"
      using energy_game_axioms 3 "2" 
      by metis
    then obtain g' where move: "((spectroscopy_moves (Attacker_Clause p q) g')\<noteq>None) \<and> (in_wina (the (spectroscopy_moves (Attacker_Clause p q) g') e) g')" 
      and IH: "(\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
                   (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                         expr_pr_inner \<phi> \<le> weight g g' e)"
      using in_wina.cases 3 "2" \<open>g = Attacker_Clause p q\<close> 
      by metis
    hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q'))"
      using spectroscopy_moves.simps move spectroscopy_moves.elims
      by (smt (verit) spectroscopy_defender.elims(1))
    then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'"
      and IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and>
                         expr_pr_inner \<phi> \<le> weight g g' e)" using IH by blast
    show ?case
    proof(cases \<open>p = p'\<close>)
      case True
      hence "{q} \<Zsurj>S Q'"
        using g'_att_del local.pos_neg_clause move by presburger

      have "(\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
      = (Some min1_6)))"
          by auto
        hence "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = min1_6 e"
          using True \<open>{q} \<Zsurj>S Q'\<close> g'_att_del
          by simp
      have "(in_wina (min1_6 e) (Attacker_Delayed p Q'))"
        using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>{q} \<Zsurj>S Q'\<close> move update_gets_smaller win_a_upwards_closure 
        by (simp add: True)
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and> expr_pr_inner \<chi> \<le> (min1_6 e))"
          using IH True \<open>g = Attacker_Clause p q\<close> \<open>weight (Attacker_Clause p q) g' e = min1_6 e\<close> g'_att_del by auto
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
        = (Some (min1_6))) \<and> (in_wina (min1_6 e) (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi>))"
          by (meson \<open>in_wina (min1_6 e) (Attacker_Delayed p Q')\<close> \<open>{q} \<Zsurj>S Q'\<close> local.pos_neg_clause)
        hence "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
          using pos by blast

        have "expr_pr_conjunct (Pos \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and> expr_pr_inner \<chi> \<le> (min1_6 e))\<close> expr_pos 
          by blast 
        then show ?thesis 
          using \<open>strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)\<close>
          using \<open>g = Attacker_Clause p q\<close> by blast
      next
        case False
        hence "{p} \<Zsurj>S Q'"
          using g'_att_del local.pos_neg_clause move by presburger

        have "p' = q"
          using False 
          using g'_att_del local.pos_neg_clause move by presburger

        have "(\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
        = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))))"  
          using False \<open>p' = q\<close> by auto
        hence "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = (min1_7 (e - E 0 0 0 0 0 0 0 1))"
          using False \<open>{p} \<Zsurj>S Q'\<close> g'_att_del \<open>p' = q\<close>
          by simp
        have "(in_wina ((min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed p' Q'))"
          using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>{p} \<Zsurj>S Q'\<close> move update_gets_smaller win_a_upwards_closure False \<open>p' = q\<close>
          by auto
        
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<phi> \<and> expr_pr_inner \<phi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          using \<open>in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')\<close> IH 
          using strategy_formula_conjunct.simps 
          using \<open>g = Attacker_Clause p q\<close> \<open>weight (Attacker_Clause p q) g' e = min1_7 (e - E 0 0 0 0 0 0 0 1)\<close> g'_att_del by auto
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and> expr_pr_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          by blast
        hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
        = (Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)))) \<and> (in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi>))"
          using \<open>in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed p' Q')\<close> local.pos_neg_clause
          using False \<open>{p} \<Zsurj>S Q'\<close> \<open>p' = q\<close> by fastforce

        hence "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
          using neg \<open>p' = q\<close> by blast

        have "expr_pr_conjunct (Neg \<chi>) \<le> e"
          using \<open>(strategy_formula_inner (Attacker_Delayed p' Q') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and> expr_pr_inner \<chi> \<le> (min1_7 (e - E 0 0 0 0 0 0 0 1)))\<close>
        expr_neg
          by blast
        
        then show ?thesis 
          using \<open>strategy_formula_conjunct (Attacker_Clause p q) e (hml_srbb_conjunct.Neg \<chi>)\<close>
          using \<open>g = Attacker_Clause p q\<close> by blast 
      qed
  next
    case 4
    hence "\<not>attacker g" 
      by auto
    with "2" have False by blast
    then show ?case by blast
  next
    case 5
    hence "\<not>attacker g" 
      by auto
    with "2" have False by blast
    then show ?case by blast
  next
    case 6
    hence "\<not>attacker g" 
      by auto
    with "2" have False by blast
    then show ?case by blast
  next
    case 7
    then obtain p Q where "g=Attacker_Branch p Q " by auto

    from 2 obtain g' where IH: "spectroscopy_moves g g' \<noteq> None \<and>
        in_wina (weight g g' e) g' \<and>
        (((\<exists>p Q. g' = Attacker_Immediate p Q) \<longrightarrow>
          (\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> weight g g' e)) \<and>
         ((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
          (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)) \<and>
         ((\<exists>p q. g' = Attacker_Clause p q) \<longrightarrow>
          (\<exists>\<phi>. strategy_formula_conjunct g' (weight g g' e) \<phi> \<and> expr_pr_conjunct \<phi> \<le> weight g g' e))) \<and>
        (((\<exists>p Q. g' = Defender_Conj p Q) \<longrightarrow>
          (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)) \<and>
         ((\<exists>p Q. g' = Defender_Stable_Conj p Q) \<longrightarrow>
          (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e))) \<and>
        ((\<exists>p \<alpha> p' Q Qa. g' = Defender_Branch p \<alpha> p' Q Qa) \<longrightarrow>
         (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e)) \<and>
        ((\<exists>p Q. g' = Attacker_Branch p Q) \<longrightarrow>
         (\<exists>p Q. g' = Attacker_Branch p Q \<and>
                (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (weight g g' e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                      expressiveness_price \<phi> \<le> weight g g' e - E 1 0 0 0 0 0 0 0)))" by auto
    hence N: "spectroscopy_moves (Attacker_Branch p Q) g' \<noteq> None " using \<open>g=Attacker_Branch p Q \<close> by simp

    hence "g'=(Attacker_Immediate p Q)" using br_acct using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(17) spectroscopy_moves.simps(51) spectroscopy_moves.simps(57) spectroscopy_moves.simps(61) spectroscopy_moves.simps(66) spectroscopy_moves.simps(71)) 
     hence "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0" using \<open>g=Attacker_Branch p Q\<close> by simp

     from N have " \<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> weight g g' e" using \<open>g=Attacker_Branch p Q \<close> IH \<open>g' = Attacker_Immediate p Q\<close> by auto
     then obtain \<phi> where "strategy_formula g' (weight g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> weight g g' e" by auto
     hence "(strategy_formula (Attacker_Immediate p Q) (e- E 1 0 0 0 0 0 0 0) \<phi> ) \<and> (expressiveness_price \<phi> \<le> (e- E 1 0 0 0 0 0 0 0))" 
       using \<open>spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0\<close> \<open>g'=(Attacker_Immediate p Q)\<close> by simp
     hence "(g=Attacker_Branch p Q) \<and> (strategy_formula (Attacker_Immediate p Q) (e- E 1 0 0 0 0 0 0 0) \<phi> ) \<and> (expressiveness_price \<phi> \<le> (e- E 1 0 0 0 0 0 0 0))" using \<open>g=Attacker_Branch p Q\<close> by simp
     thus ?case by auto
  }
next
  case (3 g e)
  {
    case 1
    then show ?case 
      using "3" by force
  next
    case 2
    then show ?case using "3" 
      by force
  next
    case 3
    then show ?case
      using "3.IH" by force
  next
    case 4
    from 4 obtain p Q where "g = Defender_Conj p Q" by auto
    hence "\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (in_wina (the (spectroscopy_moves (Defender_Conj p Q) g') e) g') \<and> (\<exists>q. g' = (Attacker_Clause p q))"
      using "3"
      by (metis "4" \<open>\<And>thesis. (\<And>p Q. g = Defender_Conj p Q \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> local.conj_answer spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(36) spectroscopy_moves.simps(48) spectroscopy_moves.simps(54) spectroscopy_moves.simps(64) spectroscopy_moves.simps(69) spectroscopy_moves.simps(74))

    then show ?case proof(cases "Q = {}")
      case True
      hence "\<exists>\<Phi>.\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
            = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
              \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"
        by (simp add: emptyE)
      from this obtain \<Phi> where "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
            = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
              \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)" by auto
       hence Strat: "strategy_formula_inner (Defender_Conj p Q) e (Conj {} \<Phi>)"
         using \<open>Q = {}\<close> conj by blast
       then have  "modal_depth_srbb_inner (Conj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)"
                  "branch_conj_depth_inner (Conj Q \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                  "inst_conj_depth_inner (Conj Q \<Phi>) = 0"
                  "st_conj_depth_inner (Conj Q \<Phi>) = Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                  "imm_conj_depth_inner (Conj Q \<Phi>) = Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                  "max_pos_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                  "max_neg_conj_depth_inner (Conj Q \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
                  "neg_depth_inner (Conj Q \<Phi>) = Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q)"
       using modal_depth_srbb_inner.simps(3) branch_conj_depth_inner.simps st_conj_depth_inner.simps
        inst_conj_depth_inner.simps imm_conj_depth_inner.simps max_pos_conj_depth_inner.simps
        max_neg_conj_depth_inner.simps neg_depth_inner.simps \<open>Q = {}\<close>
       by auto+
        hence "modal_depth_srbb_inner (Conj Q \<Phi>) = 0"
            "branch_conj_depth_inner (Conj Q \<Phi>) = 0"
            "inst_conj_depth_inner (Conj Q \<Phi>) = 0"
            "st_conj_depth_inner (Conj Q \<Phi>) = 0"
            "imm_conj_depth_inner (Conj Q \<Phi>) = 0"
            "max_pos_conj_depth_inner (Conj Q \<Phi>) = 0"
            "max_neg_conj_depth_inner (Conj Q \<Phi>) = 0"
            "neg_depth_inner (Conj Q \<Phi>) = 0"
  
        using \<open>Q = {}\<close> image_empty comp_apply
        by (simp add: bot_enat_def)+
         hence "expr_pr_inner (Conj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)"
        using expr_pr_inner.simps \<open>Q = {}\<close>
        by force
      have "(e - (E 0 0 0 0 0 0 0 0)) = e" 
        by (simp add: "3" leq_not_eneg minus_energy_def)
      hence price: "expr_pr_inner (Conj Q \<Phi>) \<le> e"
        using \<open>expr_pr_inner (hml_srbb_inner.Conj Q \<Phi>) = E 0 0 0 0 0 0 0 0\<close> minus_energy_def \<open>e - E 0 0 0 0 0 0 0 0 = e\<close> "3" 
        by presburger
      with Strat price have "(\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
        using \<open>Q = {}\<close> \<open>g = Defender_Conj p Q\<close> by blast
      have "\<exists>\<Phi>.\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
            = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
              \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"
        by (simp add: \<open>Q = {}\<close>)
      from this obtain \<Phi> where "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
            = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
              \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)" by auto
       hence Strat: "strategy_formula (Defender_Conj p Q) e (ImmConj {} \<Phi>)"
         using \<open>Q = {}\<close> imm_conj by blast
       hence Strat: "strategy_formula (Defender_Conj p Q) e (ImmConj {} \<Phi>)"
         using \<open>Q = {}\<close> imm_conj by blast
       then have "modal_depth_srbb (ImmConj  {}  \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ>  \<Phi>) ` {})"
                 "branching_conjunction_depth (ImmConj {}  \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ>  \<Phi>) ` {})" 
                 "instable_conjunction_depth (ImmConj {}  \<Phi>) =
                    (if {} = {}
                      then 0
                     else 1 + Sup ((inst_conj_depth_conjunct \<circ>  \<Phi>) ` {}))"
                  "stable_conjunction_depth (ImmConj {} \<Phi>) = Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                  "immediate_conjunction_depth (ImmConj {}  \<Phi>) =
                    (if {} = {}
                      then 0
                     else 1 + Sup ((imm_conj_depth_conjunct \<circ>  \<Phi>) ` {}))"
                  "max_positive_conjunct_depth (ImmConj {} \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                  "max_negative_conjunct_depth (ImmConj {} \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` {})"
                  "negation_depth (ImmConj {}  \<Phi>) = Sup ((neg_depth_conjunct \<circ>  \<Phi>) ` {})"
       using modal_depth_srbb_inner.simps(3) branch_conj_depth_inner.simps st_conj_depth_inner.simps
        inst_conj_depth_inner.simps imm_conj_depth_inner.simps max_pos_conj_depth_inner.simps
        max_neg_conj_depth_inner.simps neg_depth_inner.simps \<open>Q = {}\<close>
       by auto+
        hence   "modal_depth_srbb (ImmConj  {}  \<Phi>) = 0"
                 "branching_conjunction_depth (ImmConj {}  \<Phi>) = 0" 
                 "instable_conjunction_depth (ImmConj {}  \<Phi>) = 0"
                  "stable_conjunction_depth (ImmConj {} \<Phi>) = 0"
                  "immediate_conjunction_depth (ImmConj {}  \<Phi>) = 0"
                  "max_positive_conjunct_depth (ImmConj {} \<Phi>) = 0"
                  "max_negative_conjunct_depth (ImmConj {} \<Phi>) = 0"
                  "negation_depth (ImmConj {}  \<Phi>) = 0"
        using \<open>Q = {}\<close> image_empty comp_apply
        by (simp add: bot_enat_def)+
        hence "expressiveness_price (ImmConj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)"
        using expr_pr_inner.simps \<open>Q = {}\<close>
        by force
        have "(e - (E 0 0 0 0 0 0 0 0)) = e"
        by (simp add: "3" leq_not_eneg minus_energy_def)
        hence price: "expressiveness_price (ImmConj Q \<Phi>) \<le> e"
          using \<open>expressiveness_price (ImmConj Q \<Phi>) = E 0 0 0 0 0 0 0 0\<close> minus_energy_def \<open>e - E 0 0 0 0 0 0 0 0 = e\<close> "3" 
          by presburger
      then show ?thesis
        using Strat True \<open>\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e\<close> \<open>g = Defender_Conj p Q\<close> 
        by blast
    next
      case False
      assume assm: "Q \<noteq> {}"
      hence "(\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (\<exists>q. g' = Attacker_Clause p q))"
        using \<open>\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> in_wina (weight (Defender_Conj p Q) g' e) g' \<and> (\<exists>q. g' = Attacker_Clause p q)\<close> by blast
      hence fa_q: "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 1 0 0 0 0 0) \<and> in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)"
        using \<open>g = Defender_Conj p Q\<close> 
        using \<open>\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> in_wina (weight (Defender_Conj p Q) g' e) g' \<and> (\<exists>q. g' = Attacker_Clause p q)\<close> 
        by force 
      hence "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 1 0 0 0 0 0)" by blast
      hence "\<forall>q \<in> Q. \<exists>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None" 
        by blast
      hence "\<forall>q \<in> Q. \<exists>g'. in_wina (weight g g' e) g' \<and> (\<exists>\<phi>. strategy_formula_conjunct g' (weight g g' e) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g g' e)"
        using "3" \<open>g = Defender_Conj p Q\<close> assm 
        by (metis \<open>\<forall>q\<in>Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = subtract 0 0 1 0 0 0 0 0\<close> option.distinct(1))
      hence "\<forall>q \<in> Q. in_wina (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q) \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q) e)" 
        by (metis "3" \<open>\<forall>q\<in>Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = subtract 0 0 1 0 0 0 0 0 \<and> in_wina (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q)\<close> \<open>g = Defender_Conj p Q\<close> option.distinct(1) option.sel)

      hence "\<exists>\<Phi>. \<forall>q \<in> Q. in_wina (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q) \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q) \<and>
                  expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e)"
        by meson 

      hence "\<exists>\<Phi>. \<forall>q \<in> Q. in_wina (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q) \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q) \<and>
                  expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))"
        using \<open>g = Defender_Conj p Q\<close> by auto
      then obtain \<Phi> where IH: "\<forall>q \<in> Q. in_wina (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q) \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q) \<and>
                  expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))" by auto

      hence "strategy_formula_inner g e (Conj Q \<Phi>)"
        by (simp add: \<open>g = Defender_Conj p Q\<close> conj)
      from IH have "expr_pr_inner (Conj Q \<Phi>) \<le> e" using expr_conj \<open>Q \<noteq> {}\<close>
        by metis
      thus ?thesis using \<open>strategy_formula_inner g e (Conj Q \<Phi>)\<close> by auto
    qed
  next
    case 5
    then obtain p Q where "g = Defender_Stable_Conj p Q" by blast
    hence cases: "\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (in_wina (the (spectroscopy_moves (Defender_Stable_Conj p Q) g') e) g') \<and>((\<exists>p' q. g' = (Attacker_Clause p' q)) \<or> (\<exists>p' Q'. g' = (Defender_Conj p' Q')))"
      using spectroscopy_defender.cases spectroscopy_moves.simps(42) spectroscopy_moves.simps(49) spectroscopy_moves.simps(55) spectroscopy_moves.simps(65) spectroscopy_moves.simps(75)
      by (metis "3")
    have "Q = {} \<or> (Q \<noteq> {} \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (\<exists>p' q. g' = (Attacker_Clause p' q))))"
      by (metis \<open>g = Defender_Stable_Conj p Q\<close> cases local.empty_stbl_conj_answer)
    then show ?case proof(rule disjE)
      assume "Q = {}"
      hence \<Phi>_ex: "\<exists>\<Phi>. (spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p Q) 
    = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)
      \<and> strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 1 0 0 0 0)) (Conj Q \<Phi>))"
        using conj
        by (metis "3" \<open>g = Defender_Stable_Conj p Q\<close> all_not_in_conv local.empty_stbl_conj_answer option.sel option.simps(3))
      hence "in_wina (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)" by blast

      from \<Phi>_ex obtain \<Phi> where \<Phi>_prop: "(spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p Q) 
    = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)
      \<and> strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 1 0 0 0 0)) (Conj Q \<Phi>))"
        by blast
      hence "strategy_formula_inner g e (StableConj Q \<Phi>)" 
        using \<open>g = Defender_Stable_Conj p Q\<close> stable_conj_answer by blast
      have "\<nexists>p' q. p = p' \<and> q \<in> Q" using \<open>Q = {}\<close> 
        by blast
      hence "\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' = None"
      proof-
        have "\<forall>g'. (spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<longrightarrow> (\<exists>p' q. g' = (Attacker_Clause p' q)))"
          by (metis spectroscopy_defender.cases spectroscopy_moves.simps(36) spectroscopy_moves.simps(48) spectroscopy_moves.simps(54) spectroscopy_moves.simps(64) spectroscopy_moves.simps(69) spectroscopy_moves.simps(74))
        with \<open>\<nexists>p' q. p = p' \<and> q \<in> Q\<close> show ?thesis 
          by auto
      qed
      hence "(e - (E 0 0 0 1 0 0 0 0)) \<noteq> eneg" 
        using \<open>in_wina (e - E 0 0 0 1 0 0 0 0) (Defender_Conj p Q)\<close> in_wina.simps by blast
      hence "e \<ge> (E 0 0 0 1 0 0 0 0)" 
        by (meson minus_energy_def)

      have "expr_pr_inner (StableConj Q \<Phi>) = E (Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (1 + Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q))" by simp
      hence "expr_pr_inner (StableConj Q \<Phi>) = E 0 0 0 1 0 0 0 0" using \<open>Q={}\<close>
        by (simp add: bot_enat_def) 
      then show ?thesis using \<open>e \<ge> (E 0 0 0 1 0 0 0 0)\<close> \<open>strategy_formula_inner g e (StableConj Q \<Phi>)\<close>
        by metis
    next
      assume assm: "Q \<noteq> {} \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (\<exists>p' q. g' = Attacker_Clause p' q))"
      have fa_q: "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)"
        using \<open>g = Defender_Stable_Conj p Q\<close> cases by force
      hence "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0)" by blast
      hence "\<forall>q \<in> Q. \<exists>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None" 
        by blast
      hence "\<forall>q \<in> Q. \<exists>g'. in_wina (weight g g' e) g' \<and> (\<exists>\<phi>. strategy_formula_conjunct g' (weight g g' e) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g g' e)"
        using "3" \<open>g = Defender_Stable_Conj p Q\<close> cases
        by (metis assm)
      hence IH: "\<forall>q \<in> Q. in_wina (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q) \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q) e)" 
        by (metis "3" \<open>\<forall>q\<in>Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) = subtract 0 0 0 1 0 0 0 0 \<and> in_wina (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q)\<close> \<open>g = Defender_Stable_Conj p Q\<close> option.distinct(1) option.sel)

      hence "\<exists>\<Phi>. \<forall>q \<in> Q. in_wina (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q) \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
                  expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e)"
        by meson 
      hence "\<exists>\<Phi>. (\<forall>q \<in> Q. strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)
              \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
              expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e))"
        using "3" \<open>g = Defender_Stable_Conj p Q\<close> cases  
        by meson
      hence "\<exists>\<Phi>. (\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)
          \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
              expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e))"
        using fa_q by blast
      then obtain \<Phi> where \<Phi>_prop: "(\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)
          \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
              expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e))"
        by blast
      hence "\<forall>q \<in> Q. expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 0 0 1 0 0 0 0))" 
        by (simp add: \<open>g = Defender_Stable_Conj p Q\<close>)
      hence "expr_pr_inner (StableConj Q \<Phi>) \<le> e"
        using expr_st_conj assm 
        by metis
      then show ?thesis using \<Phi>_prop 
        using \<open>g = Defender_Stable_Conj p Q\<close> stable_conj by blast
    qed
  next
    case 6
    then obtain p \<alpha> p' Q Qa where "g = Defender_Branch p \<alpha> p' Q Qa " by auto
    hence M: "\<forall>q\<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) = (subtract 0 1 1 0 0 0 0 0)"
      by simp 
    hence "\<forall>q\<in>Q. (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q)  (weight g (Attacker_Clause p q)  e) \<phi> \<and> expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q)  e)"
      using "3" \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> by (metis option.distinct(1)) 
    (* take those formulas somehow...HML Magic? *)

    from M have "\<forall>q \<in> Q. in_wina (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)" using assms
      by (metis "3" \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> option.distinct(1) option.sel) 
    hence A: "\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> in_wina (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q)" using M  sorry (* using HML magic *)
    



    have E: "\<exists>p Q. Attacker_Branch p' (soft_step_set Qa \<alpha>) = Attacker_Branch p Q" by auto

    have M: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) =Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
      by (simp add: soft_step_set_is_soft_step_set) 
    hence "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) \<noteq> None"
      by (simp add: option.discI) 
    hence "(\<exists>p Q. (Attacker_Branch p' (soft_step_set Qa \<alpha>)) = Attacker_Branch p Q \<and>
                  (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0))" using E 3 \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close>
      by (metis (no_types, lifting) spectroscopy_position.inject(2))
    then obtain p'' Q'' where IH2: "(Attacker_Branch p' (soft_step_set Qa \<alpha>)) = Attacker_Branch p'' Q'' \<and>
                  (\<exists>\<phi>. strategy_formula (Attacker_Immediate p'' Q'') (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0)" by auto
    hence "p''=p'" and "Q'' = (soft_step_set Qa \<alpha>)" by auto
    then obtain \<phi> where "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0" using IH2 by auto
    hence "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))  \<phi> \<and>
                        expressiveness_price \<phi> \<le> ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) " using M
      by (simp add: \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> comp_apply option.sel) 
    hence A1: "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))  \<phi>" by simp

    have A2: "spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) = (subtract 1 0 0 0 0 0 0 0)" by simp

    from M have "in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0))) (Attacker_Branch p' (soft_step_set Qa \<alpha>))" using assms
      by (metis "3" E \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> bot_enat_def comp_apply option.distinct(1) option.sel)
    hence "\<exists>g''. ((spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None) \<and> (in_wina ((weight (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'') (min1_6 (e - E 0 1 1 0 0 0 0 0))) g''))" 
      using in_wina.simps
      by (meson spectroscopy_defender.simps(2)) 
    then obtain g'' where X: "((spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None) \<and> (in_wina ((weight (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'') (min1_6 (e - E 0 1 1 0 0 0 0 0))) g''))" by auto
    hence "g''= (Attacker_Immediate p' (soft_step_set Qa \<alpha>))" using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(17) spectroscopy_moves.simps(51) spectroscopy_moves.simps(57) spectroscopy_moves.simps(61) spectroscopy_moves.simps(66) spectroscopy_moves.simps(71)) 
    hence "(in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))
                  (Attacker_Immediate p' (soft_step_set Qa \<alpha>)))" using X A1
      by (simp add: A2 option.sel)

    hence "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' (soft_step_set Qa \<alpha>)))
            \<and> strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>" using M A2 A1 by auto

    hence E: "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' Q') 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>"
      by blast 
    
    hence S: "strategy_formula_inner g e (BranchConj \<alpha> \<phi> Q \<Phi>)" using A E branch_conj
      by (simp add: \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close>) 

    have "expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) =  E (modal_depth_srbb_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (branch_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (inst_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (st_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (imm_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (max_pos_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (max_neg_conj_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))
                 (neg_depth_inner (BranchConj \<alpha> \<phi> Q \<Phi>))" by simp
    hence "expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) =  E ( Sup ({1 + modal_depth_srbb \<phi>} \<union> ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)))
                 ((if Q = {}
                  then branching_conjunction_depth \<phi>
                  else 1 + Sup ({branching_conjunction_depth \<phi>} \<union> ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q))))
                 ( Sup ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 ( 1 + Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 (Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q))
                 ( Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q))" sorry


    have "expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e" sorry

    then show ?case using S by blast
  next
    case 7
    hence "attacker g"
      by auto
    then show ?case using 3
      by blast
  }
qed

lemma strategy_formulas_distinguish:
  shows "(strategy_formula g e \<phi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  distinguishes_from \<phi> p Q
      | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q
      | _ \<Rightarrow> True))
      \<and> 
      (strategy_formula_inner g e \<chi> \<longrightarrow>
        (case g of
       Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>((p \<mapsto> \<alpha> p') \<and> (Qa \<noteq> {})) \<longrightarrow> distinguishes_from_inner \<chi> p (Q\<union>Qa)
      | _ \<Rightarrow> True))
      \<and>
      (strategy_formula_conjunct g e \<psi> \<longrightarrow>
        (case g of
        Attacker_Clause p q \<Rightarrow> distinguishes_conjunct \<psi> p q
      | _ \<Rightarrow> True))"
proof(induction rule: strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct)
  case (delay p Q e \<chi>)
  then show ?case
    by (smt (verit) distinguishes_from_def option.discI silent_reachable.intros(1) silent_reachable_trans spectroscopy_moves.simps(1) spectroscopy_position.simps(50) spectroscopy_position.simps(53))
next
  case (procrastination p Q e \<chi>)
  from this obtain p' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = Some id \<and>
       in_wina e (Attacker_Delayed p' Q) \<and>
       strategy_formula_inner (Attacker_Delayed p' Q) e \<chi> \<and>
       (case Attacker_Delayed p' Q of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p' Q"
    using spectroscopy_position.simps(53) by fastforce
  from IH have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = Some id" by auto
  hence "p \<Zsurj>p'"
    by (metis option.discI silent_reachable.intros(1) silent_reachable_append_\<tau> spectroscopy_moves.simps(2)) 
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q" using D
    by (smt (verit, del_insts) distinguishes_def distinguishes_from_def hml_models.simps(3) hml_srbb_models.elims(2) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(2) silent_reachable_trans)
  then show ?case by simp
next
  case (observation p Q e \<phi> \<alpha>)
  then obtain p' Q' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and>
     in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
     (strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
      (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<phi> p Q
       | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q | _ \<Rightarrow> True)) \<and>
     p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'" by auto
  hence D: "distinguishes_from \<phi> p' Q'" by auto 
  hence "p' \<Turnstile>SRBB \<phi>" using distinguishes_from_def by auto

  have observation: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
      = (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then (subtract 1 0 0 0 0 0 0 0) else None)"
    for p p' Q Q' by simp
  from IH have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
    = subtract 1 0 0 0 0 0 0 0" by simp
  also have "... \<noteq> None" by blast
  finally have "(\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q')" unfolding observation by metis
  
  from IH have "p \<mapsto>a \<alpha> p'" and "Q \<mapsto>aS \<alpha> Q'"  by auto
  hence P: "p \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))" using \<open>p' \<Turnstile>SRBB \<phi>\<close>
    using silent_reachable.intros(1) by auto
  have "Q \<Zsurj>S Q \<longrightarrow> (\<forall>q\<in>Q. \<not>(q \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))))" proof (rule impI)
    assume "Q \<Zsurj>S Q"
    show "\<forall>q\<in>Q. \<not> q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" proof 
      fix q 
      show "q \<in> Q \<Longrightarrow> \<not> q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" proof 
        assume "q \<in> Q" and "q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" 
        hence "\<exists>q'.  q \<Zsurj> q' \<and> hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by simp 
        then obtain q' where X: "q \<Zsurj> q' \<and> hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by auto
        hence "hml_srbb_inner_models (Obs \<alpha> \<phi>) q'" by simp
        hence "q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))"
          by simp

        from X have "q'\<in>Q" using \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
        hence "\<exists>q''\<in>Q'. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" using \<open>Q \<mapsto>aS \<alpha> Q'\<close> \<open>q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))\<close>
          by (smt (verit, del_insts) D dist_from_srbb_eq_dist_from_hml distinguishes_from_hml_def hml_models.simps(2) hml_models.simps(4))
        then obtain q'' where "q''\<in>Q'\<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" by auto
        thus "False" using D
          using distinguishes_from_def by auto
      qed
    qed
  qed
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal (hml_srbb_inner.Obs \<alpha> \<phi>)) p Q" using P
    by (meson distinguishes_def distinguishes_from_def)
  then show ?case by simp
next
  case (early_conj Q p Q' e \<phi>)
  then show ?case
    by (smt (verit, del_insts) local.finishing_or_early_conj option.distinct(1) spectroscopy_position.simps(50) spectroscopy_position.simps(55))
next
  case (late_conj p Q e \<chi>)
  hence "distinguishes_from_inner \<chi> p Q" by simp
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q"
    by (metis distinguishes_from_def distinguishes_from_inner_def hml_models.simps(3) hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_models.simps hml_srbb_to_hml.simps(2) silent_reachable.intros(1))
  then show ?case by simp 
next
  case (conj Q p e \<Phi>)
  hence A: "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto
  hence P: "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p" using distinguishes_conjunct_def by simp
  hence "\<forall>q\<in>Q. distinguishes_inner (hml_srbb_inner.Conj Q \<Phi>) p q" using A srbb_dist_conjunct_implies_dist_conjunction by simp
  hence "distinguishes_from_inner (hml_srbb_inner.Conj Q \<Phi>) p Q" using distinguishes_from_inner_def P
    by (metis dist_from_inner_srbb_eq_dist_from_hml distinguishes_from_hml_def distinguishes_from_inner'_def distinguishes_from_inner_prime empty_iff hml_models.simps(1) hml_srbb_inner_to_hml.simps(2) tt_eq_empty_conj) 
  then show ?case by simp 
next
  case (imm_conj Q p e \<Phi>)
  hence D: "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto
  hence "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p" using distinguishes_conjunct_def by simp
  hence "\<forall>q\<in>Q. distinguishes (ImmConj Q \<Phi>) p q" using D srbb_dist_conjunct_implies_dist_imm_conjunction by simp
  hence "distinguishes_from (ImmConj Q \<Phi>) p Q" using distinguishes_from_def
    by (metis distinguishes_from'_def distinguishes_from_prime empty_iff hml_models.simps(1) hml_srbb_models.elims(3) hml_srbb_to_hml.simps(3) tt_eq_empty_conj) 
  then show ?case by simp 
next
  case (pos p q e \<chi>)
  then obtain Q' where IH: "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') = Some min1_6 \<and>
       in_wina (min1_6 e) (Attacker_Delayed p Q') \<and>
       strategy_formula_inner (Attacker_Delayed p Q') (min1_6 e) \<chi> \<and>
       (case Attacker_Delayed p Q' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "Q' \<Zsurj>S Q' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q'" by simp
  have "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q')= Some min1_6" using IH by simp
  hence "{q} \<Zsurj>S Q'" using spectroscopy_moves.simps
    by (metis (no_types, lifting) option.discI) 
  have "Q' \<Zsurj>S Q' \<longrightarrow> q \<in> Q'"
    by (simp add: \<open>{q} \<Zsurj>S Q'\<close> silent_reachable.intros(1)) 
  hence "distinguishes_conjunct (hml_srbb_conjunct.Pos \<chi>) p q" using D \<open>{q} \<Zsurj>S Q'\<close>
    by (smt (verit, ccfv_threshold) LTS_Tau.silent_reachable_trans distinguishes_conjunct_def distinguishes_def distinguishes_from_def hml_conjunct_models.simps(1) hml_srbb_conjunct_models.elims(2) hml_srbb_conjunct_models.elims(3) hml_srbb_conjunct_to_hml_conjunct.simps(1) hml_srbb_models.elims(1) hml_srbb_to_hml.simps(2) silent_reachable.intros(1)) 
  then show ?case by simp
next
  case (neg p q e \<chi>)
  then obtain P' where IH: "(spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') = Some (min1_7 \<circ> (\<lambda>x. x - E 0 0 0 0 0 0 0 1)) \<and>
        in_wina (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed q P')) \<and>
       strategy_formula_inner (Attacker_Delayed q P') (min1_7 (e - E 0 0 0 0 0 0 0 1)) \<chi> \<and>
       (case Attacker_Delayed q P' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence D: "P' \<Zsurj>S P' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) q P'" by simp
  from IH have "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') = Some (min1_7 \<circ> (\<lambda>x. x - E 0 0 0 0 0 0 0 1))" by auto
  hence "{p} \<Zsurj>S P'" using spectroscopy_moves.simps
    by (metis (no_types, lifting) not_Some_eq) 
  have "P' \<Zsurj>S P' \<longrightarrow> p \<in> P'" using \<open>{p} \<Zsurj>S P'\<close>  by (simp add: silent_reachable.intros(1)) 
  hence "distinguishes_conjunct (hml_srbb_conjunct.Neg \<chi>) p q" using D \<open>{p} \<Zsurj>S P'\<close>
    by (metis LTS_Tau.silent_reachable_trans distinguishes_conjunct_def distinguishes_from_def hml_conjunct_models.simps(2) hml_srbb_conjunct_models.elims(2) hml_srbb_conjunct_models.elims(3) hml_srbb_conjunct_to_hml_conjunct.simps(2) hml_srbb_models.elims(1) hml_srbb_to_hml.simps(2) silent_reachable.intros(1)) 
  then show ?case by simp
next
  case (stable p Q e \<chi>)
  then obtain Q' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some id \<and>
       in_wina e (Defender_Stable_Conj p Q') \<and>
       strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi> \<and>
       (case Defender_Stable_Conj p Q' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence M:"spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some id" by simp
  hence "(\<nexists>p''. p \<mapsto>\<tau> p'')"
    by (metis local.late_stbl_conj option.distinct(1)) 

  from IH have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q'" by simp
  hence "distinguishes_from_inner \<chi> p Q'" using \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close> by auto
  hence "hml_srbb_inner_models \<chi> p"
    by (simp add: distinguishes_from_inner_def)
  hence "p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)"
    using hml_impl_iffI pre_\<epsilon> by auto

  have "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q" proof
    assume "Q \<Zsurj>S Q"
    have "(\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>)))" proof
      fix q
      assume "q \<in> Q"
      show "\<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))" proof
        assume "(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))"
        hence "\<exists>q'. q \<Zsurj> q' \<and> (q' \<Turnstile> (hml_srbb_inner_to_hml \<chi>))" by auto
        hence "\<exists>q'. q \<Zsurj> q' \<and> (hml_srbb_inner_models \<chi> q')" by simp
        then obtain q' where X:"q \<Zsurj> q' \<and> (hml_srbb_inner_models \<chi> q')" by auto
        hence "q' \<in> Q" using \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
        then show "False" proof(cases "q' \<in> Q'")
          case True (* stable cases *)
          thus "False" using X \<open>distinguishes_from_inner \<chi> p Q'\<close>
            by (simp add: distinguishes_from_inner_def)
        next
          case False (* instable cases *)
          from IH have "strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>" by simp
          hence "\<exists>\<Phi>. \<chi>=(StableConj Q' \<Phi>)" using strategy_formula_inner.simps
            by (smt (verit) spectroscopy_position.distinct(35) spectroscopy_position.distinct(39) spectroscopy_position.distinct(41) spectroscopy_position.inject(7))
          then obtain \<Phi> where P: "\<chi>=(StableConj Q' \<Phi>)" by auto

          from M have "Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}"
            by (metis (full_types) local.late_stbl_conj option.distinct(1))
          hence "\<exists>q''. q' \<mapsto>\<tau> q''" using False \<open>q' \<in> Q\<close> by simp

          from X have "(hml_srbb_inner_models (StableConj Q' \<Phi>) q')" using P by auto
          hence "q' \<Turnstile> (hml_conjunct.Neg (hml.Obs \<tau> hml.TT)
     \<and>hml hml_conjunct.Pos (hml.Conj Q' (hml_srbb_conjunct_to_hml_conjunct \<circ> \<Phi>)))" by simp

          then show ?thesis using \<open>\<exists>q''. q' \<mapsto>\<tau> q''\<close> by simp
        qed
      qed
    qed
    thus "distinguishes_from (hml_srbb.Internal \<chi>) p Q" using \<open>p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)\<close>
      by (simp add: distinguishes_from_def)
  qed
  then show ?case by simp
next
  case (stable_conj Q p e \<Phi>)
  hence IH: "\<forall>q\<in> Q. distinguishes_conjunct (\<Phi> q) p q" by simp
  hence Q: "\<forall>q \<in> Q. hml_srbb_conjunct_models (\<Phi> q) p"
    by (simp add: distinguishes_conjunct_def) 
  have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner (StableConj Q \<Phi>) p Q" proof
    assume "(\<forall>q. \<not> p \<mapsto>\<tau> q)"
    thus  "distinguishes_from_inner (StableConj Q \<Phi>) p Q" using IH Q srbb_dist_conjunct_or_stable_implies_dist_stable_conjunction
      by (smt (verit, ccfv_threshold) LTS_Tau.hml_models.simps(2) dist_from_inner_srbb_eq_dist_from_hml distinguishes_from_hml_def distinguishes_from_inner'_def distinguishes_from_inner_prime distinguishes_inner_def hml_conjunct_models.simps(1) hml_conjunct_models.simps(2) hml_models.simps(1) hml_models.simps(5) hml_srbb_inner_models.elims(3) hml_srbb_inner_to_hml.simps(3) tt_eq_empty_conj) 
  qed
  then show ?case by simp
next
  case (stable_conj_answer p Q e \<Phi>)
  hence  "distinguishes_from_inner (hml_srbb_inner.Conj Q \<Phi>) p Q" by simp
  hence IH: "hml_srbb_inner_models (hml_srbb_inner.Conj Q \<Phi>) p \<and> (\<forall>q \<in> Q. \<not>(hml_srbb_inner_models (hml_srbb_inner.Conj Q \<Phi>) q))"
    by (simp add: distinguishes_from_inner_def)
  hence "hml_srbb_inner_models (hml_srbb_inner.Conj Q \<Phi>) p " by simp
  hence "p \<Turnstile>  hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> \<Phi>)" by simp
  hence "\<forall>i \<in> Q. hml_conjunct_models p ((hml_srbb_conjunct_to_hml_conjunct \<circ> \<Phi>) i)" by simp
  hence IH1: "hml_conjunct_models p (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> \<Phi>)))" by simp

  have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner (StableConj Q \<Phi>) p Q" proof
    assume "(\<forall>q. \<not> p \<mapsto>\<tau> q)"
    hence "hml_conjunct_models p (hml_conjunct.Neg (hml.Obs \<tau> hml.TT))" by simp
    hence "hml_srbb_inner_models (StableConj Q \<Phi>) p" using IH1 by simp
    have "(\<forall>q \<in> Q. \<not>(hml_srbb_inner_models (StableConj Q \<Phi>) q))" proof
      fix q 
      assume "q\<in> Q"
      hence "\<not>(hml_srbb_inner_models (hml_srbb_inner.Conj Q \<Phi>) q)" using IH by simp
      hence "\<not> (hml_conjunct_models q (hml_conjunct.Pos (hml.Conj Q (hml_srbb_conjunct_to_hml_conjunct \<circ> \<Phi>))))" by simp
      thus "\<not>(hml_srbb_inner_models (StableConj Q \<Phi>) q)"
        using hml_and_and hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps(3) by presburger 
    qed
    thus "distinguishes_from_inner (StableConj Q \<Phi>) p Q" using \<open>hml_srbb_inner_models (StableConj Q \<Phi>) p\<close>
      using distinguishes_from_inner_def by blast 
  qed
  then show ?case by simp
next
  case (branch p Q e \<chi>)
  then obtain p' Q' \<alpha> Q\<alpha> where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id \<and>
     in_wina e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) \<and>
     strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi> \<and>
     (case Defender_Branch p \<alpha> p' Q' Q\<alpha> of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by blast
  hence "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id" by simp
  hence "p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {}"
    by (metis local.br_conj option.distinct(1)) 
  from IH have "p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" by simp
  hence D: "distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" using \<open>p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close> by auto

  from IH have "Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q"
    by (metis local.br_conj option.distinct(1))
  hence "Q=(Q' \<union> Q\<alpha>)" by auto
  hence "distinguishes_from_inner \<chi> p Q" using D by auto
  hence " Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q"
    using dist_from_inner_srbb_eq_dist_from_hml dist_from_srbb_eq_dist_from_hml distinguishes_from_hml_def hml_impl_iffI pre_\<epsilon> by auto 
  then show ?case by simp
next
  case (branch_conj p \<alpha> p' Q1 Q\<alpha> e \<psi> \<Phi>)
  hence A1: "\<forall>q\<in>Q1. hml_srbb_conjunct_models (\<Phi> q) p" by (simp add: distinguishes_conjunct_def)

  from branch_conj obtain Q' where IH: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q') =
         Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0)) \<and>
         spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and>
         in_wina (min1_6 (e - E 0 1 1 0 0 0 0 0) - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
         strategy_formula (Attacker_Immediate p' Q') (min1_6 (e - E 0 1 1 0 0 0 0 0) - E 1 0 0 0 0 0 0 0) \<psi> \<and>
         (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<psi> p Q
          | Defender_Conj p Q \<Rightarrow> distinguishes_from \<psi> p Q | _ \<Rightarrow> True)" by auto
  hence " distinguishes_from \<psi> p' Q'" by simp
  hence X:"p' \<Turnstile>SRBB \<psi>" by (simp add: distinguishes_from_def) 
  have Y: "\<forall>q \<in> Q'. \<not>(q \<Turnstile>SRBB \<psi>)" using \<open>distinguishes_from \<psi> p' Q'\<close>  by (simp add: distinguishes_from_def) 

  have "(p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}) \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>) " proof
    assume "p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}"
    hence "p \<mapsto> \<alpha> p'" by simp
    from IH have "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q') =
         Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0))" by auto
    hence "Q\<alpha> \<mapsto>aS \<alpha> Q'"
      by (metis local.br_obsv option.distinct(1))

    hence A2: "hml_srbb_inner_models (Obs \<alpha> \<psi>) p" using X \<open>p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close>  by auto  

    have A3: "\<forall>q \<in> (Q1 \<union> Q\<alpha>). distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" proof
      fix q
      assume "q\<in>(Q1 \<union> Q\<alpha>)"     
      show "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" proof (cases "q\<in>Q1")
        case True
        hence  "distinguishes_conjunct (\<Phi> q) p q" using branch_conj(2) by simp
        thus "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction True by blast
      next
        case False
        hence "q\<in> Q\<alpha>" using \<open>q\<in>(Q1 \<union> Q\<alpha>)\<close> by simp
        have "\<not>(hml_srbb_inner_models (Obs \<alpha> \<psi>) q)" proof
          assume "hml_srbb_inner_models (Obs \<alpha> \<psi>) q"
          hence "q \<Turnstile> ( HML_soft_poss \<alpha> (hml_srbb_to_hml \<psi>))" by simp
          hence "\<exists>q'. q\<mapsto>a \<alpha> q' \<and> (q' \<Turnstile>SRBB \<psi>)"
            by (smt (verit) hml_models.simps(2) hml_models.simps(4) hml_srbb_models.elims(3)) 
          then obtain q' where Z: "q\<mapsto>a \<alpha> q' \<and> (q' \<Turnstile>SRBB \<psi>)" by auto
          hence "q' \<in> Q' " using \<open>q\<in> Q\<alpha>\<close> \<open>Q\<alpha> \<mapsto>aS \<alpha> Q'\<close>
            by blast
          from Z have "\<not>(q' \<in> Q')" using Y
            by auto
          thus "False"
            by (simp add: \<open>q' \<in> Q'\<close>) 
        qed
        hence "distinguishes_inner (Obs \<alpha> \<psi>) p q" using A2
          by (simp add: distinguishes_inner_def) 
        thus  "distinguishes_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q" using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction by blast    
      qed
    qed

    from \<open>p \<mapsto> \<alpha> p' \<and> Q\<alpha> \<noteq> {}\<close> have "\<exists>qa. qa \<in> Q\<alpha>" by auto
    then obtain qa where "qa \<in> Q\<alpha>" by auto
    hence A4: "hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) p" using A3
      by (meson Un_iff distinguishes_inner_def) 

    from A3 have "\<forall>q \<in> (Q1 \<union> Q\<alpha>). \<not>(hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) q)"
      using distinguishes_inner_def by blast 

    thus "distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)" using A4 distinguishes_from_inner_def by simp 
  qed 
  then show ?case by simp
qed

theorem spectroscopy_game_correctness:
  shows "(\<exists>\<phi> \<in> \<O> e. distinguishes_from \<phi> p Q)
       = (in_wina e (Attacker_Immediate p Q))"
proof
  assume "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
  then obtain \<phi> where
    "distinguishes_from \<phi> p Q" and le: "expressiveness_price \<phi> \<le> e"
    unfolding \<O>_def by blast 
  from distinction_implies_winning_budgets this(1)
    have budget: "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)" .
  thus "in_wina e (Attacker_Immediate p Q)" using win_a_upwards_closure le by simp
next
  assume "in_wina e (Attacker_Immediate p Q)"
  with winning_budget_implies_strategy_formula
    have "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" by force
  hence "\<exists>\<phi>\<in>\<O> e. strategy_formula (Attacker_Immediate p Q) e \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by fastforce 
qed


end (* context full_spec_game *)

end
