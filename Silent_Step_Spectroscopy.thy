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
  oops

lemma winning_budget_implies_strategy_formula:
  fixes g e
  assumes "in_wina e g"
  shows
    "(\<exists>p Q. g = Attacker_Immediate p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Delayed p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p q. g = Attacker_Clause p q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e)"
    "(\<exists>p Q. g = Defender_Conj p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>  (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
    "(\<exists>p Q. g =  Defender_Stable_Conj p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p \<alpha> p' Q Qa. g = Defender_Branch p \<alpha> p' Q Qa) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Branch p Q) \<Longrightarrow> True"
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
    then show ?case using Strat 
      price sorry
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
    from assms have A: "in_wina e ( Defender_Branch p \<alpha> p' Q Qa)"
    using "1" G in_wina.intros(1) by blast 
    have "in_wina e (Defender_Branch p \<alpha> p' Q Qa) = (spectroscopy_defender g) \<and> (\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)"
      using "1" A by blast
    hence "(\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)" by auto
    hence "\<forall>g'. spectroscopy_moves g g' = None" by blast
    hence A1: "\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) g' = None"
      using \<open>g =  Defender_Branch p \<alpha> p' Q Qa\<close> by blast
    have "\<forall>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' Q') = None"
      using A1 by blast
    from this obtain Q' where "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' Q') = None" by auto
    (*hence "\<exists>\<psi>. (\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p q) 
        = subtract 1 0 0 0 0 0 0 0 
            \<and> (in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') e \<psi>)"
      by blast*)
    then show ?case sorry
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
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e) \<and> 
      (\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> weight g g' e)) \<and> 
    ((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
      (\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e))" 
      using in_wina.cases 1 "2" 
      by (metis \<open>g = Attacker_Immediate p Q\<close>)     
      from move have move_cases: "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
        using spectroscopy_moves.simps
        by (smt (verit) spectroscopy_defender.elims(1))
      have IH: "((\<exists>p' Q'. g' = Defender_Conj p Q) \<longrightarrow> 
                  ((\<exists>\<phi>. strategy_formula_inner g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
                        expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e) \<and>
                  (\<exists>\<phi>. strategy_formula g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight (Attacker_Immediate p Q) g' e)))"
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
            expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e) \<and>
            (\<exists>\<phi>. strategy_formula g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
            expressiveness_price \<phi> \<le> weight (Attacker_Immediate p Q) g' e)"
            using \<open>g' = Defender_Conj p' Q'\<close>
            using \<open>g = Attacker_Immediate p Q\<close> move by force
        have "(in_wina e (Defender_Conj p Q'))"
          using \<open>g' = Defender_Conj p' Q'\<close> \<open>p = p'\<close> move update_gets_smaller win_a_upwards_closure 
          by blast
          
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
            expr_pr_inner \<phi> \<le> weight (Attacker_Immediate p Q) g' e) \<and>
            (\<exists>\<phi>. strategy_formula g' (weight (Attacker_Immediate p Q) g' e) \<phi> \<and>
            expressiveness_price \<phi> \<le> weight (Attacker_Immediate p Q) g' e)"
            using \<open>g = Attacker_Immediate p Q\<close> move by auto

          hence "(\<exists>\<phi>. strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            using \<open>in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q')\<close> IH_case 
            using \<open>Q = Q'\<close> \<open>p = p'\<close> \<open>weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e = e - E 0 0 0 0 1 0 0 0\<close> g'_def_conj by auto

          then obtain \<phi> where "(strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
            by blast
          hence "strategy_formula (Attacker_Immediate p Q) e \<phi>"
            using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj False \<open>Q = Q'\<close>
            by (metis (no_types, lifting) \<open>in_wina (e - E 0 0 0 0 1 0 0 0) (Defender_Conj p Q')\<close> local.finishing_or_early_conj)
          have "expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))"
            using \<open>strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0))\<close>
            by blast
          then show ?thesis
            using \<open>strategy_formula (Attacker_Immediate p Q) e \<phi>\<close> 
            using gets_smaller transitivity 
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
                               expr_pr_inner \<phi> \<le> weight g g' e) \<and>
                         (\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and>
                               expressiveness_price \<phi> \<le> weight g g' e)"
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
      assume "\<exists>p' Q'. g' = Attacker_Immediate p' Q'"
      then obtain p' Q' where g'_att_imm: "g' = Attacker_Immediate p' Q'" and
                          IH: "(\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and>
                          expressiveness_price \<phi> \<le> weight g g' e)" using IH by blast 
      hence "(\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>)" using local.observation move g_att_del 
        by (smt (verit, best) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.observation)
      then obtain \<alpha> where \<alpha>_prop: "p \<mapsto> \<alpha> p'" "Q \<mapsto>S \<alpha> Q'" "\<alpha> \<noteq> \<tau>" by blast
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')) e) = (e - (E 1 0 0 0 0 0 0 0))"
        by fastforce
      hence "(in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q'))"
        using g'_att_imm \<open>p \<mapsto> \<alpha> p'\<close> \<open>Q \<mapsto>S \<alpha> Q'\<close> \<open>\<alpha> \<noteq> \<tau>\<close> "2.IH" \<open>g = Attacker_Delayed p Q\<close> id_apply in_wina.intros(2) move
        by presburger

      have "(weight g g' e) = (e - (E 1 0 0 0 0 0 0 0))"
        using g'_att_imm g_att_del
        using \<open>weight (Attacker_Delayed p Q) (Attacker_Immediate p' Q') e = e - E 1 0 0 0 0 0 0 0\<close> by blast

      then obtain \<phi> where \<phi>_prop: "(strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi> \<and> expressiveness_price \<phi> \<le> (e - (E 1 0 0 0 0 0 0 0)))"
        using IH g'_att_imm
        by auto 

      have "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
       = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')"
        by (smt (verit, best) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.observation \<open>in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q')\<close> g'_att_imm move)

      hence "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
       = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
        \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
        \<and> p \<mapsto>\<alpha> p' \<and> Q \<mapsto>S \<alpha> Q'"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay observation
          \<alpha>_prop \<phi>_prop \<open>in_wina (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q')\<close> local.observation
        by auto

      hence "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)"
        using local.observation 
        by presburger

      have "expr_pr_inner (Obs \<alpha> \<phi>) \<le> e" sorry

      then show ?thesis using \<open>strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)\<close>
        using g_att_del by blast
    next
      case Def_Conj
      assume "\<exists>p Q. g' = Defender_Conj p Q"
      then obtain p' Q' where g'_def_conj: "g' = Defender_Conj p' Q'" and
                          IH: "(\<exists>\<phi>. strategy_formula_inner g' (weight g g' e) \<phi> \<and> expr_pr_inner \<phi> \<le> weight g g' e) \<and>
                              (\<exists>\<phi>. strategy_formula g' (weight g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> weight g g' e)" 
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
        using g_att_del local.stable sorry (*Problem: Q \<noteq> Q'*)
      
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

      from \<chi>_prop have "\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
       = (Some id) \<and> in_wina e (Defender_Stable_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>"
        using g'_def_br \<open>in_wina e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)\<close> local.branch move
        sorry (*in local.branch: muss es nicht "\<exists>p' p'' Q' \<alpha> Q\<alpha>. ... heißen?!*)

      hence "strategy_formula_inner g e \<chi>"
        using g_att_del local.stable sorry (*Problem: Q \<noteq> Q'*)
      
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
     (*have B: "(\<forall>g'. (\<exists>p Q. g' = Attacker_Immediate p Q)  \<longrightarrow> (\<exists>\<phi>. strategy_formula g' e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<and>
          (\<exists>p Q. g' = Attacker_Delayed p Q)  \<longrightarrow> (\<exists>\<phi>. strategy_formula_inner g' e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>
          (\<exists>p q. g' = Attacker_Clause p q)  \<longrightarrow> (\<exists>\<phi>. strategy_formula_conjunct g' e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e) \<and>
          (\<exists>p Q. g' = Defender_Conj p Q)  \<longrightarrow> (\<exists>\<phi>. strategy_formula_inner g' e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>  (\<exists>\<phi>. strategy_formula g' e \<phi> \<and> expressiveness_price \<phi> \<le> e) \<and>
          (\<exists>p Q. g' =  Defender_Stable_Conj p Q)  \<longrightarrow> (\<exists>\<phi>. strategy_formula_inner g' e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>
          (\<exists>p \<alpha> p' Q Qa. g' = Defender_Branch p \<alpha> p' Q Qa) \<longrightarrow> (\<exists>\<phi>. strategy_formula_inner g' e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>
          (\<exists>p Q. g' = Attacker_Branch p Q) \<longrightarrow>  True)"
      by blast
    consider "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)" | 
             "in_wina e (Defender_Conj p Q) = (\<not>spectroscopy_defender g) \<and> (\<exists>g'. spectroscopy_moves g g' \<noteq>  None \<and> (in_wina (the (spectroscopy_moves g g') e) g'))" |
             "in_wina e (Defender_Conj p Q) = (spectroscopy_defender g) \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq>  None \<longrightarrow>  (in_wina (the (spectroscopy_moves g g') e) g'))"
      using "1" A by blast
      then show ?case
      proof (cases)
        case 1
        have "(\<forall>g'. \<not>spectroscopy_moves g g' \<noteq> None)"
          using "1.hyps" by blast
        hence "\<forall>g'. spectroscopy_moves g g' = None"
          by blast
          from B have "(\<forall>g'.(\<exists>p' Q'. g' = (Attacker_Delayed p' Q') 
                 \<or> g' = (Defender_Conj p' Q')
                 \<or> g' = (Attacker_Immediate p' Q')
                 \<or> g' = (Defender_Stable_Conj p' Q')
                 \<or> g' = (Attacker_Branch p' Q'))
                 \<or> (\<exists>p' q'. g' = (Attacker_Clause p' q')) 
                 \<or> (\<exists>p \<alpha> p' Q Qa. g' = Defender_Branch p \<alpha> p' Q Qa))"
            by (meson spectroscopy_defender.cases)
        then show ?thesis sorry
      next
        case 2
        then show ?thesis
          using "1" by blast
      next
        case 3
        have "(\<forall>g'. spectroscopy_moves g g' \<noteq>  None \<longrightarrow>  (in_wina (the (spectroscopy_moves g g') e) g'))"
          using "1" by blast
        consider "\<forall>g'. spectroscopy_moves g g' \<noteq>  None"|
                 "\<exists>g'. spectroscopy_moves g g' =  None"
          by fastforce
        then show ?thesis
      proof (cases)
        case 1
        have "(\<forall>g'. in_wina (the (spectroscopy_moves g g') e) g')"
          using "1" "1.hyps" by fastforce
        then show ?thesis
          using "1" "1.hyps" by auto 
      next
        case 2
        from 2 obtain g' where "spectroscopy_moves g g' =  None" by (rule exE)
        have A1:  "((\<exists>p' Q'. g' = (Attacker_Delayed p' Q') 
                   \<or> g' = (Defender_Conj p' Q')
                   \<or> g' = (Attacker_Immediate p' Q')
                   \<or> g' = (Defender_Stable_Conj p' Q')
                   \<or> g' = (Attacker_Branch p' Q'))
                   \<or> (\<exists>p' q'. g' = (Attacker_Clause p' q')) 
                   \<or> (\<exists>p \<alpha> p' Q Qa. g' = Defender_Branch p \<alpha> p' Q Qa))"
          by (meson spectroscopy_defender.cases)
         then show ?thesis 
         proof (elim disjE)
           assume A2: "\<exists>p' Q'.
                   g' = Attacker_Delayed p' Q' \<or>
                   g' = Defender_Conj p' Q' \<or>
                   g' = Attacker_Immediate p' Q' \<or> 
                   g' = Defender_Stable_Conj p' Q' \<or> 
                   g' = Attacker_Branch p' Q'"
           show "(\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
           proof -
             from A2 obtain p' Q' where 
                  "g' = Attacker_Delayed p' Q' \<or>
                   g' = Defender_Conj p' Q' \<or>
                   g' = Attacker_Immediate p' Q' \<or> 
                   g' = Defender_Stable_Conj p' Q' \<or> 
                   g' = Attacker_Branch p' Q'" by auto
             then show ?thesis
             proof (elim disjE)
               assume "g' = Attacker_Delayed p' Q'"
               from this have "spectroscopy_moves (Defender_Conj p Q) (Attacker_Delayed p' Q') =  None" by auto
               show ?thesis sorry
             next
               assume "g' = Defender_Conj p' Q'"
               have "spectroscopy_moves (Defender_Conj p Q) (Defender_Conj p' Q') =  None" by auto
               show ?thesis sorry
             next
               assume "g' = Attacker_Immediate p' Q'"
               have "spectroscopy_moves (Defender_Conj p Q) (Attacker_Immediate p' Q') =  None" by auto
               show ?thesis sorry
             next
               assume "g' = Defender_Stable_Conj p' Q'"
               have "spectroscopy_moves (Defender_Conj p Q) (Defender_Stable_Conj p' Q') =  None" by auto
               show ?thesis sorry
             next 
               assume "g' = Attacker_Branch p' Q'"
               have "spectroscopy_moves (Defender_Conj p Q) (Attacker_Branch p' Q') =  None" by auto
               show ?thesis sorry
             qed
           qed
         next
           assume "\<exists>p' q'. g' = Attacker_Clause p' q'"
           from this obtain p' q' where "g' = Attacker_Clause p' q'" by auto
           hence "spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p' q') =  None" using 2 sorry
           hence "p \<noteq> p' \<or> q' \<notin> Q"
             by force 
           show ?thesis sorry
           (*proof (rule disjE)
             assume "p \<noteq> p'"
             show ?thesis sorry
           next
             assume "q' \<notin> Q"
             show ?thesis sorry
           qed*)
         next
           assume "\<exists>p \<alpha> p' Q Qa. g' = Defender_Branch p \<alpha> p' Q Qa"
           from this obtain p \<alpha> p' Q Qa where "g' = Defender_Branch p \<alpha> p' Q Qa" by auto
           show ?thesis sorry
        qed
      qed
    qed*)
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  next
    case 6
    then show ?case sorry
  next
    case 7
    then show ?case sorry
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
    then show ?case sorry
  next
    case 5
    then show ?case sorry
  next
    case 6
    then show ?case sorry
  next
    case 7
    then show ?case
      by blast
  }
qed

lemma strategy_formulas_distinguish:
  assumes "strategy_formula (Attacker_Immediate p Q) e \<phi>"
  shows "distinguishes_from \<phi> p Q"
  sorry

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
    using strategy_formulas_distinguish by blast
qed


end (* context full_spec_game *)

end
