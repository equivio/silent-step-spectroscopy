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

lemma winning_budget_implies_strategy_formula:
  fixes g e
  assumes "in_wina e g"
  shows
    "(\<exists>p Q. g = Attacker_Immediate p Q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
    "(\<exists> p Q. g = Attacker_Delayed p Q) ==> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists> p q. g = Attacker_Clause p q) \<Longrightarrow> (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e)"
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
    from assms obtain p Q where A: "in_wina e (Defender_Conj p Q)" using 4 in_wina.intros(1) "1" by blast
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
        then show ?thesis sorry
      qed
    qed
  next
    case 5
    then obtain p Q where "g = Defender_Stable_Conj p Q" by blast
    hence "\<forall>q\<in>Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) = None"
      using "1" by blast
    hence "Q = {}" using local.conj_s_answer 
      by simp
    hence "\<exists>\<Phi>. (\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q))"
      by blast
    then obtain \<Phi> where strat_pre: "(\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q))"
      by blast
    then have Strat: "strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj {} \<Phi>)"
      using \<open>Q = {}\<close> stable_conj by blast
    from strat_pre 5
    have  "modal_depth_srbb_inner (StableConj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)"
          "branch_conj_depth_inner (StableConj Q \<Phi>) = Sup ((branch_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "inst_conj_depth_inner (StableConj Q \<Phi>) = Sup ((inst_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "st_conj_depth_inner (StableConj Q \<Phi>) = 1 + Sup ((st_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "imm_conj_depth_inner (StableConj Q \<Phi>) = Sup ((imm_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "max_pos_conj_depth_inner (StableConj Q \<Phi>) = Sup ((max_pos_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "max_neg_conj_depth_inner (StableConj Q \<Phi>) = Sup ((max_neg_conj_depth_conjunct \<circ> \<Phi>) ` Q)"
          "neg_depth_inner (StableConj Q \<Phi>) = Sup ((neg_depth_conjunct \<circ> \<Phi>) ` Q)"
      using modal_depth_srbb_inner.simps(3) branch_conj_depth_inner.simps st_conj_depth_inner.simps
      inst_conj_depth_inner.simps imm_conj_depth_inner.simps max_pos_conj_depth_inner.simps
      max_neg_conj_depth_inner.simps neg_depth_inner.simps 
      by auto+

    hence "modal_depth_srbb_inner (StableConj Q \<Phi>) = 0"
          "branch_conj_depth_inner (StableConj Q \<Phi>) = 0"
          "inst_conj_depth_inner (StableConj Q \<Phi>) = 0"
          "st_conj_depth_inner (StableConj Q \<Phi>) = 1"
          "imm_conj_depth_inner (StableConj Q \<Phi>) = 0"
          "max_pos_conj_depth_inner (StableConj Q \<Phi>) = 0"
          "max_neg_conj_depth_inner (StableConj Q \<Phi>) = 0"
          "neg_depth_inner (StableConj Q \<Phi>) = 0"

      using \<open>Q = {}\<close> image_empty comp_apply
      by (simp add: bot_enat_def)+
    hence "expr_pr_inner (StableConj Q \<Phi>) = (E 0 0 0 1 0 0 0 0)"
      using expr_pr_inner.simps \<open>Q = {}\<close>
      by force
    hence "expr_pr_inner (StableConj Q \<Phi>) \<le> e"
      sorry
    then show ?case using Strat 
      using \<open>Q = {}\<close> 
      using \<open>g = Defender_Stable_Conj p Q\<close> by blast
  next
    case 6
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
    then show ?case sorry
  next
    case 3
    then show ?case sorry
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
    then show ?case sorry
  }
next
  case (3 g e)
  {
    case 1
    then show ?case sorry
  next
    case 2
    then show ?case sorry
  next
    case 3
    then show ?case sorry
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
    then show ?case sorry
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
