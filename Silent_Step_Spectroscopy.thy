theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin  

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

lemma winning_budget_implies_strategy_formula:
  fixes g e
  assumes "in_wina e g"
  shows
  "case g of
    Attacker_Immediate p Q \<Rightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)
  | Attacker_Delayed p Q => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)
  | Attacker_Clause p q => (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e)
  
  | Defender_Conj p Q \<Rightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e) \<and>  (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)
  | Defender_Stable_Conj p Q => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)
  | Defender_Branch p \<alpha> p' Q Qa => (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)
  | Attacker_Branch p Q \<Rightarrow> True"
  using assms proof(induction rule: in_wina.induct)
  case (1 g e)
  then show ?case proof(induction g)
    case (Attacker_Immediate x1 x2)
    then show ?case
      by simp 
  next
    case (Attacker_Branch x1 x2)
    then show ?case by simp
  next
    case (Attacker_Clause x1 x2)
    then show ?case by simp
  next
    case (Attacker_Delayed x1 x2)
    then show ?case by simp
  next
    case (Defender_Branch x1 x2 x3 x4 x5)
    then show ?case sorry
  next
    case (Defender_Conj x1 x2)
    then show ?case sorry
  next
    case (Defender_Stable_Conj p Q)
    hence "\<forall>q\<in>Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) = None"
      by blast
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
    from strat_pre Defender_Stable_Conj
    have "modal_depth_srbb_inner (StableConj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)"
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
      using \<open>Q = {}\<close> by auto
    qed
next
  case (2 g e)
  then show ?case sorry
next
  case (3 g e)
  then show ?case sorry
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
