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
    case (Defender_Stable_Conj x1 x2)
    then show ?case proof
      have Strat: "strategy_formula_inner (Defender_Stable_Conj x1 x2) e (StableConj {} \<phi>)" sorry

      have " expr_pr_inner (StableConj {} \<phi>) = E 0 0 0 0 0 0 0 0" sorry (* Soweit ich Sup auf enats verstanden habe, sollte hier das Supremum einer leeren Menge 0 sein.*)
      hence " expr_pr_inner (StableConj {} \<phi>) \<le> e" using 1
        by (simp add: energy.sel(5) energy.sel(7))

      from Strat this show ?thesis by auto
    qed
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
