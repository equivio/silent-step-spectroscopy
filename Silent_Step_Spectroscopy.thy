subsection \<open>Correctness Theorem\<close>

theory Silent_Step_Spectroscopy
  imports Strategy_Formulas Distinction_Implies_Winning_Budgets
begin

context weak_spectroscopy_game 
begin

text \<open>\label{th1}\<close>

theorem spectroscopy_game_correctness:
  fixes e p Q
  shows "(\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e)
       = (attacker_wins e (Attacker_Immediate p Q))"
proof
  assume "\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e"
  then obtain \<phi> where
    "distinguishes_from \<phi> p Q" and le: "expressiveness_price \<phi> \<le> e"
    unfolding \<O>_def by blast 
  from distinction_implies_winning_budgets this(1)
    have budget: "attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q)" .
  thus "attacker_wins e (Attacker_Immediate p Q)" using win_a_upwards_closure le by simp
next
  assume "attacker_wins e (Attacker_Immediate p Q)"
  with winning_budget_implies_strategy_formula have
    "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e"
    by force
  hence "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e"
    unfolding \<O>_def by blast
  thus "\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e"
    using strategy_formulas_distinguish by fastforce
qed

end (* context weak_spectroscopy_game *)

end
