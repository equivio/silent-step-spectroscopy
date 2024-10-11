subsection \<open>Correctness Theorem\<close>

theory Silent_Step_Spectroscopy
  imports
    Distinction_Implies_Winning_Budgets
    Strategy_Formulas
begin

context weak_spectroscopy_game
begin

text \<open>\label{th1}\<close>

theorem spectroscopy_game_correctness:
  fixes e p Q
  shows \<open>(\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e)
       = (attacker_wins e (Attacker_Immediate p Q))\<close>
proof
  assume \<open>\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e\<close>
  then obtain \<phi> where
    \<open>distinguishes_from \<phi> p Q\<close> and le: \<open>expressiveness_price \<phi> \<le> e\<close>
    unfolding \<O>_def by blast
  from distinction_implies_winning_budgets this(1)
    have budget: \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close> .
  thus \<open>attacker_wins e (Attacker_Immediate p Q)\<close> using win_a_upwards_closure le by simp
next
  assume \<open>attacker_wins e (Attacker_Immediate p Q)\<close>
  with winning_budget_implies_strategy_formula have
    \<open>\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close>
    by force
  hence \<open>\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e\<close>
    unfolding \<O>_def by blast
  thus \<open>\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e\<close>
    using strategy_formulas_distinguish by fastforce
qed

end (* context weak_spectroscopy_game *)

end
