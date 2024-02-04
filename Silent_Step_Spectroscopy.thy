section \<open>Correctness\<close>

theory Silent_Step_Spectroscopy
  imports Strategy_Formulas Distinction_Implies_Winning_Budgets
begin

context full_spec_game 
begin

text \<open>As in theorem 1 of \cite[p. 14]{bisping2023lineartimebranchingtime} we state in what sense winning energy levels and equivalences coincide as the theorem \<open>spectroscopy_game_correctness\<close>:
There exists a formula \<open>\<phi>\<close> distinguishing a process \<open>p\<close> from a set of processes \<open>Q\<close> with 
expressiveness price of at most \<open>e\<close> if and only if \<open>e\<close> is in the winning budget of \<open>Attacker_Immediate p Q\<close>. 


The proof utilizes three lemmas. The forward direction is given by the lemma \<open>distinction_implies_winning_budgets\<close> combined with the upwards closure of winning budgets. 
To show the other direction one can construct a (strategy) formula with an appropriate price using 
the constructive proof of \<open>winning_budget_implies_strategy_formula\<close>. From lemma 
\<open>strategy_formulas_distinguish\<close> we then know that this formula actually distinguishes \<open>p\<close> from \<open>Q\<close>.
\<close>

theorem spectroscopy_game_correctness:
  fixes e p Q
  shows "(\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e)
       = (in_wina e (Attacker_Immediate p Q))"
proof
  assume "\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e"
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
  hence "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" unfolding \<O>_def by blast
  thus "\<exists>\<phi>. distinguishes_from \<phi> p Q \<and> expressiveness_price \<phi> \<le> e"
    using strategy_formulas_distinguish by fastforce 
qed

end (* context full_spec_game *)

end
