theory Silent_Step_Spectroscopy
  imports Spectroscopy_Game Expressiveness_Price HML_SRBB Weak_Traces
begin

context full_spec_game begin

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
  sorry

lemma winning_budget_implies_strategy_formula:
  assumes "in_wina e (Attacker_Immediate p Q)"
  shows "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e"
  sorry

thm strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct
thm strategy_formula.simps 
thm strategy_formula_inner.simps 
thm strategy_formula_conjunct.simps

lemma strategy_formulas_distinguish:
  shows "strategy_formula g e \<phi> \<Longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  distinguishes_from \<phi> p Q
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q)\<longrightarrow>((strategy_formula_inner g e \<chi> \<and> Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q)
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True)" 
      and 
       "strategy_formula_inner g e \<chi> \<Longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> (Qa\<inter>Q={}) \<longrightarrow> distinguishes_from_inner \<chi> p (Q\<union>Qa)
      | Attacker_Branch p Q \<Rightarrow> True)"
      and 
      "strategy_formula_conjunct g e \<psi> \<Longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> True
      | Attacker_Clause p q \<Rightarrow> distinguishes_conjunct \<psi> p q

      | Defender_Conj p Q \<Rightarrow> True
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True)"
  sorry


(*
proof (cases g)
  case (Attacker_Immediate p Q)
  have "strategy_formula g e \<phi> \<longrightarrow> distinguishes_from \<phi> p Q" proof (rule impI)
    assume "strategy_formula g e \<phi>"

    hence "(\<exists>p Q e' \<chi>.
     g = Attacker_Immediate p Q \<and>
     e  = e' \<and>
     \<phi> = hml_srbb.Internal \<chi> \<and>
     (\<exists>Q'. spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') = Some id \<and>
           in_wina e' (Attacker_Delayed p Q') \<and> strategy_formula_inner (Attacker_Delayed p Q') e' \<chi>)) 
      \<or>
     (\<exists>Q p Q' e' \<phi>'.
     g = Attacker_Immediate p Q \<and>
     e = e' \<and>
     \<phi> = \<phi>' \<and>
     (if Q = {}
      then \<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') = Some id \<and>
                in_wina e' (Defender_Conj p' Q') \<and> strategy_formula (Defender_Conj p' Q') e' \<phi>'
      else \<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') = subtract 0 0 0 0 1 0 0 0 \<and>
                in_wina (e' - E 0 0 0 0 1 0 0 0) (Defender_Conj p' Q') \<and>
                strategy_formula (Defender_Conj p' Q') (e' - E 0 0 0 0 1 0 0 0) \<phi>'))" 
      using strategy_formula.simps Attacker_Immediate
      by (smt (verit) spectroscopy_position.distinct(5) spectroscopy_position.distinct(9))

    show "distinguishes_from \<phi> p Q " 
    proof (cases "(\<exists>p Q e' \<chi>.
     g = Attacker_Immediate p Q \<and>
     e  = e' \<and>
     \<phi> = hml_srbb.Internal \<chi> \<and>
     (\<exists>Q'. spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') = Some id \<and>
           in_wina e' (Attacker_Delayed p Q') \<and> strategy_formula_inner (Attacker_Delayed p Q') e' \<chi>))")
      case True (* Delay *)
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
  then show ?thesis by (simp add: Attacker_Immediate) 
next
  case (Attacker_Branch x21 x22)
  then show ?thesis sorry
next
  case (Attacker_Clause x31 x32)
  then show ?thesis sorry
next
  case (Attacker_Delayed x41 x42)
  then show ?thesis sorry
next
  case (Defender_Branch x51 x52 x53 x54 x55)
  then show ?thesis sorry
next
  case (Defender_Conj x61 x62)
  then show ?thesis sorry
next
  case (Defender_Stable_Conj x71 x72)
  then show ?thesis sorry
qed
*)

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
    have "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" .
  hence "\<exists>\<phi>\<in>\<O> e. strategy_formula (Attacker_Immediate p Q) e \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by fastforce 
qed


end (* context full_spec_game *)

end
