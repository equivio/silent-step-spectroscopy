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
  shows "(strategy_formula g e \<phi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  distinguishes_from \<phi> p Q
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q)\<longrightarrow>((strategy_formula_inner g e \<chi> \<and> Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q)
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True))
      \<and> 
      (strategy_formula_inner g e \<chi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> (Q \<Zsurj>S Q) \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Attacker_Clause p q \<Rightarrow> True

      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> (Qa\<inter>Q={}) \<longrightarrow> distinguishes_from_inner \<chi> p (Q\<union>Qa)
      | Attacker_Branch p Q \<Rightarrow> True))
      \<and>
      (strategy_formula_conjunct g e \<psi> \<longrightarrow>
        (case g of
        Attacker_Immediate p Q \<Rightarrow>  True
      | Attacker_Delayed p Q \<Rightarrow> True
      | Attacker_Clause p q \<Rightarrow> distinguishes_conjunct \<psi> p q

      | Defender_Conj p Q \<Rightarrow> True
      | Defender_Stable_Conj p Q \<Rightarrow> True
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> True
      | Attacker_Branch p Q \<Rightarrow> True))"
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
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> Qa \<inter> Q = {} \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
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
       | Attacker_Delayed p Q \<Rightarrow>
           Q \<Zsurj>S Q \<longrightarrow>
           strategy_formula_inner (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<chi> \<and> Q \<Zsurj>S Q \<longrightarrow>
           distinguishes_from (hml_srbb.Internal \<chi>) p Q
       | Defender_Conj p Q \<Rightarrow> distinguishes_from \<phi> p Q | _ \<Rightarrow> True)) \<and>
     p \<mapsto>\<alpha> p' \<and> Q \<mapsto>S \<alpha> Q' " by auto
  hence D: "distinguishes_from \<phi> p' Q'" by auto 
  hence "p' \<Turnstile>SRBB \<phi>" using distinguishes_from_def distinguishes_def sorry (* should work?! *)
  from IH have "p \<mapsto>\<alpha> p'" and "Q \<mapsto>S \<alpha> Q'" by auto 
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
        hence "\<exists>q''. q' \<mapsto> \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" sorry
        hence "\<exists>q' q''. q \<Zsurj> q' \<and> q' \<mapsto> \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" using X by auto
        then show "False" using \<open>Q \<Zsurj>S Q\<close>
          by (metis D \<open>Q \<mapsto>S \<alpha> Q'\<close> \<open>q \<in> Q\<close> distinguishes_def distinguishes_from_def) 
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
    by (metis distinguishes_def distinguishes_from_def distinguishes_from_inner_def distinguishes_inner_def hml_models.simps(3) hml_srbb_inner_models.elims(2) hml_srbb_inner_models.elims(3) hml_srbb_models.simps hml_srbb_to_hml.simps(2) silent_reachable.intros(1))
  then show ?case by simp 
next
  case (conj Q p e \<Phi>)
  hence "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto 
  hence "distinguishes_from_inner (hml_srbb_inner.Conj Q \<Phi>) p Q" sorry (* Der Bezug von dis_conj zu dis_inner fehlt...*)
  then show ?case by simp 
next
  case (imm_conj Q p e \<Phi>)
  hence "\<forall>q \<in> Q. distinguishes_conjunct (\<Phi> q) p q" by auto
  have "distinguishes_from (ImmConj Q \<Phi>) p Q" sorry (* wie bei conj *)
  then show ?case by simp 
next
  case (pos p q e \<chi>)
  then show ?case sorry
next
  case (neg p q e P' \<chi>)
  then show ?case sorry
next
  case (stable p Q e \<chi>)
  then show ?case
    using spectroscopy_position.distinct(41) strategy_formula.cases by auto 
next
  case (stable_conj Q p e \<Phi>)
  then show ?case sorry
next
  case (branch p Q p'' e \<chi>)
  then show ?case
    by (smt (verit) full_spec_game.strategy_formula.cases full_spec_game_axioms spectroscopy_position.distinct(31) spectroscopy_position.distinct(37) spectroscopy_position.distinct(7))
next
  case (branch_conj p \<alpha> p' Q Q\<alpha> e e' \<psi> \<Phi> Qa)
  then show ?case sorry
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
    have "\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) e \<phi> \<and> expressiveness_price \<phi> \<le> e" .
  hence "\<exists>\<phi>\<in>\<O> e. strategy_formula (Attacker_Immediate p Q) e \<phi>" unfolding \<O>_def by blast
  thus "\<exists>\<phi>\<in>\<O> e. distinguishes_from \<phi> p Q"
    using strategy_formulas_distinguish by fastforce 
qed


end (* context full_spec_game *)

end
