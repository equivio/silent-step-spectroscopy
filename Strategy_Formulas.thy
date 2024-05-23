text \<open>\newpage\<close>
section \<open>Strategy Formulas\<close>
theory Strategy_Formulas
    imports Spectroscopy_Game Expressiveness_Price
begin

text\<open>In this section, we introduce strategy formulas as a tool of proving the corresponding lemma, \\
\<open>spectroscopy_game_correctness\<close>, in section \ref{th1}. 
We first define strategy formulas, creating a bridge between HML formulas, the
spectroscopy game and winning budgets. We then show that for some energy \<open>e\<close> in a winning budget there 
exists a strategy formula with expressiveness price \<open>\<le> e\<close>. Afterwards, we prove that this formula 
actually distinguishes the corresponding processes.\<close>

context full_spec_game
begin
text \<open>\label{stratFormula}\<close>
text \<open>We define strategy formulas inductively. For example for \<open>\<langle>\<alpha>\<rangle>\<phi>\<close> to be a strategy formula for some attacker
delayed position \<open>g\<close> with energy \<open>e\<close> the following must hold: \<open>\<phi>\<close> is a strategy formula at the from \<open> g\<close> through an observation move
reached attacker (immediate) position with the energy \<open> e \<close> updated according to the move. Then the function 
\<open>strategy_formula_inner g e \<langle>\<alpha>\<rangle>\<phi>\<close> returns true. Similarly, every derivation rule for strategy formulas corresponds to 
possible moves in the spectroscopy game. To account for the three different data types a HML$_{\text{SRBB}}$
formula can have in our formalization, we define three functions at the same time:\<close>
inductive
strategy_formula :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb \<Rightarrow> bool"
and strategy_formula_inner 
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_inner \<Rightarrow> bool"
and strategy_formula_conjunct
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_conjunct \<Rightarrow> bool"
where
  delay:
    "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
      if "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some Some)) \<and> (attacker_wins e (Attacker_Delayed p Q')) 
          \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))" |
  
  procrastination:
    "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
      if "(\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) 
         = (Some Some) \<and> attacker_wins e (Attacker_Delayed p' Q)
          \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>)"|
  
  observation: 
    "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)" 
      if "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
         = (subtract 1 0 0 0 0 0 0 0) 
          \<and> attacker_wins (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
          \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
          \<and> p \<mapsto>a\<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'" |
  
  early_conj:
    "strategy_formula (Attacker_Immediate p Q) e \<phi>" 
      if "\<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
                = (subtract 0 0 0 0 1 0 0 0) 
                  \<and> attacker_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p' Q')
                  \<and> strategy_formula (Defender_Conj p' Q') (e - (E 0 0 0 0 1 0 0 0)) \<phi>"|
  
  late_conj:
    "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
      if "(spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) 
         = (Some Some) \<and> (attacker_wins e (Defender_Conj p Q)) 
           \<and> strategy_formula_inner (Defender_Conj p Q) e \<chi>)"|
  
  conj:
  "strategy_formula_inner (Defender_Conj p Q) e (Conj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) 
            \<and> (attacker_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|

  imm_conj:
  "strategy_formula (Defender_Conj p Q) e (ImmConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) 
            \<and> (attacker_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|
  
  pos:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
    if "(\<exists>Q'. spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
      = Some min1_6 \<and> attacker_wins (the (min1_6 e)) (Attacker_Delayed p Q')
        \<and> strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>)"|
  
  neg:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)" 
    if "\<exists>P'. (spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') 
      = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)
        \<and> attacker_wins (the (min1_7 (e - (E 0 0 0 0 0 0 0 1)))) (Attacker_Delayed q P'))
        \<and> strategy_formula_inner (Attacker_Delayed q P') (the (min1_7 (e - (E 0 0 0 0 0 0 0 1)))) \<chi>" |
  
  stable:
  "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>" 
    if "(\<exists>Q'. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') 
      = (Some Some) \<and> attacker_wins e (Defender_Stable_Conj p Q') 
        \<and> strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>)"|

  stable_conj:
    "strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) 
          \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)"|

  branch:
  "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>" 
    if "\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) 
      = (Some Some) \<and> attacker_wins e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) 
        \<and> strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi>"|

  branch_conj:
  "strategy_formula_inner (Defender_Branch p \<alpha> p' Q Q\<alpha>) e (BranchConj \<alpha> \<psi> Q \<Phi>)"
    if "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p' Q') 
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (attacker_wins (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))  \<psi>"
        
        "\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q)"

text \<open>To prove \<open>spectroscopy_game_correctness\<close> we need the following implication:
If \<open>e\<close> is in the winning budget of \<open>Attacker_Immediate p Q\<close>, there is a strategy formula \<open>\<phi>\<close> for
\<open>Attacker_Immediate p Q\<close> with energy \<open>e\<close> with expressiveness price \<open>\<le> e\<close>. 
\\
\\
We prove a more detailed result for all possible game positions \<open>g\<close> by induction over the structure of winning budgets (Cases $1-3$:\label{deviation:lemma2}
\begin{enumerate}
  \item We first show that the statement holds if \<open>g\<close> has no outgoing edges. This can only be the case for  defender positions.
  \item If \<open>g\<close> is an attacker  position, by \<open>e\<close> being in the winning budget of \<open>g\<close>, we know there exists a successor of \<open>g\<close> that  the attacker can move to. 
  If by induction the property holds true for that successor, we show that it then holds for \<open>g\<close> as well.
  \item If a defender position \<open>g\<close> has outgoing edges and the statement holds true for all successors, we show that the statement holds true for \<open>g\<close> as well.
\end{enumerate}
\<close>
lemma winning_budget_implies_strategy_formula:
  fixes g e
  assumes "attacker_wins e g"
  shows
    "(\<exists>p Q. g = Attacker_Immediate p Q)
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Delayed p Q) 
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p q. g = Attacker_Clause p q)  
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula_conjunct g e \<phi> \<and> expr_pr_conjunct \<phi> \<le> e)"
    "(\<exists>p Q. g = Defender_Conj p Q) 
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p Q. g =  Defender_Stable_Conj p Q)
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi>  \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p \<alpha> p' Q Qa. g = Defender_Branch p \<alpha> p' Q Qa) 
        \<Longrightarrow> (\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
    "(\<exists>p Q. g = Attacker_Branch p Q) 
        \<Longrightarrow> \<exists>p Q. (g = Attacker_Branch p Q 
              \<and> (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e- E 1 0 0 0 0 0 0 0) \<phi> 
              \<and> expressiveness_price \<phi> \<le> (e- E 1 0 0 0 0 0 0 0)))"
  using assms 
proof(induction rule: attacker_wins.induct)
  case (Attack g g' e e')
  {
    case 1
    then obtain p Q where g_def: "g =  Attacker_Immediate p Q" by blast
    hence move: "((spectroscopy_moves (Attacker_Immediate p Q) g')\<noteq>None) \<and> (attacker_wins (updated (Attacker_Immediate p Q) g' e) g') \<and>
      ((\<exists>p Q. g' = Defender_Conj p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weight g g' e)) \<phi> \<and> expr_pr_inner \<phi> \<le> updated g g' e)) \<and> 
      ((\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weight g g' e)) \<phi> \<and> expr_pr_inner \<phi> \<le> updated g g' e))" 
      using attacker_wins.cases 1 Attack by simp
    from move have move_cases: "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
      using spectroscopy_moves.simps
      by (smt (verit) spectroscopy_defender.elims(1))
    show ?case using move_cases
    proof(rule disjE)
      assume "\<exists>p' Q'. g' = Attacker_Delayed p' Q'"
      then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
      have e_comp: "(the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e) = (Some e)"
        by (smt (verit, ccfv_threshold) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay g'_att_del move option.exhaust_sel option.inject)
      have "p' = p"
        by (metis \<open>g' = Attacker_Delayed p' Q'\<close> move spectroscopy_moves.simps(1))
      have "(attacker_wins e (Attacker_Delayed p Q'))"
        using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> move win_a_upwards_closure e_comp
        by simp
      from Attack g'_att_del have "(\<exists>\<phi>. strategy_formula_inner g' (the (weight (Attacker_Immediate p Q) g' e)) \<phi> \<and>
        expr_pr_inner \<phi> \<le> updated (Attacker_Immediate p Q) g' e)"
        using \<open>attacker_wins e (Attacker_Delayed p Q')\<close>
        using \<open>p' = p\<close>
        using \<open>g = Attacker_Immediate p Q\<close> move by blast
      then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using \<open>p' = p\<close> \<open>weight (Attacker_Immediate p Q) (Attacker_Delayed p' Q') e = Some e\<close> g'_att_del by auto
      hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
      = (Some Some)) \<and> (attacker_wins e (Attacker_Delayed p Q')) 
        \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))"
        using g'_att_del
        by (smt (verit) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay \<open>attacker_wins e (Attacker_Delayed p Q')\<close> move)
      hence "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
      moreover have "expressiveness_price (Internal \<chi>) \<le> e"
        using \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)\<close>
        by auto
      ultimately show ?case 
        using g_def by blast
    next
      assume "\<exists>p' Q'. g' = Defender_Conj p' Q'"
      then obtain p' Q' where g'_def_conj: "g' = Defender_Conj p' Q'" by blast
      hence M: "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') = (subtract 0 0 0 0 1 0 0 0)"
        using local.f_or_early_conj move by presburger
      hence Qp': "Q\<noteq>{}" "Q = Q'" "p = p'"
        using Attack.hyps(2) g_def g'_def_conj local.f_or_early_conj by metis+
      from M have "updated (Attacker_Immediate p Q) (Defender_Conj p' Q') e
                = e - (E 0 0 0 0 1 0 0 0)"
        using Attack.hyps(3) g'_def_conj g_def
        by (smt (verit) option.distinct(1) option.sel)
      have "(attacker_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q'))"
         using g'_def_conj Qp' move win_a_upwards_closure 
         using \<open>the (weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e) = e - E 0 0 0 0 1 0 0 0\<close> by force
      with Attack g'_def_conj have IH_case: "\<exists>\<phi>. strategy_formula_inner g' (updated (Attacker_Immediate p Q) g' e) \<phi> \<and>
        expr_pr_inner \<phi> \<le> updated (Attacker_Immediate p Q) g' e"
        using g_def move by auto
      hence "(\<exists>\<phi>. strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expr_pr_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
        using \<open>attacker_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q')\<close> IH_case Qp'
          \<open>the (weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e) = e - E 0 0 0 0 1 0 0 0\<close> g'_def_conj by auto
      then obtain \<phi> where S: "(strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<phi> \<and> expr_pr_inner \<phi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
        by blast
      hence "\<exists>\<psi>. \<phi> = Conj Q \<psi>"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj Qp' g'_def_conj move unfolding Qp'
        by (smt (verit) spectroscopy_moves.simps(60,70) spectroscopy_position.distinct(33) spectroscopy_position.inject(6) strategy_formula_inner.simps)
      then obtain \<psi> where "\<phi> = Conj Q \<psi>" by auto
      hence "strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) (ImmConj Q \<psi>)"
        using S strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj strategy_formula_strategy_formula_inner_strategy_formula_conjunct.imm_conj
        by (smt (verit) Qp' g'_def_conj hml_srbb_inner.inject(2) move spectroscopy_defender.simps(4,6) spectroscopy_moves.simps(60) spectroscopy_moves.simps(70) strategy_formula_inner.cases) 
      hence SI: "strategy_formula (Attacker_Immediate p Q) e (ImmConj Q \<psi>)"
         using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj Qp'
         by (metis (no_types, lifting) \<open>attacker_wins (e - E 0 0 0 0 1 0 0 0) (Defender_Conj p Q')\<close> local.f_or_early_conj)
      have "expr_pr_inner (Conj Q \<psi>) \<le> (e - (E 0 0 0 0 1 0 0 0))" using S \<open>\<phi> = Conj Q \<psi>\<close> by simp
      hence "expressiveness_price (ImmConj Q \<psi>) \<le> e" using expr_imm_conj Qp'
        by (smt (verit) Attack.hyps(3) M g'_def_conj g_def option.sel option.simps(3))
      thus ?thesis using SI
         using \<open>g = Attacker_Immediate p Q\<close> by blast
      qed
  next
    case 2
    then obtain p Q where g_att_del: "g = Attacker_Delayed p Q" by blast
    then consider
      (Att_Del) "(\<exists>p Q. g' = Attacker_Delayed p Q)" | (Att_Imm) "(\<exists>p' Q'. g' = (Attacker_Immediate p' Q'))" |
      (Def_Conj) "(\<exists>p Q. g' = (Defender_Conj p Q))" | (Def_St_Conj) "(\<exists>p Q. g' = (Defender_Stable_Conj p Q))" |
      (Def_Branch) "(\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
      using Attack
      by (metis spectroscopy_defender.cases spectroscopy_moves.simps(53) spectroscopy_moves.simps(59))
    then show ?case proof (cases)
      case Att_Del
      then obtain p' Q' where
        g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
      show "\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e"
      proof-
        have Qp': "Q' = Q" "p \<noteq> p'" "p \<mapsto> \<tau> p'"
          using Attack.hyps g_att_del g'_att_del Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.procrastination
          by metis+
        hence e_comp: "(the (spectroscopy_moves (Attacker_Delayed p Q) g') e) = Some e"
          using g'_att_del
          by simp
        hence att_win: "(attacker_wins e (Attacker_Delayed p' Q'))"
          using g'_att_del Qp' g_att_del attacker_wins.Defense e_comp Attack.hyps
          by (metis option.sel)
        have "(updated g g' e) = e"
          using g'_att_del g_att_del
          using e_comp by fastforce
        then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
          using Attack g'_att_del
          by auto 
        hence "\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = (Some Some)
           \<and>  attacker_wins e (Attacker_Delayed p' Q)
           \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>"
          using e_comp g'_att_del Qp' local.procrastination Attack.hyps att_win
            Spectroscopy_Game.Inhabited_Tau_LTS.procrastination
          by (metis Inhabited_Tau_LTS_axioms)
        hence "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.procrastination by blast
        have "expr_pr_inner \<chi> \<le> e"
          using \<open>strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close> by blast
        then show ?thesis 
          using \<open>strategy_formula_inner (Attacker_Delayed p Q) e \<chi>\<close> g_att_del by blast
      qed
    next
      case Att_Imm
      then obtain p' Q' where
        g'_att_imm: "g' = Attacker_Immediate p' Q'" by blast 
      hence "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') \<noteq> None"
        using Attack.hyps g_att_del by blast
      hence "\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q'" unfolding spectroscopy_moves.simps(3) by presburger
      then obtain \<alpha> where \<alpha>_prop: "p \<mapsto>a \<alpha> p'" "Q \<mapsto>aS \<alpha> Q'" by blast
      hence weight: "weight (Attacker_Delayed p Q) (Attacker_Immediate p' Q') e = subtract_fn 1 0 0 0 0 0 0 0 e"
        by (simp, metis)
      hence update: "updated g g' e = e - (E 1 0 0 0 0 0 0 0)"
        using g'_att_imm g_att_del Attack.hyps(3)
        by (metis option.discI option.sel)
      then obtain \<phi> where \<phi>_prop:
        "strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<phi>"
        "expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0"
        using Attack g'_att_imm
        by auto
      hence "\<exists>p' Q'.
        spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0
        \<and> attacker_wins (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
        \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
        \<and> p \<mapsto>a\<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q'"
        using \<alpha>_prop update Attack.hyps(3,4) g'_att_imm by fastforce
      hence "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)"
        using local.observation by auto
      moreover have "expr_pr_inner (Obs \<alpha> \<phi>) \<le> e"
        using expr_obs \<phi>_prop weight Attack.hyps update  g'_att_imm g_att_del
        by (metis option.sel) 
      ultimately show ?thesis
        using g_att_del by blast
    next
      case Def_Conj
      then obtain p' Q' where
        g'_def_conj: "g' = Defender_Conj p' Q'" by blast
      hence  "p = p'" "Q = Q'" 
        using local.late_inst_conj Attack.hyps unfolding g_att_del by presburger+
      hence "the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')) e = Some e"
        by fastforce
      hence "attacker_wins e (Defender_Conj p' Q')"  "updated g g' e = e" 
        using Attack unfolding g'_def_conj g_att_del by force+
      then obtain \<chi> where
        \<chi>_prop: "(strategy_formula_inner (Defender_Conj p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using Attack g'_def_conj by auto
      hence 
        "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q') = Some Some
        \<and> attacker_wins e (Defender_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Conj p' Q') e \<chi>"
        by (simp add: \<open>Q = Q'\<close> \<open>attacker_wins e (Defender_Conj p' Q')\<close> \<open>p = p'\<close>)
      then show ?thesis
        using \<chi>_prop \<open>Q = Q'\<close> \<open>attacker_wins e (Defender_Conj p' Q')\<close> \<open>p = p'\<close>
          full_spec_game.late_conj full_spec_game_axioms g_att_del by fastforce
    next
      case Def_St_Conj
      then obtain p' Q' where g'_def: "g' = Defender_Stable_Conj p' Q'" by blast
      hence pQ': "p = p'" "Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}" "\<nexists>p''. p \<mapsto>\<tau> p''"
        using local.late_stbl_conj \<open>g' = Defender_Stable_Conj p' Q'\<close> g_att_del Attack
        by meson+
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')) e) = Some e"
        by auto
      hence "attacker_wins e (Defender_Stable_Conj p' Q')" "updated g g' e = e" 
        using Attack unfolding g'_def g_att_del by force+
      then obtain \<chi> where \<chi>_prop: "strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>" "expr_pr_inner \<chi> \<le> e"
        using Attack g'_def by auto
      have "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') = Some Some
        \<and> attacker_wins e (Defender_Stable_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>"
        using Attack \<chi>_prop \<open>attacker_wins e (Defender_Stable_Conj p' Q')\<close> local.late_stbl_conj  pQ'
        unfolding g_att_del g'_def
        by force
      thus "?thesis"
        using g_att_del local.stable pQ' \<chi>_prop by blast
    next
      case Def_Branch
      then obtain p' \<alpha> p'' Q' Q\<alpha> where
        g'_def_br: "g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>" by blast
      hence pQ': "p = p'" "Q' = Q - Q\<alpha>" "p \<mapsto>a \<alpha> p''" "Q\<alpha> \<subseteq> Q"
        using local.br_conj Attack unfolding g_att_del by metis+
      hence "the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) e = Some e"
        by auto
      hence post: "attacker_wins e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)" "updated g g' e = e" 
        using Attack option.inject unfolding g'_def_br g_att_del by auto
      then obtain \<chi> where \<chi>_prop:
        "strategy_formula_inner (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e \<chi>" "expr_pr_inner \<chi> \<le> e"
        using g'_def_br g_att_del Attack
        by auto 
      hence "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) = Some Some
         \<and> attacker_wins e (Defender_Branch p \<alpha> p'' Q' Q\<alpha>)
         \<and> strategy_formula_inner (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) e \<chi>"
        using g'_def_br local.branch Attack post pQ' by simp
      hence "strategy_formula_inner g e \<chi>"
        using g_att_del local.stable branch
        by blast
      thus ?thesis using \<chi>_prop 
        by blast
    qed
  next
    case 3
    then obtain p q where g_def: "g = Attacker_Clause p q" by blast
    hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q'))"
      using Attack.hyps  spectroscopy_moves.simps
      by (smt (verit, del_insts) spectroscopy_defender.elims(1))
    then obtain p' Q' where
      g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
    show ?case
    proof(cases \<open>p = p'\<close>)
      case True
      hence "{q} \<Zsurj>S Q'"
        using g'_att_del g_def local.pos_neg_clause Attack by presburger
      hence post_win:
        "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = min1_6 e"
         "(attacker_wins (the (min1_6 e)) (Attacker_Delayed p Q'))"
        using \<open>{q} \<Zsurj>S Q'\<close> Attack.hyps win_a_upwards_closure unfolding True  g'_att_del g_def
        by auto
      then obtain \<chi> where \<chi>_spec:
        "strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>"
        "expr_pr_inner \<chi> \<le> the (min1_6 e)"
        using Attack True post_win unfolding g_def g'_att_del
        by (metis option.sel)
      hence
        "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') = Some min1_6"
        "attacker_wins (the (min1_6 e)) (Attacker_Delayed p Q')"
        "strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>"
        using \<open>{q} \<Zsurj>S Q'\<close> local.pos_neg_clause post_win by auto
      hence "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
        using pos by blast
      thus ?thesis
        using \<chi>_spec expr_pos g_def by blast 
      next
        case False
        hence Qp': "{p} \<Zsurj>S Q'" "p' = q"
          using  local.pos_neg_clause Attack.hyps unfolding g_def g'_att_del
          by presburger+
        hence move: "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q')
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)"
          using False by auto
        hence win: "attacker_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed p' Q')"
          using Attack.hyps unfolding g'_att_del g_def
          by (smt (verit) bind.bind_lunit bind.bind_lzero option.distinct(1) option.sel)
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q') (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<phi>
          \<and> expr_pr_inner \<phi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          using Attack move unfolding g_def g'_att_del g_def
          by (smt (verit) bind.bind_lunit bind_eq_None_conv option.discI option.sel)
        then obtain \<chi> where \<chi>_spec:
            "strategy_formula_inner (Attacker_Delayed p' Q') (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi>"
            "expr_pr_inner \<chi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1))"
          by blast
        hence "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
            neg Qp' win move by blast
        thus ?thesis
          using \<chi>_spec  Attack.hyps expr_neg move
          unfolding g'_att_del g_def
          by (smt (verit, best) bind.bind_lunit bind_eq_None_conv option.distinct(1) option.sel)
      qed
  next
    case 4
    hence "\<not>attacker g" by auto
    with Attack show ?case by blast
  next
    case 5
    hence "\<not>attacker g" by auto
    with Attack show ?case by blast
  next
    case 6
    hence "\<not>attacker g" by auto
    with Attack show ?case by blast
  next
    case 7
    then obtain p Q where g_def: "g = Attacker_Branch p Q " by auto
    hence N: "spectroscopy_moves (Attacker_Branch p Q) g' \<noteq> None " using Attack by simp
    hence g'_def: "g' = Attacker_Immediate p Q" using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(17,51,57,61,66,71)) 
    hence move: "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0" using g_def by simp
    from N have " \<exists>\<phi>. strategy_formula g' (updated g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> updated g g' e"
      using g_def g'_def Attack by auto
     then obtain \<phi> where "strategy_formula g' (updated g g' e) \<phi> \<and> expressiveness_price \<phi> \<le> updated g g' e" by auto
     hence "(strategy_formula (Attacker_Immediate p Q) (e - E 1 0 0 0 0 0 0 0) \<phi>)
        \<and> expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0" 
       using move Attack.hyps(3) unfolding g_def g'_def
       by (smt (verit, del_insts) option.distinct(1) option.sel)
     thus ?case unfolding g_def by auto
  }
next
  case (Defense g e)
  {
    case 1
    then show ?case using Defense by force
  next
    case 2
    then show ?case using Defense by force
  next
    case 3
    then show ?case using Defense by force
  next
    case 4
    then obtain p Q where g_def: "g = Defender_Conj p Q" by auto
    hence moves:
      "\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (\<exists>e'. weight g g' e = Some e' \<and> attacker_wins e' g')
        \<and> (\<exists>q. g' = (Attacker_Clause p q))"
      using Defense local.conj_answer
      by (metis (no_types, lifting) spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(34,35,36,37,38,39))
    show ?case
    proof (cases "Q = {}")
      case True
      then obtain \<Phi> where "\<forall>q \<in> Q.
          spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q)  = (subtract 0 0 1 0 0 0 0 0)
          \<and> (attacker_wins (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"
        by (auto simp add: emptyE)
      hence Strat: "strategy_formula_inner (Defender_Conj p Q) e (Conj {} \<Phi>)"
        using \<open>Q = {}\<close> conj by blast
      hence
        "modal_depth_srbb_inner (Conj Q \<Phi>) = Sup ((modal_depth_srbb_conjunct \<circ> \<Phi>) ` Q)"
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
      hence
        "modal_depth_srbb_inner (Conj Q \<Phi>) = 0"
        "branch_conj_depth_inner (Conj Q \<Phi>) = 0"
        "inst_conj_depth_inner (Conj Q \<Phi>) = 0"
        "st_conj_depth_inner (Conj Q \<Phi>) = 0"
        "imm_conj_depth_inner (Conj Q \<Phi>) = 0"
        "max_pos_conj_depth_inner (Conj Q \<Phi>) = 0"
        "max_neg_conj_depth_inner (Conj Q \<Phi>) = 0"
        "neg_depth_inner (Conj Q \<Phi>) = 0"
        using \<open>Q = {}\<close> by (simp add: bot_enat_def)+
      hence "expr_pr_inner (Conj Q \<Phi>) = (E 0 0 0 0 0 0 0 0)"
        using \<open>Q = {}\<close> by force
      hence price: "expr_pr_inner (Conj Q \<Phi>) \<le> e"
        by auto
      with Strat price show "(\<exists>\<phi>. strategy_formula_inner g e \<phi> \<and> expr_pr_inner \<phi> \<le> e)"
        using True g_def by blast
    next
      case False
      hence fa_q: "\<forall>q \<in> Q. \<exists>e'.
        Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
        \<and> spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = (subtract 0 0 1 0 0 0 0 0)
        \<and> attacker_wins e' (Attacker_Clause p q)"
        using moves local.conj_answer option.distinct(1) unfolding g_def
        by (smt (z3) option.sel)
      have q_ex_e': "\<forall>q \<in> Q.  \<exists>e'.
           spectroscopy_moves g (Attacker_Clause p q) = subtract 0 0 1 0 0 0 0 0
        \<and> Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
        \<and> attacker_wins e' (Attacker_Clause p q)
        \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<phi> \<and> expr_pr_conjunct \<phi> \<le> e')"
      proof safe
        fix q
        assume \<open>q \<in> Q\<close>
        then obtain e' where e'_spec:
          \<open>Some e' = subtract_fn 0 0 1 0 0 0 0 0 e\<close>
          \<open>spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = (subtract 0 0 1 0 0 0 0 0)\<close>
          \<open>attacker_wins e' (Attacker_Clause p q)\<close>
          using fa_q by blast
        hence \<open>weight g (Attacker_Clause p q) e = Some e'\<close>
          by (simp add: g_def)
        then have \<open>\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<phi> \<and> expr_pr_conjunct \<phi> \<le> e'\<close>
          using Defense.IH e'_spec unfolding g_def
          by (metis (no_types, lifting) option.distinct(1) option.sel)
        thus \<open>\<exists>e'. spectroscopy_moves g (Attacker_Clause p q) = (subtract 0 0 1 0 0 0 0 0) \<and>
              Some e' = subtract_fn 0 0 1 0 0 0 0 0 e \<and>
              attacker_wins e' (Attacker_Clause p q) \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<phi> \<and> expr_pr_conjunct \<phi> \<le> e')\<close>
          using e'_spec g_def by blast
      qed
      hence "\<exists>\<Phi>. \<forall>q \<in> Q.
        attacker_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q)
        \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))"
        unfolding g_def
        by (metis (no_types, opaque_lifting) option.distinct(1) option.inject)
      then obtain \<Phi> where IH:
          "\<forall>q \<in> Q. attacker_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q)
            \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
            \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))" by auto
      hence "strategy_formula_inner g e (Conj Q \<Phi>)"
        by (simp add: \<open>g = Defender_Conj p Q\<close> conj)
      from IH have "expr_pr_inner (Conj Q \<Phi>) \<le> e"
        using expr_conj \<open>Q \<noteq> {}\<close> q_ex_e'
        by (metis (no_types, lifting) equals0I option.distinct(1))
      thus ?thesis using \<open>strategy_formula_inner g e (Conj Q \<Phi>)\<close> by blast
    qed
  next
    case 5
    then obtain p Q where "g = Defender_Stable_Conj p Q" by blast
    hence cases: "\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (attacker_wins (the (spectroscopy_moves (Defender_Stable_Conj p Q) g') e) g') \<and>((\<exists>p' q. g' = (Attacker_Clause p' q)) \<or> (\<exists>p' Q'. g' = (Defender_Conj p' Q')))"
      using spectroscopy_defender.cases spectroscopy_moves.simps(42) spectroscopy_moves.simps(49) spectroscopy_moves.simps(55) spectroscopy_moves.simps(65) spectroscopy_moves.simps(75)
      by (metis Defense)
    have "Q = {} \<or> (Q \<noteq> {} \<and> (\<forall>g'. spectroscopy_moves g g' \<noteq> None \<longrightarrow> (\<exists>p' q. g' = (Attacker_Clause p' q))))"
      by (metis \<open>g = Defender_Stable_Conj p Q\<close> cases local.empty_stbl_conj_answer)
    then show ?case proof(rule disjE)
      assume "Q = {}"
      hence \<Phi>_ex: "\<exists>\<Phi>. (spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p Q) 
    = (subtract 0 0 0 1 0 0 0 0) \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)
      \<and> strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 1 0 0 0 0)) (Conj Q \<Phi>))"
        using conj
        by (metis Defense \<open>g = Defender_Stable_Conj p Q\<close> all_not_in_conv local.empty_stbl_conj_answer option.sel option.simps(3))
      hence "attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)" by blast

      from \<Phi>_ex obtain \<Phi> where \<Phi>_prop: "(spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p Q) 
    = (subtract 0 0 0 1 0 0 0 0) \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Defender_Conj p Q)
      \<and> strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 1 0 0 0 0)) (Conj Q \<Phi>))"
        by blast
      hence "strategy_formula_inner g e (StableConj Q \<Phi>)" 
        using \<open>g = Defender_Stable_Conj p Q\<close> by (simp add: \<open>Q = {}\<close> \<open>g = Defender_Stable_Conj p Q\<close> stable_conj)
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
        using \<open>attacker_wins (e - E 0 0 0 1 0 0 0 0) (Defender_Conj p Q)\<close> attacker_wins.simps by blast
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
        = (subtract 0 0 0 1 0 0 0 0) \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)"
        using \<open>g = Defender_Stable_Conj p Q\<close> cases by force
      hence "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0)" by blast
      hence "\<forall>q \<in> Q. \<exists>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None" 
        by blast
      hence "\<forall>q \<in> Q. \<exists>g'. attacker_wins (weight g g' e) g' \<and> (\<exists>\<phi>. strategy_formula_conjunct g' (weight g g' e) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g g' e)"
        using Defense \<open>g = Defender_Stable_Conj p Q\<close> cases
        by (metis assm)
      hence IH: "\<forall>q \<in> Q. attacker_wins (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q) \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) \<phi> \<and>
                  expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q) e)" 
        by (metis Defense \<open>\<forall>q\<in>Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) = subtract 0 0 0 1 0 0 0 0 \<and> attacker_wins (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q)\<close> \<open>g = Defender_Stable_Conj p Q\<close> option.distinct(1) option.sel)

      hence "\<exists>\<Phi>. \<forall>q \<in> Q. attacker_wins (e - E 0 0 0 1 0 0 0 0) (Attacker_Clause p q) \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
                  expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e)"
        by meson 
      hence "\<exists>\<Phi>. (\<forall>q \<in> Q. strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)
              \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
              expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e))"
        using Defense \<open>g = Defender_Stable_Conj p Q\<close> cases  
        by meson
      hence "\<exists>\<Phi>. (\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)
          \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 0 1 0 0 0 0) (\<Phi> q) \<and>
              expr_pr_conjunct (\<Phi> q) \<le> weight g (Attacker_Clause p q) e))"
        using fa_q by blast
      then obtain \<Phi> where \<Phi>_prop: "(\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> attacker_wins (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
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
    hence F: "\<forall>q\<in>Q. (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q)  (weight g (Attacker_Clause p q)  e) \<phi> \<and> expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q)  e)"
      using Defense \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> by (metis option.distinct(1)) 

    have A: "\<forall> q\<in> Q. \<exists>\<phi>. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) \<phi> \<and> expr_pr_conjunct \<phi> \<le> (e - (E 0 1 1 0 0 0 0 0))" proof
      fix q
      assume "q\<in> Q"
      hence  "(\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q)  (weight g (Attacker_Clause p q)  e) \<phi> \<and> expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q)  e)" using F by simp
      then obtain \<phi> where " strategy_formula_conjunct (Attacker_Clause p q)  (weight g (Attacker_Clause p q)  e) \<phi> \<and> expr_pr_conjunct \<phi> \<le> weight g (Attacker_Clause p q)  e" by auto
      hence F: "strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) \<phi> \<and> expr_pr_conjunct \<phi> \<le> (e - (E 0 1 1 0 0 0 0 0))" using M \<open>q\<in> Q\<close>
        using \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> option.sel by auto

      from M have "attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)" using assms \<open>q\<in> Q\<close>
        by (metis Defense \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> option.distinct(1) option.sel) 
      hence  "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) \<phi> \<and> expr_pr_conjunct \<phi> \<le> (e - (E 0 1 1 0 0 0 0 0))" using F \<open>q\<in> Q\<close> M by simp
      thus "\<exists>\<phi>. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) \<phi> \<and> expr_pr_conjunct \<phi> \<le> (e - (E 0 1 1 0 0 0 0 0))" by auto
    qed
    define \<Phi> where "\<Phi>=(\<lambda>q. if q\<in> Q then (SOME \<phi>.(spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) \<phi>) \<and> expr_pr_conjunct \<phi> \<le> (e - (E 0 1 1 0 0 0 0 0))) else undefined)"
    hence "\<exists>\<Phi>.\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q) \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 1 1 0 0 0 0 0))" using A M
      by meson
    then obtain \<Phi> where A: "\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> attacker_wins (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q) \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 1 1 0 0 0 0 0))" by auto

    have E: "\<exists>p Q. Attacker_Branch p' (soft_step_set Qa \<alpha>) = Attacker_Branch p Q" by auto

    have M: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) =Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
      by (simp add: soft_step_set_is_soft_step_set) 
    hence "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) \<noteq> None"
      by (simp add: option.discI) 
    hence "(\<exists>p Q. (Attacker_Branch p' (soft_step_set Qa \<alpha>)) = Attacker_Branch p Q \<and>
                  (\<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0))" using E Defense \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close>
      by (metis (no_types, lifting) spectroscopy_position.inject(2))
    then obtain p'' Q'' where IH2: "(Attacker_Branch p' (soft_step_set Qa \<alpha>)) = Attacker_Branch p'' Q'' \<and>
                  (\<exists>\<phi>. strategy_formula (Attacker_Immediate p'' Q'') (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0)" by auto
    hence "p''=p'" and "Q'' = (soft_step_set Qa \<alpha>)" by auto
    then obtain \<phi> where "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) (weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi> \<and>
                        expressiveness_price \<phi> \<le> weight g (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0" using IH2 by auto
    hence A0: "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))  \<phi> \<and>
                        expressiveness_price \<phi> \<le> ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) " using M
      by (simp add: \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> comp_apply option.sel) 
    hence A1: "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))  \<phi>" by simp

    have A2: "spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) = (subtract 1 0 0 0 0 0 0 0)" by simp

    from M have win_branch: "attacker_wins ((min1_6 (e - E 0 1 1 0 0 0 0 0))) (Attacker_Branch p' (soft_step_set Qa \<alpha>))" using assms
      by (metis Defense E \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close> bot_enat_def comp_apply option.distinct(1) option.sel)
    hence "\<exists>g''. ((spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None) \<and> (attacker_wins ((weight (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'') (min1_6 (e - E 0 1 1 0 0 0 0 0))) g''))" 
      using attacker_wins.simps
      by (meson spectroscopy_defender.simps(2)) 
    then obtain g'' where X: "((spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None) \<and> (attacker_wins ((weight (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'') (min1_6 (e - E 0 1 1 0 0 0 0 0))) g''))" by auto
    hence "g''= (Attacker_Immediate p' (soft_step_set Qa \<alpha>))" using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(17) spectroscopy_moves.simps(51) spectroscopy_moves.simps(57) spectroscopy_moves.simps(61) spectroscopy_moves.simps(66) spectroscopy_moves.simps(71)) 
    hence win_immediate: "(attacker_wins ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))
                  (Attacker_Immediate p' (soft_step_set Qa \<alpha>)))" using X A1
      by (simp add: A2 option.sel)

    hence "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (attacker_wins ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' (soft_step_set Qa \<alpha>)))
            \<and> strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>" using M A2 A1 by auto
    hence E: "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' Q') 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (attacker_wins ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>"
      by blast 
    
    hence S: "strategy_formula_inner g e (BranchConj \<alpha> \<phi> Q \<Phi>)" using A E branch_conj
      by (simp add: \<open>g = Defender_Branch p \<alpha> p' Q Qa\<close>)

    have above_one: \<open>0 < min (one e) (six e)\<close>
      using win_immediate win_branch
      by (metis  energy.distinct(1) energy.sel(1,6) gr_zeroI idiff_0_right attacker_wins.simps
          leq_not_eneg min_1_6_simps(1) min_eneg(1) minus_energy_def not_one_le_zero)

    from A have "\<forall>q \<in> Q. expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 1 1 0 0 0 0 0))" by auto
    moreover from A0 have "expressiveness_price \<phi> \<le> ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))" by simp
    moreover hence \<open>modal_depth_srbb \<phi> \<le> min (one e) (six e) - 1\<close>
      by (auto, smt (verit, best) antisim eneg_leq energy.distinct(1) energy.sel(1) energy.sel(6) idiff_0_right leq_not_eneg min_1_6_simps(1) min_eneg(1) minus_energy_def)
    hence \<open>1 + modal_depth_srbb \<phi> \<le> min (one e) (six e)\<close> using above_one
      by (metis add.right_neutral add_diff_cancel_enat add_mono_thms_linordered_semiring(1) enat.simps(3) enat_defs(2) ileI1 le_iff_add plus_1_eSuc(1)) 
    moreover hence \<open>1 + modal_depth_srbb \<phi> \<le> six e\<close> by simp
    ultimately have "expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e"
      using expr_br_conj
      by metis
    then show ?case using S by blast
  next
    case 7
    hence "attacker g"
      by auto
    then show ?case using Defense
      by blast
  }
qed

text \<open>To prove \<open>spectroscopy_game_correctness\<close> we need the following implication:
If \<open>\<phi>\<close> is a strategy formula for \<open>Attacker_Immediate p Q\<close> with energy \<open>e\<close>, then \<open>\<phi>\<close> distinguishes 
\<open>p\<close> from \<open>Q\<close>. 
\\
\\
We prove a more detailed result for all possible game positions \<open>g\<close> by induction. Note that the 
case of \<open>g\<close> being an attacker branching position is not explicitly needed as part of the induction
hypothesis but is proven as a part of case \<open>branch_conj\<close>. The induction relies on the inductive 
structure of strategy formulas. 
\\
Since our formalization differentiates immediate conjunctions and conjunctions, two \<open>Defender_Conj\<close> 
cases are necessary. Specifically, the strategy construction rule \<open>early_conj\<close> uses immediate 
conjunctions, while \<open>late_conj\<close> uses conjunctions. \label{deviation:lemma3}
\<close>

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
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) 
          \<longrightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>(p \<mapsto>a \<alpha> p')
          \<longrightarrow> distinguishes_from_inner \<chi> p (Q\<union>Qa)
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
       attacker_wins e (Attacker_Delayed p' Q) \<and>
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
     attacker_wins (e - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
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
    by (smt (verit, del_insts) local.f_or_early_conj option.distinct(1) spectroscopy_position.simps(50) spectroscopy_position.simps(55))
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
       attacker_wins (min1_6 e) (Attacker_Delayed p Q') \<and>
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
        attacker_wins (min1_7 (e - E 0 0 0 0 0 0 0 1)) (Attacker_Delayed q P')) \<and>
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
       attacker_wins e (Defender_Stable_Conj p Q') \<and>
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
  case (branch p Q e \<chi>)
  then obtain p' Q' \<alpha> Q\<alpha> where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id \<and>
     attacker_wins e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) \<and>
     strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi> \<and>
     (case Defender_Branch p \<alpha> p' Q' Q\<alpha> of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> distinguishes_from_inner \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> distinguishes_from_inner \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> distinguishes_from_inner \<chi> p Q | _ \<Rightarrow> True)" by blast
  hence "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some id" by simp
  hence "p \<mapsto>a \<alpha> p'"
    by (metis local.br_conj option.distinct(1)) 
  from IH have "p \<mapsto>a \<alpha> p' \<longrightarrow> distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" by simp
  hence D: "distinguishes_from_inner \<chi> p (Q' \<union> Q\<alpha>)" using \<open>p \<mapsto>a \<alpha> p'\<close> by auto

  from IH have "Q' = Q - Q\<alpha> \<and> p \<mapsto>a \<alpha> p' \<and> Q\<alpha> \<subseteq> Q"
    by (metis (no_types, lifting) br_conj option.discI)
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
         attacker_wins (min1_6 (e - E 0 1 1 0 0 0 0 0) - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
         strategy_formula (Attacker_Immediate p' Q') (min1_6 (e - E 0 1 1 0 0 0 0 0) - E 1 0 0 0 0 0 0 0) \<psi> \<and>
         (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<psi> p Q
          | Defender_Conj p Q \<Rightarrow> distinguishes_from \<psi> p Q | _ \<Rightarrow> True)" by auto
  hence " distinguishes_from \<psi> p' Q'" by simp
  hence X:"p' \<Turnstile>SRBB \<psi>" by (simp add: distinguishes_from_def) 
  have Y: "\<forall>q \<in> Q'. \<not>(q \<Turnstile>SRBB \<psi>)" using \<open>distinguishes_from \<psi> p' Q'\<close>  by (simp add: distinguishes_from_def) 

  have "(p \<mapsto>a \<alpha> p') \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>) " proof
    assume "p \<mapsto>a \<alpha> p'"
    hence "p \<mapsto>a \<alpha> p'" by simp
    from IH have "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q') =
         Some (min1_6 \<circ> (\<lambda>x. x - E 0 1 1 0 0 0 0 0))" by auto
    hence "Q\<alpha> \<mapsto>aS \<alpha> Q'"
      by (metis local.br_obsv option.distinct(1))

    hence A2: "hml_srbb_inner_models (Obs \<alpha> \<psi>) p" using X \<open>p \<mapsto>a \<alpha> p'\<close>  by auto  

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

    have A4: "hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) p"
      using A3 A2 unfolding distinguishes_inner_def
      by fastforce
    from A3 have "\<forall>q \<in> (Q1 \<union> Q\<alpha>). \<not>(hml_srbb_inner_models (BranchConj \<alpha> \<psi> Q1 \<Phi>) q)"
      using distinguishes_inner_def by blast 

    thus "distinguishes_from_inner (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)" using A4 distinguishes_from_inner_def by simp 
  qed 
  then show ?case by simp
qed

end (* context full_spec_game *)

end
