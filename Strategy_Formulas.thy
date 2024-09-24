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
  "strategy_formula_inner (Defender_Branch p \<alpha> p' Q Q\<alpha>) e (BranchConj \<alpha> \<phi> Q \<Phi>)"
    if "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p' Q') 
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (attacker_wins (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>"
        
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
    "case g of
        Attacker_Immediate p Q \<Rightarrow> \<exists>\<phi>. strategy_formula g e \<phi> \<and> expressiveness_price \<phi> \<le> e
      | Attacker_Delayed p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
      | Attacker_Clause p q \<Rightarrow> \<exists>\<psi>. strategy_formula_conjunct g e \<psi> \<and> expr_pr_conjunct \<psi> \<le> e
      | Defender_Conj p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
      | Defender_Stable_Conj p Q \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi>  \<and> expr_pr_inner \<chi> \<le> e
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> \<exists>\<chi>. strategy_formula_inner g e \<chi> \<and> expr_pr_inner \<chi> \<le> e
      | Attacker_Branch p Q \<Rightarrow>
            \<exists>\<phi>. strategy_formula (Attacker_Immediate p Q) (e - E 1 0 0 0 0 0 0 0) \<phi>
              \<and> expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0"
  using assms 
proof(induction rule: attacker_wins.induct)
  case (Attack g g' e e')
  then show ?case
  proof (induct g)
    case (Attacker_Immediate p Q)
    hence move: "
      (\<exists>p Q. g' = Defender_Conj p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weight g g' e)) \<phi> \<and> expr_pr_inner \<phi> \<le> updated g g' e) \<and> 
      (\<exists>p Q. g' = Attacker_Delayed p Q) \<longrightarrow>
        (\<exists>\<phi>. strategy_formula_inner g' (the (weight g g' e)) \<phi> \<and> expr_pr_inner \<phi> \<le> updated g g' e)" 
      using attacker_wins.cases
      by simp
    from move Attacker_Immediate have move_cases: "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g' = (Defender_Conj p' Q'))"
      using spectroscopy_moves.simps
      by (smt (verit, del_insts) spectroscopy_defender.elims(2,3))
    show ?case using move_cases
    proof(rule disjE)
      assume "\<exists>p' Q'. g' = Attacker_Delayed p' Q'"
      then obtain p' Q' where g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
      have e_comp: "(the (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')) e) = (Some e)"
        by (smt (verit, ccfv_threshold) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay g'_att_del Attacker_Immediate move option.exhaust_sel option.inject)
      have "p' = p"
        by (metis g'_att_del Attacker_Immediate(2) spectroscopy_moves.simps(1))
      moreover have "(attacker_wins e (Attacker_Delayed p Q'))"
        using \<open>g' = Attacker_Delayed p' Q'\<close> \<open>p' = p\<close> Attacker_Immediate win_a_upwards_closure e_comp
        by simp
      ultimately have "(\<exists>\<chi>. strategy_formula_inner g' (the (weight (Attacker_Immediate p Q) g' e)) \<chi> \<and>
        expr_pr_inner \<chi> \<le> updated (Attacker_Immediate p Q) g' e)"
        using g'_att_del Attacker_Immediate by fastforce
      then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using \<open>p' = p\<close> \<open>weight (Attacker_Immediate p Q) (Attacker_Delayed p' Q') e = Some e\<close> g'_att_del by auto
      hence "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
      = (Some Some)) \<and> (attacker_wins e (Attacker_Delayed p Q')) 
        \<and> strategy_formula_inner (Attacker_Delayed p Q') e \<chi>))"
        using g'_att_del
        by (smt (verit) Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.delay \<open>attacker_wins e (Attacker_Delayed p Q')\<close> Attacker_Immediate)
      hence "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay by blast
      moreover have "expressiveness_price (Internal \<chi>) \<le> e"
        using \<open>(strategy_formula_inner (Attacker_Delayed p Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)\<close>
        by auto
      ultimately show ?case by auto
    next
      assume "\<exists>p' Q'. g' = Defender_Conj p' Q'"
      then obtain p' Q' where g'_def_conj: "g' = Defender_Conj p' Q'" by blast
      hence M: "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') = (subtract 0 0 0 0 1 0 0 0)"
        using local.f_or_early_conj Attacker_Immediate by presburger
      hence Qp': "Q\<noteq>{}" "Q = Q'" "p = p'"
        using Attack.hyps(2) Attacker_Immediate g'_def_conj local.f_or_early_conj by metis+
      from M have "updated (Attacker_Immediate p Q) (Defender_Conj p' Q') e
                = e - (E 0 0 0 0 1 0 0 0)"
        using Attack.hyps(3) g'_def_conj Attacker_Immediate
        by (smt (verit) option.distinct(1) option.sel)
      hence "(attacker_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q'))"
         using g'_def_conj Qp' Attacker_Immediate win_a_upwards_closure by force
      with g'_def_conj have IH_case: "\<exists>\<chi>. strategy_formula_inner g' (updated (Attacker_Immediate p Q) g' e) \<chi> \<and>
        expr_pr_inner \<chi> \<le> updated (Attacker_Immediate p Q) g' e"
        using Attacker_Immediate by auto
      hence "(\<exists>\<chi>. strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<chi> \<and> expr_pr_inner \<chi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
        using \<open>attacker_wins (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p Q')\<close> IH_case Qp'
          \<open>the (weight (Attacker_Immediate p Q) (Defender_Conj p' Q') e) = e - E 0 0 0 0 1 0 0 0\<close> g'_def_conj by auto
      then obtain \<chi> where S: "(strategy_formula_inner (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) \<chi> \<and> expr_pr_inner \<chi> \<le> (e - (E 0 0 0 0 1 0 0 0)))"
        by blast
      hence "\<exists>\<psi>. \<chi> = Conj Q \<psi>"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj Qp' g'_def_conj Attacker_Immediate unfolding Qp'
        by (smt (verit) spectroscopy_moves.simps(60,70) spectroscopy_position.distinct(33) spectroscopy_position.inject(6) strategy_formula_inner.simps)
      then obtain \<psi> where "\<chi> = Conj Q \<psi>" by auto
      hence "strategy_formula (Defender_Conj p Q) (e - (E 0 0 0 0 1 0 0 0)) (ImmConj Q \<psi>)"
        using S strategy_formula_strategy_formula_inner_strategy_formula_conjunct.conj strategy_formula_strategy_formula_inner_strategy_formula_conjunct.imm_conj
        by (smt (verit) Qp' g'_def_conj hml_srbb_inner.inject(2) Attacker_Immediate spectroscopy_defender.simps(4,6) spectroscopy_moves.simps(60) spectroscopy_moves.simps(70) strategy_formula_inner.cases) 
      hence SI: "strategy_formula (Attacker_Immediate p Q) e (ImmConj Q \<psi>)"
         using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay early_conj Qp'
         by (metis (no_types, lifting) \<open>attacker_wins (e - E 0 0 0 0 1 0 0 0) (Defender_Conj p Q')\<close> local.f_or_early_conj)
      have "expr_pr_inner (Conj Q \<psi>) \<le> (e - (E 0 0 0 0 1 0 0 0))" using S \<open>\<chi> = Conj Q \<psi>\<close> by simp
      hence "expressiveness_price (ImmConj Q \<psi>) \<le> e" using expr_imm_conj Qp'
        by (smt (verit) M g'_def_conj Attacker_Immediate option.sel option.simps(3))
      thus ?thesis using SI by auto
    qed
  next
    case (Attacker_Branch p Q)
    hence g'_def: "g' = Attacker_Immediate p Q" using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(17,51,57,61,66,71)) 
    hence move: "spectroscopy_moves (Attacker_Branch p Q) g' = subtract 1 0 0 0 0 0 0 0" by simp
    then obtain \<phi> where
      "strategy_formula g' (updated (Attacker_Branch p Q) g' e) \<phi> \<and>
       expressiveness_price \<phi> \<le> updated (Attacker_Branch p Q) g' e"
      using Attacker_Branch g'_def by auto
    hence "(strategy_formula (Attacker_Immediate p Q) (e - E 1 0 0 0 0 0 0 0) \<phi>)
        \<and> expressiveness_price \<phi> \<le> e - E 1 0 0 0 0 0 0 0" 
      using move Attacker_Branch unfolding g'_def
      by (smt (verit, del_insts) option.distinct(1) option.sel)
    then show ?case by auto
  next
    case (Attacker_Clause p q)
    hence "(\<exists>p' Q'. g' = (Attacker_Delayed p' Q'))"
      using Attack.hyps spectroscopy_moves.simps
      by (smt (verit, del_insts) spectroscopy_defender.elims(1))
    then obtain p' Q' where
      g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
    show ?case
    proof(cases \<open>p = p'\<close>)
      case True
      hence "{q} \<Zsurj>S Q'"
        using g'_att_del local.pos_neg_clause Attacker_Clause by presburger
      hence post_win:
        "(the (spectroscopy_moves (Attacker_Clause p q) g') e) = min1_6 e"
         "(attacker_wins (the (min1_6 e)) (Attacker_Delayed p Q'))"
        using \<open>{q} \<Zsurj>S Q'\<close> Attacker_Clause win_a_upwards_closure unfolding True g'_att_del
        by auto
      then obtain \<chi> where \<chi>_spec:
        "strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>"
        "expr_pr_inner \<chi> \<le> the (min1_6 e)"
        using Attacker_Clause Attack True post_win unfolding g'_att_del
        by (smt (verit) option.sel spectroscopy_position.simps(53))
      hence
        "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') = Some min1_6"
        "attacker_wins (the (min1_6 e)) (Attacker_Delayed p Q')"
        "strategy_formula_inner (Attacker_Delayed p Q') (the (min1_6 e)) \<chi>"
        using \<open>{q} \<Zsurj>S Q'\<close> local.pos_neg_clause post_win by auto
      hence "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay pos
        by blast
      thus ?thesis
        using \<chi>_spec expr_pos by fastforce
      next
        case False
        hence Qp': "{p} \<Zsurj>S Q'" "p' = q"
          using  local.pos_neg_clause Attacker_Clause unfolding g'_att_del
          by presburger+
        hence move: "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q')
          = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)"
          using False by auto
        hence win: "attacker_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed p' Q')"
          using Attacker_Clause unfolding g'_att_del
          by (smt (verit) bind.bind_lunit bind.bind_lzero option.distinct(1) option.sel)
        hence "(\<exists>\<phi>. strategy_formula_inner (Attacker_Delayed p' Q') (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<phi>
          \<and> expr_pr_inner \<phi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1)))"
          using Attack Attacker_Clause move unfolding g'_att_del
          by (smt (verit, del_insts) bind.bind_lunit bind_eq_None_conv option.discI option.sel spectroscopy_position.simps(53))
        then obtain \<chi> where \<chi>_spec:
            "strategy_formula_inner (Attacker_Delayed p' Q') (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi>"
            "expr_pr_inner \<chi> \<le> the (min1_7 (e - E 0 0 0 0 0 0 0 1))"
          by blast
        hence "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)"
          using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.delay
            neg Qp' win move by blast
        thus ?thesis
          using \<chi>_spec Attacker_Clause expr_neg move
          unfolding g'_att_del
          by (smt (verit, best) bind.bind_lunit bind_eq_None_conv option.distinct(1) option.sel spectroscopy_position.simps(52))
      qed
  next
    case (Attacker_Delayed p Q)
    then consider
      (Att_Del) "(\<exists>p Q. g' = Attacker_Delayed p Q)" | (Att_Imm) "(\<exists>p' Q'. g' = (Attacker_Immediate p' Q'))" |
      (Def_Conj) "(\<exists>p Q. g' = (Defender_Conj p Q))" | (Def_St_Conj) "(\<exists>p Q. g' = (Defender_Stable_Conj p Q))" |
      (Def_Branch) "(\<exists>p' \<alpha> p'' Q' Q\<alpha>. g' = (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
      by (smt (verit, ccfv_threshold) spectroscopy_defender.elims(1) spectroscopy_moves.simps(27,28))
    then show ?case
    proof (cases)
      case Att_Del
      then obtain p' Q' where
        g'_att_del: "g' = Attacker_Delayed p' Q'" by blast
      have Qp': "Q' = Q" "p \<noteq> p'" "p \<mapsto> \<tau> p'"
        using Attacker_Delayed g'_att_del Inhabited_Tau_LTS_axioms Spectroscopy_Game.Inhabited_Tau_LTS.procrastination
        by metis+
      hence e_comp: "(the (spectroscopy_moves (Attacker_Delayed p Q) g') e) = Some e"
        using g'_att_del
        by simp
      hence att_win: "(attacker_wins e (Attacker_Delayed p' Q'))"
        using g'_att_del Qp' Attacker_Delayed attacker_wins.Defense e_comp
        by (metis option.sel)
      have "(updated (Attacker_Delayed p Q) g' e) = e"
        using g'_att_del Attacker_Delayed e_comp by fastforce
      then obtain \<chi> where "(strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e)"
        using Attacker_Delayed g'_att_del by auto 
      hence "\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = (Some Some)
         \<and>  attacker_wins e (Attacker_Delayed p' Q)
         \<and> strategy_formula_inner (Attacker_Delayed p' Q) e \<chi>"
        using e_comp g'_att_del Qp' local.procrastination Attack.hyps att_win
          Spectroscopy_Game.Inhabited_Tau_LTS.procrastination
        by (metis Inhabited_Tau_LTS_axioms)
      hence "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
        using strategy_formula_strategy_formula_inner_strategy_formula_conjunct.procrastination by blast
      moreover have "expr_pr_inner \<chi> \<le> e"
        using \<open>strategy_formula_inner (Attacker_Delayed p' Q') e \<chi> \<and> expr_pr_inner \<chi> \<le> e\<close> by blast
      ultimately show ?thesis by auto
    next
      case Att_Imm
      then obtain p' Q' where
        g'_att_imm: "g' = Attacker_Immediate p' Q'" by blast 
      hence move: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') \<noteq> None"
        using Attacker_Delayed by blast
      hence "\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q'" unfolding spectroscopy_moves.simps(3) by presburger
      then obtain \<alpha> where \<alpha>_prop: "p \<mapsto>a \<alpha> p'" "Q \<mapsto>aS \<alpha> Q'" by blast
      moreover then have weight:
        "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0"
        by (simp, metis)
      moreover then have update: "updated (Attacker_Delayed p Q) g' e = e - (E 1 0 0 0 0 0 0 0)"
        using g'_att_imm Attacker_Delayed
        by (smt (verit, del_insts) option.distinct(1) option.sel)
      moreover then obtain \<chi> where \<chi>_prop:
        "strategy_formula (Attacker_Immediate p' Q') (e - E 1 0 0 0 0 0 0 0) \<chi>"
        "expressiveness_price \<chi> \<le> e - E 1 0 0 0 0 0 0 0"
        using Attacker_Delayed g'_att_imm
        by auto
      moreover have \<open>attacker_wins (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')\<close> 
        using attacker_wins.Attack Attack.hyps(4) Attacker_Delayed.prems(3) calculation(4) g'_att_imm
        by force
      ultimately have "strategy_formula_inner (Attacker_Delayed p Q) e (Obs \<alpha> \<chi>)"
        using local.observation[of p Q e \<chi> \<alpha>] by blast
      moreover have "expr_pr_inner (Obs \<alpha> \<chi>) \<le> e"
        using expr_obs \<chi>_prop Attacker_Delayed g'_att_imm weight update
        by (smt (verit) option.sel)
      ultimately show ?thesis by auto
    next
      case Def_Conj
      then obtain p' Q' where
        g'_def_conj: "g' = Defender_Conj p' Q'" by blast
      hence  "p = p'" "Q = Q'" 
        using local.late_inst_conj Attacker_Delayed by presburger+
      hence "the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')) e = Some e"
        by fastforce
      hence "attacker_wins e (Defender_Conj p' Q')"  "updated g g' e = e" 
        using Attacker_Delayed Attack unfolding g'_def_conj by simp+
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
          full_spec_game.late_conj full_spec_game_axioms by fastforce
    next
      case Def_St_Conj
      then obtain p' Q' where g'_def: "g' = Defender_Stable_Conj p' Q'" by blast
      hence pQ': "p = p'" "Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}" "\<nexists>p''. p \<mapsto>\<tau> p''"
        using local.late_stbl_conj Attacker_Delayed
        by meson+
      hence "(the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')) e) = Some e"
        by auto
      hence "attacker_wins e (Defender_Stable_Conj p' Q')" "updated g g' e = e" 
        using Attacker_Delayed Attack unfolding g'_def by force+
      then obtain \<chi> where \<chi>_prop:
        "strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>" "expr_pr_inner \<chi> \<le> e"
        using Attack g'_def by auto
      have "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') = Some Some
        \<and> attacker_wins e (Defender_Stable_Conj p' Q')
        \<and> strategy_formula_inner (Defender_Stable_Conj p' Q') e \<chi>"
        using Attack \<chi>_prop \<open>attacker_wins e (Defender_Stable_Conj p' Q')\<close> local.late_stbl_conj  pQ'
        unfolding g'_def
        by force
      thus ?thesis using local.stable[of p Q e \<chi>] pQ' \<chi>_prop by fastforce 
    next
      case Def_Branch
      then obtain p' \<alpha> p'' Q' Q\<alpha> where
        g'_def_br: "g' = Defender_Branch p' \<alpha> p'' Q' Q\<alpha>" by blast
      hence pQ': "p = p'" "Q' = Q - Q\<alpha>" "p \<mapsto>a \<alpha> p''" "Q\<alpha> \<subseteq> Q"
        using local.br_conj Attacker_Delayed by metis+
      hence "the (spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)) e = Some e"
        by auto
      hence post: "attacker_wins e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)" "updated g g' e = e" 
        using Attack option.inject Attacker_Delayed unfolding g'_def_br by auto
      then obtain \<chi> where \<chi>_prop:
        "strategy_formula_inner (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e \<chi>" "expr_pr_inner \<chi> \<le> e"
        using g'_def_br Attack Attacker_Delayed
        by auto
      hence "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) = Some Some
         \<and> attacker_wins e (Defender_Branch p \<alpha> p'' Q' Q\<alpha>)
         \<and> strategy_formula_inner (Defender_Branch p \<alpha> p'' Q' Q\<alpha>) e \<chi>"
        using g'_def_br local.branch Attack post pQ' by simp
      hence "strategy_formula_inner (Attacker_Delayed p Q) e \<chi>"
        using Attack Attacker_Delayed local.br_conj branch
        unfolding g'_def_br by fastforce
      thus ?thesis using \<chi>_prop
        by fastforce
    qed
  next
    case (Defender_Branch)
    thus ?case by force
  next
    case (Defender_Conj)
    thus ?case by force
  next
    case (Defender_Stable_Conj)
    thus ?case by force
  qed
next
  case (Defense g e)
  thus ?case
  proof (induct g)
    case (Attacker_Immediate)
    thus ?case by force
  next
    case (Attacker_Branch)
    thus ?case by force
  next
    case (Attacker_Clause)
    thus ?case by force
  next
    case (Attacker_Delayed)
    thus ?case by force
  next
    case (Defender_Branch p \<alpha> p' Q Qa)
    hence conjs:
      "\<forall>q\<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) = (subtract 0 1 1 0 0 0 0 0)"
      by simp
    obtain e' where e'_spec:
      \<open>\<forall>q\<in>Q. weight (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Clause p q) e = Some e'
        \<and> attacker_wins e' (Attacker_Clause p q)
        \<and> (\<exists>\<psi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<psi> \<and> expr_pr_conjunct \<psi> \<le> e')\<close> 
      using conjs Defender_Branch option.distinct(1) option.sel
      by (smt (z3) spectroscopy_position.simps(52))
    hence e'_def: \<open>Q \<noteq> {} \<Longrightarrow> e' = e - E 0 1 1 0 0 0 0 0\<close> using conjs
        by (smt (verit) all_not_in_conv option.distinct(1) option.sel)
    then obtain \<Phi> where \<Phi>_spec:
      "\<forall>q \<in> Q. strategy_formula_conjunct (Attacker_Clause p q) e' (\<Phi> q) \<and> expr_pr_conjunct (\<Phi> q) \<le> e'"
      using e'_spec by metis

    have obs: "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) =
      Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)"
      by (simp add: soft_step_set_is_soft_step_set)
    have \<open>\<forall>p Q. (Attacker_Branch p' (soft_step_set Qa \<alpha>)) = (Attacker_Branch p Q) \<longrightarrow> p = p' \<and> Q = soft_step_set Qa \<alpha>\<close> by blast   
    with option.discI[OF obs] obtain e'' where
      "\<exists>\<phi>. strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) (e'' - E 1 0 0 0 0 0 0 0) \<phi> 
        \<and> expressiveness_price \<phi> \<le> e'' - E 1 0 0 0 0 0 0 0"
      using Defense.IH option.distinct(1) option.sel
      by (smt (verit, best) Defender_Branch.prems(2) spectroscopy_position.simps(51))
    then obtain \<phi> where
      "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
        (updated (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0) \<phi>" 
      "expressiveness_price \<phi> \<le> updated (Defender_Branch p \<alpha> p' Q Qa) (Attacker_Branch p' (soft_step_set Qa \<alpha>)) e - E 1 0 0 0 0 0 0 0"
      using Defender_Branch.prems(2) option.discI[OF obs]
      by (smt (verit, best) option.sel spectroscopy_position.simps(51))
    hence obs_strat:
      "strategy_formula (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) \<phi>"
      "expressiveness_price \<phi> \<le> (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0))"
      by (smt (verit, best) Defender_Branch.prems(2) bind.bind_lunit bind.bind_lzero obs option.distinct(1) option.sel)+
    have  "spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) 
          = (subtract 1 0 0 0 0 0 0 0)" by simp
    obtain e'' where win_branch:
        \<open>Some e'' = min1_6 (e - E 0 1 1 0 0 0 0 0)\<close>
        "attacker_wins e'' (Attacker_Branch p' (soft_step_set Qa \<alpha>))"
      using Defender_Branch
      by (smt (verit, ccfv_threshold) bind.bind_lunit bind_eq_None_conv obs option.discI option.sel)
    then obtain g'' where g''_spec:
      "spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' \<noteq> None"
      "attacker_wins (updated (Attacker_Branch p' (soft_step_set Qa \<alpha>)) g'' (the (min1_6 (e - E 0 1 1 0 0 0 0 0)))) g''"
      using attacker_wins_GaE
      by (metis option.sel spectroscopy_defender.simps(2)) 
    hence move_immediate:
      "g'' = (Attacker_Immediate p' (soft_step_set Qa \<alpha>))
      \<and> spectroscopy_moves (Attacker_Branch p' (soft_step_set Qa \<alpha>)) (Attacker_Immediate p' (soft_step_set Qa \<alpha>)) = subtract 1 0 0 0 0 0 0 0"
      using br_acct
      by (metis (no_types, lifting) spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(17,51,57,61,66,71)) 
    then obtain e''' where win_immediate:
      "Some e''' = subtract_fn 1 0 0 0 0 0 0 0 e''"
      "attacker_wins e''' (Attacker_Immediate p' (soft_step_set Qa \<alpha>))"
      using g''_spec win_branch attacker_wins.simps local.br_acct
      by (smt (verit) option.distinct(1) option.sel spectroscopy_defender.elims(1) spectroscopy_moves.simps(17,19,20,51,57,61))
    hence strat: "strategy_formula_inner (Defender_Branch p \<alpha> p' Q Qa) e (BranchConj \<alpha> \<phi> Q \<Phi>)"
      using branch_conj obs move_immediate obs_strat \<Phi>_spec conjs e'_def e'_spec
      by (smt (verit, best) option.distinct(1) option.sel win_branch(1))

    have \<open>E 1 0 0 0 0 0 0 0 \<le> e''\<close> using win_branch g''_spec
      by (metis option.distinct(1) win_immediate(1))
    hence above_one: \<open>0 < min (one e) (six e)\<close>
      using win_immediate win_branch
      by (metis energy.sel(1) energy.sel(6) gr_zeroI idiff_0_right leq_components
            min_1_6_simps(1) minus_energy_def not_one_le_zero option.sel)
    have "\<forall>q \<in> Q. expr_pr_conjunct (\<Phi> q) \<le> (e - (E 0 1 1 0 0 0 0 0))"
      using \<Phi>_spec e'_def by blast
    moreover have "expressiveness_price \<phi> \<le> the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0"
      using obs_strat(2) by blast
    moreover hence \<open>modal_depth_srbb \<phi> \<le> min (one e) (six e) - 1\<close>
      by simp
    hence \<open>1 + modal_depth_srbb \<phi> \<le> min (one e) (six e)\<close>
      by (metis above_one add.right_neutral add_diff_cancel_enat add_mono_thms_linordered_semiring(1) enat.simps(3) enat_defs(2) ileI1 le_iff_add plus_1_eSuc(1))
    moreover hence \<open>1 + modal_depth_srbb \<phi> \<le> six e\<close> by simp
    ultimately have "expr_pr_inner (BranchConj \<alpha> \<phi> Q \<Phi>) \<le> e"
      using expr_br_conj[of e e' e'' e''' \<phi> Q \<Phi> \<alpha>] e'_def obs Defender_Branch(2) win_branch(1) win_immediate(1)
      by (smt (verit, best) bind_eq_None_conv expr_br_conj option.distinct(1) option.sel option.simps(3))
    then show ?case using strat by force
  next
    case (Defender_Conj p Q)
    hence moves:
      "\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<longrightarrow> (\<exists>e'. weight (Defender_Conj p Q) g' e = Some e' \<and> attacker_wins e' g')
        \<and> (\<exists>q. g' = (Attacker_Clause p q))"
      using local.conj_answer
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
      with Strat price True show ?thesis by auto
    next
      case False
      hence fa_q: "\<forall>q \<in> Q. \<exists>e'.
        Some e' = subtract_fn 0 0 1 0 0 0 0 0 e
        \<and> spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = (subtract 0 0 1 0 0 0 0 0)
        \<and> attacker_wins e' (Attacker_Clause p q)"
        using moves local.conj_answer option.distinct(1)
        by (smt (z3) option.sel)
      have q_ex_e': "\<forall>q \<in> Q.  \<exists>e'.
           spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = subtract 0 0 1 0 0 0 0 0
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
        hence \<open>weight (Defender_Conj p Q) (Attacker_Clause p q) e = Some e'\<close>
          by simp
        then have \<open>\<exists>\<psi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<psi> \<and> expr_pr_conjunct \<psi> \<le> e'\<close>
          using Defender_Conj e'_spec
          by (smt (verit, best) option.distinct(1) option.sel spectroscopy_position.simps(52))
        thus \<open>\<exists>e'. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) = (subtract 0 0 1 0 0 0 0 0) \<and>
              Some e' = subtract_fn 0 0 1 0 0 0 0 0 e \<and>
              attacker_wins e' (Attacker_Clause p q) \<and> (\<exists>\<phi>. strategy_formula_conjunct (Attacker_Clause p q) e' \<phi> \<and> expr_pr_conjunct \<phi> \<le> e')\<close>
          using e'_spec by blast
      qed
      hence "\<exists>\<Phi>. \<forall>q \<in> Q.
        attacker_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q)
        \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))"
        by (metis (no_types, opaque_lifting) option.distinct(1) option.inject)
      then obtain \<Phi> where IH:
          "\<forall>q \<in> Q. attacker_wins (e - E 0 0 1 0 0 0 0 0) (Attacker_Clause p q)
            \<and> (strategy_formula_conjunct (Attacker_Clause p q) (e - E 0 0 1 0 0 0 0 0) (\<Phi> q)
            \<and> expr_pr_conjunct (\<Phi> q) \<le> (e - E 0 0 1 0 0 0 0 0))" by auto
      hence "strategy_formula_inner (Defender_Conj p Q) e (Conj Q \<Phi>)"
        by (simp add: conj)
      moreover have "expr_pr_inner (Conj Q \<Phi>) \<le> e"
        using IH expr_conj \<open>Q \<noteq> {}\<close> q_ex_e'
        by (metis (no_types, lifting) equals0I option.distinct(1))
      ultimately show ?thesis by auto
    qed
  next
    case (Defender_Stable_Conj p Q)
    hence cases:
      "\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None \<longrightarrow> 
       (\<exists>e'. weight (Defender_Stable_Conj p Q) g' e = Some e' \<and> attacker_wins e' g')
        \<and> ((\<exists>p' q. g' = (Attacker_Clause p' q)) \<or> (\<exists>p' Q'. g' = (Defender_Conj p' Q')))"
      by (metis (no_types, opaque_lifting)
            spectroscopy_defender.elims(2,3) spectroscopy_moves.simps(40,42,43,44,55))
    show ?case
    proof(cases \<open>Q = {}\<close>)
      case True
      then obtain e' where e'_spec:
        \<open>weight (Defender_Stable_Conj p Q) (Defender_Conj p Q) e = Some e'\<close>
        \<open>e' = e - (E 0 0 0 1 0 0 0 0)\<close>
        \<open>attacker_wins e' (Defender_Conj p Q)\<close>
        using cases local.empty_stbl_conj_answer
        by (smt (verit, best) option.discI option.sel)
      then obtain \<Phi> where \<Phi>_prop: "strategy_formula_inner (Defender_Conj p Q) e' (Conj Q \<Phi>)"
        using conj True by blast
      hence strategy: "strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)" 
        by (simp add: True stable_conj)
      have \<open>E 0 0 0 1 0 0 0 0 \<le> e\<close> using e'_spec
        using option.sel True by fastforce
      moreover have \<open>expr_pr_inner (StableConj Q \<Phi>) = E 0 0 0 1 0 0 0 0\<close>
        using True by (simp add: bot_enat_def)
      ultimately have \<open>expr_pr_inner (StableConj Q \<Phi>) \<le> e\<close> by simp
      with strategy show ?thesis by auto
    next
      case False
      then obtain e' where e'_spec:
        \<open>e' = e - (E 0 0 0 1 0 0 0 0)\<close>
        \<open>\<forall>q \<in> Q. weight (Defender_Stable_Conj p Q) (Attacker_Clause p q) e = Some e'
          \<and> attacker_wins e' (Attacker_Clause p q)\<close>
        using cases local.conj_s_answer
        by (smt (verit, del_insts) option.distinct(1) option.sel)
      hence IH: "\<forall>q \<in> Q. \<exists>\<psi>.
        strategy_formula_conjunct (Attacker_Clause p q) e' \<psi> \<and>
        expr_pr_conjunct \<psi> \<le> e'"
        using Defender_Stable_Conj local.conj_s_answer
        by (smt (verit, best) option.distinct(1) option.inject spectroscopy_position.simps(52))
      hence "\<exists>\<Phi>. \<forall>q \<in> Q.
        strategy_formula_conjunct (Attacker_Clause p q) e' (\<Phi> q) \<and>
        expr_pr_conjunct (\<Phi> q) \<le> e'"
        by meson
      then obtain \<Phi> where \<Phi>_prop: "\<forall>q \<in> Q.
        strategy_formula_conjunct (Attacker_Clause p q) e' (\<Phi> q)
        \<and> expr_pr_conjunct (\<Phi> q) \<le> e'"
        by blast
      have \<open>E 0 0 0 1 0 0 0 0 \<le> e\<close>
        using e'_spec False by fastforce
      hence "expr_pr_inner (StableConj Q \<Phi>) \<le> e"
        using expr_st_conj e'_spec \<Phi>_prop False by metis
      moreover have \<open>strategy_formula_inner (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)\<close>
        using \<Phi>_prop e'_spec full_spec_game_axioms full_spec_game.stable_conj
        unfolding e'_spec  by fastforce
      ultimately show ?thesis by auto
    qed
  qed
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
      | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto> \<tau> q) 
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow>(p \<mapsto>a \<alpha> p')
          \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q\<union>Qa)
      | _ \<Rightarrow> True))
      \<and>
      (strategy_formula_conjunct g e \<psi> \<longrightarrow>
        (case g of
        Attacker_Clause p q \<Rightarrow> hml_srbb_conj.distinguishes \<psi> p q
      | _ \<Rightarrow> True))"
proof(induction rule: strategy_formula_strategy_formula_inner_strategy_formula_conjunct.induct)
  case (delay p Q e \<chi>)
  then show ?case
    by (smt (verit) distinguishes_from_def option.discI silent_reachable.intros(1) silent_reachable_trans spectroscopy_moves.simps(1) spectroscopy_position.simps(50) spectroscopy_position.simps(53))
next
  case (procrastination p Q e \<chi>)
  from this obtain p' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) = Some Some \<and>
       attacker_wins e (Attacker_Delayed p' Q) \<and>
       strategy_formula_inner (Attacker_Delayed p' Q) e \<chi> \<and>
       (case Attacker_Delayed p' Q of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q | _ \<Rightarrow> True)" by fastforce
  hence D: "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p' Q"
    using spectroscopy_position.simps(53) by fastforce
  from IH have "p \<Zsurj>p'"
    by (metis option.discI silent_reachable.intros(1) silent_reachable_append_\<tau> spectroscopy_moves.simps(2)) 
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q" using D 
    by (smt (verit) LTS_Tau.silent_reachable_trans distinguishes_from_def hml_srbb_models.simps(2))
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
  hence "p' \<Turnstile>SRBB \<phi>" by auto

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
  have "Q \<Zsurj>S Q \<longrightarrow> (\<forall>q\<in>Q. \<not>(q \<Turnstile>SRBB (Internal (Obs \<alpha> \<phi>))))"
  proof (rule+)
    fix q
    assume
      "Q \<Zsurj>S Q"
      "q \<in> Q"
      "q \<Turnstile>SRBB Internal (Obs \<alpha> \<phi>)" 
    hence "\<exists>q'.  q \<Zsurj> q' \<and> hml_srbb_inner_models q' (Obs \<alpha> \<phi>)" by simp 
    then obtain q' where X: "q \<Zsurj> q' \<and> hml_srbb_inner_models q' (Obs \<alpha> \<phi>)" by auto
    hence "hml_srbb_inner_models q' (Obs \<alpha> \<phi>)" by simp
    hence "q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))"
      using hml_srbb_and_hml_semantics_match by simp
    from X have "q'\<in>Q" using \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
    hence "\<exists>q''\<in>Q'. q' \<mapsto>a \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" using \<open>Q \<mapsto>aS \<alpha> Q'\<close> \<open>q' \<Turnstile> (HML_soft_poss \<alpha> (hml_srbb_to_hml \<phi>))\<close>
      using hml_srbb_and_hml_semantics_match by auto
    then obtain q'' where "q''\<in>Q'\<and> q' \<mapsto>a \<alpha> q'' \<and> q'' \<Turnstile>SRBB \<phi>" by auto
    thus "False" using D by auto
  qed
  hence "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal (hml_srbb_inner.Obs \<alpha> \<phi>)) p Q"
    using P by fastforce
  then show ?case by simp
next
  case (early_conj Q p Q' e \<phi>)
  then show ?case
    by (simp, metis not_None_eq)
next
  case (late_conj p Q e \<chi>)
  then show ?case
    using silent_reachable.intros(1)
    by auto
next
  case (conj Q p e \<Phi>)
  then show ?case by auto 
next
  case (imm_conj Q p e \<Phi>)
  then show ?case by auto
next
  case (pos p q e \<chi>)
  then show ?case using silent_reachable.refl
    by (simp) (metis option.discI silent_reachable_trans)
next
  case (neg p q e \<chi>)
  then obtain P' where IH:
    "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') =  Some (\<lambda>e. Option.bind (subtract_fn 0 0 0 0 0 0 0 1 e) min1_7)"
    "attacker_wins (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) (Attacker_Delayed q P') \<and>
       strategy_formula_inner (Attacker_Delayed q P') (the (min1_7 (e - E 0 0 0 0 0 0 0 1))) \<chi> \<and>
       (case Attacker_Delayed q P' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q | _ \<Rightarrow> True)" by fastforce
  hence D: "P' \<Zsurj>S P' \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) q P'" by simp
  have "{p} \<Zsurj>S P'" using IH(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) not_Some_eq) 
  have "P' \<Zsurj>S P' \<longrightarrow> p \<in> P'" using \<open>{p} \<Zsurj>S P'\<close>  by (simp add: silent_reachable.intros(1)) 
  hence "hml_srbb_conj.distinguishes (hml_srbb_conjunct.Neg \<chi>) p q" using D \<open>{p} \<Zsurj>S P'\<close>
    unfolding hml_srbb_conj.distinguishes_def distinguishes_from_def 
    by (smt (verit) LTS_Tau.silent_reachable_trans hml_srbb_conjunct_models.simps(2) hml_srbb_models.simps(2) silent_reachable.refl)
  then show ?case by simp
next
  case (stable p Q e \<chi>)
  then obtain Q' where IH: "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some Some"
       "attacker_wins e (Defender_Stable_Conj p Q') \<and>
       strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi> \<and>
       (case Defender_Stable_Conj p Q' of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q
        | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>\<alpha> p' \<and> Qa \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
        | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
        | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q | _ \<Rightarrow> True)" by auto
  hence "(\<nexists>p''. p \<mapsto>\<tau> p'')"
    by (metis local.late_stbl_conj option.distinct(1)) 

  from IH have "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q'" by simp
  hence "hml_srbb_inner.distinguishes_from \<chi> p Q'" using \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close> by auto
  hence "hml_srbb_inner_models p \<chi>" by simp
  hence "p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)"
    using pre_\<epsilon> and hml_srbb_and_hml_semantics_match by auto
  have "Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (hml_srbb.Internal \<chi>) p Q"
  proof
    assume "Q \<Zsurj>S Q"
    have "(\<forall>q \<in> Q. \<not>(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>)))"
    proof (clarify)
      fix q
      assume "q \<in> Q" "(q \<Turnstile>SRBB (hml_srbb.Internal \<chi>))"
      hence "\<exists>q'. q \<Zsurj> q' \<and> (q' \<Turnstile> (hml_srbb_inner_to_hml \<chi>))" using hml_srbb_and_hml_semantics_match by auto
      hence "\<exists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>" using hml_srbb_and_hml_semantics_match by simp
      then obtain q' where X: "q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>" by auto
      hence "q' \<in> Q" using \<open>Q \<Zsurj>S Q\<close> \<open>q \<in> Q\<close> by blast
      then show "False"
      proof (cases "q' \<in> Q'")
        case True (* stable cases *)
        thus "False" using X \<open>hml_srbb_inner.distinguishes_from \<chi> p Q'\<close>
          by simp
      next
        case False (* instable cases *)
        from IH have "strategy_formula_inner (Defender_Stable_Conj p Q') e \<chi>" by simp
        hence "\<exists>\<Phi>. \<chi>=(StableConj Q' \<Phi>)" using strategy_formula_inner.simps
          by (smt (verit) spectroscopy_position.distinct(35) spectroscopy_position.distinct(39) spectroscopy_position.distinct(41) spectroscopy_position.inject(7))
        then obtain \<Phi> where P: "\<chi>=(StableConj Q' \<Phi>)" by auto
        from IH(1) have "Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}"
          by (metis (full_types) local.late_stbl_conj option.distinct(1))
        hence "\<exists>q''. q' \<mapsto>\<tau> q''" using False \<open>q' \<in> Q\<close> by simp
        from X have "hml_srbb_inner_models q' (StableConj Q' \<Phi>)" using P by auto
        then show ?thesis using \<open>\<exists>q''. q' \<mapsto>\<tau> q''\<close> by simp
      qed
    qed
    thus "distinguishes_from (hml_srbb.Internal \<chi>) p Q"
      using \<open>p \<Turnstile>SRBB (hml_srbb.Internal \<chi>)\<close> by simp
  qed
  then show ?case by simp
next
  case (stable_conj Q p e \<Phi>)
  hence IH: "\<forall>q\<in> Q. hml_srbb_conj.distinguishes (\<Phi> q) p q" by simp
  hence Q: "\<forall>q \<in> Q. hml_srbb_conjunct_models p (\<Phi> q)" by simp
  hence "(\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from (StableConj Q \<Phi>) p Q"
    using IH left_right_distinct by auto
  then show ?case by simp
next
  case (branch p Q e \<chi>)
  then obtain p' Q' \<alpha> Q\<alpha> where IH:
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' Q' Q\<alpha>) = Some Some"
    "attacker_wins e (Defender_Branch p \<alpha> p' Q' Q\<alpha>) \<and>
     strategy_formula_inner (Defender_Branch p \<alpha> p' Q' Q\<alpha>) e \<chi> \<and>
     (case Defender_Branch p \<alpha> p' Q' Q\<alpha> of Attacker_Delayed p Q \<Rightarrow> Q \<Zsurj>S Q \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
      | Defender_Branch p \<alpha> p' Q Qa \<Rightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qa)
      | Defender_Conj p Q \<Rightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
      | Defender_Stable_Conj p Q \<Rightarrow> (\<forall>q. \<not> p \<mapsto>\<tau> q) \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q | _ \<Rightarrow> True)" by blast
  from IH(1) have "p \<mapsto>a \<alpha> p'"
    by (metis local.br_conj option.distinct(1)) 
  from IH have "p \<mapsto>a \<alpha> p' \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q' \<union> Q\<alpha>)" by simp
  hence D: "hml_srbb_inner.distinguishes_from \<chi> p (Q' \<union> Q\<alpha>)" using \<open>p \<mapsto>a \<alpha> p'\<close> by auto
  from IH have "Q' = Q - Q\<alpha> \<and> p \<mapsto>a \<alpha> p' \<and> Q\<alpha> \<subseteq> Q"
    by (metis (no_types, lifting) br_conj option.discI)
  hence "Q=(Q' \<union> Q\<alpha>)" by auto
  then show ?case
    using pre_\<epsilon> D hml_srbb_and_hml_semantics_match by auto 
next
  case (branch_conj p \<alpha> p' Q1 Q\<alpha> e \<psi> \<Phi>)
  hence A1: "\<forall>q\<in>Q1. hml_srbb_conjunct_models p (\<Phi> q)" by simp
  from branch_conj obtain Q' where IH:
    "spectroscopy_moves (Defender_Branch p \<alpha> p' Q1 Q\<alpha>) (Attacker_Branch p' Q')
      = Some (\<lambda>e. Option.bind (subtract_fn 0 1 1 0 0 0 0 0 e) min1_6)"
    "spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q') = subtract 1 0 0 0 0 0 0 0 \<and>
     attacker_wins (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0) (Attacker_Immediate p' Q') \<and>
     strategy_formula (Attacker_Immediate p' Q') (the (min1_6 (e - E 0 1 1 0 0 0 0 0)) - E 1 0 0 0 0 0 0 0) \<psi> \<and>
     (case Attacker_Immediate p' Q' of Attacker_Immediate p Q \<Rightarrow> distinguishes_from \<psi> p Q
          | Defender_Conj p Q \<Rightarrow> distinguishes_from \<psi> p Q | _ \<Rightarrow> True)" by auto
  hence "distinguishes_from \<psi> p' Q'" by simp
  hence X:"p' \<Turnstile>SRBB \<psi>" by simp
  have Y: "\<forall>q \<in> Q'. \<not>(q \<Turnstile>SRBB \<psi>)" using \<open>distinguishes_from \<psi> p' Q'\<close> by simp

  have "(p \<mapsto>a \<alpha> p') \<longrightarrow> hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)"
  proof
    assume "p \<mapsto>a \<alpha> p'"
    hence "p \<mapsto>a \<alpha> p'" by simp
    with IH(1) have "Q\<alpha> \<mapsto>aS \<alpha> Q'"
      by (simp, metis option.discI)
    hence A2: "hml_srbb_inner_models p (Obs \<alpha> \<psi>)" using X \<open>p \<mapsto>a \<alpha> p'\<close>  by auto  
    have A3: "\<forall>q \<in> (Q1 \<union> Q\<alpha>). hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q"
    proof (safe)
      fix q
      assume "q \<in> Q1"
      hence  "hml_srbb_conj.distinguishes (\<Phi> q) p q" using branch_conj(2) by simp
      thus "hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q"
        using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction \<open>q \<in> Q1\<close> by blast
    next
      fix q
      assume "q \<in> Q\<alpha>"
      hence "\<not>(hml_srbb_inner_models q (Obs \<alpha> \<psi>))"
        using Y \<open>Q\<alpha> \<mapsto>aS \<alpha> Q'\<close> by auto
      hence "hml_srbb_inner.distinguishes (Obs \<alpha> \<psi>) p q"
        using A2 by auto
      thus "hml_srbb_inner.distinguishes (BranchConj \<alpha> \<psi> Q1 \<Phi>) p q"
        using A1 A2 srbb_dist_conjunct_or_branch_implies_dist_branch_conjunction by blast    
    qed
    have A4: "hml_srbb_inner_models p (BranchConj \<alpha> \<psi> Q1 \<Phi>)"
      using A3 A2 by fastforce
    with A3 show "hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<psi> Q1 \<Phi>) p (Q1 \<union> Q\<alpha>)"
      by simp 
  qed 
  then show ?case by simp
qed

end (* context full_spec_game *)

end
