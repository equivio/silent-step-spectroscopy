section \<open>Correctness\<close>

text \<open>As in the main theorem of \cite{bisping2023lineartimebranchingtime}, we state in what sense winning energy levels and equivalences coincide as the theorem \<open>spectroscopy_game_correctness\<close>:
There exists a formula \<open>\<phi>\<close> distinguishing a process \<open>p\<close> from a set of processes \<open>Q\<close> with
expressiveness price of at most \<open>e\<close> if and only if \<open>e\<close> is in the winning budget of \<open>Attacker_Immediate p Q\<close>.

The proof is split into three lemmas. The forward direction is given by the lemma \<open>distinction_implies_winning_budgets\<close> combined with the upwards closure of winning budgets.
To show the other direction one can construct a (strategy) formula with an appropriate price using
the constructive proof of \<open>winning_budget_implies_strategy_formula\<close>. From lemma
\<open>strategy_formulas_distinguish\<close> we then know that this formula actually distinguishes \<open>p\<close> from \<open>Q\<close>.
\<close>

subsection \<open>Distinction Implies Winning Budgets\<close>

theory Distinction_Implies_Winning_Budgets
  imports Spectroscopy_Game Expressiveness_Price
begin

context weak_spectroscopy_game
begin

text \<open>In this section, we prove that if a formula distinguishes a process @{term \<open>p\<close>}
      from a set of process @{term \<open>Q\<close>}, then the price of this formula is in the attackers-winning
      budget. This is the same statement as that of lemma $1$ in the paper \cite[p. 20]{bisping2023lineartimebranchingtime}.
      We likewise also prove it in the same manner.

      First, we show that the statement holds if @{term \<open>Q = {}\<close>}. This is the case, as the
      attacker can move, at no cost, from the starting position, @{term \<open>Attacker_Immediate p {}\<close>},
      to the defender position @{term \<open>Defender_Conj p {}\<close>}. In this position the defender is then
      unable to make any further moves. Hence, the attacker wins the game with any budget.\<close>

lemma defender_conj_empty_att_wins:
  shows \<open>attacker_wins e (Defender_Conj p {})\<close>
proof -
  have is_last_move: \<open>spectroscopy_moves (Defender_Conj p {}) g' = None\<close> for g'
    by(rule spectroscopy_moves.elims, auto)
  moreover have \<open>spectroscopy_defender (Defender_Conj p {})\<close> by simp
  ultimately show \<open>attacker_wins e (Defender_Conj p {})\<close>
    by (simp add: attacker_wins.Defense)
qed

lemma att_empty_att_wins:
  shows \<open>attacker_wins e (Attacker_Delayed p {})\<close>
proof -
  have \<open>spectroscopy_moves (Attacker_Delayed p {}) (Defender_Conj p {}) = Some Some\<close> by simp
  thus ?thesis
    using defender_conj_empty_att_wins Attack spectroscopy_defender.simps(5) by fastforce
qed

lemma distinction_implies_winning_budgets_empty_Q:
  assumes \<open>distinguishes_from \<phi> p {}\<close>
  shows \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p {})\<close>
proof-
  from late_inst_conj[of p \<open>{}\<close> p \<open>{}\<close>] have next_move0:
    \<open>spectroscopy_moves (Attacker_Delayed p {}) (Defender_Conj p {}) = Some Some\<close> by force

  from delay[of p \<open>{}\<close> p \<open>{}\<close>] have next_move1:
    \<open>spectroscopy_moves (Attacker_Immediate p {}) (Attacker_Delayed p {}) = Some Some\<close> by force

  moreover have \<open>attacker (Attacker_Immediate p {})\<close> by simp
  ultimately show ?thesis using attacker_wins.Attack[of \<open>Attacker_Immediate p {}\<close> _ \<open>expressiveness_price \<phi>\<close>]
    using next_move0 next_move1 attacker_wins_Ga_with_id_step[OF defender_conj_empty_att_wins]
    by fastforce
qed

text \<open>Next, we show the statement for the case that @{term \<open>Q \<noteq> {}\<close>}. Following the proof of
      \cite[p. 20]{bisping2023lineartimebranchingtime}, we do this by induction on a more
      complex property.\<close>
lemma distinction_implies_winning_budgets:
  assumes \<open>distinguishes_from \<phi> p Q\<close>
  shows \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close>
proof-
  have \<open>\<And>\<phi> \<chi> \<psi>.
        (\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q Qr. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qr) \<longrightarrow> (\<forall>q \<in> Q \<union> Qr. stable_state q)
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q Qr))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
             Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
               \<longrightarrow> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Clause p q))
        \<and> (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
               \<longrightarrow> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Stable_Clause p q))\<close>
    \<comment> \<open>Likely, I should add another induction hypothesis to cater for conjuncts that distinguish from sets ... ?\<close>
  proof -
    fix \<phi> \<chi> \<psi>
    show \<open>(\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p Q
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q Qr. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from \<chi> p (Q \<union> Qr) \<longrightarrow> (\<forall>q \<in> Q \<union> Qr. stable_state q)
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q Qr))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            hml_srbb_inner.distinguishes_from \<chi> p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
             Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
            \<longrightarrow> attacker_wins (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
               \<longrightarrow> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Clause p q))
        \<and> (\<forall>p q. hml_srbb_conj.distinguishes \<psi> p q
               \<longrightarrow> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Stable_Clause p q))\<close>
    proof (induct rule: hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct[of _ _ _ \<phi> \<chi> \<psi>])
      case TT
      then show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close>
          and \<open>distinguishes_from TT p Q\<close>
        hence \<open>\<exists>q. q \<in> Q\<close>
          by blast
        then obtain q where \<open>q \<in> Q\<close> by auto

        from \<open>distinguishes_from TT p Q\<close>
         and \<open>q \<in> Q\<close>
        have \<open>distinguishes TT p q\<close>
          using distinguishes_from_def by auto

        with verum_never_distinguishes
        show \<open>attacker_wins (expressiveness_price TT) (Attacker_Immediate p Q)\<close>
          by blast
      qed
    next
      case (Internal \<chi>)
      show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close>
           and \<open>distinguishes_from (Internal \<chi>) p Q\<close>
        then have \<open>\<exists>p'. p \<Zsurj> p' \<and> hml_srbb_inner_models p' \<chi>\<close>
              and \<open>\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> hml_srbb_inner_models q' \<chi>)\<close>
          by auto
        hence \<open>\<forall>q \<in> Q. (\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>(hml_srbb_inner_models q' \<chi>))\<close> by auto
        then have \<open>\<forall>q \<in> Q. (\<forall>q'\<in>Q'. q \<Zsurj> q' \<longrightarrow> \<not>(hml_srbb_inner_models q' \<chi>))\<close>
          for Q' by blast
        then have \<open>Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(hml_srbb_inner_models q' \<chi>))\<close>
          for Q' using \<open>Q \<noteq> {}\<close> by blast

        define Q\<tau> where \<open>Q\<tau> \<equiv> silent_reachable_set Q\<close>
        with \<open>\<And>Q'. Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(hml_srbb_inner_models q' \<chi>))\<close>
        have \<open>\<forall>q' \<in> Q\<tau>. \<not>(hml_srbb_inner_models q' \<chi>)\<close>
          using sreachable_set_is_sreachable by presburger
        have \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> unfolding Q\<tau>_def
          by (metis silent_reachable_trans sreachable_set_is_sreachable
              silent_reachable.intros(1))

        from \<open>\<exists>p'. p \<Zsurj> p' \<and> (hml_srbb_inner_models p' \<chi>)\<close>
        obtain p' where \<open>p \<Zsurj> p'\<close> and \<open>hml_srbb_inner_models p' \<chi>\<close> by auto
        from this(1) have \<open>p \<Zsurj>L p'\<close> by(rule silent_reachable_impl_loopless)

        have \<open>Q\<tau> \<noteq> {}\<close>
          using silent_reachable.intros(1) sreachable_set_is_sreachable Q\<tau>_def \<open>Q \<noteq> {}\<close>
          by fastforce

        from \<open>hml_srbb_inner_models p' \<chi>\<close>
         and \<open>\<forall>q' \<in> Q\<tau>. \<not>(hml_srbb_inner_models q' \<chi>)\<close>
        have \<open>hml_srbb_inner.distinguishes_from \<chi> p' Q\<tau>\<close> by simp

        with \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> \<open>Q\<tau> \<noteq> {}\<close> Internal
        have \<open>attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed p' Q\<tau>)\<close>
          by blast

        moreover have \<open>expr_pr_inner \<chi> = expressiveness_price (Internal \<chi>)\<close> by simp
        ultimately have \<open>attacker_wins (expressiveness_price (Internal \<chi>))
            (Attacker_Delayed p' Q\<tau>)\<close> by simp

        hence \<open>attacker_wins (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
        proof(induct rule: silent_reachable_loopless.induct[of \<open>p\<close> \<open>p'\<close>, OF \<open>p \<Zsurj>L p'\<close>])
          case (1 p)
          thus ?case by simp
        next
          case (2 p p' p'')
          hence \<open>attacker_wins (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p' Q\<tau>)\<close>
            by simp
          moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q\<tau>) (Attacker_Delayed p' Q\<tau>)
            = Some Some\<close> using spectroscopy_moves.simps(2) \<open>p \<noteq> p'\<close> \<open>p \<mapsto>\<tau> p'\<close> by auto
          moreover have \<open>attacker (Attacker_Delayed p Q\<tau>)\<close> by simp
          ultimately show ?case using attacker_wins_Ga_with_id_step by auto
        qed
        have  \<open>Q \<Zsurj>S Q\<tau>\<close>
          using Q\<tau>_def sreachable_set_is_sreachable by simp
        hence \<open>spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q\<tau>) = Some Some\<close>
          using spectroscopy_moves.simps(1) by simp
        with \<open>attacker_wins (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
        show \<open>attacker_wins (expressiveness_price (Internal \<chi>)) (Attacker_Immediate p Q)\<close>
          using attacker_wins_Ga_with_id_step
          by (metis option.discI option.sel spectroscopy_defender.simps(1))
        qed
    next
      case (ImmConj I \<psi>s)
      show ?case
      proof (clarify)
        fix Q p
        assume \<open>Q \<noteq> {}\<close> and \<open>distinguishes_from (ImmConj I \<psi>s) p Q\<close>
        from this(2) have \<open>\<forall>q\<in>Q. p \<Turnstile>SRBB ImmConj I \<psi>s \<and> \<not> q \<Turnstile>SRBB ImmConj I \<psi>s\<close>
          unfolding distinguishes_from_def distinguishes_def by blast
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conjunct_models p (\<psi>s i) \<and> \<not>hml_srbb_conjunct_models q (\<psi>s i)\<close>
          by simp
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          using hml_srbb_conj.distinguishes_def by simp
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. ((\<psi>s i) \<in> range \<psi>s) \<and> hml_srbb_conj.distinguishes (\<psi>s i) p q\<close> by blast
        hence \<open>\<forall>q\<in>Q. \<exists>i\<in>I. attacker_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close> using ImmConj by blast
        hence a_clause_wina: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. attacker_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 0) (Attacker_Clause p q)\<close>
          using expressiveness_price_ImmConj_geq_parts win_a_upwards_closure by fast
        from this \<open>Q \<noteq> {}\<close> have \<open>I \<noteq> {}\<close> by blast
        hence subtracts:
          \<open>subtract_fn 0 0 1 0 1 0 0 0 0 (expressiveness_price (ImmConj I \<psi>s)) = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 0)\<close>
          \<open>subtract_fn 0 0 1 0 0 0 0 0 0 (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0 0) = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 0)\<close>
          by (simp add: \<open>I \<noteq> {}\<close>)+
        have def_conj: \<open>spectroscopy_defender (Defender_Conj p Q)\<close> by simp
        have \<open>spectroscopy_moves (Defender_Conj p Q) N \<noteq> None
              \<Longrightarrow> N = Attacker_Clause (attacker_state N) (defender_state N)\<close> for N
          by (cases N) auto
        hence move_kind: \<open>spectroscopy_moves (Defender_Conj p Q) N \<noteq> None \<Longrightarrow> \<exists>q\<in>Q. N = Attacker_Clause p q\<close> for N
          using conj_answer by metis
        hence update: \<open>\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow>
          weight (Defender_Conj p Q) g' = subtract_fn 0 0 1 0 0 0 0 0 0\<close>
          by fastforce
        hence move_wina: \<open>\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow>
          (subtract_fn 0 0 1 0 0 0 0 0 0) (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0 0)
               = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 0) \<and>
          attacker_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 1 0 1 0 0 0 0) g'\<close>
          using move_kind a_clause_wina subtracts by blast
        from attacker_wins_Gd[OF def_conj] update move_wina have def_conj_wina:
          \<open>attacker_wins (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0 0) (Defender_Conj p Q)\<close>
          by blast
        have imm_to_conj: \<open>spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p Q) \<noteq> None\<close>
          by (simp add: \<open>Q \<noteq> {}\<close>)
        have imm_to_conj_wgt: \<open>weight (Attacker_Immediate p Q) (Defender_Conj p Q) (expressiveness_price (ImmConj I \<psi>s))
          = Some (expressiveness_price (ImmConj I \<psi>s) - E 0 0 0 0 1 0 0 0 0)\<close>
          using \<open>Q \<noteq> {}\<close> leq_components subtracts(1) by force
        from Attack[OF _ imm_to_conj imm_to_conj_wgt] def_conj_wina
        show \<open>attacker_wins (expressiveness_price (ImmConj I \<psi>s)) (Attacker_Immediate p Q)\<close>
          by simp
      qed
    next
      case (Obs \<alpha> \<phi>)
      have \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> Q \<Zsurj>S Q
                \<longrightarrow> attacker_wins (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)\<close>
      proof(clarify)
        fix p Q
        assume \<open>Q \<noteq> {}\<close> \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> \<open> \<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close>
        have \<open>\<exists>p' Q'. p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q' \<and> attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close>
        proof(cases \<open>\<alpha> = \<tau>\<close>)
          case True
          with \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          have dist_unfold:  \<open>((\<exists>p'. p \<mapsto>\<tau> p' \<and> p' \<Turnstile>SRBB \<phi>) \<or> p \<Turnstile>SRBB \<phi>)\<close> by simp
          then obtain p' where \<open>p' \<Turnstile>SRBB \<phi>\<close> \<open>p \<mapsto>a \<alpha> p'\<close>
            unfolding True by blast

          from \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> have
            \<open>\<forall>q\<in>Q. (\<not> q \<Turnstile>SRBB \<phi>) \<and> (\<nexists>q'. q \<mapsto>\<tau> q' \<and> q' \<Turnstile>SRBB \<phi>)\<close>
            using True by auto
          hence \<open>\<forall>q\<in>Q. \<not>q \<Turnstile>SRBB \<phi>\<close>
            using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> by fastforce

          hence \<open>distinguishes_from \<phi> p' Q\<close>
            using \<open>p' \<Turnstile>SRBB \<phi>\<close> by auto

          with Obs have \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q)\<close>
            using \<open>Q \<noteq> {}\<close> by blast
          moreover have \<open>Q \<mapsto>aS \<alpha> Q\<close>
            unfolding True
            using \<open>\<forall>p\<in>Q. \<forall>q. p \<Zsurj> q \<longrightarrow> q \<in> Q\<close> silent_reachable_append_\<tau> silent_reachable.intros(1) by blast
          ultimately show ?thesis using \<open>p \<mapsto>a \<alpha> p'\<close> by blast
        next
          case False
          with \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          obtain p'' where \<open>(p \<mapsto>\<alpha> p'') \<and> (p'' \<Turnstile>SRBB \<phi>)\<close> by auto

          let ?Q' = \<open>step_set Q \<alpha>\<close>
          from \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close>
          have \<open>\<forall>q\<in>?Q'. \<not> q \<Turnstile>SRBB \<phi>\<close>
            using \<open>Q \<noteq> {}\<close> and step_set_is_step_set
            by force
          from \<open>\<forall>q\<in>step_set Q \<alpha>. \<not> q \<Turnstile>SRBB \<phi>\<close> \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile>SRBB \<phi>\<close>
          have \<open>distinguishes_from \<phi> p'' ?Q'\<close> by simp
          hence \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p'' ?Q')\<close>
            by (metis Obs distinction_implies_winning_budgets_empty_Q)
          moreover have \<open>p \<mapsto>\<alpha> p''\<close> using \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile>SRBB \<phi>\<close> by simp
          moreover have \<open>Q \<mapsto>aS \<alpha> ?Q'\<close> by (simp add: False LTS.step_set_is_step_set)
          ultimately show ?thesis by blast
        qed
        then obtain p' Q' where p'_Q': \<open>p \<mapsto>a \<alpha> p'\<close> \<open>Q \<mapsto>aS \<alpha> Q'\<close> and
          wina: \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close> by blast
        have attacker: \<open>attacker (Attacker_Delayed p Q)\<close> by simp
        have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
              (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then Some (subtract_fn 1 0 0 0 0 0 0 0 0) else None)\<close>
          for p Q p' Q' by simp
        from this[of p Q p' Q'] have
          \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
               Some (subtract_fn 1 0 0 0 0 0 0 0 0)\<close> using p'_Q' by auto
        with expr_obs_phi[of \<alpha> \<phi>] show
          \<open>attacker_wins (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)\<close>
          using Attack[OF attacker _ _ wina]
          by (smt (verit, best) option.sel option.simps(3))
      qed
      then show ?case by fastforce
    next
      case (Conj I \<psi>s)
      have main_case: \<open>\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
             Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q
             \<longrightarrow> attacker_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence distinctions: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          by auto
        hence inductive_wins: \<open>\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> attacker_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close>
          using Conj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
            \<and> attacker_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present: \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (pos_conjuncts_sec   ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` Q))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` Q))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close>
          unfolding e'_def
          by (metis SUP_upper energy.sel leq_components)
        with \<psi>qs_spec win_a_upwards_closure
          have clause_win: \<open>\<forall>q\<in>Q. attacker_wins e' (Attacker_Clause p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts_sec   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` Q \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def leq_components
          by (simp add: Sup_subset_mono image_mono)
        define e where \<open>e = E
          (modal_depth e')
          (br_conj_depth e')
          (1 + conj_depth e')
          (st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (pos_conjuncts_sec e')
          (neg_conjuncts e')
          (neg_depth e')\<close>
        have \<open>e' = e - (E 0 0 1 0 0 0 0 0 0)\<close> unfolding e_def e'_def by simp
        hence \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0 0) e\<close>
          by (auto, smt (verit) add_increasing2 e_def energy.sel energy_leq_cases i0_lb le_numeral_extra(4))
        have expr_lower: \<open>(E 0 0 1 0 0 0 0 0 0) \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using case_assms(1) subset_form by auto
        have eu'_comp: \<open>eu' = (expr_pr_inner (Conj I \<psi>s)) - (E 0 0 1 0 0 0 0 0 0)\<close>
          unfolding eu'_def
          by (auto simp add: bot_enat_def image_image)
        with expr_lower have eu'_characterization: \<open>Some eu' = (subtract_fn 0 0 1 0 0 0 0 0 0) (expr_pr_inner (Conj I \<psi>s))\<close>
          by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Clause p q) = g') \<and> spectroscopy_moves (Defender_Conj p Q) g' = Some (subtract_fn 0 0 1 0 0 0 0 0 0)\<close>
        proof clarify
          fix g' upd
          assume upd_def: \<open>spectroscopy_moves (Defender_Conj p Q) g' = Some upd\<close>
          hence \<open>\<And>px q. g' = Attacker_Clause px q \<Longrightarrow> p = px \<and> q \<in> Q \<and> upd = (subtract_fn 0 0 1 0 0 0 0 0 0)\<close>
            by (metis (mono_tags, lifting) local.conj_answer option.sel option.simps(3))
          with upd_def show \<open>(\<exists>q\<in>Q. Attacker_Clause p q = g') \<and> spectroscopy_moves (Defender_Conj p Q) g' = Some (subtract_fn 0 0 1 0 0 0 0 0 0)\<close>
            by (cases g', auto)
        qed
        hence \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Conj p Q) g')) e = Some e' \<and> attacker_wins e' g')\<close>
          unfolding e_def
          using clause_win \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0 0) e\<close> e_def by force
        hence \<open>attacker_wins e (Defender_Conj p Q)\<close>
          unfolding e_def using attacker_wins.Defense
          by auto
        moreover have \<open>e \<le> expr_pr_inner (Conj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization \<open>Some e' = (subtract_fn 0 0 1 0 0 0 0 0 0) e\<close> expr_lower case_assms(1) subset_form
          unfolding e_def
          by (smt (verit, ccfv_threshold) eu'_comp add_diff_cancel_enat
              add_mono_thms_linordered_semiring(1) enat.simps(3) enat_defs(2) energy.sel
              expr_pr_inner.simps idiff_0_right inst_conj_depth_inner.simps(2) le_numeral_extra(4)
              leq_components minus_energy_def not_one_le_zero)
        ultimately show \<open>attacker_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using win_a_upwards_closure by blast
      qed
      moreover have
        \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
             \<longrightarrow> attacker_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q)\<close>
      proof clarify
        fix p Q
        assume
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (hml_srbb_inner.Conj I \<psi>s) p Q\<close>
        hence att_win: \<open>attacker_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q)\<close>
          using main_case by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) = Some Some\<close>
          by auto
        ultimately show \<open>attacker_wins (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q)\<close>
          using attacker_wins_Ga_with_id_step[OF att_win] by auto
      qed
      ultimately show ?case by fastforce
    next
      case (StableConj I \<psi>s)
      have main_case: \<open>\<forall>\<Psi>_I \<Psi> p Q Qr. Q \<noteq> {} \<longrightarrow>
           hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p (Q \<union> Qr) \<longrightarrow>
           (\<forall>q\<in>Q \<union> Qr. stable_state q) \<longrightarrow> attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q Qr)\<close>
      proof clarify
        fix p Q Qr
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p (Q \<union> Qr)\<close>
          \<open>\<forall>q\<in>Q\<union>Qr. stable_state q\<close>
        hence distinctions: \<open>\<forall>q\<in>Q\<union>Qr. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          by simp
        hence inductive_wins: \<open>\<forall>q\<in>Q\<union>Qr. \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> attacker_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)
            \<and> attacker_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Stable_Clause p q)\<close>
          using StableConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Clause p q)
            \<and> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Stable_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>Q\<union>Qr. \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
            \<and> attacker_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)
            \<and> attacker_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Stable_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present: \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))
                \<union> pos_conjuncts_sec   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (pos_conjuncts_sec   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup ({1} \<union> neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))\<close>
        from conjuncts_present have conj_prices: \<open>\<forall>q\<in>Q\<union>Qr. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close> unfolding e'_def
          by (smt (z3) Sup_upper UnI1 UnI2 energy.sel image_insert insert_iff leq_components mk_disjoint_insert)
        hence clause_win: \<open>\<forall>q\<in>Q. attacker_wins e' (Attacker_Stable_Clause p q)\<close>
          using \<psi>qs_spec win_a_upwards_closure by blast
        have clause_win_revivals: \<open>attacker_wins e' (Attacker_Delayed p Qr)\<close>
          using conj_prices \<psi>qs_spec win_a_upwards_closure sorry
        define revivals where \<open>revivals \<equiv> revival_conjunct_index I \<psi>s\<close>
        show \<open>attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q Qr)\<close>
        proof (cases \<open>revivals = {}\<close>)
          case True
          define eu' where \<open>eu' = E
            (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup (((\<lambda>\<psi>. case \<psi> of (Pos \<chi>) \<Rightarrow> modal_depth_srbb_conjunct \<psi> | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) \<circ> \<psi>s)
            ` I ))
            (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
            (Sup ({1} \<union> neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
          have secondary_conjs: \<open>\<forall>i\<in>I. (max_pos_conj_secondary_depth_conjunct (\<psi>s i)
                 \<le> (case \<psi>s i of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct (\<psi>s i)
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct (\<psi>s i)))\<close>
            using modal_depth_dominates_pos_conjuncts max_positive_conjunct_depth_dominates_secondary(3)
            by (metis hml_srbb_conjunct.case_eq_if order.trans order_class.order_eq_iff)
          hence \<open>Sup { max_pos_conj_secondary_depth_conjunct (\<psi>s i) |i. i \<in> I }
                 \<le> Sup { case (\<psi>s i) of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct (\<psi>s i)
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct (\<psi>s i) |i. i \<in> I }\<close>
            by (smt (verit, ccfv_SIG) Sup_mono mem_Collect_eq)
          moreover have equal_sets:
            \<open>{ max_pos_conj_secondary_depth_conjunct (\<psi>s i) |i. i \<in> I } = max_pos_conj_secondary_depth_conjunct ` \<psi>s ` I\<close>
            \<open>{ case (\<psi>s i) of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct (\<psi>s i)
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct (\<psi>s i) |i. i \<in> I } = (\<lambda>\<psi>. case \<psi> of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct \<psi>
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) ` \<psi>s ` I\<close>
            by auto
          ultimately have \<open>Sup (max_pos_conj_secondary_depth_conjunct ` \<psi>s ` I)
                 \<le> Sup ((\<lambda>\<psi>. case \<psi> of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct \<psi>
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) ` \<psi>s ` I )\<close>
            by simp
          moreover have subset_form: \<open>\<psi>qs ` (Q\<union>Qr) \<subseteq> \<psi>s ` I\<close>
            using \<psi>qs_spec by fastforce
          ultimately have sup_Q_I: \<open>Sup (max_pos_conj_secondary_depth_conjunct ` \<psi>qs ` (Q\<union>Qr))
                 \<le> Sup ((\<lambda>\<psi>. case \<psi> of
                      Pos \<chi> \<Rightarrow> modal_depth_srbb_conjunct \<psi>
                    | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) ` \<psi>s ` I )\<close>
            by (smt (verit, best) Orderings.order_eq_iff SUP_subset_mono order_trans)
          hence \<open>e' \<le> eu'\<close>
            unfolding e'_def eu'_def
            using subset_form
            apply (auto simp add: Sup_subset_mono image_mono sup.coboundedI2)
             defer
            apply
               (smt (z3) SUP_cong Sup_le_iff Sup_upper sup_Q_I equal_sets(2) dual_order.trans
                energy.sel(7) image_iff image_image mem_Collect_eq)
            proof -
              assume a1: "\<psi>qs ` (Q \<union> Qr) \<subseteq> \<psi>s ` I"
              obtain ee :: "enat \<Rightarrow> enat set \<Rightarrow> enat" where
                f2: "\<forall>x0 x1. (\<exists>v2. v2 \<in> x1 \<and> \<not> v2 \<le> x0) = (ee x0 x1 \<in> x1 \<and> \<not> ee x0 x1 \<le> x0)"
                by moura
              obtain hh :: "(('a, 's) hml_srbb_conjunct \<Rightarrow> enat) \<Rightarrow> (('a, 's) hml_srbb_conjunct \<Rightarrow> enat) \<Rightarrow> ('a, 's) hml_srbb_conjunct set \<Rightarrow> ('a, 's) hml_srbb_conjunct" where
                f3: "\<forall>x0 x1 x3. (\<exists>v4. v4 \<in> x3 \<and> \<not> x1 v4 \<le> x0 v4) = (hh x0 x1 x3 \<in> x3 \<and> \<not> x1 (hh x0 x1 x3) \<le> x0 (hh x0 x1 x3))"
                by moura
              have f4: "\<forall>E e. (\<not> Sup E \<le> e \<or> (\<forall>ea. ea \<notin> E \<or> ea \<le> e)) \<and> (Sup E \<le> e \<or> ee e E \<in> E \<and> \<not> ee e E \<le> e)"
                using f2 by (metis (no_types) Sup_le_iff)
              have f5: "\<forall>H Ha f fa. \<not> H \<subseteq> Ha \<or> hh fa f H \<in> H \<and> \<not> f (hh fa f H) \<le> fa (hh fa f H) \<or> Sup (f ` H) \<le> Sup (fa ` Ha)"
                using f3 by (metis SUP_subset_mono)
              then have f6: "\<forall>e. e \<notin> (\<lambda>h. pos_conjuncts_sec (E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h))) ` \<psi>qs ` (Q \<union> Qr) \<or> e \<le> Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)"
                using f4 a1 by (smt (z3) energy.sel(6) energy.sel(7) image_image max_positive_conjunct_depth_dominates_secondary(3))
              have "\<forall>e. e \<notin> (\<lambda>h. pos_conjuncts (E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h))) ` \<psi>qs ` (Q \<union> Qr) \<or> e \<le> Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)"
                using f5 f4 a1 by (smt (z3) image_image nle_le)
              then have "ee (Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)) (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr) \<union> pos_conjuncts_sec ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr)) \<notin> pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr) \<union> pos_conjuncts_sec ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr) \<or> ee (Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)) (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr) \<union> pos_conjuncts_sec ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr)) \<le> Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)"
                using f6 by blast
              then show "Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr) \<union> pos_conjuncts_sec ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>qs ` (Q \<union> Qr)) \<le> Sup (pos_conjuncts ` (\<lambda>h. E (modal_depth_srbb_conjunct h) (branch_conj_depth_conjunct h) (inst_conj_depth_conjunct h) (st_conj_depth_conjunct h) (imm_conj_depth_conjunct h) (max_pos_conj_depth_conjunct h) (max_pos_conj_secondary_depth_conjunct h) (max_neg_conj_depth_conjunct h) (neg_depth_conjunct h)) ` \<psi>s ` I)"
                using f4 by meson
            qed
          define e where \<open>e = E
            (modal_depth e')
            (br_conj_depth e')
            (conj_depth e')
            (1 + st_conj_depth e')
            (imm_conj_depth e')
            (pos_conjuncts e')
            (pos_conjuncts_sec e')
            (neg_conjuncts e')
            (sup 1 (neg_depth e'))\<close>
          have \<open>e' = e - (E 0 0 0 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
          hence \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0 0) e\<close>
            by (metis e_def energy.sel energy_leq_cases i0_lb le_iff_add)
          have expr_lower: \<open>(E 0 0 0 1 0 0 0 0 0) \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
            using case_assms(1) subset_form by force
          have eu'_comp: \<open>eu' = (expr_pr_inner (StableConj I \<psi>s)) - (E 0 0 0 1 0 0 0 0 0)\<close>
            using energy.sel True
            unfolding eu'_def revivals_def 
            by (auto simp add: bot_enat_def hml_srbb_conjunct.case_eq_if image_image)
              (smt (verit, ccfv_threshold) Int_Collect SUP_cong Sup_union_distrib
                    hml_srbb_conjunct.collapse(1) modal_depth_srbb_rewrite)
          with expr_lower have eu'_characterization: \<open>Some eu' = (subtract_fn 0 0 0 1 0 0 0 0 0) (expr_pr_inner (StableConj I \<psi>s))\<close>
            by presburger
          have moves: \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' \<noteq> None
          \<longrightarrow> ((\<exists>q\<in>Q. (Attacker_Stable_Clause p q) = g') \<and> spectroscopy_moves (Defender_Stable_Conj p Q Qr) g'
                 = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 1 0 0 0 0 0) e) min6_7)
            \<or> Attacker_Delayed p Qr = g' \<and> spectroscopy_moves (Defender_Stable_Conj p Q Qr) g'
                 = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 1 0 0 0 0 0) e) min1_6)
            \<or> Defender_Conj p {} = g' \<and> spectroscopy_moves (Defender_Stable_Conj p Q Qr) g'
                 = (subtract 0 0 0 1 0 0 0 0 1))\<close>
          proof (rule, rule)
            fix g'
            assume case_assm: \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' \<noteq> None\<close>
            then obtain upd where
                \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' = Some upd\<close>
                \<open>None \<noteq> Some upd\<close>
              by blast
            thus \<open>(\<exists>q\<in>Q. Attacker_Stable_Clause p q = g') \<and>
              spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
              Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 1 0 0 0 0 0 \<le> e then None else Some (e - E 0 0 0 1 0 0 0 0 0)) min6_7) \<or>
              Attacker_Delayed p Qr = g' \<and>
              spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
              Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 1 0 0 0 0 0 \<le> e then None else Some (e - E 0 0 0 1 0 0 0 0 0)) min1_6) \<or>
              Defender_Conj p {} = g' \<and>
              spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
              Some (\<lambda>x. if \<not> E 0 0 0 1 0 0 0 0 1 \<le> x then None else Some (x - E 0 0 0 1 0 0 0 0 1))\<close>
              using case_assm conj_s_answer conj_s_revival empty_stbl_conj_answer
              by (cases g') (metis (no_types, lifting) | simp)+
          qed
          have \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' \<noteq> None
            \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Stable_Conj p Q Qr) g')) e = Some e' \<and> attacker_wins e' g')\<close>
          proof safe
            fix g' eu
            assume \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' = Some eu\<close>
            then consider 
                (stable_answer)
                  \<open>(\<exists>q\<in>Q. Attacker_Stable_Clause p q = g')\<close>
                  \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
                    Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 1 0 0 0 0 0 \<le> e then None else Some (e - E 0 0 0 1 0 0 0 0 0)) min6_7)\<close>
              | (stable_revival)
                  \<open>Attacker_Delayed p Qr = g'\<close>
                  \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
                    Some (\<lambda>e. Option.bind (if \<not> E 0 0 0 1 0 0 0 0 0 \<le> e then None else Some (e - E 0 0 0 1 0 0 0 0 0)) min1_6)\<close>
              | (stability_check)
                  \<open>Defender_Conj p {} = g'\<close>
                  \<open>spectroscopy_moves (Defender_Stable_Conj p Q Qr) g' =
                    Some (\<lambda>x. if \<not> E 0 0 0 1 0 0 0 0 1 \<le> x then None else Some (x - E 0 0 0 1 0 0 0 0 1))\<close>
              using moves by auto
            thus \<open>\<exists>e'. weight (Defender_Stable_Conj p Q Qr) g' e = Some e' \<and> attacker_wins e' g'\<close>
            proof cases
              case stable_answer
              then show ?thesis
                using clause_win \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0 0) e\<close>
                unfolding e_def
                sledgehammer
            next
              case stable_revival
              then show ?thesis using clause_win_revivals sorry
            next
              case stability_check
              then show ?thesis
                using defender_conj_empty_att_wins by (auto simp add: e_def)
            qed
          qed
          hence \<open>attacker_wins e (Defender_Stable_Conj p Q Qr)\<close>
            unfolding e_def
            by (auto simp add: attacker_wins.Defense)
          moreover have \<open>e \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
            using \<open>e' \<le> eu'\<close> eu'_characterization \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0 0) e\<close> expr_lower case_assms(1) subset_form
            unfolding e_def eu'_comp minus_energy_def leq_components
            by (metis \<open>e' = e - E 0 0 0 1 0 0 0 0 0\<close> \<open>e' \<le> eu'\<close> e_def energy_subtraction_inequallity eu'_comp leq_components option.discI)
         ultimately show \<open>attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q Qr)\<close>
            using win_a_upwards_closure by blast
        next
          case False
          then obtain \<psi>r where \<open>revivals = {\<psi>r}\<close>
            unfolding revivals_def revival_conjunct_index_def empty_iff
            by (metis (no_types, lifting))

          then show ?thesis sorry
        qed


        have conjuncts_present: \<open>\<forall>q\<in>Q. expr_pr_conjunct (\<psi>qs q) \<in> expr_pr_conjunct ` (\<psi>qs ` Q)\<close>
          using \<open>Q \<noteq> {}\<close> by blast
        define e' where \<open>e' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup (((\<lambda>\<psi>. case \<psi> of (Pos \<chi>) \<Rightarrow> modal_depth_srbb_inner \<chi> | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) \<circ> \<psi>qs)
            ` ((Q\<union>Qr) - (revival_conjunct_index (Q\<union>Qr) \<psi>qs))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))
          (Sup ({1} \<union> neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q\<union>Qr)))))\<close>
        from conjuncts_present have \<open>\<forall>q\<in>Q\<union>Qr. (expr_pr_conjunct (\<psi>qs q)) \<le> e'\<close> unfolding e'_def
          by (smt (z3) Sup_upper UnI2 energy.sel image_insert insert_iff leq_components mk_disjoint_insert)
        with \<psi>qs_spec win_a_upwards_closure
          have clause_win: \<open>\<forall>q\<in>Q. attacker_wins e' (Attacker_Stable_Clause p q)\<close> by blast
        define eu' where \<open>eu' = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (((\<lambda>\<psi>. case \<psi> of (Pos \<chi>) \<Rightarrow> modal_depth_srbb_inner \<chi> | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) \<circ> \<psi>s)
          ` (I - (revival_conjunct_index I \<psi>s))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup ({1} \<union> neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` (Q\<union>Qr) \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        \<comment> \<open>TODO: encode this computation\<close>
        term \<open>Sup (((\<lambda>\<psi>. case \<psi> of (Pos \<chi>) \<Rightarrow> modal_depth_srbb_inner \<chi> | _ \<Rightarrow> max_pos_conj_secondary_depth_conjunct \<psi>) \<circ> \<psi>s)
          ` (I - (revival_conjunct_index I \<psi>s)))\<close>

        hence \<open>e' \<le> eu'\<close> unfolding e'_def eu'_def
          by (simp add: Sup_subset_mono image_mono sup.coboundedI2)
        define e where \<open>e = E
          (modal_depth e')
          (br_conj_depth e')
          (conj_depth e')
          (1 + st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (pos_conjuncts_sec e')
          (neg_conjuncts e')
          (sup 1 (neg_depth e'))\<close>
        have \<open>e' = e - (E 0 0 0 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0 0) e\<close>
          by (metis e_def energy.sel energy_leq_cases i0_lb le_iff_add)
        have expr_lower: \<open>(E 0 0 0 1 0 0 0 0 0) \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using case_assms(1) subset_form by force
        have eu'_comp: \<open>eu' = (expr_pr_inner (StableConj I \<psi>s)) - (E 0 0 0 1 0 0 0 0 0)\<close>
          unfolding eu'_def using energy.sel
          apply (auto simp add: bot_enat_def)
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
             apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          defer
            apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) energy.sel(9) image_cong image_image)
          sledgehammer
          apply (metis (no_types, lifting) SUP_cong energy.sel image_image)
          apply (metis (no_types, lifting) SUP_cong image_image)
          by (auto simp add: bot_enat_def, (metis (no_types, lifting) SUP_cong image_image)+)
        with expr_lower have eu'_characterization: \<open>Some eu' = (subtract_fn 0 0 0 1 0 0 0 0) (expr_pr_inner (StableConj I \<psi>s))\<close>
          by presburger
        have \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
        \<longrightarrow> (\<exists>q\<in>Q. (Attacker_Clause p q) = g') \<and> spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
        proof clarify
          fix g' upd
          assume upd_def: \<open>spectroscopy_moves (Defender_Stable_Conj p Q) g' = Some upd\<close>
          hence \<open>\<And>px q. g' = Attacker_Clause px q \<Longrightarrow> p = px \<and> q \<in> Q \<and> upd = (subtract_fn 0 0 0 1 0 0 0 0)\<close>
            by (metis (no_types, lifting) local.conj_s_answer option.discI option.inject)
          with upd_def case_assms(1) show
            \<open>(\<exists>q\<in>Q. Attacker_Clause p q = g') \<and> spectroscopy_moves (Defender_Stable_Conj p Q) g' = (subtract 0 0 0 1 0 0 0 0)\<close>
            by (cases g', auto)
        qed
        hence \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Stable_Conj p Q) g')) e = Some e' \<and> attacker_wins e' g')\<close>
          unfolding e_def
          using clause_win \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close> e_def by force
        hence \<open>attacker_wins e (Defender_Stable_Conj p Q)\<close>
          unfolding e_def
          by (auto simp add: attacker_wins.Defense)
        moreover have \<open>e \<le> expr_pr_inner (StableConj I \<psi>s)\<close>
          using \<open>e' \<le> eu'\<close> eu'_characterization \<open>Some e' = (subtract_fn 0 0 0 1 0 0 0 0) e\<close> expr_lower case_assms(1) subset_form
          unfolding e_def eu'_comp minus_energy_def leq_components
          by (metis add_diff_assoc_enat add_diff_cancel_enat add_left_mono enat.simps(3) enat_defs(2) energy.sel idiff_0_right)
       ultimately show \<open>attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q)\<close>
          using win_a_upwards_closure by blast
      qed
      moreover have
        \<open>(\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q))\<close>
      proof clarify
        \<comment> \<open>This is where things are more complicated than in the Conj-case. (We have to differentiate
            situations where the stability requirement finishes the distinction.)\<close>
        fix p Q
        assume case_assms:
          \<open>Q \<noteq> {}\<close>
          \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q\<close>
          \<open>\<forall>q'\<in>Q. \<exists>q\<in>Q. q \<Zsurj> q'\<close>
          \<open>\<forall>q\<in>Q. \<forall>q'. q \<Zsurj> q' \<longrightarrow> q' \<in> Q\<close>
        define Q' where \<open>Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')}\<close>
        with case_assms(2) have Q'_spec: \<open>hml_srbb_inner.distinguishes_from (StableConj I \<psi>s) p Q'\<close> \<open>\<nexists>p''. p \<mapsto>\<tau> p''\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        hence move: \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q') = Some Some\<close>
          unfolding Q'_def by auto
        show \<open>attacker_wins (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q)\<close>
        proof (cases \<open>Q' = {}\<close>)
          case True
          hence
            \<open>spectroscopy_moves (Defender_Stable_Conj p Q') (Defender_Conj p {})
            = (subtract 0 0 0 1 0 0 0 0)\<close> by auto
          moreover have
            \<open>\<forall>g'. spectroscopy_moves (Defender_Stable_Conj p Q') g' \<noteq> None \<longrightarrow> g' = (Defender_Conj p {})\<close>
          proof clarify
            fix g' u
            assume
              \<open>spectroscopy_moves (Defender_Stable_Conj p Q') g' = Some u\<close>
            with True show \<open>g' = Defender_Conj p {}\<close>
              by (induct g', auto, metis option.discI, metis empty_iff option.discI)
          qed
          ultimately have win_transfer:
            \<open>\<forall>e. E 0 0 0 1 0 0 0 0 \<le> e \<and> attacker_wins (e - E 0 0 0 1 0 0 0 0) (Defender_Conj p {}) \<longrightarrow> attacker_wins e (Defender_Stable_Conj p Q')\<close>
            using attacker_wins.Defense
            by (smt (verit, ccfv_SIG)  option.sel spectroscopy_defender.simps(7))
          have \<open>\<forall>g'. spectroscopy_moves (Defender_Conj p {}) g' = None\<close>
          proof
            fix g'
            show \<open>spectroscopy_moves (Defender_Conj p {}) g' = None\<close> by (induct g', auto)
          qed
          hence \<open>\<forall>e. attacker_wins e (Defender_Conj p {})\<close> using attacker_wins_Gd by fastforce
          moreover have \<open>\<forall>e. (subtract_fn 0 0 0 1 0 0 0 0) e \<noteq> None \<longrightarrow> e \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            using minus_energy_def by presburger
          ultimately have \<open>\<forall>e. e \<ge> (E 0 0 0 1 0 0 0 0) \<longrightarrow> attacker_wins e (Defender_Stable_Conj p Q')\<close>
            using win_transfer by presburger
          moreover have \<open>expr_pr_inner (StableConj I \<psi>s) \<ge> (E 0 0 0 1 0 0 0 0)\<close>
            by auto
          ultimately show ?thesis
            by (metis move attacker_wins_Ga_with_id_step option.discI option.sel spectroscopy_defender.simps(4))
        next
          case False
          with move show ?thesis using main_case Q'_spec attacker_wins_Ga_with_id_step unfolding Q'_def
            by (metis (mono_tags, lifting) mem_Collect_eq option.distinct(1) option.sel spectroscopy_defender.simps(4))
        qed
      qed
      ultimately show ?case by blast
    next
      case (BranchConj \<alpha> \<phi> I \<psi>s)
      have main_case:
        \<open>\<forall>p Q p' Q_\<alpha>.
             hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> p \<mapsto>a \<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
             Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)
             \<longrightarrow> attacker_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
      proof ((rule allI)+, (rule impI)+)
        fix p Q p' Q_\<alpha>
        assume case_assms:
          \<open>hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
          \<open>p \<mapsto>a \<alpha> p'\<close>
          \<open>p' \<Turnstile>SRBB \<phi>\<close>
          \<open>Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)\<close>
        from case_assms(1) have distinctions:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
            \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q\<close>
          using srbb_dist_branch_conjunction_implies_dist_conjunct_or_branch
            hml_srbb_inner.distinction_unlifting unfolding hml_srbb_inner.distinguishes_def
          by (metis Int_Collect)
        hence inductive_wins: \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
          \<exists>i\<in>I. hml_srbb_conj.distinguishes (\<psi>s i) p q
            \<and> attacker_wins (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)\<close>
          using BranchConj by blast
        define \<psi>qs where
          \<open>\<psi>qs \<equiv> \<lambda>q. (SOME \<psi>. \<exists>i\<in>I. \<psi> = \<psi>s i \<and>  hml_srbb_conj.distinguishes \<psi> p q
            \<and> attacker_wins (expr_pr_conjunct \<psi>) (Attacker_Clause p q))\<close>
        with inductive_wins someI have \<psi>qs_spec:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)).
            \<exists>i\<in>I. \<psi>qs q = \<psi>s i \<and> hml_srbb_conj.distinguishes (\<psi>qs q ) p q
              \<and> attacker_wins (expr_pr_conjunct (\<psi>qs q)) (Attacker_Clause p q)\<close>
          by (smt (verit))
        have conjuncts_present:
          \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)). expr_pr_conjunct (\<psi>qs q)
            \<in> expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)))\<close>
          by blast
        define e'0 where \<open>e'0 = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>))))))\<close>
        from conjuncts_present have branch_answer_bound:
            \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)). (expr_pr_conjunct (\<psi>qs q)) \<le> e'0\<close>
          unfolding e'0_def using SUP_upper energy.sel energy.simps(3) energy_leq_cases image_iff
          by (smt (z3))
        with \<psi>qs_spec win_a_upwards_closure have
          conj_wins: \<open>\<forall>q\<in>(Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)). attacker_wins e'0 (Attacker_Clause p q)\<close> by blast
        define eu'0 where \<open>eu'0 = E
          (Sup (modal_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (conj_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (st_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (imm_conj_depth  ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (pos_conjuncts   ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (neg_depth ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
        have subset_form: \<open>\<psi>qs ` (Q \<inter> hml_srbb_inner.model_set (Obs \<alpha> \<phi>)) \<subseteq> \<psi>s ` I\<close>
          using \<psi>qs_spec by fastforce
        hence \<open>e'0 \<le> eu'0\<close> unfolding e'0_def eu'0_def
          by (metis (mono_tags, lifting) Sup_subset_mono energy.sel energy_leq_cases image_mono)
        have no_q_way: \<open>\<forall>q\<in>Q_\<alpha>. \<nexists>q'. q \<mapsto> \<alpha> q' \<and> hml_srbb_models q' \<phi>\<close>
          using case_assms(4)
          by fastforce
        define Q' where \<open>Q' \<equiv> (soft_step_set Q_\<alpha> \<alpha>)\<close>
        hence \<open>distinguishes_from \<phi> p' Q'\<close>
          using case_assms(2,3) no_q_way soft_step_set_is_soft_step_set mem_Collect_eq
          unfolding case_assms(4)
          by fastforce
        with BranchConj have win_a_branch:
          \<open>attacker_wins (expressiveness_price \<phi>) (Attacker_Immediate p' Q')\<close>
          using distinction_implies_winning_budgets_empty_Q by (cases \<open>Q' = {}\<close>) auto
        have \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<ge> (E 1 0 0 0 0 0 0 0)\<close> by auto
        hence \<open>(subtract_fn 1 0 0 0 0 0 0 0) (expr_pr_inner (Obs \<alpha> \<phi>)) = Some (expressiveness_price \<phi>)\<close>
          using expr_obs_phi by auto
        with win_a_branch have win_a_step:
          \<open>attacker_wins (the ((subtract_fn 1 0 0 0 0 0 0 0) (expr_pr_inner (Obs \<alpha> \<phi>)))) (Attacker_Immediate p' Q')\<close> by auto
        define e' where \<open>e' = E
          (Sup (modal_depth   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (br_conj_depth   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (st_conj_depth  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (imm_conj_depth  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup ({1 + modal_depth_srbb \<phi>}
             \<union> (pos_conjuncts   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))
          (Sup (neg_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (neg_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))\<close>
        have \<open>eu'0 \<le> e'\<close> unfolding e'_def eu'0_def
          by (auto, meson sup.cobounded2 sup.coboundedI2)
        have \<open>spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q') = Some (subtract_fn 1 0 0 0 0 0 0 0)\<close> by simp
        with win_a_step attacker_wins_Ga have obs_later_win: \<open>attacker_wins (expr_pr_inner (Obs \<alpha> \<phi>)) (Attacker_Branch p' Q')\<close>
          by force
        hence e'_win: \<open>attacker_wins e' (Attacker_Branch p' Q')\<close>
          unfolding e'_def using win_a_upwards_closure
          by auto
        have depths: \<open>1 + modal_depth_srbb \<phi> = modal_depth (expr_pr_inner (Obs \<alpha> \<phi>))\<close> by simp
        have six_e': \<open>pos_conjuncts e' = Sup ({1 + modal_depth_srbb \<phi>} \<union> (pos_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))\<close>
          using energy.sel(6) unfolding e'_def by blast
        hence six_e'_simp: \<open>pos_conjuncts e' = Sup ({1 + modal_depth_srbb \<phi>} \<union> (pos_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))\<close>
          by (auto simp add: modal_depth_dominates_pos_conjuncts add_increasing  sup.absorb2 sup.coboundedI1)
        hence \<open>pos_conjuncts e' \<le> modal_depth e'\<close>
          unfolding e'_def
          by (auto, smt (verit) SUP_mono energy.sel(1) energy.sel(6) image_iff modal_depth_dominates_pos_conjuncts sup.coboundedI2)
        hence \<open>modal_depth (the (min1_6 e')) = (pos_conjuncts e')\<close>
          by simp
        with six_e' have min_e'_def: \<open>min1_6 e' = Some (E
          (Sup ({1 + modal_depth_srbb \<phi>} \<union> pos_conjuncts ` (expr_pr_conjunct ` (\<psi>s ` I))))
          (Sup (br_conj_depth   ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (conj_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (st_conj_depth  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (imm_conj_depth  ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup ({1 + modal_depth_srbb \<phi>} \<union> (pos_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))
          (Sup (neg_conjuncts ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I)))))
          (Sup (neg_depth ` ({expr_pr_inner (Obs \<alpha> \<phi>)} \<union> (expr_pr_conjunct ` (\<psi>s ` I))))))\<close>
          using e'_def min1_6_def six_e'_simp
          by (smt (z3) energy.case_eq_if energy.sel min_1_6_simps(1))
        hence \<open>expr_pr_inner (Obs \<alpha> \<phi>) \<le> the (min1_6 e')\<close>
          by force
        hence obs_win: \<open>attacker_wins (the (min1_6 e')) (Attacker_Branch p' Q')\<close>
          using obs_later_win win_a_upwards_closure by blast
        define e where \<open>e = E
          (modal_depth e')
          (1 + br_conj_depth e')
          (1 + conj_depth e')
          (st_conj_depth e')
          (imm_conj_depth e')
          (pos_conjuncts e')
          (neg_conjuncts e')
          (neg_depth e')\<close>
        have \<open>e' = e - (E 0 1 1 0 0 0 0 0)\<close> unfolding e_def e'_def by auto
        hence e'_comp: \<open>Some e' = (subtract_fn 0 1 1 0 0 0 0 0) e\<close>
          by (metis e_def energy.sel energy_leq_cases i0_lb le_iff_add)
        have expr_lower: \<open>(E 0 1 1 0 0 0 0 0) \<le> expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)\<close>
          using case_assms subset_form by auto
        have e'_minus: \<open>e' = expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) - E 0 1 1 0 0 0 0 0\<close>
          unfolding e'_def using energy.sel
          by (auto simp add: bot_enat_def sup.left_commute,
             (metis (no_types, lifting) SUP_cong image_image)+)
        with expr_lower have e'_characterization:
            \<open>Some e' = (subtract_fn 0 1 1 0 0 0 0 0) (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s))\<close>
          by presburger
        have moves: \<open>\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
        \<longrightarrow> (((Attacker_Branch p' Q' = g')
            \<and> (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)))
          \<or> ((\<exists>q\<in>(Q - Q_\<alpha>). Attacker_Clause p q = g'
            \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = (subtract 0 1 1 0 0 0 0 0))))\<close>
        proof clarify
          fix g' u
          assume no_subtr_move:
            \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = Some u\<close>
            \<open>\<not> (\<exists>q\<in>Q - Q_\<alpha>. Attacker_Clause p q = g' \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' = subtract 0 1 1 0 0 0 0 0)\<close>
          hence \<open>g' = Attacker_Branch p' Q'\<close>
            unfolding Q'_def using soft_step_set_is_soft_step_set no_subtr_move local.br_answer
            by (cases g', auto, (metis (no_types, lifting)  option.discI)+)
          moreover have \<open>Attacker_Branch p' Q' = g' \<longrightarrow> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' =  Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)\<close>
            unfolding Q'_def using soft_step_set_is_soft_step_set by auto
          ultimately show \<open>Attacker_Branch p' Q' = g' \<and> spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' =  Some (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)\<close>
            by blast
        qed
        have obs_e: \<open>\<exists>e'. (\<lambda>e. Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6) e = Some e' \<and> attacker_wins e' (Attacker_Branch p' Q')\<close>
          using obs_win e'_comp min_e'_def
          by (smt (verit, best) bind.bind_lunit min_1_6_some option.collapse)
        have \<open>\<forall>q\<in>(Q - Q_\<alpha>). spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) (Attacker_Clause p q) = (subtract 0 1 1 0 0 0 0 0)
          \<longrightarrow> attacker_wins e'0 (Attacker_Clause p q)\<close>
          using conj_wins \<open>eu'0 \<le> e'\<close> case_assms(4) by blast
        with obs_e moves have move_wins: \<open>\<forall>g'. spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g' \<noteq> None
          \<longrightarrow> (\<exists>e'. (the (spectroscopy_moves (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) g')) e = Some e' \<and> attacker_wins e' g')\<close>
          using  \<open>eu'0 \<le> e'\<close> e'_comp \<open>e'0 \<le> eu'0\<close> win_a_upwards_closure
         by (smt (verit, ccfv_SIG) option.sel)
        moreover have \<open>expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s) = e\<close>
          using e'_characterization e'_minus unfolding e_def by force
        ultimately show \<open>attacker_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
        using attacker_wins.Defense spectroscopy_defender.simps(5)
          by metis
      qed
      moreover have
        \<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q
             \<longrightarrow> attacker_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)\<close>
      proof clarify
        fix p Q
        assume case_assms:
          \<open>hml_srbb_inner.distinguishes_from (BranchConj \<alpha> \<phi> I \<psi>s) p Q\<close>
        from case_assms(1) obtain p' where p'_spec: \<open>p \<mapsto>a \<alpha> p'\<close> \<open>p' \<Turnstile>SRBB \<phi>\<close>
          unfolding hml_srbb_inner.distinguishes_from_def
              and distinguishes_def by auto
        define Q_\<alpha> where \<open>Q_\<alpha> = Q - hml_srbb_inner.model_set (Obs \<alpha> \<phi>)\<close>
        have \<open>attacker_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)\<close>
          using main_case case_assms(1) p'_spec Q_\<alpha>_def by blast
        moreover have \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>) = Some Some\<close>
          using p'_spec Q_\<alpha>_def by auto
        ultimately show \<open>attacker_wins (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q)\<close>
          using attacker_wins_Ga_with_id_step by auto
      qed
      ultimately show ?case by blast
    next
      case (Pos \<chi>)
      show ?case
      proof clarify
        fix p q
        assume case_assms: \<open>hml_srbb_conj.distinguishes (Pos \<chi>) p q\<close>
        then obtain p' where p'_spec: \<open>p \<Zsurj> p'\<close> \<open>p' \<in> hml_srbb_inner.model_set \<chi>\<close>
          unfolding hml_srbb_conj.distinguishes_def by auto
        moreover have q_reach: \<open>silent_reachable_set {q} \<inter> hml_srbb_inner.model_set \<chi> = {}\<close>
          using case_assms sreachable_set_is_sreachable
          unfolding hml_srbb_conj.distinguishes_def by force
        ultimately have distinction: \<open>hml_srbb_inner.distinguishes_from \<chi> p' (silent_reachable_set {q})\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        have q_reach_nonempty:
            \<open>silent_reachable_set {q} \<noteq> {}\<close>
            \<open>silent_reachable_set {q} \<Zsurj>S silent_reachable_set {q} \<close>
          unfolding silent_reachable_set_def
          using silent_reachable.intros(1) silent_reachable_trans by auto
        hence \<open>attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed p' (silent_reachable_set {q}))\<close>
          using distinction Pos by blast
        from p'_spec(1) this have \<open>attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed p (silent_reachable_set {q}))\<close>
          by (induct, auto,
              metis attacker_wins_Ga_with_id_step local.procrastination option.distinct(1) option.sel spectroscopy_defender.simps(4))
        moreover have \<open>spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p (silent_reachable_set {q})) = Some min1_6\<close>
          using q_reach_nonempty sreachable_set_is_sreachable by fastforce
        moreover have \<open>the (min1_6 (expr_pr_conjunct (Pos \<chi>))) \<ge> expr_pr_inner \<chi>\<close>
          unfolding min1_6_def by (auto simp add: energy_leq_cases modal_depth_dominates_pos_conjuncts)
        ultimately show \<open>attacker_wins (expr_pr_conjunct (Pos \<chi>)) (Attacker_Clause p q)\<close>
          using attacker_wins_Ga win_a_upwards_closure spectroscopy_defender.simps(3)
          by (metis (no_types, lifting) min_1_6_some option.discI option.exhaust_sel option.sel)
      qed
    next
      case (Neg \<chi>)
      show ?case
      proof clarify
        fix p q
        assume case_assms: \<open>hml_srbb_conj.distinguishes (Neg \<chi>) p q\<close>
        then obtain q' where q'_spec: \<open>q \<Zsurj> q'\<close> \<open>q' \<in> hml_srbb_inner.model_set \<chi>\<close>
          unfolding hml_srbb_conj.distinguishes_def by auto
        moreover have p_reach: \<open>silent_reachable_set {p} \<inter> hml_srbb_inner.model_set \<chi> = {}\<close>
          using case_assms sreachable_set_is_sreachable
          unfolding hml_srbb_conj.distinguishes_def by force
        ultimately have distinction: \<open>hml_srbb_inner.distinguishes_from \<chi> q' (silent_reachable_set {p})\<close>
          unfolding hml_srbb_inner.distinguishes_from_def by auto
        have \<open>p \<noteq> q\<close> using case_assms unfolding hml_srbb_conj.distinguishes_def by auto
        have p_reach_nonempty:
            \<open>silent_reachable_set {p} \<noteq> {}\<close>
            \<open>silent_reachable_set {p} \<Zsurj>S silent_reachable_set {p}\<close>
          unfolding silent_reachable_set_def
          using silent_reachable.intros(1) silent_reachable_trans by auto
        hence \<open>attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed q' (silent_reachable_set {p}))\<close>
          using distinction Neg by blast
        from q'_spec(1) this have \<open>attacker_wins (expr_pr_inner \<chi>) (Attacker_Delayed q (silent_reachable_set {p}))\<close>
          by (induct, auto,
              metis attacker_wins_Ga_with_id_step local.procrastination option.distinct(1) option.sel spectroscopy_defender.simps(4))
        moreover have \<open>spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q (silent_reachable_set {p}))
             = Some (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
          using p_reach_nonempty sreachable_set_is_sreachable \<open>p \<noteq> q\<close> by fastforce
        moreover have \<open>the (min1_7 (expr_pr_conjunct (Neg \<chi>) - E 0 0 0 0 0 0 0 1)) \<ge> (expr_pr_inner \<chi>)\<close>
          using min1_7_def energy_leq_cases
          by (simp add: modal_depth_dominates_neg_conjuncts)
        moreover from this have \<open>\<exists>e'. Some e' = ((\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) (expr_pr_conjunct (Neg \<chi>))) \<and> e' \<ge> (expr_pr_inner \<chi>)\<close>
          unfolding min_1_7_subtr_simp by auto
        ultimately show \<open>attacker_wins (expr_pr_conjunct (Neg \<chi>)) (Attacker_Clause p q)\<close>
          using attacker_wins.Attack win_a_upwards_closure spectroscopy_defender.simps(3)
          by (metis (no_types, lifting) option.discI option.sel)
      qed
    qed
  qed
  thus ?thesis
    by (metis assms distinction_implies_winning_budgets_empty_Q)
qed

end (* context weak_spectroscopy_game *)

end