section \<open>Distinction Implies Winning Budgets\<close>
theory Distinction_Implies_Winning_Budgets
  imports Spectroscopy_Game Expressiveness_Price
begin

context full_spec_game
begin

lemma distinction_implies_winning_budgets_empty_Q:
  assumes "distinguishes_from \<phi> p {}"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p {})"
proof-
  have not_neg: "expressiveness_price \<phi> \<noteq> eneg" by auto
  moreover have is_last_move: "spectroscopy_moves (Defender_Conj p {}) p' = None" for p' 
    by(rule spectroscopy_moves.elims, auto)
  moreover have "spectroscopy_defender (Defender_Conj p {})" by simp
  ultimately have conj_win: "in_wina (expressiveness_price \<phi>) (Defender_Conj p {})" 
    by (simp add: in_wina.intros(1))

  from finishing_or_early_conj[of p "{}" p "{}"] have next_move: 
    "spectroscopy_moves (Attacker_Immediate p {}) (Defender_Conj p {}) = Some id" 
    by force

  moreover have "attacker (Attacker_Immediate p {})" by simp
  ultimately show ?thesis using in_wina.intros(2)[of "Attacker_Immediate p {}" "expressiveness_price \<phi>"]
    by (metis conj_win id_apply not_neg option.distinct(1) option.sel)
qed

lemma distinction_implies_winning_budgets:
  assumes "distinguishes_from \<phi> p Q"
  shows "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
proof-
text \<open>
The inductive property of lemma 1 is formalized as follows
\begin{itemize}
\item [1.] At attacker positions, if \<open>\<phi> :: hml_srbb\<close> distinguishes \<open>p\<close> from \<open>Q \<noteq> {}\<close>,
   then \<open>expr(\<phi>) \<in> Win_a((p,Q)_a)\<close>.\\
\<open>\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
       \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)\<close>

\item[2.] At attacker positions, if \<open>\<chi>\<close> distinguishes \<open>p\<close> from \<open>Q \<noteq> {}\<close> and \<open>Q\<close> is closed under \<open>\<Zsurj>\<close> (i.e. \<open>Q \<Zsurj> Q\<close>),
   then \<open>expr^\<epsilon>(\<chi>) \<in> Win_a((p,Q)^\<epsilon>_a)\<close>.\\
\<open>\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
       \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q)\<close>

\item [4.] At defender positions, if \<open>\<And>\<Psi>\<close> distinguishes \<open>p\<close> from \<open>Q \<noteq> {}\<close>,
   then \<open>expr^\<epsilon>(\<And>\<Psi>) \<in> Win_a((p,Q)_d)\<close>.\\
\<open>\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
       Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
       \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q)\<close>

\item[5.] At defender positions, if \<open>\<And>({\<not>\<langle>\<tau>\<rangle>\<top>} \<union> \<Psi>)\<close> distinguishes \<open>p\<close> from \<open>Q \<noteq> {}\<close> and the processes in \<open>Q\<close> are stable,
   then \<open>expr^\<epsilon>(\<And>({\<not>\<langle>\<tau>\<rangle>\<top>} \<union> \<Psi>)) \<in> Win_a((p,Q)^s_d)\<close>.\\
\<open>\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
       Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
       \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q)\<close>

\item[6.] At defender positions, if \<open>\<And>({(\<alpha>)\<phi>} \<union> \<Psi>)\<close> distinguishes \<open>p\<close> from \<open>Q\<close>,
   for any \<open>p \<mapsto> \<alpha> p' \<in> \<lbrakk>\<phi>\<rbrakk>\<close> and \<open>Q \<inter> \<lbrakk>\<And>\<Psi>\<rbrakk> \<subseteq> Q_\<alpha> \<subseteq> Q - \<lbrakk>(\<alpha>)\<phi>\<rbrakk>\<close>,
   then \<open>expr^\<epsilon>(\<And>({(\<alpha>)\<phi>} \<union> \<Psi>)) \<in> Win_a((p,\<alpha>,p',Q - Q_\<alpha>, Q_\<alpha>)^\<eta>_d)\<close>.\\
\<open>\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
       distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
       Q \<inter> model_set_inner (Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow> Q_\<alpha> \<subseteq> Q - model_set_inner (Obs \<alpha> \<phi>)
       \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))\<close>

\item[3.] At attacker positions, if \<open>\<psi>\<close> distinguishes \<open>p\<close> from \<open>q\<close>,
   then \<open>expr^\^(\<psi>) \<in> Win_a((p,q)^\^_a)\<close>.\\
\<open>\<forall>p q. distinguishes_conjunct \<psi> p q
       \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)\<close>
\end{itemize}
\<close>
  have "\<And>\<phi> \<chi> \<psi>.
        (\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
               \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q))
      \<and>
        ((\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = Conj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
            Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q \<in> Q. \<nexists>q'. q \<mapsto> \<tau> q')
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
        \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
            distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
            Q \<inter> model_set_inner (Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow> Q_\<alpha> \<subseteq> Q - model_set_inner (Obs \<alpha> \<phi>)
            \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>)))
      \<and>
        (\<forall>p q. distinguishes_conjunct \<psi> p q
               \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q))"

  proof (rule hml_srbb_hml_srbb_inner_hml_srbb_conjunct.induct)
    show "\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from TT p Q
                \<longrightarrow> in_wina (expressiveness_price TT) (Attacker_Immediate p Q)"
    proof (rule allI, rule allI, rule impI, rule impI)
      fix Q p
      assume "Q \<noteq> {}"
        and "distinguishes_from TT p Q"
      hence "\<exists>q. q \<in> Q" 
        by blast
      then obtain q where "q \<in> Q" by auto

      from \<open>distinguishes_from TT p Q\<close>
       and \<open>q \<in> Q\<close>
      have "distinguishes TT p q" 
        using distinguishes_from_def by auto

      with verum_never_distinguishes
      show "in_wina (expressiveness_price TT) (Attacker_Immediate p Q)" 
        by blast
    qed

  next

    fix \<chi>
    assume
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
    hence IH1:
      "\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q)"
      and IH2:
      "(\<forall>\<Psi>_I \<Psi> p Q. \<chi> = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))"
      and IH3:
      "(\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))"
      and IH4:
      "(\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
      by auto

    show "\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from (Internal \<chi>) p Q
                \<longrightarrow> in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Immediate p Q)"
    proof (rule allI, rule allI, rule impI, rule impI)
      fix Q p
      assume "Q \<noteq> {}"
         and "distinguishes_from (Internal \<chi>) p Q"
      hence "(\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> hml_srbb_inner_to_hml \<chi>)
           \<and> (\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))"
        unfolding distinguishes_from_def
              and distinguishes_def
              and hml_srbb_models.simps
              and hml_srbb_to_hml.simps
              and hml_models.simps
        by blast
      then have "\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> hml_srbb_inner_to_hml \<chi>"
            and "\<forall>q \<in> Q. (\<nexists>q'. q \<Zsurj> q' \<and> q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)"
        by auto
      hence "\<forall>q \<in> Q. (\<forall>q'. q \<Zsurj> q' \<longrightarrow> \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))" by auto
      then have "\<forall>q \<in> Q. (\<forall>q'\<in>Q'. q \<Zsurj> q' \<longrightarrow> \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))" 
        for Q' by blast
      then have "Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))"
        for Q' using \<open>Q \<noteq> {}\<close> by blast

      define Q\<tau> where "Q\<tau> \<equiv> silent_reachable_set Q"
      with \<open>\<And>Q'. Q \<Zsurj>S Q' \<longrightarrow> (\<forall>q' \<in> Q'. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>))\<close>
      have "\<forall>q' \<in> Q\<tau>. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)" 
        using sreachable_set_is_sreachable by presburger
      have "Q\<tau> \<Zsurj>S Q\<tau>" unfolding Q\<tau>_def 
        by (metis silent_reachable_trans sreachable_set_is_sreachable 
            silent_reachable.intros(1))

      from \<open>\<exists>p'. p \<Zsurj> p' \<and> p' \<Turnstile> hml_srbb_inner_to_hml \<chi>\<close>
      obtain p' where "p \<Zsurj> p'" and "p' \<Turnstile> hml_srbb_inner_to_hml \<chi>" by auto
      from this(1) have "p \<Zsurj>L p'" by(rule silent_reachable_impl_loopless)

      have "Q\<tau> \<noteq> {}"
        using silent_reachable.intros(1) sreachable_set_is_sreachable Q\<tau>_def \<open>Q \<noteq> {}\<close> 
        by fastforce

      from \<open>p' \<Turnstile> hml_srbb_inner_to_hml \<chi>\<close>
       and \<open>\<forall>q' \<in> Q\<tau>. \<not>(q' \<Turnstile> hml_srbb_inner_to_hml \<chi>)\<close>
      have "distinguishes_from_inner \<chi> p' Q\<tau>" 
        by (simp add: distinguishes_from_inner_def distinguishes_inner_def)

      
      with \<open>Q\<tau> \<Zsurj>S Q\<tau>\<close> \<open>Q\<tau> \<noteq> {}\<close>
       and IH1
      have "in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p' Q\<tau>)" 
        by blast

      moreover have "expr_pr_inner \<chi> = expressiveness_price (Internal \<chi>)" by simp
      ultimately have "in_wina (expressiveness_price (Internal \<chi>)) 
          (Attacker_Delayed p' Q\<tau>)" by simp

      hence "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)"
      proof(induct rule: silent_reachable_loopless.induct[of "p" "p'", OF \<open>p \<Zsurj>L p'\<close>])
        case (1 p)                    
        thus ?case by simp
      next
        case (2 p p' p'')
        hence "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p' Q\<tau>)"
          by simp
        moreover have "spectroscopy_moves (Attacker_Delayed p Q\<tau>) (Attacker_Delayed p' Q\<tau>) 
          = Some id" using spectroscopy_moves.simps(2) \<open>p \<noteq> p'\<close> \<open>p \<mapsto>\<tau> p'\<close> by auto
        moreover have "attacker (Attacker_Delayed p Q\<tau>)" by simp
        ultimately show ?case using in_wina_Ga_with_id_step by auto
      qed

      have  "Q \<Zsurj>S Q\<tau>" 
        using Q\<tau>_def sreachable_set_is_sreachable by simp
      hence "spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q\<tau>) = Some id"
        using spectroscopy_moves.simps(1) by simp
      with \<open>in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Delayed p Q\<tau>)\<close>
      show "in_wina (expressiveness_price (Internal \<chi>)) (Attacker_Immediate p Q)" 
        using in_wina_Ga_with_id_step
        by (metis option.discI option.sel spectroscopy_defender.simps(1))
      qed

  next

    fix I :: "'s set"
    and \<psi>s :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct"
    assume IH: "\<And>\<psi>. \<psi> \<in> range \<psi>s \<Longrightarrow> \<forall>p q. distinguishes_conjunct \<psi> p q
                  \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)"
    show "\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from (ImmConj I \<psi>s) p Q
                \<longrightarrow> in_wina (expressiveness_price (ImmConj I \<psi>s)) (Attacker_Immediate p Q)"
    proof(rule allI, rule allI, rule impI, rule impI)
      fix Q p
      assume "Q \<noteq> {}" and "distinguishes_from (ImmConj I \<psi>s) p Q"
      from this(2) have "\<forall>q\<in>Q. p \<Turnstile>SRBB ImmConj I \<psi>s \<and> \<not> q \<Turnstile>SRBB ImmConj I \<psi>s" 
        unfolding distinguishes_from_def distinguishes_def by blast
      hence "\<forall>q\<in>Q. \<exists>i\<in>I. hml_srbb_conjunct_models (\<psi>s i) p \<and> \<not>hml_srbb_conjunct_models (\<psi>s i) q"
        by simp
      hence "\<forall>q\<in>Q. \<exists>i\<in>I. distinguishes_conjunct (\<psi>s i) p q"
        using distinguishes_conjunct_def by simp
      hence "\<forall>q\<in>Q. \<exists>i\<in>I. ((\<psi>s i) \<in> range \<psi>s) \<and> distinguishes_conjunct (\<psi>s i) p q" by blast
      hence "\<forall>q\<in>Q. \<exists>i\<in>I. in_wina (expr_pr_conjunct (\<psi>s i)) (Attacker_Clause p q)" using IH by blast
      hence a_clause_wina: "\<forall>q\<in>Q. \<exists>i\<in>I. in_wina (e3 (e5 (expressiveness_price (ImmConj I \<psi>s)))) 
        (Attacker_Clause p q)"
        using expressiveness_price_ImmConj_geq_parts' win_a_upwards_closure by fast

      from this \<open>Q \<noteq> {}\<close> have "I \<noteq> {}" by blast         
      with expressiveness_price_ImmConj_geq_parts \<psi>_price_never_neg have
          "e5 (e3 (expressiveness_price (ImmConj I \<psi>s))) \<noteq> eneg"
        by (simp add: direct_minus_eq energy_leq_cases)
      hence "e5 (expressiveness_price (ImmConj I \<psi>s)) \<noteq> eneg"
        using leq_not_eneg minus_energy_def 
        by (metis \<open>Q \<noteq> {}\<close> a_clause_wina defender_win_level_not_in_wina
            energy.discI equals0I gets_smaller win_a_upwards_closure)

      have def_conj: "spectroscopy_defender (Defender_Conj p Q)" by simp
      have  "spectroscopy_moves (Defender_Conj p Q) N \<noteq> None 
            \<Longrightarrow> N = Attacker_Clause (attacker_state N) (defender_state N)" for N
        by (metis spectroscopy_moves.simps(34,35,36,38,64,74) spectroscopy_position.exhaust_sel)
      hence  move_kind: "spectroscopy_moves (Defender_Conj p Q) N \<noteq> None \<Longrightarrow> \<exists>q\<in>Q. N = Attacker_Clause p q" for N
        using conj_answer by metis   

      hence update: "\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow> 
        weight (Defender_Conj p Q) g' = e3"
        by fastforce

      have move_wina: "\<And>g'. spectroscopy_moves (Defender_Conj p Q) g' \<noteq> None \<Longrightarrow>
       in_wina (e3 (e5 (expressiveness_price (ImmConj I \<psi>s)))) g'"
        using move_kind a_clause_wina by blast
  
      from in_wina_Gd[OF def_conj \<open>e5 (expressiveness_price (ImmConj I \<psi>s)) \<noteq> eneg\<close> update move_wina]
      have def_conj_wina: "in_wina (e5 (expressiveness_price (ImmConj I \<psi>s))) (Defender_Conj p Q)" by blast

      have imm_to_conj: "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p Q) \<noteq> None" 
        by simp
      have imm_to_conj_wgt: "weight (Attacker_Immediate p Q) (Defender_Conj p Q) = e5" 
        by (simp add: \<open>Q \<noteq> {}\<close>)

      from in_wina_Ga[of e5, OF def_conj_wina, of "Attacker_Immediate p Q"] imm_to_conj imm_to_conj_wgt
      show "in_wina (expressiveness_price (ImmConj I \<psi>s)) (Attacker_Immediate p Q)" by simp
    qed

  next

    fix \<alpha> \<phi>
    assume IH: "\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
                  \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
    have "\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> Q \<Zsurj>S Q
                \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)" 
    proof(rule allI, rule allI, rule impI, rule impI, rule impI)
      fix p Q
      assume "Q \<noteq> {}" "distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q" "Q \<Zsurj>S Q"
      have "\<exists>p' Q'. p \<mapsto>a \<alpha> p' \<and> Q \<mapsto>aS \<alpha> Q' \<and> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q')" 
      proof(cases "\<alpha> = \<tau>")
        case True
        with \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> have dist_unfold:
             "p \<Turnstile> Silent (hml_srbb_to_hml \<phi>) \<and> (\<forall>q\<in>Q. \<not> q \<Turnstile> Silent (hml_srbb_to_hml \<phi>))"
          unfolding True distinguishes_from_inner_def distinguishes_inner_def
          hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps hml_models.simps(4)
          by simp
        hence "((\<exists>p'. p \<mapsto>\<tau> p' \<and> p' \<Turnstile> hml_srbb_to_hml \<phi>) \<or> p \<Turnstile> hml_srbb_to_hml \<phi>)"
          unfolding True distinguishes_from_inner_def distinguishes_inner_def
          hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps hml_models.simps(4)
          by simp
        then obtain p' where "p' \<Turnstile> hml_srbb_to_hml \<phi>" "p \<mapsto>a \<alpha> p'" 
          unfolding True by blast

        from dist_unfold have
          "\<forall>q\<in>Q. (\<not> q \<Turnstile> hml_srbb_to_hml \<phi>) \<and> (\<nexists>q'. q \<mapsto>\<tau> q' \<and> q' \<Turnstile> hml_srbb_to_hml \<phi>)"
          by simp
        hence "\<forall>q\<in>Q. \<not>q \<Turnstile> hml_srbb_to_hml \<phi>" using \<open>Q \<Zsurj>S Q\<close> by fastforce
        

        hence "distinguishes_from \<phi> p' Q"
          by (simp add: \<open>p' \<Turnstile> hml_srbb_to_hml \<phi>\<close> distinguishes_def distinguishes_from_def)
        with IH have "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q)" 
          using \<open>Q \<noteq> {}\<close> by blast
        moreover have "Q \<mapsto>aS \<alpha> Q" unfolding True using \<open>Q \<Zsurj>S Q\<close> using silent_reachable_append_\<tau> by blast
        ultimately show ?thesis using \<open>p \<mapsto>a \<alpha> p'\<close> by blast
      next
        case False
        with \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> 
        obtain p'' where "(p \<mapsto>\<alpha> p'') \<and> (p'' \<Turnstile> (hml_srbb_to_hml \<phi>))" 
          unfolding distinguishes_from_inner_def distinguishes_inner_def
            hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps 
          using hml_models.simps \<open>Q \<noteq> {}\<close> by auto

        let ?Q' = "step_set Q \<alpha>"
        from \<open>distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q\<close> 
        have "\<forall>q\<in>Q. \<not> q \<Turnstile> hml.Obs \<alpha> (hml_srbb_to_hml \<phi>)" 
          unfolding distinguishes_from_inner_def distinguishes_inner_def
            hml_srbb_inner_models.simps hml_srbb_inner_to_hml.simps 
          using hml_models.simps \<open>Q \<noteq> {}\<close> by (metis (full_types))
        hence "\<forall>q\<in>?Q'. \<not> q \<Turnstile> hml_srbb_to_hml \<phi>"
          using step_set_is_step_set by fastforce

        from \<open>\<forall>q\<in>step_set Q \<alpha>. \<not> q \<Turnstile> hml_srbb_to_hml \<phi>\<close> \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile> hml_srbb_to_hml \<phi>\<close>
        have "distinguishes_from \<phi> p'' ?Q'"
          by (simp add: distinguishes_def distinguishes_from_def)
        hence "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p'' ?Q')"
          by (metis IH distinction_implies_winning_budgets_empty_Q)
        moreover have "p \<mapsto>\<alpha> p''" using \<open>p \<mapsto>\<alpha> p'' \<and> p'' \<Turnstile> hml_srbb_to_hml \<phi>\<close> by simp
        moreover have "Q \<mapsto>aS \<alpha> ?Q'" by (simp add: False LTS.step_set_is_step_set)
        ultimately show ?thesis by blast
      qed
      then obtain p' Q' where p'_Q': "p \<mapsto>a \<alpha> p'" "Q \<mapsto>aS \<alpha> Q'" and
        wina: "in_wina (expressiveness_price \<phi>) (Attacker_Immediate p' Q')" by blast

      have attacker: "attacker (Attacker_Delayed p Q)" by simp

      have "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') =
            (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then Some e1 else None)"
        for p Q p' Q' by simp
      from this[of p Q p' Q'] have 
        "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = 
             Some e1" using p'_Q' by auto
     
      with expr_obs_phi[of \<alpha> \<phi>] wina attacker show
        "in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q)"
        using in_wina_Ga by (metis option.discI option.sel)
    qed
    then show
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Obs \<alpha> \<phi> = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Obs \<alpha> \<phi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha>' \<phi>' p Q p' Q_\<alpha>. hml_srbb_inner.Obs \<alpha> \<phi> = BranchConj \<alpha>' \<phi>' \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner (hml_srbb_inner.Obs \<alpha> \<phi>) p Q \<longrightarrow> p \<mapsto>\<alpha>' p' \<longrightarrow> p' \<Turnstile>SRBB \<phi>' \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha>' \<phi>')
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Obs \<alpha> \<phi>)) (Defender_Branch p \<alpha>' p' (Q - Q_\<alpha>) Q_\<alpha>))" 
      by fastforce

  next

    fix I :: "'s set"
    and \<psi>s :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct"
    assume IH: "\<And>\<psi>. \<psi> \<in> range \<psi>s \<Longrightarrow> \<forall>p q. distinguishes_conjunct \<psi> p q
                  \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)"
    have
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q))" sorry
    then show
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. hml_srbb_inner.Conj I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. hml_srbb_inner.Conj I \<psi>s = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner (hml_srbb_inner.Conj I \<psi>s) p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner (hml_srbb_inner.Conj I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
      by fastforce

  next

    fix I :: "'s set"
    and \<psi>s :: "'s \<Rightarrow> ('a, 's) hml_srbb_conjunct"
    assume IH: "\<And>\<psi>. \<psi> \<in> range \<psi>s \<Longrightarrow> \<forall>p q. distinguishes_conjunct \<psi> p q
                  \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)"
    have
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. StableConj I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q))" sorry
    then show
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. StableConj I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. StableConj I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. StableConj I \<psi>s = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner (StableConj I \<psi>s) p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner (StableConj I \<psi>s)) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
      by fastforce

  next

    fix \<alpha> :: 'a
    and \<phi> :: "('a, 's) hml_srbb"
    and I :: "'s set"
    and \<psi>s :: "'s \<Rightarrow> ('a,'s) hml_srbb_conjunct"
    assume IH1:
          "\<forall>Q p. Q \<noteq> {} \<longrightarrow> distinguishes_from \<phi> p Q
            \<longrightarrow> in_wina (expressiveness_price \<phi>) (Attacker_Immediate p Q)"
       and IH2:
          "\<And>\<psi>. \<psi> \<in> range \<psi>s \<Longrightarrow> \<forall>p q. distinguishes_conjunct \<psi> p q
            \<longrightarrow> in_wina (expr_pr_conjunct \<psi>) (Attacker_Clause p q)"
    have
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha>' \<phi>' p Q p' Q_\<alpha>. BranchConj \<alpha> \<phi> I \<psi>s = BranchConj \<alpha>' \<phi>' \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> p \<mapsto>\<alpha>' p' \<longrightarrow> p' \<Turnstile>SRBB \<phi>' \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha>' \<phi>')
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha>' p' (Q - Q_\<alpha>) Q_\<alpha>))" sorry
    then show
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. BranchConj \<alpha> \<phi> I \<psi>s = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. BranchConj \<alpha> \<phi> I \<psi>s = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha>' \<phi>' p Q p' Q_\<alpha>. BranchConj \<alpha> \<phi> I \<psi>s = BranchConj \<alpha>' \<phi>' \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner (BranchConj \<alpha> \<phi> I \<psi>s) p Q \<longrightarrow> p \<mapsto>\<alpha>' p' \<longrightarrow> p' \<Turnstile>SRBB \<phi>' \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha>' \<phi>')
           \<longrightarrow> in_wina (expr_pr_inner (BranchConj \<alpha> \<phi> I \<psi>s)) (Defender_Branch p \<alpha>' p' (Q - Q_\<alpha>) Q_\<alpha>))"
      by fastforce

  next

    fix \<chi>
    assume IH:
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
    show "\<forall>p q. distinguishes_conjunct (hml_srbb_conjunct.Pos \<chi>) p q \<longrightarrow>
             in_wina (expr_pr_conjunct (hml_srbb_conjunct.Pos \<chi>)) (Attacker_Clause p q)" sorry

  next

    fix \<chi>
    assume IH: 
      "(\<forall>p Q. Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> Q \<Zsurj>S Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Attacker_Delayed p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = hml_srbb_inner.Conj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> p Q. \<chi> = StableConj \<Psi>_I \<Psi> \<longrightarrow>
           Q \<noteq> {} \<longrightarrow> distinguishes_from_inner \<chi> p Q \<longrightarrow> (\<forall>q\<in>Q. \<nexists>q'. q \<mapsto>\<tau> q')
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Stable_Conj p Q))
     \<and> (\<forall>\<Psi>_I \<Psi> \<alpha> \<phi> p Q p' Q_\<alpha>. \<chi> = BranchConj \<alpha> \<phi> \<Psi>_I \<Psi> \<longrightarrow>
           distinguishes_from_inner \<chi> p Q \<longrightarrow> p \<mapsto>\<alpha> p' \<longrightarrow> p' \<Turnstile>SRBB \<phi> \<longrightarrow>
           Q \<inter> model_set_inner (hml_srbb_inner.Conj \<Psi>_I \<Psi>) \<subseteq> Q_\<alpha> \<longrightarrow>
           Q_\<alpha> \<subseteq> Q - model_set_inner (hml_srbb_inner.Obs \<alpha> \<phi>)
           \<longrightarrow> in_wina (expr_pr_inner \<chi>) (Defender_Branch p \<alpha> p' (Q - Q_\<alpha>) Q_\<alpha>))"
    show "\<forall>p q. distinguishes_conjunct (hml_srbb_conjunct.Neg \<chi>) p q
           \<longrightarrow> in_wina (expr_pr_conjunct (hml_srbb_conjunct.Neg \<chi>)) (Attacker_Clause p q)" sorry
  qed
  
  thus ?thesis
    by (metis assms distinction_implies_winning_budgets_empty_Q)
qed

end (* context full_spec_game *)

end