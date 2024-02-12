section \<open>Weak Spectroscopy Game\<close>
theory Spectroscopy_Game
  imports Energy_Games Energy LTS
begin

text \<open>In this theory we define the weak spectroscopy game as a locale.
This game is an energy game constructed by adding stable and branching conjunctions to a delay bisimulation game that depends on an LTS.
We play the spectroscopy game to compare the behaviour of processes and analyze which behavioural equivalences apply.
The moves of a spectroscopy game depend on the transitions of the processes and the available energy.
So in other words: \\If the defender wins the spectroscopy game starting with a certain energy, a corresponding behavioral equivalence applies.
\\ We differentiate the positions accordingly and define the moves of the game corresponding to their names in \cite{bisping2023lineartimebranchingtime}.\<close>
datatype ('s, 'a) spectroscopy_position = 
                          Attacker_Immediate (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Branch (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Clause (attacker_state: "'s") (defender_state: "'s") |
                          Attacker_Delayed (attacker_state: "'s") (defender_states: "'s set") |

                          Defender_Branch (attacker_state: "'s") (attack_action: "'a") (attacker_state_succ: "'s") (defender_states: "'s set") (defender_branch_states: "'s set") |
                          Defender_Conj (attacker_state: "'s") (defender_states: "'s set") |
                          Defender_Stable_Conj (attacker_state: "'s") (defender_states: "'s set")

context Inhabited_Tau_LTS begin


text\<open>\label{specmoves}\<close>

fun spectroscopy_moves :: "('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position \<Rightarrow> energy update option" where 
  delay: 
    "spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q') 
     = (if p' = p \<and> Q \<Zsurj>S Q' then Some id else None)" |

  procrastination: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q')     
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then Some id else None)" |

  observation: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
      = (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then (subtract 1 0 0 0 0 0 0 0) else None)" |

  f_or_early_conj:
    "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
      =(if (Q\<noteq>{} \<and> Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0) else None)" |

  late_inst_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q') 
      = (if p = p' \<and> Q = Q' then Some id else None)" |

  conj_answer: 
    "spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 1 0 0 0 0 0) else None)" |
  
  pos_neg_clause: 
    "spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p' Q') 
      = (if (p = p') then 
          (if {q} \<Zsurj>S Q' then Some min1_6 else None) 
         else (if ({p} \<Zsurj>S Q'\<and> q=p')then Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)) else None))" |

  late_stbl_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') 
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p'')) then Some id else None)" |

  conj_s_answer: 
    "spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0) else None)" |

  empty_stbl_conj_answer: "spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p' Q') 
      = (if Q = {} \<and> Q = Q' \<and> p = p' then (subtract 0 0 0 1 0 0 0 0) else None)" |

  br_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
      = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p'' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q)then Some id else None)" |

  br_answer: 
    "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p'' q) 
      = (if (p = p'' \<and> q \<in> Q) then (subtract 0 1 1 0 0 0 0 0) else None)" |

  br_obsv: 
    "spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p'' Q') 
      = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q') then Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) else None)" |

  br_acct: 
    "spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q') 
      = (if p = p' \<and> Q = Q' then subtract 1 0 0 0 0 0 0 0 else None)" |

  others: "spectroscopy_moves _ _ = None"

fun spectroscopy_defender where
  "spectroscopy_defender (Attacker_Immediate _ _) = False" |
  "spectroscopy_defender (Attacker_Branch _ _) = False" |
  "spectroscopy_defender (Attacker_Clause _ _) = False" |
  "spectroscopy_defender (Attacker_Delayed _ _) = False" |
  "spectroscopy_defender (Defender_Branch _ _ _ _ _) = True" |
  "spectroscopy_defender (Defender_Conj _ _) = True" |
  "spectroscopy_defender (Defender_Stable_Conj _ _) = True"


text \<open>In the following, we check whether our definitions are compatible with those of energy games.
For this purpose we show the monotonicity of energy updates and that they are only decreasing.\<close>

lemma update_monotonicity: 
  fixes g g' e e'
  assumes "(spectroscopy_moves g g') \<noteq> None" and "(e \<le> e')"
  shows "((the (spectroscopy_moves g g')e) \<le> (the (spectroscopy_moves g g')e'))"
using assms proof (cases g)
  case (Attacker_Immediate x11 x12)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g'= (Defender_Conj p' Q'))" using assms
    using spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(45) spectroscopy_moves.simps(50) spectroscopy_moves.simps(56) spectroscopy_moves.simps(60) spectroscopy_moves.simps(71)
    by (metis spectroscopy_moves.simps(70))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (D_Conj) "(\<exists> p' Q'. g'= (Defender_Conj p' Q'))" by auto
  then show ?thesis proof (cases)
    case A_Delayed (*delay*)
    then have "spectroscopy_moves g g' = Some id"
      using Attacker_Immediate assms(1) local.delay
      by (smt (verit, best))
      
    then show ?thesis using assms(2) by simp
  next
    case D_Conj (*early_conj*)
    then have "spectroscopy_moves g g' = (subtract 0 0 0 0 1 0 0 0)" using assms(1)
      by (metis Attacker_Immediate local.f_or_early_conj)
    then show ?thesis using assms(2) gets_smaller
      using mono_subtract option.sel by auto
  qed
next
  case (Attacker_Branch x21 x22) (*br_acct*)
  then have "\<exists>p' Q'. g'= (Attacker_Immediate p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0"
    by (metis Attacker_Branch assms(1) local.br_acct) 
  then show ?thesis using assms(2) mono_subtract by simp
next
  case (Attacker_Clause x31 x32) (*pos_neg_clause *)
  then have "\<exists>p' Q'. g'= (Attacker_Delayed p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = Some min1_6 \<or> spectroscopy_moves g g' = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))" using assms(1)
    by (smt (verit) Attacker_Clause local.pos_neg_clause)
  then show ?thesis using assms(2) mono_min_1_6 mono_min_1_7 mono_subtract
    by (metis (no_types, lifting) comp_apply monoE option.sel) 
next
  case (Attacker_Delayed p Q)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists>p' Q'. g'=(Attacker_Immediate p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Conj p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q')) \<or> (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    using assms spectroscopy_defender.cases spectroscopy_moves.simps(26) spectroscopy_moves.simps(27)
    by (metis spectroscopy_moves.simps(59))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (A_Immediate) "(\<exists>p' Q'. g'=(Attacker_Immediate p' Q'))" | (D_Conj) "(\<exists>p' Q'. g'=(Defender_Conj p' Q'))" | (D_Stable_Conj) "(\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q'))" | (D_Branch) "(\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    by blast
  then show ?thesis proof (cases)
    case A_Delayed (* procrastination *)
    then show ?thesis using assms(2)
      by (metis Attacker_Delayed assms(1) id_apply local.procrastination option.sel)
  next
    case A_Immediate (* observation *)
    then obtain p' Q' where g': "g' = Attacker_Immediate p' Q'" by blast
    have "(if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q') then (subtract 1 0 0 0 0 0 0 0) else None) =
          spectroscopy_moves g g'" 
      unfolding g' Attacker_Delayed by auto
    with assms(1) have "... = subtract 1 0 0 0 0 0 0 0" unfolding g' Attacker_Delayed by metis
    then show ?thesis using assms(2) mono_subtract
      by simp
  next
    case D_Conj (* late_inst_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms(1) assms(2) id_apply local.late_inst_conj option.sel) 
  next
    case D_Stable_Conj (* late_stbl_conj *)
    then show ?thesis
      by (metis (mono_tags, lifting) Attacker_Delayed assms(1) assms(2) id_apply local.late_stbl_conj option.sel) 
  next
    case D_Branch (* br_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms(1) assms(2) id_apply local.br_conj option.sel) 
  qed
next
  case (Defender_Branch x51 x52 x53 x54 x55) (* br_answer or br_obsv *)
  then have "(\<exists>p'' q. g' = (Attacker_Clause p'' q)) \<or> (\<exists>p'' Q'. g'=(Attacker_Branch p'' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(28) spectroscopy_moves.simps(29) spectroscopy_moves.simps(31) spectroscopy_moves.simps(32) spectroscopy_moves.simps(63)
    by (metis spectroscopy_moves.simps(30) spectroscopy_moves.simps(33))
  then have "spectroscopy_moves g g' = (subtract 0 1 1 0 0 0 0 0) \<or> spectroscopy_moves g g' = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
    using Defender_Branch assms(1) local.br_answer local.br_obsv by auto (metis option.discI option.inject)+
  then show ?thesis using assms(2) mono_subtract mono_min_1_6
    using comp_eq_dest_lhs monoD monoE mono_onI monotoneD option.sel by fastforce 
next
  case (Defender_Conj x61 x62) (* conj_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q)" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(33) spectroscopy_moves.simps(34) spectroscopy_moves.simps(35) spectroscopy_moves.simps(36) spectroscopy_moves.simps(38) spectroscopy_moves.simps(69)
    by (metis spectroscopy_moves.simps(37) spectroscopy_moves.simps(39))
  then have "spectroscopy_moves g g' = (subtract 0 0 1 0 0 0 0 0)"
    by (metis Defender_Conj assms(1) local.conj_answer)
  then show ?thesis using assms(2) mono_subtract
    by simp
next
  case (Defender_Stable_Conj x71 x72) (* conj_s_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q) \<or> (\<exists>p' Q'. g' = Defender_Conj p' Q')" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(39) spectroscopy_moves.simps(40) spectroscopy_moves.simps(41) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43)
    by (smt (verit) spectroscopy_defender.elims(1) spectroscopy_moves.simps(40) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43) spectroscopy_moves.simps(55) spectroscopy_moves.simps(75))

  then consider (A_Clause) "\<exists>p' q. g'=(Attacker_Clause p' q)" | (D_Conj) "(\<exists>p' Q'. g' = Defender_Conj p' Q')"
    by blast
  then show ?thesis proof (cases)
    case A_Clause
    then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
      using Defender_Stable_Conj assms(1) local.conj_s_answer
      by meson
    then show ?thesis using assms(2) mono_subtract by simp
  next
    case D_Conj
    then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
      by (metis Defender_Stable_Conj assms(1) local.empty_stbl_conj_answer)
    then show ?thesis using assms(2) mono_subtract by simp
  qed
qed
  
lemma update_gets_smaller: 
  fixes g g' e 
  assumes "(spectroscopy_moves g g') \<noteq> None"
  shows "(the (spectroscopy_moves g g')e)\<le> e"
using assms proof (cases g)
  case (Attacker_Immediate x11 x12)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists> p' Q'. g'= (Defender_Conj p' Q'))" using assms
    using spectroscopy_defender.elims(2) spectroscopy_defender.elims(3) spectroscopy_moves.simps(45) spectroscopy_moves.simps(50) spectroscopy_moves.simps(56) spectroscopy_moves.simps(60) spectroscopy_moves.simps(71)
    by (metis spectroscopy_moves.simps(70))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (D_Conj) "(\<exists> p' Q'. g'= (Defender_Conj p' Q'))" by auto
  then show ?thesis proof (cases)
    case A_Delayed (*delay*)
    then have "spectroscopy_moves g g' = Some id"
      using Attacker_Immediate assms(1) local.delay
      by (smt (verit, del_insts))
    then show ?thesis by simp
  next
    case D_Conj (*early_conj*)
    then have "spectroscopy_moves g g' = (subtract 0 0 0 0 1 0 0 0)" using assms(1)
      by (metis Attacker_Immediate local.f_or_early_conj)
    then show ?thesis using gets_smaller by auto 
  qed
next
  case (Attacker_Branch x21 x22) (*br_acct*)
  then have "\<exists>p' Q'. g'= (Attacker_Immediate p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = subtract 1 0 0 0 0 0 0 0"
    by (metis Attacker_Branch assms(1) local.br_acct) 
  then show ?thesis using gets_smaller by auto 
next
  case (Attacker_Clause x31 x32) (*pos_neg_clause *)
  then have "\<exists>p' Q'. g'= (Attacker_Delayed p' Q')" using assms(1) spectroscopy_moves.simps
    by (metis (no_types, lifting) spectroscopy_defender.elims(2) spectroscopy_defender.elims(3))
  then have "spectroscopy_moves g g' = Some min1_6 \<or> spectroscopy_moves g g' = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))" using assms(1)
    by (smt (verit) Attacker_Clause local.pos_neg_clause) 
  then show ?thesis using gets_smaller
    using dual_order.trans gets_smaller_min_1_6 gets_smaller_min_1_7 option.sel by fastforce 
next
  case (Attacker_Delayed p Q)
  then have "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q')) \<or> (\<exists>p' Q'. g'=(Attacker_Immediate p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Conj p' Q')) \<or> (\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q')) \<or> (\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    using assms spectroscopy_defender.cases spectroscopy_moves.simps(26) spectroscopy_moves.simps(27)
    by (metis spectroscopy_moves.simps(28))

  then consider (A_Delayed) "(\<exists>p' Q'. g'=(Attacker_Delayed p' Q'))" | (A_Immediate) "(\<exists>p' Q'. g'=(Attacker_Immediate p' Q'))" | (D_Conj) "(\<exists>p' Q'. g'=(Defender_Conj p' Q'))" | (D_Stable_Conj) "(\<exists>p' Q'. g'=(Defender_Stable_Conj p' Q'))" | (D_Branch) "(\<exists>p' p'' Q' \<alpha> Q\<alpha> . g'= (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>))"
    by blast
  then show ?thesis proof (cases)
    case A_Delayed (* procrastination *)
    then show ?thesis using assms
      by (metis Attacker_Delayed Orderings.order_eq_iff id_apply local.procrastination option.sel)
  next
    case A_Immediate (* observation *)
    then obtain p' Q' where " g' = Attacker_Immediate p' Q' " by auto
    hence "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') \<noteq> None" 
      using assms(1) Attacker_Delayed by auto
    hence "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') = (subtract 1 0 0 0 0 0 0 0)" 
      unfolding observation by argo 

    hence "spectroscopy_moves g g' = (subtract 1 0 0 0 0 0 0 0)" using Attacker_Delayed \<open>g' = Attacker_Immediate p' Q'\<close> by simp
    then show ?thesis using gets_smaller by simp
  next
    case D_Conj (* late_inst_conj *)
    then show ?thesis
      by (metis Attacker_Delayed assms eq_id_iff local.late_inst_conj option.sel order_refl)
  next
    case D_Stable_Conj (* late_stbl_conj *)
    then show ?thesis using assms
      by (metis (no_types, lifting) Attacker_Delayed Orderings.order_eq_iff id_apply local.late_stbl_conj option.sel)
  next
    case D_Branch (* br_conj *)
    then show ?thesis using assms
      by (metis Attacker_Delayed Orderings.order_eq_iff id_apply local.br_conj option.sel) 
  qed
next
  case (Defender_Branch x51 x52 x53 x54 x55) (* br_answer or br_obsv *)
  then have "(\<exists>p'' q. g' = (Attacker_Clause p'' q)) \<or> (\<exists>p'' Q'. g'=(Attacker_Branch p'' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(28) spectroscopy_moves.simps(29) spectroscopy_moves.simps(31) spectroscopy_moves.simps(32) spectroscopy_moves.simps(63)
    by (metis spectroscopy_moves.simps(30) spectroscopy_moves.simps(33))
  then have "spectroscopy_moves g g' = (subtract 0 1 1 0 0 0 0 0) \<or> spectroscopy_moves g g' = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0))"
    using Defender_Branch assms(1) local.br_answer local.br_obsv by auto (metis option.discI option.inject)+
  then show ?thesis using gets_smaller gets_smaller_min_1_6
    using dual_order.trans by fastforce
next
  case (Defender_Conj x61 x62) (* conj_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q)" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(33) spectroscopy_moves.simps(34) spectroscopy_moves.simps(35) spectroscopy_moves.simps(36) spectroscopy_moves.simps(38) spectroscopy_moves.simps(69)
    by (metis spectroscopy_moves.simps(39) spectroscopy_moves.simps(64))
  then have "spectroscopy_moves g g' = (subtract 0 0 1 0 0 0 0 0)"
    by (metis Defender_Conj assms(1) local.conj_answer)
  then show ?thesis using gets_smaller by auto
next
  case (Defender_Stable_Conj x71 x72) (* conj_s_answer *)
  then have "\<exists>p' q. g'=(Attacker_Clause p' q) \<or> (\<exists>p' Q'. g' = (Defender_Conj p' Q'))" using assms(1)
    using spectroscopy_defender.cases spectroscopy_moves.simps(39) spectroscopy_moves.simps(40) spectroscopy_moves.simps(41) spectroscopy_moves.simps(42) spectroscopy_moves.simps(43)
    by (metis spectroscopy_moves.simps(44))
  then have "spectroscopy_moves g g' = (subtract 0 0 0 1 0 0 0 0)"
    using Defender_Stable_Conj assms(1) local.conj_s_answer 
    by (metis local.empty_stbl_conj_answer)
  then show ?thesis using gets_smaller by auto
qed

interpretation Game: energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" "less_eq" 
proof 
  fix e e' e''::energy
  show "e \<le> e' \<Longrightarrow> e' \<le> e'' \<Longrightarrow> e \<le> e''" unfolding less_eq_energy_def by (smt (z3) energy.case_eq_if order_trans)
  show "e \<le> e" unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show "e \<le> e' \<Longrightarrow> e' \<le> e \<Longrightarrow> e = e'" unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
  show "eneg \<le> e" using eneg_leq .
  show "\<And>g g' e e'. spectroscopy_moves g g' \<noteq> None \<Longrightarrow> e \<le> e' \<Longrightarrow> the (spectroscopy_moves g g') e \<le> the (spectroscopy_moves g g') e'" using update_monotonicity by simp
  show "\<And>g g' e. spectroscopy_moves g g' \<noteq> None \<Longrightarrow> the (spectroscopy_moves g g') e \<le> e" using update_gets_smaller by simp
qed

end

text \<open>Now we are able to define the weak spectroscopy game on an arbitrary (but inhabited) LTS.\<close>
locale full_spec_game =
  Inhabited_Tau_LTS step left right \<tau>
  + energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" "less_eq"
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>_ _\<close> [70, 70, 70] 80) and
      left :: 's and
      right :: 's and
      \<tau> :: 'a

end
