text \<open>\newpage\<close>
section \<open>Weak Spectroscopy Game\<close>
theory Spectroscopy_Game
  imports Galois_Energy_Games.Natural_Galois_Energy_Game Energy LTS
begin

text \<open>In this theory, we define the weak spectroscopy game as a locale.
This game is an energy game constructed by adding stable and branching conjunctions to a delay bisimulation game that depends on a LTS.
We play the weak spectroscopy game to compare the behaviour of processes and analyze which behavioural equivalences apply.
The moves of a weak spectroscopy game depend on the transitions of the processes and the available energy.
So in other words: If the defender wins the weak spectroscopy game starting with a certain energy, the corresponding behavioural equivalence applies.
\\ Since we added adding stable and branching conjunctions to a delay bisimulation game, we differentiate the positions accordingly.\<close>
datatype ('s, 'a) spectroscopy_position =
  Attacker_Immediate (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Attacker_Delayed (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Attacker_Conjunct (attacker_state: \<open>'s\<close>) (defender_state: \<open>'s\<close>) |
  Attacker_Branch (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  
  Defender_Conj (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Defender_Stable_Conj (attacker_state: \<open>'s\<close>) (defender_states: \<open>'s set\<close>) |
  Defender_Branch (attacker_state: \<open>'s\<close>) (attack_action: \<open>'a\<close>)
                 (attacker_state_succ: \<open>'s\<close>) (defender_states: \<open>'s set\<close>)
                 (defender_branch_states: \<open>'s set\<close>)

context LTS_Tau begin

text\<open>\label{specmoves}\<close>
text\<open>We also define the moves of the weak spectroscopy game. Their names indicate the respective HML formulas they correspond to. This correspondence will be shown in section \ref{deviation:lemma3}. \<close>
fun spectroscopy_moves :: \<open>('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position \<Rightarrow> update option\<close> where
  delay:
    \<open>spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q')
     = (if p' = p \<and> Q \<Zsurj>S Q' then id_up else None)\<close> |

  procrastination:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q')
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then id_up else None)\<close> |

  observation:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q')
      = (if (\<exists>a. p \<mapsto>a a p' \<and> Q \<mapsto>aS a Q')
        then Some [minus_one, zero, zero, zero, zero, zero, zero, zero]
        else None)\<close> |

  f_or_early_conj:
    \<open>spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q')
      = (if (Q\<noteq>{} \<and> Q = Q' \<and> p = p')
        then Some [zero, zero, zero, zero, minus_one, zero, zero, zero]
        else None)\<close> |

  late_inst_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p' Q')
      = (if p = p' \<and> Q = Q' then id_up else None)\<close> |

  conj_answer:
    \<open>spectroscopy_moves (Defender_Conj p Q) (Attacker_Conjunct p' q)
      = (if p = p' \<and> q \<in> Q
        then Some [zero, zero, minus_one, zero, zero, zero, zero, zero]
        else None)\<close> |

  pos_neg_clause:
    \<open>spectroscopy_moves (Attacker_Conjunct p q) (Attacker_Delayed p' Q')
      = (if (p = p') then
          (if {q} \<Zsurj>S Q'
              then Some [min_set {1,6}, zero, zero, zero, zero, zero, zero, zero]
              else None)
           else (if ({p} \<Zsurj>S Q'\<and> q=p')
              then Some [min_set {1,7}, zero, zero, zero, zero, zero, zero, minus_one]
              else None))\<close> |

  late_stbl_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q')
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p''))
          then id_up else None)\<close> |

  conj_s_answer:
    \<open>spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Conjunct p' q)
      = (if p = p' \<and> q \<in> Q
        then Some [zero, zero, zero, minus_one, zero, zero, zero, zero]
        else None)\<close> |

  empty_stbl_conj_answer:
    \<open>spectroscopy_moves (Defender_Stable_Conj p Q) (Defender_Conj p' Q')
      = (if Q = {} \<and> Q = Q' \<and> p = p'
        then Some [zero, zero, zero, minus_one, zero, zero, zero, zero]
        else None)\<close> |

  br_conj:
    \<open>spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>)
      = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>a \<alpha> p'' \<and> Q\<alpha> \<subseteq> Q)
        then id_up
        else None)\<close> |

  br_answer:
    \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Conjunct p'' q)
      = (if (p = p'' \<and> q \<in> Q)
        then Some [zero, minus_one, minus_one, zero, zero, zero, zero, zero]
        else None)\<close> |

  br_obsv:
    \<open>spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p'' Q')
      = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q')
        then Some [min_set {1,6}, minus_one, minus_one, zero, zero, zero, zero, zero]
        else None)\<close> |

  br_acct:
    \<open>spectroscopy_moves (Attacker_Branch p Q) (Attacker_Immediate p' Q')
      = (if p = p' \<and> Q = Q'
        then Some [minus_one, zero, zero, zero, zero, zero, zero, zero]
        else None)\<close> |

  others: \<open>spectroscopy_moves _ _ = None\<close>

fun spectroscopy_attacker where
  \<open>spectroscopy_attacker (Attacker_Immediate _ _) = True\<close> |
  \<open>spectroscopy_attacker (Attacker_Branch _ _) = True\<close> |
  \<open>spectroscopy_attacker (Attacker_Conjunct _ _) = True\<close> |
  \<open>spectroscopy_attacker (Attacker_Delayed _ _) = True\<close> |
  \<open>spectroscopy_attacker (Defender_Branch _ _ _ _ _) = False\<close> |
  \<open>spectroscopy_attacker (Defender_Conj _ _) = False\<close> |
  \<open>spectroscopy_attacker (Defender_Stable_Conj _ _) = False\<close>

abbreviation \<open>attacker_positions \<equiv> {p. spectroscopy_attacker p}\<close>

abbreviation spectroscopy_defender where
  \<open>spectroscopy_defender p \<equiv> \<not>(spectroscopy_attacker p)\<close>

text \<open>All updates appearing in the game are 8-dimensional and valid\<close>

lemma concrete_8dim_updates:
  \<open>length [zero, zero, zero, zero, zero, zero, zero, zero] = 8\<close>
  \<open>length [minus_one, zero, zero, zero, zero, zero, zero, zero] = 8\<close>
  \<open>length [zero, zero, zero, zero, minus_one, zero, zero, zero] = 8\<close>
  \<open>length [zero, zero, minus_one, zero, zero, zero, zero, zero] = 8\<close>
  \<open>length [min_set {1,6}, zero, zero, zero, zero, zero, zero, zero] = 8\<close>
  \<open>length [min_set {1,7}, zero, zero, zero, zero, zero, zero, minus_one] = 8\<close>
  \<open>length [zero, zero, zero, minus_one, zero, zero, zero, zero] = 8\<close>
  \<open>length [zero, minus_one, minus_one, zero, zero, zero, zero, zero] = 8\<close>
  \<open>length [min_set {1,6}, minus_one, minus_one, zero, zero, zero, zero, zero] = 8\<close>
  by simp+

lemma concrete_valid_updates:
  \<open>valid_update [zero, zero, zero, zero, zero, zero, zero, zero]\<close>
  \<open>valid_update [minus_one, zero, zero, zero, zero, zero, zero, zero]\<close>
  \<open>valid_update [zero, zero, zero, zero, minus_one, zero, zero, zero]\<close>
  \<open>valid_update [zero, zero, minus_one, zero, zero, zero, zero, zero]\<close>
  \<open>valid_update [min_set {1,6}, zero, zero, zero, zero, zero, zero, zero]\<close>
  \<open>valid_update [min_set {1,7}, zero, zero, zero, zero, zero, zero, minus_one]\<close>
  \<open>valid_update [zero, zero, zero, minus_one, zero, zero, zero, zero]\<close>
  \<open>valid_update [zero, minus_one, minus_one, zero, zero, zero, zero, zero]\<close>
  \<open>valid_update [min_set {1,6}, minus_one, minus_one, zero, zero, zero, zero, zero]\<close>
  using update_component.distinct
  by (simp add: nth_Cons')+

lemma spectroscopy_game_valid_updates:
  fixes g g'
    assumes \<open>spectroscopy_moves g g' \<noteq> None\<close>
    shows
      \<open>length (the (spectroscopy_moves g g')) = 8 \<and> valid_update (the (spectroscopy_moves g g'))\<close>
using assms
proof (induct g)
  case (Attacker_Immediate p Q)
  thus ?case
  proof (induct g')
    case (Attacker_Delayed)
    thus ?case
      using concrete_8dim_updates(1) concrete_valid_updates(1)
      by (smt (verit, ccfv_threshold) local.delay mem_Collect_eq option.sel subsetD subsetI)
  next
    case (Defender_Conj)
    thus ?case 
      using concrete_8dim_updates(3) concrete_valid_updates(3)
      by (metis local.f_or_early_conj option.sel)
  qed (simp_all)
next
  case (Attacker_Branch p Q)
  thus ?case
    by (cases g', simp_all, metis LTS_Tau.concrete_8dim_updates(2) LTS_Tau.concrete_valid_updates(2) eight_def option.discI)
next
  case (Attacker_Conjunct p q)
  then obtain p' Q' where g'_def: \<open>g' = (Attacker_Delayed p' Q')\<close>
    by (induct, auto)
  show ?case 
    using concrete_8dim_updates(5,6) concrete_valid_updates(5,6) Attacker_Conjunct
    unfolding g'_def
    sorry
next
  case (Attacker_Delayed x1 x2)
  then show ?case sorry
next
  case (Defender_Conj x1 x2)
  then show ?case sorry
next
  case (Defender_Stable_Conj x1 x2)
  then show ?case sorry
next
  case (Defender_Branch x1 x2 x3 x4 x5)
  then show ?case sorry
qed


text \<open>Now, we are able to define the weak spectroscopy game on an arbitrary LTS.\<close>

sublocale weak_spectroscopy_game: bispings_energy_game \<open>attacker_positions\<close> \<open>spectroscopy_moves\<close> \<open>8\<close>
  using bispings_energy_game.intro spectroscopy_game_valid_updates by blast

end

end
