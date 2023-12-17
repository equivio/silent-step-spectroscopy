theory Spectroscopy_Game
  imports Energy_Games Energy LTS
begin

datatype ('s, 'a) spectroscopy_position = 
                          Attacker_Immediate (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Branch (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Clause (attacker_state: "'s") (defender_state: "'s") |
                          Attacker_Delayed (attacker_state: "'s") (defender_states: "'s set") |

                          Defender_Branch (attacker_state: "'s") (attack_action: "'a") (attacker_state_succ: "'s") (defender_states: "'s set") (defender_branch_states: "'s set") |
                          Defender_Conj (attacker_state: "'s") (defender_states: "'s set") |
                          Defender_Stable_Conj (attacker_state: "'s") (defender_states: "'s set")
context LTS_Tau begin

(*define moves in a spectroscopy game dependend on a LTS*)
fun weight_opt :: "('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position \<Rightarrow> energy update option" where 
  delay: 
    "weight_opt (Attacker_Immediate p Q) (Attacker_Delayed p' Q') 
     = (if p' = p \<and> Q \<Zsurj>S Q' then Some id else None)" |

  procrastination: 
    "weight_opt (Attacker_Delayed p Q) (Attacker_Delayed p' Q')     
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then Some id else None)" |

  observation: 
    "weight_opt (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
      = (if (\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>) then (subtract 1 0 0 0 0 0 0 0) else None)" |

  finishing_or_early_conj: 
    "weight_opt (Attacker_Immediate p Q) (Defender_Conj p' Q') 
      = (if Q = {} \<and> Q' = {} then 
          (if (p = p') then Some id else None) 
         else 
          (if (Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0) else None))" |

  late_inst_conj: 
    "weight_opt (Attacker_Delayed p Q) (Defender_Conj p' Q') 
      = (if p = p' \<and> Q = Q' then Some id else None)" |

  conj_answer: 
    "weight_opt (Defender_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 1 0 0 0 0 0) else None)" |
  
  pos_neg_clause: 
    "weight_opt (Attacker_Clause p q) (Attacker_Delayed p' Q') 
      = (if (p = p') then 
          (if {q} \<Zsurj>S Q' then Some min1_6 else None) 
         else (if {p} \<Zsurj>S Q' then Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)) else None))" |

  late_stbl_conj: 
    "weight_opt (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') 
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p'')) then Some id else None)" |

  conj_s_answer: 
    "weight_opt (Defender_Stable_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0) else None)" |

  br_conj: 
    "weight_opt (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
      = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p'' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q)then Some id else None)" |

  br_answer: 
    "weight_opt (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p'' q) 
      = (if (p = p'' \<and> q \<in> Q) then (subtract 0 1 1 0 0 0 0 0) else None)" |

  br_obsv: 
    "weight_opt (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p'' Q') 
      = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q') then Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) else None)" |

  br_acct: 
    "weight_opt (Attacker_Branch p Q) (Attacker_Immediate p' Q') 
      = (if p = p' \<and> Q = Q' then subtract 1 0 0 0 0 0 0 0 else None)" |

  others: "weight_opt _ _ = None"

(*define defender positions in a spectroscopy game dependent on a LTS*)
fun defender where
  "defender (Attacker_Immediate _ _) = False" |
  "defender (Attacker_Branch _ _) = False" |
  "defender (Attacker_Clause _ _) = False" |
  "defender (Attacker_Delayed _ _) = False" |
  "defender (Defender_Branch _ _ _ _ _) = True" |
  "defender (Defender_Conj _ _) = True" |
  "defender (Defender_Stable_Conj _ _) = True"

  
interpretation Game: energy_game "weight_opt" "defender" "eneg" .

end

locale full_spec_game = LTS: LTS_Tau step tau + energy_game "LTS.weight_opt" "LTS.defender" "eneg"
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>_ _\<close> [70, 70, 70] 80) and
      tau :: "'a"
begin

end

end