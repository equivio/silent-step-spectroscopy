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
                  
context Inhabited_Tau_LTS begin

(*define moves in a spectroscopy game dependend on a LTS*)
fun spectroscopy_moves :: "('s, 'a) spectroscopy_position \<Rightarrow> ('s, 'a) spectroscopy_position \<Rightarrow> energy update option" where 
  delay: 
    "spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p' Q') 
     = (if p' = p \<and> Q \<Zsurj>S Q' then Some id else None)" |

  procrastination: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q')     
      = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then Some id else None)" |

  observation: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
      = (if (\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>) then (subtract 1 0 0 0 0 0 0 0) else None)" |

  finishing_or_early_conj: 
    "spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
      = (if Q = {} \<and> Q' = {} then 
          (if (p = p') then Some id else None) 
         else 
          (if (Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0) else None))" |

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
         else (if {p} \<Zsurj>S Q' then Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)) else None))" |

  late_stbl_conj: 
    "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p' Q') 
      = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p'')) then Some id else None)" |

  conj_s_answer: 
    "spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p' q) 
      = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0) else None)" |

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

(*define defender positions in a spectroscopy game dependent on a LTS*)
fun spectroscopy_defender where
  "spectroscopy_defender (Attacker_Immediate _ _) = False" |
  "spectroscopy_defender (Attacker_Branch _ _) = False" |
  "spectroscopy_defender (Attacker_Clause _ _) = False" |
  "spectroscopy_defender (Attacker_Delayed _ _) = False" |
  "spectroscopy_defender (Defender_Branch _ _ _ _ _) = True" |
  "spectroscopy_defender (Defender_Conj _ _) = True" |
  "spectroscopy_defender (Defender_Stable_Conj _ _) = True"

sublocale energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" .

end

end
