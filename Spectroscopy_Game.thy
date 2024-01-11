theory Spectroscopy_Game
  imports Energy_Games Energy LTS HML_SRBB
begin

text \<open>In this theory the full spectroscopy game is defined (as a locale). 
The definition corresponds to definition 16 in the paper. (Definition 16 is an extension of 
definition 14, which extends definition 12, which is a energy game depending on a LTS. We omit these 
steps and give a definition directly.) 

The full spectroscopy game is an energy game that can be constructed by adding stable and branching 
conjunctions to a delay bisimulation game, which is  depending on a LTS. In the following we 
differentiate the positions accordingly:\<close>

datatype ('s, 'a) spectroscopy_position = 
                          Attacker_Immediate (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Branch (attacker_state: "'s") (defender_states: "'s set") |
                          Attacker_Clause (attacker_state: "'s") (defender_state: "'s") |
                          Attacker_Delayed (attacker_state: "'s") (defender_states: "'s set") |

                          Defender_Branch (attacker_state: "'s") (attack_action: "'a") (attacker_state_succ: "'s") (defender_states: "'s set") (defender_branch_states: "'s set") |
                          Defender_Conj (attacker_state: "'s") (defender_states: "'s set") |
                          Defender_Stable_Conj (attacker_state: "'s") (defender_states: "'s set")

context Inhabited_Tau_LTS begin

text \<open>Now we define the moves in a full spectroscopy game depending on a LTS:\<close>
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

text \<open>The definition of defender positions in a full spectroscopy game is implicitly given by the 
possible positions. Now we make them explicit:\<close>
fun spectroscopy_defender where
  "spectroscopy_defender (Attacker_Immediate _ _) = False" |
  "spectroscopy_defender (Attacker_Branch _ _) = False" |
  "spectroscopy_defender (Attacker_Clause _ _) = False" |
  "spectroscopy_defender (Attacker_Delayed _ _) = False" |
  "spectroscopy_defender (Defender_Branch _ _ _ _ _) = True" |
  "spectroscopy_defender (Defender_Conj _ _) = True" |
  "spectroscopy_defender (Defender_Stable_Conj _ _) = True"

text \<open>To check whether these definitions are compatible with our definition of energy games we proof 
an interpretation:\<close>
interpretation Game: energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg" .

end

text \<open>Now we can write down the full spectroscopy game depending on an arbitrary (but inhabitated) LTS:\<close>
locale full_spec_game =
  Inhabited_Tau_LTS step left right \<tau>
  + energy_game "spectroscopy_moves" "spectroscopy_defender" "eneg"
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>_ _\<close> [70, 70, 70] 80) and
      left :: 's and
      right :: 's and
      \<tau> :: 'a
begin

inductive 
strategy_formula :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb \<Rightarrow> bool"
and strategy_formula_conjunction 
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_conjunction \<Rightarrow> bool"
and strategy_formula_conjunct
  :: "('s, 'a) spectroscopy_position \<Rightarrow> energy \<Rightarrow> ('a, 's)hml_srbb_conjunct \<Rightarrow> bool"
where
  delay:
    "strategy_formula (Attacker_Immediate p Q) e (Internal \<chi>)"
      if "((\<exists>Q'. (spectroscopy_moves (Attacker_Immediate p Q) (Attacker_Delayed p Q') 
        = (Some (id:: energy \<Rightarrow> energy))) \<and> (in_wina e (Attacker_Delayed p Q')) 
          \<and> strategy_formula_conjunction (Attacker_Delayed p Q') e \<chi>))" |
  
  procrastination:
    "strategy_formula_conjunction (Attacker_Delayed p Q) e \<chi>"
      if "(\<exists>p'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Delayed p' Q) 
         = (Some id) \<and> in_wina e (Attacker_Delayed p' Q)
          \<and> strategy_formula_conjunction (Attacker_Delayed p' Q) e \<chi>)"|
  
  observation: 
    "strategy_formula_conjunction (Attacker_Delayed p Q) e (Obs \<alpha> \<phi>)" 
      if "\<exists>p' Q'. spectroscopy_moves (Attacker_Delayed p Q) (Attacker_Immediate p' Q') 
         = (subtract 1 0 0 0 0 0 0 0) \<and> in_wina (e - (E 1 0 0 0 0 0 0 0)) (Attacker_Immediate p' Q')
          \<and> strategy_formula (Attacker_Immediate p' Q') (e - (E 1 0 0 0 0 0 0 0)) \<phi>
          \<and> p \<mapsto>\<alpha> p' \<and> Q \<mapsto>S \<alpha> Q'" |
  
  early_conj:
    "strategy_formula (Attacker_Immediate p Q) e \<phi>" 
      if "(if Q = {} then (\<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
                          = (Some id) \<and> in_wina e (Defender_Conj p' Q') 
                            \<and> strategy_formula (Defender_Conj p' Q') e \<phi>)

           else \<exists>p'. spectroscopy_moves (Attacker_Immediate p Q) (Defender_Conj p' Q') 
                = (subtract 0 0 0 0 1 0 0 0) \<and> in_wina (e - (E 0 0 0 0 1 0 0 0)) (Defender_Conj p' Q')
                  \<and> strategy_formula (Defender_Conj p' Q') (e - (E 0 0 0 0 1 0 0 0)) \<phi>)"|
  
  late_conj:
    "strategy_formula_conjunction (Attacker_Delayed p Q) e \<chi>"
      if "(spectroscopy_moves (Attacker_Delayed p Q) (Defender_Conj p Q) 
         = (Some id) \<and> (in_wina e (Defender_Conj p Q)) 
           \<and> strategy_formula_conjunction (Defender_Conj p Q) e \<chi>)"|
  
  conj:
  "strategy_formula_conjunction (Defender_Conj p Q) e (Conj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|

  imm_conj:
  "strategy_formula (Defender_Conj p Q) e (ImmConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Conj p Q) (Attacker_Clause p q) 
          = (subtract 0 0 1 0 0 0 0 0) \<and> (in_wina (e - (E 0 0 1 0 0 0 0 0)) (Attacker_Clause p q)) 
            \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 1 0 0 0 0 0)) (\<Phi> q)"|
  
  pos:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Pos \<chi>)"
    if "(\<exists>Q'. spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed p Q') 
      = Some min1_6 \<and> in_wina (min1_6 e) (Attacker_Delayed p Q')
        \<and> strategy_formula_conjunction (Attacker_Delayed p Q') (min1_6 e) \<chi>)"|
  
  neg:
  "strategy_formula_conjunct (Attacker_Clause p q) e (Neg \<chi>)" 
    if "(\<exists>P'. spectroscopy_moves (Attacker_Clause p q) (Attacker_Delayed q P') 
      = Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1))
        \<and> in_wina ((min1_7 (e - (E 0 0 0 0 0 0 0 1)))) (Attacker_Delayed q P'))
        \<and> strategy_formula_conjunction (Attacker_Delayed q P') ((min1_7 (e - (E 0 0 0 0 0 0 0 1)))) \<chi>" |
  
  stable:
  "strategy_formula (Attacker_Delayed p Q) e \<chi>" 
    if "spectroscopy_moves (Attacker_Delayed p Q) (Defender_Stable_Conj p Q) 
      = (Some id) \<and> in_wina e (Defender_Stable_Conj p Q) 
        \<and> strategy_formula (Defender_Stable_Conj p Q) e \<chi>"|

  stable_conj:
    "strategy_formula_conjunction (Defender_Stable_Conj p Q) e (StableConj Q \<Phi>)"
      if "\<forall>q \<in> Q. spectroscopy_moves (Defender_Stable_Conj p Q) (Attacker_Clause p q) 
        = (subtract 0 0 0 1 0 0 0 0) \<and> in_wina (e - (E 0 0 0 1 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 0 0 1 0 0 0 0)) (\<Phi> q)"|
  
  branch:
  "strategy_formula (Attacker_Delayed p Q) e \<chi>" 
    if "\<exists>p' Q' \<alpha> Q\<alpha>. spectroscopy_moves (Attacker_Delayed p Q) (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
      = (Some id) \<and> in_wina e (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) 
        \<and> strategy_formula (Defender_Branch p' \<alpha> p'' Q' Q\<alpha>) e \<chi>"|

  branch_conj:
  "strategy_formula_conjunction (Defender_Branch p \<alpha> p' Q Qa) e (BranchConj \<alpha> \<psi> Q \<Phi>)"
    if "\<exists>Q'. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Branch p' Q') 
          = Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) 
            \<and> spectroscopy_moves (Attacker_Branch p' Q') (Attacker_Immediate p' Q')
            = subtract 1 0 0 0 0 0 0 0 
            \<and> (in_wina ((min1_6 (e - E 0 1 1 0 0 0 0 0)) - (E 1 0 0 0 0 0 0 0)) 
                  (Attacker_Immediate p' Q'))
            \<and> strategy_formula (Attacker_Immediate p' Q') e' \<psi>"
        
        "\<forall>q \<in> Q. spectroscopy_moves (Defender_Branch p \<alpha> p' Q Q\<alpha>) (Attacker_Clause p q) 
          = (subtract 0 1 1 0 0 0 0 0)
          \<and> in_wina (e - (E 0 1 1 0 0 0 0 0)) (Attacker_Clause p q)
          \<and> strategy_formula_conjunct (Attacker_Clause p q) (e - (E 0 1 1 0 0 0 0 0)) (\<Phi> q)"

end

end