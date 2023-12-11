theory Full_Spectroscopy_Game
  imports Energy_Games Energy LTS
begin

(* TODO: ask Ben for better names *)
datatype ('s, 'a) position = attacker_basic (p_p: "'s") (Q_Q: "'s set") |
                          attacker_branch (p_p: "'s") (Q_Q: "'s set") |
                          attacker_clause (p_p: "'s") (q_q: "'s") |
                          attacker_delay (p_p: "'s") (Q_Q: "'s set") |

                          defender_branch (p_p: "'s") (\<alpha>_\<alpha>: "'a") (p'_p': "'s") (Q_Q: "'s set") (Q\<alpha>_Q\<alpha>: "'s set") |
                          defender_conj (p_p: "'s") (Q_Q: "'s set") |
                          defender_s_conj (p_p: "'s") (Q_Q: "'s set")
context LTS_Tau begin

fun weight_opt :: "('s, 'a) position \<Rightarrow> ('s, 'a) position \<Rightarrow> energy update option" where 
  delay: "weight_opt (attacker_basic p Q) (attacker_delay p' Q') = (if p' = p \<and> Q \<Zsurj>S Q' then Some id else None)" |
  procrastination: "weight_opt (attacker_delay p Q) (attacker_delay p' Q') = (if (Q' = Q \<and> p \<noteq> p' \<and> p \<mapsto> \<tau> p') then Some id else None)" |
  observation: "weight_opt (attacker_delay p Q) (attacker_basic p' Q') = (if (\<exists>a. p \<mapsto> a p' \<and> Q \<mapsto>S a Q' \<and> a \<noteq> \<tau>) then (subtract 1 0 0 0 0 0 0 0) else None)" |
  finishing_or_early_conj: "weight_opt (attacker_basic p Q) (defender_conj p' Q') = 
    (if Q = {} \<and> Q' = {} then (if (p = p') then Some id else None) else (if (Q = Q' \<and> p = p') then (subtract 0 0 0 0 1 0 0 0) else None))" |
  late_inst_conj: "weight_opt (attacker_delay p Q) (defender_conj p' Q') = (if p = p' \<and> Q = Q' then Some id else None)" |
  conj_awns: "weight_opt (defender_conj p Q) (attacker_clause p' q) = (if p = p' \<and> q \<in> Q then (subtract 0 0 1 0 0 0 0 0) else None)" |
  pos_neg_clause: "weight_opt (attacker_clause p q) (attacker_delay p' Q') = 
    (if (p = p') then (if {q} \<Zsurj>S Q' then Some min1_6 else None) else (if {p} \<Zsurj>S Q' then Some (min1_7 \<circ> (\<lambda>x. x- E 0 0 0 0 0 0 0 1)) else None))" |
  late_stbl_conj: "weight_opt (attacker_delay p Q) (defender_s_conj p' Q') = (if (p = p' \<and> Q' = { q \<in> Q. (\<nexists>q'. q \<mapsto>\<tau> q')} \<and> (\<nexists>p''. p \<mapsto>\<tau> p'')) then Some id else None)" |
  conj_s_awns: "weight_opt (defender_s_conj p Q) (attacker_clause p' q) = (if p = p' \<and> q \<in> Q then (subtract 0 0 0 1 0 0 0 0) else None)" |
  br_conj: "weight_opt (attacker_delay p Q) (defender_branch p' \<alpha> p'' Q' Q\<alpha>) = (if (p = p' \<and> Q' = Q - Q\<alpha> \<and> p \<mapsto>\<alpha> p'' \<and> Q\<alpha> \<noteq> {} \<and> Q\<alpha> \<subseteq> Q)then Some id else None)" |
  br_awns: "weight_opt (defender_branch p \<alpha> p' Q Q\<alpha>) (attacker_clause p'' q) = (if (p = p'' \<and> q \<in> Q) then (subtract 0 1 1 0 0 0 0 0) else None)" |
  br_obsv: "weight_opt (defender_branch p \<alpha> p' Q Q\<alpha>) (attacker_branch p'' Q') = (if (p' = p'' \<and> Q\<alpha> \<mapsto>aS \<alpha> Q') then Some (min1_6 \<circ> (\<lambda>x. x- E 0 1 1 0 0 0 0 0)) else None)" |
  br_acct: "weight_opt (attacker_branch p Q) (attacker_basic p' Q') = (if p = p' \<and> Q = Q' then subtract 1 0 0 0 0 0 0 0 else None)" |
  others: "weight_opt _ _ = None"

fun defender where
  "defender (attacker_basic _ _) = False" |
  "defender (attacker_branch _ _) = False" |
  "defender (attacker_clause _ _) = False" |
  "defender (attacker_delay _ _) = False" |
  "defender (defender_branch _ _ _ _ _) = True" |
  "defender (defender_conj _ _) = True" |
  "defender (defender_s_conj _ _) = True"

  
interpretation Game: energy_game "weight_opt" "defender" "eneg" .

end

locale full_spec_game = LTS: LTS_Tau step tau + energy_game "LTS.weight_opt" "LTS.defender" "eneg"
  for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto>_ _\<close> [70, 70, 70] 80) and
      tau :: "'a"
begin

end

end