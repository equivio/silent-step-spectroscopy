section "Energy Games"

theory EnergyGames
  imports Main
begin

section \<open>Energy Games\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"
locale energy_game =
  fixes g0 :: "'gstate" and
        e0 :: "'energy" and
        moves :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool" (infix "\<Zinj>" 70) and
        weight :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update" and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy"
begin

abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>wgt _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (weight g1 g2 = u)"

fun energy_level :: "'gstate list \<Rightarrow> 'energy" where
  "energy_level p = (
    if p = [g0] then 
      e0 
    else 
      (if (p \<noteq> []) then 
        ((weight (last (butlast p)) (last p)) (energy_level (butlast p))) 
       else 
        undefined))"

lemma energy_level_def1:
  shows "energy_level [g0] = e0"
  by simp

lemma energy_level_def2:
  assumes "p' \<noteq> []"
  shows "energy_level (p' @ [gn]) = weight (last p') gn (energy_level p')"
  using assms by simp

lemma energy_level_def3:
  shows "energy_level [] = undefined"
  by simp

lemma energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0" and e0: "e0 \<noteq> undefined" and weight_well_def: "\<And>g1 g2 e1. (weight g1 g2) e1 \<noteq> undefined"
  shows "energy_level p \<noteq> undefined"
using assms proof(induct p rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  thus ?case proof(cases "xs = []")
    case True
    hence "xs @ [x] = [x]" by simp
    with snoc(3) have "x = g0" by simp
    hence "energy_level [x] = e0" by simp
    thus ?thesis unfolding \<open>xs @ [x] = [x]\<close> using e0 by simp
  next
    case False
    then show ?thesis 
      using energy_level_def2 weight_well_def by simp
  qed
qed

subsection \<open>Finite Plays\<close>
inductive finite_play :: "'gstate list \<Rightarrow> bool" where
  "finite_play [g0]" |
  "finite_play (p @ [gn])" if "finite_play p" and "last p \<Zinj> gn" and "(w (last p) gn) (energy_level p) \<noteq> defender_win_level"

lemma finite_play_prefix:
  assumes "finite_play (a @ b)" "a \<noteq> []"
  shows "finite_play a"
using assms proof(induct "a @ b" arbitrary: b rule: finite_play.induct)
  case 1
  thus ?case
    by (metis Nil_is_append_conv butlast_append butlast_snoc finite_play.simps)
next
  case (2 p gn)
  thus ?case
    by (metis butlast_append butlast_snoc finite_play.intros(2))
qed

corollary finite_play_suffix:
  assumes "finite_play (p @ [gn])" and "p \<noteq> []"
  shows "finite_play p"
  using assms finite_play_prefix by fast

lemma finite_play_min_len: "finite_play p \<Longrightarrow> length p \<ge> 1"
  by (metis One_nat_def Suc_le_eq energy_game.finite_play.simps length_greater_0_conv not_Cons_self snoc_eq_iff_butlast)

fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs p = (if length p \<le> 1 then [] else (hd p, hd (tl p)) # pairs (tl p))"

lemma pairs_is_zip:
  shows "pairs p \<equiv> zip (p) (tl p)"
  by (induct p, simp_all, smt (verit, ccfv_threshold) One_nat_def Suc_lessI energy_game.pairs.elims length_0_conv length_Suc_conv length_greater_0_conv linorder_not_less list.collapse list.sel(3) nat_neq_iff zip.simps(1) zip_Cons_Cons)

(* some intuition on this definition*)
lemma "pairs [1,2,3] = [(1,2), (2,3)]" by simp
lemma empty_pair: "pairs [] = []" by simp
lemma single_pair: "pairs [x] = []" by simp
lemma pairs_append_single: "pairs (p @ [gn]) = (if length p \<ge> 1 then (pairs p) @ [(last p, gn)] else [])" 
  by (induct p, simp_all add: not_less_eq_eq)

lemma energy_level_fold_eq:
  assumes "finite_play p"
  shows "energy_level p = fold (\<lambda>(g1, g2) e. (weight g1 g2) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case 1
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (2 p gn)
  have "length p \<ge> 1" using 2(1) finite_play_min_len by auto
  hence pred_eq: "(pairs (p @ [gn])) = (pairs p) @ [(last p, gn)]" using pairs_append_single by metis

  have "fold (\<lambda>(g1, g2). weight g1 g2) [(last p, gn)] = weight (last p) gn" by simp
  hence "fold (\<lambda>(g1, g2). weight g1 g2) ((pairs p) @ [(last p, gn)]) = (weight (last p) gn) \<circ> (fold (\<lambda>(g1, g2). weight g1 g2) (pairs p))" 
    using fold_append by simp
  with 2 show ?case using pred_eq by fastforce
qed

abbreviation "play_stuck p \<equiv>  \<nexists>gn. finite_play (p @ [gn])"

lemma play_stuck_def:
  shows "play_stuck p \<longleftrightarrow> (\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps))"
proof
  assume asm: "\<nexists>gn. finite_play (p @ [gn])"
  show "\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps)" proof(rule ccontr)
    assume "\<not>(\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps))"
    hence "\<exists>gn ps. finite_play (p @ [gn] @ ps)" by (metis append_Cons append_Nil list.exhaust)
    hence "\<exists>gn. finite_play (p @ [gn])" using finite_play_prefix by (metis append.assoc snoc_eq_iff_butlast)
    with asm show "False" by simp
  qed
next
  show "\<nexists>ps. ps \<noteq> [] \<and> finite_play (p @ ps) \<Longrightarrow> play_stuck p" by auto
qed

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

lemma next_turn_well_def:  "is_defender_turn p \<or> is_attacker_turn p" and "is_defender_turn p \<longleftrightarrow> \<not> is_attacker_turn p" by simp+

definition won_by_defender:: "'gstate list \<Rightarrow> bool" where
  "won_by_defender p \<equiv> play_stuck p \<and> is_attacker_turn p"

definition won_by_attacker:: "'gstate list \<Rightarrow> bool" where
  "won_by_attacker p \<equiv> play_stuck p \<and> is_defender_turn p"

abbreviation no_winner:: "'gstate list \<Rightarrow> bool" where
  "no_winner p \<equiv> \<not>play_stuck p"

lemma play_won_cases:
  shows "won_by_defender p \<or> won_by_attacker p \<or> no_winner p"
  unfolding won_by_attacker_def won_by_defender_def by blast

lemma play_won_unique:
  shows"won_by_defender p  \<longleftrightarrow>  \<not> (won_by_attacker p \<or> no_winner p)"
  and  "won_by_attacker p  \<longleftrightarrow>  \<not> (won_by_defender p \<or> no_winner p)"
  and  "no_winner p  \<longleftrightarrow>  \<not> (won_by_defender p \<or> won_by_attacker p)"
  unfolding  won_by_attacker_def won_by_defender_def by auto+

end \<comment> \<open>end of context energy_game\<close>

end
