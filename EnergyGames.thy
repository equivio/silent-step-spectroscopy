section "Energy Games"

theory EnergyGames
  imports Main
begin

section \<open>Energy Games\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"
type_synonym 'gstate strategy = "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool"
type_synonym 'gstate fplay = "'gstate list"

locale energy_game =
  fixes weight_opt :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> 'energy update option" and
        defender :: "'gstate \<Rightarrow> bool" ("Gd") and 
        defender_win_level :: "'energy"
begin


abbreviation attacker :: "'gstate \<Rightarrow> bool" ("Ga") where "Ga p \<equiv> \<not> Gd p" 

abbreviation moves :: "'gstate \<Rightarrow> 'gstate \<Rightarrow> bool" (infix "\<Zinj>" 70) where "g1 \<Zinj> g2 \<equiv> weight_opt g1 g2 \<noteq> None"

abbreviation weighted_move :: "'gstate \<Rightarrow> 'energy update \<Rightarrow> 'gstate \<Rightarrow>  bool" ("_ \<Zinj>wgt _ _" [60,60,60] 70) where
  "weighted_move g1 u g2 \<equiv> g1 \<Zinj> g2 \<and> (the (weight_opt g1 g2) = u)"

abbreviation "weight g1 g2 \<equiv> the (weight_opt g1 g2)"

fun energy_level :: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> 'energy" where
  "energy_level g0 e0 p = (
    if p = [g0] then 
      e0 
    else 
      (if (p \<noteq> []) then 
        ((weight (last (butlast p)) (last p)) (energy_level g0 e0 (butlast p))) 
       else 
        undefined))"

lemma %invisible energy_level_def1:
  shows "energy_level g0 e0 [g0] = e0"
  by simp

lemma %invisible energy_level_def2:
  assumes "p' \<noteq> []"
  shows "energy_level g0 e0 (p' @ [gn]) = weight (last p') gn (energy_level g0 e0 p')"
  using assms by simp

lemma %invisible energy_level_def3:
  shows "energy_level g0 e0 [] = undefined"
  by simp

lemma %invisible energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0" and e0: "e0 \<noteq> undefined" and weight_well_def: "\<And>g1 g2 e1. (weight g1 g2) e1 \<noteq> undefined"
  shows "energy_level g0 e0 p \<noteq> undefined"
using assms proof(induct p rule: rev_induct)
  case Nil
  thus ?case by simp
next
  case (snoc x xs)
  thus ?case proof(cases "xs = []")
    case True
    hence "xs @ [x] = [x]" by simp
    with snoc(3) have "x = g0" by simp
    hence "energy_level g0 e0 [x] = e0" by simp
    thus ?thesis unfolding \<open>xs @ [x] = [x]\<close> using e0 by simp
  next
    case False
    then show ?thesis 
      using energy_level_def2 weight_well_def by simp
  qed
qed

subsection \<open>Finite Plays\<close>
inductive finite_play :: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  base: "finite_play g0 e0 [g0]" |
  suc: "finite_play g0 e0 (p @ [gn])" if "finite_play g0 e0 p" and "last p \<Zinj> gn" and "(weight (last p) gn) (energy_level g0 e0 p) \<noteq> defender_win_level"

lemma finite_play_prefix:
  assumes "finite_play g0 e0 (a @ b)" "a \<noteq> []"
  shows "finite_play g0 e0 a"
using assms proof(induct "a @ b" arbitrary: b rule: finite_play.induct)
  case base
  thus ?case
    by (metis Nil_is_append_conv butlast_append butlast_snoc finite_play.simps)
next
  case (suc p gn)
  thus ?case
    by (metis butlast_append butlast_snoc finite_play.intros(2))
qed

corollary finite_play_suffix:
  assumes "finite_play g0 e0 (p @ [gn])" and "p \<noteq> []"
  shows "finite_play g0 e0 p"
  using assms finite_play_prefix by fast

lemma finite_play_min_len: "finite_play g0 e0 p \<Longrightarrow> length p \<ge> 1"
  by (metis (full_types) One_nat_def finite_play.simps le_zero_eq length_0_conv length_Cons list.size(3) not_less_eq_eq snoc_eq_iff_butlast)

fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs p = (if length p \<le> 1 then [] else (hd p, hd (tl p)) # pairs (tl p))"

lemma pairs_is_zip:
  shows "pairs p \<equiv> zip (p) (tl p)"
  by (induct p, simp_all, smt (verit, ccfv_threshold) One_nat_def Suc_lessI energy_game.pairs.elims length_0_conv length_Suc_conv length_greater_0_conv linorder_not_less list.collapse list.sel(3) nat_neq_iff zip.simps(1) zip_Cons_Cons)

(* some intuition on this definition*)
lemma %invisible "pairs [1,2,3] = [(1,2), (2,3)]" by simp
lemma %invisible empty_pair: "pairs [] = []" by simp
lemma %invisible single_pair: "pairs [x] = []" by simp
lemma %invisible pairs_append_single: "pairs (p @ [gn]) = (if length p \<ge> 1 then (pairs p) @ [(last p, gn)] else [])" 
  by (induct p, simp_all add: not_less_eq_eq)

lemma energy_level_fold_eq:
  assumes "finite_play g0 e0 p"
  shows "energy_level g0 e0 p = fold (\<lambda>(g1, g2) e. (weight g1 g2) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case base
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (suc g0 e0 p gn)
  have "length p \<ge> 1" using suc(1) finite_play_min_len by auto
  hence pred_eq: "(pairs (p @ [gn])) = (pairs p) @ [(last p, gn)]" using pairs_append_single by metis

  have "fold (\<lambda>(g1, g2). weight g1 g2) [(last p, gn)] = weight (last p) gn" by simp
  hence "fold (\<lambda>(g1, g2). weight g1 g2) ((pairs p) @ [(last p, gn)]) = (weight (last p) gn) \<circ> (fold (\<lambda>(g1, g2). weight g1 g2) (pairs p))" 
    using fold_append by simp
  with suc show ?case using pred_eq by fastforce
qed

lemma finite_play_never_defender_win_level:
  assumes "finite_play g0 e0 p" and "e0 \<noteq> defender_win_level"
shows "energy_level g0 e0 p \<noteq> defender_win_level"
  using assms proof(induct rule: finite_play.induct)
  case base
  thus ?case by simp
next
  case (suc g0 e0 p gn)
  from suc.hyps(1) have "p \<noteq> []" using finite_play.cases by blast
  hence "energy_level g0 e0 (p @ [gn]) = weight (last p) gn (energy_level g0 e0 p)" by simp
  thus ?case using suc.hyps(4) by auto
qed

subsection \<open>Winning\<close>
abbreviation "play_stuck g0 e0 p \<equiv>  \<nexists>gn. finite_play g0 e0 (p @ [gn])"

lemma play_stuck_def:
  shows "play_stuck g0 e0 p \<longleftrightarrow> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 e0 (p @ ps))"
proof
  assume asm: "\<nexists>gn. finite_play g0 e0 (p @ [gn])"
  show "\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 e0 (p @ ps)" proof(rule ccontr)
    assume "\<not>(\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 e0 (p @ ps))"
    hence "\<exists>gn ps. finite_play g0 e0 (p @ [gn] @ ps)" by (metis append_Cons append_Nil list.exhaust)
    hence "\<exists>gn. finite_play g0 e0 (p @ [gn])" using finite_play_prefix by (metis append.assoc snoc_eq_iff_butlast)
    with asm show "False" by simp
  qed
next
  show "\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 e0 (p @ ps) \<Longrightarrow> play_stuck g0 e0 p" by auto
qed

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

definition won_by_defender where
  "won_by_defender g0 e0 p \<equiv> (play_stuck g0 e0 p \<and> is_attacker_turn p)"

definition won_by_attacker where
  "won_by_attacker g0 e0 p \<equiv> (play_stuck g0 e0 p \<and> is_defender_turn p)"

abbreviation not_won where
  "not_won g0 e0 p \<equiv> \<not>play_stuck g0 e0 p"

lemma play_won_cases:
  shows "won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p \<or> not_won g0 e0 p"
  unfolding won_by_attacker_def won_by_defender_def by blast

lemma play_won_unique:
  shows"won_by_defender g0 e0 p  \<longleftrightarrow>  \<not> (won_by_attacker g0 e0 p \<or> not_won g0 e0 p)"
  and  "won_by_attacker g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> not_won g0 e0 p)"
  and  "not_won g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p)"
  using  won_by_attacker_def won_by_defender_def by blast+

inductive Win_a where 
  "Win_a ga e" if "Ga ga" and "ga \<Zinj>wgt u g'" and "Win_a g' (u e)" |
  "Win_a gd e" if "Gd gd" and "\<And>u g'. gd \<Zinj>wgt u g' \<Longrightarrow> Win_a g' (u e)"

end (*End of context energy_game*)
end
