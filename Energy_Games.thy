section "Energy Games"

theory Energy_Games
  imports Main Misc
begin

section \<open>Energy Games\<close>

type_synonym 'energy update = "'energy \<Rightarrow> 'energy"
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

fun energy_level :: "'gstate \<Rightarrow> 'energy \<Rightarrow>'gstate fplay \<Rightarrow> 'energy" where
  "energy_level g0 e0 p = (
    if p = [g0] then 
      e0 
    else 
      (if (p \<noteq> [] \<and> ((weight_opt (last (butlast p))(last p)) \<noteq> None)) then 
        ((weight (last (butlast p)) (last p)) (energy_level g0 e0 (butlast p))) 
       else 
        undefined))"

lemma %invisible energy_level_def1:
  shows "energy_level g0 e0 [g0] = e0"
  by simp

lemma %invisible energy_level_def2:
  assumes "p' \<noteq> []" and "energy_level g0 e0 p' \<noteq> undefined" and "weight_opt (last p') gn \<noteq> None"  
  shows "energy_level g0 e0 (p' @ [gn]) = weight (last p') gn (energy_level g0 e0 p')"
  using assms by simp

lemma %invisible energy_level_def3:
  shows "energy_level g0 e0 [] = undefined"
  by simp

lemma %invisible energy_level_def4:
  assumes "p \<noteq> []" "hd p = g0" and e0: "e0 \<noteq> undefined" and weight_well_def: "\<And>g1 g2 e1.((weight_opt g1 g2)\<noteq> None \<and> (weight g1 g2) e1 \<noteq> undefined)"
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
inductive finite_play :: "'gstate \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "finite_play g0 [g0]" |
  "finite_play g0 (p @ [gn])" if "finite_play g0 p" and "last p \<Zinj> gn"

lemma finite_play_prefix:
  assumes "finite_play g0 (a @ b)" "a \<noteq> []"
  shows "finite_play g0 a"
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
  assumes "finite_play g0 (p @ [gn])" and "p \<noteq> []"
  shows "finite_play g0 p"
  using assms finite_play_prefix by fast

lemma finite_play_suffix2:
  assumes "finite_play g0 ([g0] @ ([g1]@p))"
  shows "finite_play g1 ([g1]@p)"
using assms proof (induct p rule: rev_induct)
  case Nil
  then show ?case by (simp add: finite_play.intros(1)) 
next
  case (snoc x xs)
  then show ?case
    by (smt (verit) Cons_eq_appendI append_assoc append_same_eq distinct_adj_Cons distinct_adj_Cons_Cons eq_Nil_appendI finite_play.simps last.simps last_appendR)
qed

lemma finite_play_check_gen:
   assumes "x \<noteq> p1" and
           "p = p1 # [pn]"
   shows "\<not>finite_play x (p @ [gn])"
proof (rule notI)
  assume A1: "finite_play x (p @ [gn])"
  from assms A1 have A2: "finite_play x p"
    using finite_play_prefix by blast 
  from assms(2) A2 have A3: "finite_play x ( p1 # [pn])"
    by meson
  from A3 have A4: "finite_play x ([p1] @ [pn])"
    by simp
  from A4 have A5: "finite_play x [p1]"
    using finite_play_prefix by blast 
  have A6: "\<not>finite_play x [p1]"
    by (metis assms(1) butlast.simps(2) finite_play.simps list.distinct(1) snoc_eq_iff_butlast)
  show "False"
    using A5 A6 by auto 
qed

lemma finite_play_min_len: "finite_play g0 p \<Longrightarrow> length p \<ge> 1"
  by (metis One_nat_def Suc_le_eq energy_game.finite_play.simps length_greater_0_conv not_Cons_self snoc_eq_iff_butlast)

lemma finite_play_is_path:
  fixes p
  assumes "finite_play g0 p"
  shows "((p = ((a @ [g]) @ b)) \<and> a \<noteq>[]) \<longrightarrow> ((last a) \<Zinj> g)"
  by (metis assms butlast.simps(2) finite_play.simps finite_play_prefix snoc_eq_iff_butlast)

thm finite_play.induct

lemma energy_level_fold_eq:
  assumes "finite_play g0 p"
  shows "energy_level g0 e0 p = fold (\<lambda>(g1, g2) e. (weight g1 g2) e) (pairs p) e0"
using assms proof (induct "p" rule: finite_play.induct)
  case 1
  thus ?case unfolding single_pair[of "g0"] fold_Nil by simp
next
  case (2 g0 p gn)
  have "length p \<ge> 1" using 2(1) finite_play_min_len by auto
  hence pred_eq: "(pairs (p @ [gn])) = (pairs p) @ [(last p, gn)]" using pairs_append_single by metis

  have "fold (\<lambda>(g1, g2). weight g1 g2) [(last p, gn)] = weight (last p) gn" by simp
  hence "fold (\<lambda>(g1, g2). weight g1 g2) ((pairs p) @ [(last p, gn)]) = (weight (last p) gn) \<circ> (fold (\<lambda>(g1, g2). weight g1 g2) (pairs p))" 
    using fold_append by simp
  with 2 show ?case using pred_eq by fastforce
qed

(*
lemma %invisible energy_level_def5:
  assumes "energy_level g0 e0 ([g0]@([g1]@p)) \<noteq> undefined " and "weigth_opt g0 g1 \<noteq> None" and "((weight g0 g1)e0) \<noteq> undefined" and "finite_play g0 ([g0]@([g1]@p))" 
  shows "energy_level g0 e0 ([g0]@([g1]@p))= energy_level g1 ((weight g0 g1)e0) ([g1]@p)"
  using assms proof (induct p rule: rev_induct)
  case Nil
  then show ?case by fastforce
next
  case (snoc x xs)
  from snoc(5) have F: "finite_play g0 ([g0] @ [g1] @ xs)" using finite_play_suffix by auto
  from snoc(2) have "energy_level g0 e0 ([g0] @ [g1] @ xs @ [x]) =  ((weight (last ([g0] @ [g1] @ xs)) x) (energy_level g0 e0 ([g0] @ [g1] @ xs))) "
    by (smt (verit) Nil_is_append_conv butlast_append butlast_snoc energy_game.energy_level.simps last.simps last_append list.distinct(1) self_append_conv)
  hence "energy_level g0 e0 ([g0] @ [g1] @ xs) \<noteq> undefined" using snoc(2) sorry
  from this snoc(3) snoc(4) F have "energy_level g0 e0 ([g0] @ [g1] @ xs) = energy_level g1 (weight g0 g1 e0) ([g1] @ xs)" using snoc(1) by simp
  
  from snoc(2) have "energy_level g0 e0 ([g0] @ [g1] @ xs @ [x]) =  ((weight (last ([g0] @ [g1] @ xs)) x) (energy_level g0 e0 ([g0] @ [g1] @ xs))) "
    by (smt (verit) Nil_is_append_conv butlast_append butlast_snoc energy_game.energy_level.simps last.simps last_append list.distinct(1) self_append_conv)
  have "energy_level g1 (weight g0 g1 e0) ([g1] @ xs @ [x]) =  ((weight (last ([g1] @ xs)) x) (energy_level g1 (weight g0 g1 e0) ([g1] @ xs))) "
    by (smt (verit) Nil_is_append_conv butlast_append butlast_snoc energy_game.energy_level.simps last.simps last_append list.distinct(1) self_append_conv snoc.prems(1))
  have " ((weight (last ([g0] @ [g1] @ xs)) x) (energy_level g0 e0 ([g0] @ [g1] @ xs))) = ((weight (last ([g1] @ xs)) x) (energy_level g1 (weight g0 g1 e0) ([g1] @ xs)))" sorry
  then show ?case oops
qed
*)

subsection \<open>Winning\<close>
abbreviation "play_stuck g0 p \<equiv> (finite_play g0 p) \<and> (\<nexists>gn. finite_play g0 (p @ [gn]))"

lemma play_stuck_def:
  shows "play_stuck g0 p \<longleftrightarrow> ((finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))"
proof
  assume asm: "(finite_play g0 p) \<and> (\<nexists>gn. finite_play g0 (p @ [gn]))"
  show "((finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))" 
  proof(rule ccontr)
    assume "\<not>( (finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)))"
    hence "\<exists>gn ps. finite_play g0 (p @ [gn] @ ps)"
      by (metis Cons_eq_appendI append_self_conv2 asm list.exhaust_sel)
    hence "\<exists>gn. finite_play g0 (p @ [gn])" using finite_play_prefix by (metis append.assoc snoc_eq_iff_butlast)
    with asm show "False" by simp
  qed
next
  show "(finite_play g0 p) \<and> (\<nexists>ps. ps \<noteq> [] \<and> finite_play g0 (p @ ps)) \<Longrightarrow> play_stuck g0 p" using finite_play_suffix
    by blast
qed

abbreviation "is_defender_turn p \<equiv> Gd (last p)"
abbreviation "is_attacker_turn p \<equiv> Ga (last p)"

definition won_by_defender:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "won_by_defender g0 e0 p \<equiv> (play_stuck g0 p \<and> is_attacker_turn p) \<or> (energy_level g0 e0 p = defender_win_level)"

definition won_by_attacker:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "won_by_attacker g0 e0 p \<equiv> play_stuck g0 p \<and> is_defender_turn p \<and> (energy_level g0 e0 p \<noteq> defender_win_level)"

abbreviation no_winner:: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "no_winner g0 e0 p \<equiv> \<not>play_stuck g0 p \<and> (energy_level g0 e0 p \<noteq> defender_win_level)"

lemma play_won_cases:
  shows "won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p \<or> no_winner g0 e0 p"
  unfolding won_by_attacker_def won_by_defender_def by blast

lemma play_won_unique:
  shows"won_by_defender g0 e0 p  \<longleftrightarrow>  \<not> (won_by_attacker g0 e0 p \<or> no_winner g0 e0 p)"
  and  "won_by_attacker g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> no_winner g0 e0 p)"
  and  "no_winner g0 e0 p  \<longleftrightarrow>  \<not> (won_by_defender g0 e0 p \<or> won_by_attacker g0 e0 p)"
  using  won_by_attacker_def won_by_defender_def by blast+

(* TODO *)
lemma  won_by_defender_suffix:
  assumes "won_by_defender g0 e0 ([g0]@([g1]@p))" 
  shows "won_by_defender g1 ((weight g0 g1)e0) ([g1]@p)"  
  using assms proof(cases "energy_level g0 e0 ([g0]@([g1]@p)) = defender_win_level")
  case True
  have "energy_level g1 ((weight g0 g1)e0) ([g1]@p) = energy_level g0 e0 ([g0]@([g1]@p))" sorry
  then show ?thesis oops
next
  case False
  hence X: "(play_stuck g0 ([g0]@([g1]@p))) \<and> (is_attacker_turn ([g0]@([g1]@p)))" using assms
    by (simp add: won_by_defender_def)
  hence "(finite_play g0 ([g0]@([g1]@p))) \<and> (\<nexists>gn. finite_play g0 (([g0]@([g1]@p)) @ [gn]))" by simp 
  hence "(finite_play g1 ([g1]@p)) \<and> (\<nexists>gn. finite_play g1 ((([g1]@p)) @ [gn]))" using finite_play_suffix2
    by (metis append.assoc append_Cons append_Nil energy_game.finite_play.intros(2) energy_game.finite_play_is_path last_ConsR list.distinct(1))
  hence "(play_stuck g1 ([g1]@p)) \<and> (is_attacker_turn ([g1]@p))" using X by simp 
  then show ?thesis by (simp add: won_by_defender_def) 
qed

(* TODO *)
lemma  won_by_defender_add_prefix:
  assumes "finite_play g0 ([g0]@([g1]@p))" and "won_by_defender g1 ((weight g0 g1)e0) ([g1]@p)"
  shows "won_by_defender g0 e0 ([g0]@([g1]@p))" 
  using assms proof(cases "energy_level g1 ((weight g0 g1)e0) ([g1]@p) = defender_win_level")
  case True
  have "energy_level g1 ((weight g0 g1)e0) ([g1]@p) = energy_level g0 e0 ([g0]@([g1]@p))" sorry
  then show ?thesis oops
next
  case False
  hence X: "(play_stuck g1 ([g1]@p)) \<and> (is_attacker_turn ([g1]@p))" using assms
    by (simp add: won_by_defender_def)
  hence "(\<nexists>gn. finite_play g1 ((([g1]@p)) @ [gn]))" by simp 
  hence "(\<nexists>gn. finite_play g0 (([g0]@([g1]@p)) @ [gn]))" by (metis append_assoc finite_play_suffix2) 
  hence "(play_stuck g0 ([g0]@([g1]@p))) \<and> (is_attacker_turn ([g0]@([g1]@p)))" using X assms by auto
  then show ?thesis by (simp add: won_by_defender_def) 
qed

subsection \<open>Winning Budgets\<close>

inductive in_wina:: "'energy \<Rightarrow> 'gstate \<Rightarrow> bool " where
 "in_wina e g" if "(Gd g) \<and> (\<forall>g'. \<not>(g \<Zinj> g')) \<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Ga g) \<and> (\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g')))\<and> (e \<noteq> defender_win_level)" |
 "in_wina e g" if "(Gd g) \<and> (\<forall>g'. ((g \<Zinj> g') \<longrightarrow> (in_wina ((weight g g') e) g'))) \<and> (e \<noteq> defender_win_level)" 

lemma defender_win_level_not_in_wina:
  shows "\<forall>g. \<not>in_wina defender_win_level g"
  by (metis in_wina.cases)

lemma attacker_wins_last_wina_notempty:
  assumes "won_by_attacker g0 e0 p"
  shows "\<exists>e. in_wina e (last p)"
  using assms won_by_attacker_def finite_play.intros(2) in_wina.intros(1) by meson

lemma in_wina_Ga:
  assumes "in_wina e g" and "Ga g" 
  shows "\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g'))"
  using assms(1) assms(2) in_wina.simps by blast

inductive consistent_with_wina :: "'gstate \<Rightarrow> 'energy \<Rightarrow> 'gstate fplay \<Rightarrow> bool" where
  "consistent_with_wina g0 e0 [g0]" if "in_wina e0 g0" | 
  "consistent_with_wina g0 e0 ([g0]@([g1]@p))" if "(finite_play g0 ([g0]@([g1]@p))) \<and> (in_wina e0 g0) \<and> (consistent_with_wina g1 ((weight g0 g1)e0) ([g1]@p))"

lemma 
  assumes "consistent_with_wina g0 e0 p"
  shows "\<not>(won_by_defender g0 e0 p)"
proof - 
  from assms have "finite_play g0 p"
    using consistent_with_wina.simps finite_play.simps by blast 
  thus "\<not>(won_by_defender g0 e0 p)" using assms proof (induct "p" arbitrary: g0 e0 rule: List.list.induct)
    case Nil
    thus ?case using finite_play.cases by auto 
  next
    case (Cons x1 x2) 
    thus ?case proof(cases "x2 = []")
      case True
      assume X1:"(\<And>g0 e0. finite_play g0 x2 \<Longrightarrow> consistent_with_wina g0 e0 x2 \<Longrightarrow> \<not> won_by_defender g0 e0 x2)" 
                and X2: "x2 = []" and X3: "finite_play g0 (x1 # x2)"
                and X4: "consistent_with_wina g0 e0 (x1 # x2)" 
      hence "(x1 # x2) = [g0]"
        using consistent_with_wina.cases list.sel(1) by fastforce   
      thus ?thesis using X1 X2 X3 X4
        by (metis consistent_with_wina.cases defender_win_level_not_in_wina energy_game.energy_level_def1 energy_game.finite_play.intros(2) energy_game.won_by_defender_def in_wina_Ga last_ConsL)
    next
      case False
      hence "\<exists>x x3. (x2= (x# x3))" using list.exhaust_sel by auto
      then obtain x x3 where X2: "x2= (x# x3)" by auto 

      have "consistent_with_wina g0 e0 ([x1]@([x]@x3))" using X2 Cons(3) by simp
      hence X4: "(consistent_with_wina x ((weight g0 x)e0) ([x]@x3))"
        by (smt (verit, ccfv_threshold) Nil_is_append_conv append_self_conv2 consistent_with_wina.simps hd_append2 list.sel(1) list.sel(3) not_Cons_self2 tl_append2)

      have X3: "finite_play x x2" using X2 finite_play_suffix2 X4 Cons(2)
        by (metis Cons_eq_appendI append_self_conv2 consistent_with_wina.simps finite_play.simps)
      
      have "\<not> won_by_defender x ((weight g0 x)e0) x2" using X2 X3 X4 Cons(1) by auto
      then show ?thesis using won_by_defender_suffix Cons
        by (metis Cons_eq_appendI X2 append_self_conv2 consistent_with_wina.simps list.inject)
    qed
  qed
qed

lemma ind_beg:
  fixes ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitive: "\<forall>e e' e''. (((ord e e') \<and> (ord e' e'')) \<longrightarrow> (ord e e''))" and
          reflexive: "\<forall>e. (ord e e)" and
          antysim: "\<forall>e e'. (((ord e e') \<and> (ord e' e)) \<longrightarrow> e=e')" and
          dwl_min: "\<forall>e. (ord defender_win_level e)" and 
          update_gets_smaller: "\<forall>g g' e. (((weight_opt g g') \<noteq> None) \<longrightarrow> (ord (the (weight_opt g g')e) e))" and
          
          "(Gd g) \<and> (\<forall>g'. \<not>(g \<Zinj> g')) \<and> (e \<noteq> defender_win_level)" and "ord e e'"
  shows "in_wina e' g" by (metis antysim assms(6) assms(7) dwl_min in_wina.intros(1)) 

lemma ind_step_Ga: 
  fixes ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitive: "\<forall>e e' e''. (((ord e e') \<and> (ord e' e'')) \<longrightarrow> (ord e e''))" and
          reflexive: "\<forall>e. (ord e e)" and
          antysim: "\<forall>e e'. (((ord e e') \<and> (ord e' e)) \<longrightarrow> e=e')" and
          dwl_min: "\<forall>e. (ord defender_win_level e)" and 
          monotonicity:"\<forall>g g' e e'. (((weight_opt g g') \<noteq> None \<and> (ord e e'))  \<longrightarrow> (ord (the (weight_opt g g')e) (the (weight_opt g g')e')))" and
          update_gets_smaller: "\<forall>g g' e. (((weight_opt g g') \<noteq> None) \<longrightarrow> (ord (the (weight_opt g g')e) e))" and

          ind_hyp: "\<forall>g'.((g \<Zinj> g') \<longrightarrow> (\<forall>e e'.( ((in_wina e g') \<and> (ord e e'))\<longrightarrow> (in_wina e' g'))))" and
          "(Ga g) \<and> (\<exists>g'. ((g \<Zinj> g') \<and> (in_wina ((weight g g') e) g')))\<and> (e \<noteq> defender_win_level)" 
          and "ord e e'"
  shows "in_wina e' g"
  by (metis assms(8) assms(9) defender_win_level_not_in_wina energy_game.in_wina.intros(2) ind_hyp monotonicity update_gets_smaller) 

lemma ind_step_Gd: 
  fixes ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitive: "\<forall>e e' e''. (((ord e e') \<and> (ord e' e'')) \<longrightarrow> (ord e e''))" and
          reflexive: "\<forall>e. (ord e e)" and
          antysim: "\<forall>e e'. (((ord e e') \<and> (ord e' e)) \<longrightarrow> e=e')" and
          dwl_min: "\<forall>e. (ord defender_win_level e)" and 
          monotonicity:"\<forall>g g' e e'. (((weight_opt g g') \<noteq> None \<and> (ord e e'))  \<longrightarrow> (ord (the (weight_opt g g')e) (the (weight_opt g g')e')))" and
          update_gets_smaller: "\<forall>g g' e. (((weight_opt g g') \<noteq> None) \<longrightarrow> (ord (the (weight_opt g g')e) e))" and

          ind_hyp: "\<forall>g'.((g \<Zinj> g') \<longrightarrow> (\<forall>e e'.( ((in_wina e g') \<and> (ord e e'))\<longrightarrow> (in_wina e' g'))))" and
          "(Gd g) \<and>(\<forall>g'. ((g \<Zinj> g') \<longrightarrow> (in_wina ((weight g g') e) g'))) \<and> (e \<noteq> defender_win_level)" 
          and "ord e e'"
  shows "in_wina e' g"
  using antysim assms(8) assms(9) dwl_min in_wina.intros(3) ind_hyp monotonicity by blast
  
find_theorems in_wina
thm in_wina.cases

(* TODO *)
lemma win_a_upwards_closure: 
  fixes ord::"'energy \<Rightarrow> 'energy \<Rightarrow> bool"
  assumes transitive: "\<forall>e e' e''. (((ord e e') \<and> (ord e' e'')) \<longrightarrow> (ord e e''))" and
          reflexive: "\<forall>e. (ord e e)" and
          antysim: "\<forall>e e'. (((ord e e') \<and> (ord e' e)) \<longrightarrow> e=e')" and
          dwl_min: "\<forall>e. (ord defender_win_level e)" and 
          monotonicity:"\<forall>g g' e e'. (((weight_opt g g') \<noteq> None \<and> (ord e e'))  \<longrightarrow> (ord (the (weight_opt g g')e) (the (weight_opt g g')e')))" and
          update_gets_smaller: "\<forall>g g' e. (((weight_opt g g') \<noteq> None) \<longrightarrow> (ord (the (weight_opt g g')e) e))" and
          
          "in_wina e g" and "ord e e'"
  shows "in_wina e' g"
proof - 
  have "\<And>g e. Gd g \<and> (\<forall>g'. \<not> g \<Zinj> g') \<and> e \<noteq> defender_win_level \<Longrightarrow> in_wina e' g" using ind_beg
    by (metis antysim assms(7) assms(8) dwl_min in_wina.simps)
  show  "in_wina e' g" oops

(* Beweisidee war, von den "blättern" durchzugehen und zu färben. 
   Damit dieser Beweis aufgeht, brauche ich aber Kreisfreiheit oder sowas *)
    


end (*End of context energy_game*)
end
