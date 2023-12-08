theory Energy
  imports EnergyGames "HOL-Library.Extended_Nat" "HOL-Lattice.Orders"
begin

datatype energy = E (one: "enat") (two: "enat") (three: "enat") (four: "enat")
                    (five: "enat") (six: "enat") (seven: "enat") (eight: "enat") |
                  eneg      
instantiation energy :: order begin

definition "e1 \<le> e2 \<equiv>
  (case e1 of E a1 b1 c1 d1 e1 f1 g1 h1 \<Rightarrow> (
    case e2 of E a2 b2 c2 d2 e2 f2 g2 h2 \<Rightarrow> 
      (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2 \<and> g1 \<le> g2 \<and> h1 \<le> h2) 
    | enget \<Rightarrow> False
  ) | eneg \<Rightarrow> True)"

definition "(x::energy) < y = (x \<le> y \<and> \<not> y \<le> x)"

instance proof
  fix x y z :: energy
  show "x \<le> x" unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_energy_def by (smt (z3) energy.case_eq_if order_trans)
  show "x < y = (x \<le> y \<and> \<not> y \<le> x)" using less_energy_def .
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
qed

lemma eneg_leq:
  shows "eneg \<le> e"
  by (simp add: less_eq_energy_def)

lemma leq_not_eneg:
  assumes "e1 \<noteq> eneg" "e2 \<noteq> eneg"
  shows "e1 \<le> e2 \<equiv> (one e1 \<le> one e2 \<and> two e1 \<le> two e2 \<and> three e1 \<le> three e2 \<and>
                     four e1 \<le> four e2 \<and> five e1 \<le> five e2 \<and> six e1 \<le> six e2 \<and>
                     seven e1 \<le> seven e2 \<and> eight e1 \<le> eight e2)"
  using assms unfolding less_eq_energy_def by (simp add: energy.case_eq_if)

end

text \<open>Encode if @{term "e2"} is larger than @{term "e1"} in any component.\<close>
abbreviation somwhere_larger (infix "\<prec>c" 70) where "e1 \<prec>c e2 \<equiv> \<not>(e1 \<ge> e2)"

lemma somwhere_larger_eq:
  assumes "e1 \<prec>c e2"
  shows "(e1 = eneg \<and> e2 \<noteq> eneg) \<or> one e1 < one e2 \<or> two e1 < two e2 \<or> three e1 < three e2 \<or>
         four e1 < four e2 \<or> five e1 < five e2 \<or> six e1 < six e2 \<or> seven e1 < seven e2 \<or> 
         eight e1 < eight e2"
  by (smt (z3) assms energy.case_eq_if less_eq_energy_def linorder_le_less_linear)

instantiation energy :: minus
begin

abbreviation (input) "direct_minus e1 e2 \<equiv> E ((one e1) - (one e2)) ((two e1) - (two e2)) 
                                             ((three e1) - (three e2)) ((four e1) - (four e2)) 
                                             ((five e1) - (five e2)) ((six e1) - (six e2))
                                             ((seven e1) - (seven e2)) ((eight e1) - (eight e2))"

definition minus_energy_def: "e1 - e2 \<equiv> if e1 \<prec>c e2 then eneg else direct_minus e1 e2"

instance ..

lemma energy_minus:
  assumes "E a1 b1 c1 d1 e1 f1 g1 h1 \<ge> E a2 b2 c2 d2 e2 f2 g2 h2"
  shows "E a1 b1 c1 d1 e1 f1 g1 h1 - E a2 b2 c2 d2 e2 f2 g2 h2 = E (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2) 
          (e1 - e2) (f1 - f2) (g1 -g2) (h1 - h2)"
  unfolding minus_energy_def somwhere_larger_eq using assms by simp

lemma direct_minus_eq:
  assumes "s \<le> x"
  shows "x - s = direct_minus x s"
  unfolding minus_energy_def using assms by force

lemma minus_component_leq:
  assumes "x \<noteq> eneg" "y \<noteq> eneg" "s \<noteq> eneg" "x \<le> y" "s \<le> x"
  shows "one (x - s) \<le> one (y - s)" "two (x - s) \<le> two (y - s)" "three (x - s) \<le> three (y - s)"
        "four (x - s) \<le> four (y - s)" "five (x - s) \<le> five (y - s)" "six (x - s) \<le> six (y -s)"
        "seven (x - s) \<le> seven (y - s)" "eight (x - s) \<le> eight (y - s)"
proof-
  from assms(5) have xs: "x - s = direct_minus x s" by (rule direct_minus_eq)
  from assms(5,4) have "s \<le> y" by simp
  hence ys: "y - s = direct_minus y s" by (rule direct_minus_eq)

  from energy.sel(1) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "one (x - s) \<le> one (y - s)"  by (smt (verit, del_insts))

  from energy.sel(2) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "two (x - s) \<le> two (y - s)"  by (smt (verit, del_insts))

  from energy.sel(3) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "three (x - s) \<le> three (y - s)"  by (smt (verit, del_insts))

  from energy.sel(4) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "four (x - s) \<le> four (y - s)"  by (smt (verit, del_insts))

  from energy.sel(5) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "five (x - s) \<le> five (y - s)"  by (smt (verit, del_insts))

  from energy.sel(6) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "six (x - s) \<le> six (y - s)"  by (smt (verit, del_insts))

  from energy.sel(7) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "seven (x - s) \<le> seven (y - s)"  by (smt (verit, del_insts))

  from energy.sel(8) assms xs ys add_diff_cancel_enat \<open>s \<le> y\<close> add_mono_thms_linordered_semiring(1)
          enat_ord_simps(5) le_iff_add leq_not_eneg order_le_less verit_comp_simplify1(3) 
  show "eight (x - s) \<le> eight (y - s)"  by (smt (verit, del_insts))
qed

lemma mono:
  fixes s :: energy
  assumes "s \<noteq> eneg"
  shows "mono_on UNIV (\<lambda>x. x - s)"
proof
  fix x y :: energy
  assume "x \<le> y"

  show "x - s \<le> y - s" proof(cases "x \<prec>c s")
    case True
    hence "x - s = eneg" unfolding minus_energy_def by simp
    show ?thesis unfolding \<open>x - s = eneg\<close> by (rule eneg_leq)
  next
    case False
    hence False': "s \<le> x" by blast
    hence xs: "x - s = direct_minus x s" by (rule direct_minus_eq)

    from \<open>x \<le> y\<close> False have "s \<le> y" by simp
    hence ys: "y - s = direct_minus y s" by (rule direct_minus_eq)

    from False' assms have xn: "x \<noteq> eneg" using  eneg_leq order_antisym by auto
    with \<open>x \<le> y\<close> have yn: "y \<noteq> eneg" using eneg_leq order_antisym by auto

    have xsn: "x - s \<noteq> eneg" using xs by auto
    have ysn: "y - s \<noteq> eneg" using ys by auto

    show ?thesis unfolding leq_not_eneg[OF xsn ysn] 
                 using minus_component_leq[OF xn yn assms \<open>x \<le> y\<close> \<open>s \<le> x\<close>] by blast
  qed
qed
end

definition "min1_6 e \<equiv> case e of E a b c d e f g h \<Rightarrow> E (min a f) b c d e f g h | eneg \<Rightarrow> eneg "
definition "min1_7 e \<equiv> case e of E a b c d e f g h \<Rightarrow> E (min a g) b c d e f g h | eneg \<Rightarrow> eneg "

lemma min_eneg:
  shows "min1_6 eneg = eneg" "min1_7 eneg = eneg"
  unfolding min1_6_def min1_7_def by simp+

lemma min_1_6_simps[simp]:
  assumes "e \<noteq> eneg"
  shows "one (min1_6 e) = min (one e) (six e)"
        "two (min1_6 e) = two e" 
        "three (min1_6 e) = three e"
        "four (min1_6 e) = four e"
        "five (min1_6 e) = five e"
        "six (min1_6 e) = six e"
        "seven (min1_6 e) = seven e"
        "eight (min1_6 e) = eight e"
  unfolding min1_6_def by (simp_all add: assms energy.case_eq_if)

lemma min_1_7_simps:
  assumes "e \<noteq> eneg"
  shows "one (min1_7 e) = min (one e) (seven e)"
        "two (min1_7 e) = two e" 
        "three (min1_7 e) = three e"
        "four (min1_7 e) = four e"
        "five (min1_7 e) = five e"
        "six (min1_7 e) = six e"
        "seven (min1_7 e) = seven e"
        "eight (min1_7 e) = eight e"
  unfolding min1_7_def by (simp_all add: assms energy.case_eq_if)

lemma mono_min_1_6:
  shows "mono_on UNIV min1_6"
proof
  fix x y :: energy
  assume "x \<le> y"
  thus "min1_6 x \<le> min1_6 y" proof(cases "x = eneg \<or> y = eneg")
    case True
    thus ?thesis using \<open>x \<le> y\<close> eneg_leq min_eneg(1) order_antisym by fastforce
  next
    case False
    hence "x \<noteq> eneg" "y \<noteq> eneg" by blast+
    thus ?thesis by (smt (z3) \<open>x \<le> y\<close> energy.case_eq_if energy.case_eq_if energy.distinct(1) 
                less_eq_energy_def min1_6_def min_1_6_simps(1) min_1_6_simps(2) 
                min_1_6_simps(3) min_1_6_simps(4) min_1_6_simps(5) min_1_6_simps(6)
                min_1_6_simps(7) min_1_6_simps(8) min_def order_less_imp_le order_trans 
                verit_comp_simplify1(3))
  qed
qed

lemma mono_min_1_7:
  shows "mono_on UNIV min1_7"
proof
  fix x y :: energy
  assume "x \<le> y"
  thus "min1_7 x \<le> min1_7 y" proof(cases "x = eneg \<or> y = eneg")
    case True
    thus ?thesis using \<open>x \<le> y\<close> eneg_leq min_eneg(2) order_antisym by fastforce
  next
    case False
    hence "x \<noteq> eneg" "y \<noteq> eneg" by blast+
    thus ?thesis by (smt (z3) \<open>x \<le> y\<close> energy.case_eq_if energy.case_eq_if energy.distinct(1)
                 less_eq_energy_def min1_7_def min_1_7_simps(1) min_1_7_simps(2) min_1_7_simps(3) 
                 min_1_7_simps(4) min_1_7_simps(5) min_1_7_simps(6) min_1_7_simps(7) min_1_7_simps(8) 
                 min_def order.order_iff_strict order_le_less_trans verit_comp_simplify1(3))
  qed
qed

end