text \<open>\newpage\<close>
section \<open>Energy\<close>
theory Energy
  imports Main "HOL-Library.Extended_Nat" "HOL-Lattice.Orders"
begin
text \<open>Following the paper \cite[p. 5]{bisping2023lineartimebranchingtime}, we define energies as
      eight-dimensional vectors of natural numbers extended by @{text "\<infinity>"}.
      But deviate from \cite{bisping2023lineartimebranchingtime} in also defining
      an energy @{text "eneg"} that represents negative energy. This allows us to
      express energy updates (cf. \cite[p. 8]{bisping2023lineartimebranchingtime}) as total functions\label{deviation:eneg}.\<close>
datatype energy = E (one: "enat") (two: "enat") (three: "enat") (four: "enat")
                    (five: "enat") (six: "enat") (seven: "enat") (eight: "enat") |
                  eneg
subsection \<open>Ordering Energies\<close>
text \<open>In order to define subtraction on energies, we first lift the orderings
      @{text "\<le>"} and @{text "<"} from @{type "enat"} to @{type "energy"}.\<close>
instantiation energy :: order begin

definition "e1 \<le> e2 \<equiv>
  (case e1 of E a1 b1 c1 d1 e1 f1 g1 h1 \<Rightarrow> (
    case e2 of E a2 b2 c2 d2 e2 f2 g2 h2 \<Rightarrow> 
      (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2 \<and> g1 \<le> g2 \<and> h1 \<le> h2) 
    | eneg \<Rightarrow> False
  ) | eneg \<Rightarrow> True)"

definition "(x::energy) < y = (x \<le> y \<and> \<not> y \<le> x)"

text \<open>Next, we show that this yields a reflexive transitive antisymmetric order.\<close>

instance proof
  fix x y z :: energy
  show "x \<le> x" unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z" unfolding less_eq_energy_def 
    by (smt (z3) energy.case_eq_if order_trans)
  show "x < y = (x \<le> y \<and> \<not> y \<le> x)" using less_energy_def .
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y" unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
qed

text \<open>We further prove that @{term "eneg"} is a lower bound.\<close>
lemma eneg_leq:
  shows "eneg \<le> e"
  by (simp add: less_eq_energy_def)

lemma leq_not_eneg:
  assumes "e1 \<noteq> eneg" "e2 \<noteq> eneg"
  shows "e1 \<le> e2 \<equiv> (one e1 \<le> one e2 \<and> two e1 \<le> two e2 \<and> three e1 \<le> three e2 \<and>
                     four e1 \<le> four e2 \<and> five e1 \<le> five e2 \<and> six e1 \<le> six e2 \<and>
                     seven e1 \<le> seven e2 \<and> eight e1 \<le> eight e2)"
  using assms unfolding less_eq_energy_def by (simp add: energy.case_eq_if)

lemma energy_leq_cases:
  assumes "e2 \<noteq> eneg"
          "one e1 \<le> one e2" "two e1 \<le> two e2" "three e1 \<le> three e2"
          "four e1 \<le> four e2" "five e1 \<le> five e2" "six e1 \<le> six e2"
          "seven e1 \<le> seven e2" "eight e1 \<le> eight e2"
  shows "e1 \<le> e2" using assms by (metis eneg_leq leq_not_eneg)

end

text \<open>We then use this order to define a predicate that decides if an @{term "e1 :: energy"} 
      may be subtracted from another @{term "e2 :: energy"} without the result being negative. We encode this by @{term "e1"} being @{text "somewhere_larger"} than @{term "e2"}.\<close>

abbreviation somewhere_larger where "somewhere_larger e1 e2 \<equiv> \<not>(e1 \<ge> e2)"

lemma somewhere_larger_eq:
  assumes "somewhere_larger e1 e2"
  shows "(e1 = eneg \<and> e2 \<noteq> eneg) \<or> one e1 < one e2 \<or> two e1 < two e2 
         \<or> three e1 < three e2 \<or> four e1 < four e2 \<or> five e1 < five e2 
         \<or> six e1 < six e2 \<or> seven e1 < seven e2 \<or> eight e1 < eight e2"
  by (smt (z3) assms energy.case_eq_if less_eq_energy_def linorder_le_less_linear)

subsection \<open>Subtracting Energies\<close>
text \<open>Using \<open>somewhere_larger\<close> we define subtraction as 
  the @{text "minus"} operator on energies.\<close>

instantiation energy :: minus
begin

abbreviation (input) "direct_minus e1 e2 \<equiv> E ((one e1) - (one e2)) 
                                             ((two e1) - (two e2)) 
                                             ((three e1) - (three e2)) 
                                             ((four e1) - (four e2)) 
                                             ((five e1) - (five e2)) 
                                             ((six e1) - (six e2))
                                             ((seven e1) - (seven e2))
                                             ((eight e1) - (eight e2))"

definition minus_energy_def: "e1 - e2 \<equiv> if somewhere_larger e1 e2 then eneg else direct_minus e1 e2"

instance ..

text \<open>Afterwards, we prove some lemmas to ease the manipulation of expressions 
  using subtraction on energies.\<close>
lemma energy_minus:
  assumes "E a1 b1 c1 d1 e1 f1 g1 h1 \<ge> E a2 b2 c2 d2 e2 f2 g2 h2"
  shows "E a1 b1 c1 d1 e1 f1 g1 h1 - E a2 b2 c2 d2 e2 f2 g2 h2
         = E (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2) 
             (e1 - e2) (f1 - f2) (g1 -g2) (h1 - h2)"
  unfolding minus_energy_def somewhere_larger_eq using assms by simp

lemma direct_minus_eq:
  assumes "s \<le> x"
  shows "x - s = direct_minus x s"
  unfolding minus_energy_def using assms by force

lemma minus_component_leq:
  assumes "x \<noteq> eneg" "y \<noteq> eneg" "s \<noteq> eneg" "x \<le> y" "s \<le> x"
  shows "one (x - s) \<le> one (y - s)" "two (x - s) \<le> two (y - s)"
        "three (x - s) \<le> three (y - s)" "four (x - s) \<le> four (y - s)"
        "five (x - s) \<le> five (y - s)" "six (x - s) \<le> six (y -s)"
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

text \<open>We further show that the subtraction of non-negative energies is decreasing.\<close>
lemma mono:
  fixes s :: energy
  assumes "s \<noteq> eneg"
  shows "mono_on UNIV (\<lambda>x. x - s)" 
proof
  fix x y :: energy
  assume "x \<le> y"

  show "x - s \<le> y - s" proof(cases "somewhere_larger x s")
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

lemma gets_smaller:
  fixes s :: energy
  assumes "s \<noteq> eneg"
  shows "(\<lambda>x. x - s)x \<le> x" 
proof(cases "s\<le>x")
  case True
  hence A0: "x-s = direct_minus x s" using direct_minus_eq by simp

  have A1:  "(one x - one s) \<le> one x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
  have A2: "(two x - two s) \<le> two x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
  have A3: "(three x - three s) \<le> three x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
  have A4: "(four x - four s) \<le> four x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
   have A5: "(five x - five s) \<le> five x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
   have A6: "(six x - six s) \<le> six x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
   have A7: "(seven x - seven s) \<le> seven x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
   have A8: "(eight x - eight s) \<le> eight x" using idiff_enat_enat diff_enat_def
    by (smt (verit, ccfv_threshold) diff_le_self enat_ord_simps(1) enat_ord_simps(4) enat_ord_simps(6) idiff_infinity_right less_infinityE not_le_imp_less zero_le)
  
  thus ?thesis using assms A0 A1 A2 A3 A4 A5 A6 A7 A8
    by (metis True antisym eneg_leq energy.sel(1) energy.sel(2) energy.sel(3) energy.sel(4) energy.sel(5) energy.sel(6) energy.sel(7) energy.sel(8) leq_not_eneg)
next
  case False
  hence "x-s = eneg" by (simp add: minus_energy_def)
  thus ?thesis by (simp add: eneg_leq) 
qed

end

lemma mono_subtract: 
  assumes "x \<le> x'"
  shows "(\<lambda>x. x - (E a b c d e f g h)) x \<le> (\<lambda>x. x - (E a b c d e f g h)) x'"
  by (smt (verit) antisym assms dual_order.trans eneg_leq energy.distinct(1) leq_not_eneg minus_component_leq(1) minus_component_leq(2) minus_component_leq(3) minus_component_leq(4) minus_component_leq(5) minus_component_leq(6) minus_component_leq(7) minus_component_leq(8) minus_energy_def)


text \<open>We also define abbreviations for performing subtraction.\<close>
abbreviation "subtract_fn a b c d e f g h \<equiv> (\<lambda>x. x - (E a b c d e f g h))"
abbreviation "e1 \<equiv> subtract_fn 1 0 0 0 0 0 0 0"
abbreviation "e3 \<equiv> subtract_fn 0 0 1 0 0 0 0 0"
abbreviation "e5 \<equiv> subtract_fn 0 0 0 0 1 0 0 0"

abbreviation "subtract a b c d e f g h \<equiv> Some (subtract_fn a b c d e f g h)"

subsection \<open>Minimum Updates\<close>
text \<open>Next, we define two energy updates that replace the first component with the minimum of two other components.\<close>
definition "min1_6 e \<equiv> case e of E a b c d e f g h \<Rightarrow> E (min a f) b c d e f g h | eneg \<Rightarrow> eneg "
definition "min1_7 e \<equiv> case e of E a b c d e f g h \<Rightarrow> E (min a g) b c d e f g h | eneg \<Rightarrow> eneg "

text \<open>Again, we prove that these updates only decrease energies.\<close>

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

lemma gets_smaller_min_1_6: 
  shows "min1_6 x \<le> x"
proof(cases "x=eneg")
  case True
  thus ?thesis using min_eneg eneg_leq by simp
next
  case False
  thus ?thesis
    using min_1_6_simps min_less_iff_conj somewhere_larger_eq by fastforce
qed

lemma gets_smaller_min_1_7: 
  shows "min1_7 x \<le> x"
proof(cases "x=eneg")
  case True
  thus ?thesis using min_eneg eneg_leq by simp
next
  case False
  thus ?thesis
    using min_1_7_simps min_less_iff_conj somewhere_larger_eq by fastforce
qed

instantiation energy :: Sup
begin

definition "Sup ee \<equiv> E (Sup (one ` (ee - {eneg}))) (Sup (two ` (ee - {eneg}))) (Sup (three ` (ee - {eneg}))) (Sup (four ` (ee - {eneg})))
  (Sup (five ` (ee - {eneg}))) (Sup (six ` (ee - {eneg}))) (Sup (seven ` (ee - {eneg}))) (Sup (eight ` (ee - {eneg})))"

instance ..

end

(*
instantiation energy :: ccpo
begin


instance proof
  fix EE and e::energy
  assume \<open>Complete_Partial_Order.chain (\<le>) EE\<close> \<open>e \<in> EE\<close>
  thus \<open>e \<le> Sup EE\<close>
    by (simp add: SUP_upper Sup_energy_def energy.case_eq_if less_eq_energy_def)
next
  fix EE and e'::energy
  assume
    \<open>Complete_Partial_Order.chain (\<le>) EE\<close>
    \<open>\<And>e. e \<in> EE \<Longrightarrow> e \<le> e'\<close>
  thus \<open>Sup EE \<le> e'\<close>
    unfolding Sup_energy_def less_eq_energy_def nitpick
  
end
*)

end