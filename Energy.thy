text \<open>\newpage\<close>
section \<open>Energy\<close>
theory Energy
  imports Main "HOL-Library.Extended_Nat"
begin
text \<open>Following the paper \cite[p. 5]{bisping2023lineartimebranchingtime}, we define energies as
      eight-dimensional vectors of natural numbers extended by @{text "\<infinity>"}.
      But deviate from \cite{bisping2023lineartimebranchingtime} in also defining
      an energy @{text "eneg"} that represents negative energy. This allows us to
      express energy updates (cf. \cite[p. 8]{bisping2023lineartimebranchingtime}) as total functions\label{deviation:eneg}.\<close>
datatype energy = E (modal_depth: "enat") (br_conj_depth: "enat") (conj_depth: "enat") (st_conj_depth: "enat")
                    (imm_conj_depth: "enat") (pos_conjuncts: "enat") (neg_conjuncts: "enat") (neg_depth: "enat")

subsection \<open>Ordering Energies\<close>
text \<open>In order to define subtraction on energies, we first lift the orderings
      @{text "\<le>"} and @{text "<"} from @{type "enat"} to @{type "energy"}.\<close>
instantiation energy :: order begin

definition "e1 \<le> e2 \<equiv>
  (case e1 of E a1 b1 c1 d1 e1 f1 g1 h1 \<Rightarrow> (
    case e2 of E a2 b2 c2 d2 e2 f2 g2 h2 \<Rightarrow> 
      (a1 \<le> a2 \<and> b1 \<le> b2 \<and> c1 \<le> c2 \<and> d1 \<le> d2 \<and> e1 \<le> e2 \<and> f1 \<le> f2 \<and> g1 \<le> g2 \<and> h1 \<le> h2) 
    ))"

definition "(x::energy) < y = (x \<le> y \<and> \<not> y \<le> x)"

text \<open>Next, we show that this yields a reflexive transitive antisymmetric order.\<close>

instance proof
  fix e1 e2 e3 :: energy
  show "e1 \<le> e1" unfolding less_eq_energy_def by (simp add: energy.case_eq_if)
  show "e1 \<le> e2 \<Longrightarrow> e2 \<le> e3 \<Longrightarrow> e1 \<le> e3" unfolding less_eq_energy_def 
    by (smt (z3) energy.case_eq_if order_trans)
  show "e1 < e2 = (e1 \<le> e2 \<and> \<not> e2 \<le> e1)" using less_energy_def .
  show "e1 \<le> e2 \<Longrightarrow> e2 \<le> e1 \<Longrightarrow> e1 = e2" unfolding less_eq_energy_def
    by (smt (z3) energy.case_eq_if energy.expand nle_le)
qed


lemma leq_components[simp]:
  shows "e1 \<le> e2 \<equiv> (modal_depth e1 \<le> modal_depth e2 \<and> br_conj_depth e1 \<le> br_conj_depth e2 \<and> conj_depth e1 \<le> conj_depth e2 \<and>
                     st_conj_depth e1 \<le> st_conj_depth e2 \<and> imm_conj_depth e1 \<le> imm_conj_depth e2 \<and> pos_conjuncts e1 \<le> pos_conjuncts e2 \<and>
                     neg_conjuncts e1 \<le> neg_conjuncts e2 \<and> neg_depth e1 \<le> neg_depth e2)"
  unfolding less_eq_energy_def by (simp add: energy.case_eq_if)

lemma energy_leq_cases:
  assumes "modal_depth e1 \<le> modal_depth e2" "br_conj_depth e1 \<le> br_conj_depth e2" "conj_depth e1 \<le> conj_depth e2"
          "st_conj_depth e1 \<le> st_conj_depth e2" "imm_conj_depth e1 \<le> imm_conj_depth e2" "pos_conjuncts e1 \<le> pos_conjuncts e2"
          "neg_conjuncts e1 \<le> neg_conjuncts e2" "neg_depth e1 \<le> neg_depth e2"
  shows "e1 \<le> e2" using assms unfolding leq_components by blast

end

text \<open>We then use this order to define a predicate that decides if an @{term "e1 :: energy"} 
      may be subtracted from another @{term "e2 :: energy"} without the result being negative. We encode this by @{term "e1"} being @{text "somewhere_larger"} than @{term "e2"}.\<close>

abbreviation somewhere_larger where "somewhere_larger e1 e2 \<equiv> \<not>(e1 \<ge> e2)"

lemma somewhere_larger_eq:
  assumes "somewhere_larger e1 e2"
  shows "modal_depth e1 < modal_depth e2 \<or> br_conj_depth e1 < br_conj_depth e2 
         \<or> conj_depth e1 < conj_depth e2 \<or> st_conj_depth e1 < st_conj_depth e2 \<or> imm_conj_depth e1 < imm_conj_depth e2 
         \<or> pos_conjuncts e1 < pos_conjuncts e2 \<or> neg_conjuncts e1 < neg_conjuncts e2 \<or> neg_depth e1 < neg_depth e2"
  by (smt (z3) assms energy.case_eq_if less_eq_energy_def linorder_le_less_linear)

subsection \<open>Subtracting Energies\<close>
text \<open>Using \<open>somewhere_larger\<close> we define subtraction as 
  the @{text "minus"} operator on energies.\<close>

instantiation energy :: minus
begin

definition minus_energy_def[simp]: "e1 - e2 \<equiv> E
  ((modal_depth e1) - (modal_depth e2)) 
  ((br_conj_depth e1) - (br_conj_depth e2)) 
  ((conj_depth e1) - (conj_depth e2)) 
  ((st_conj_depth e1) - (st_conj_depth e2)) 
  ((imm_conj_depth e1) - (imm_conj_depth e2)) 
  ((pos_conjuncts e1) - (pos_conjuncts e2))
  ((neg_conjuncts e1) - (neg_conjuncts e2))
  ((neg_depth e1) - (neg_depth e2))"

instance ..

end

text \<open>Afterwards, we prove some lemmas to ease the manipulation of expressions 
  using subtraction on energies.\<close>
lemma energy_minus[simp]:
  shows "E a1 b1 c1 d1 e1 f1 g1 h1 - E a2 b2 c2 d2 e2 f2 g2 h2
         = E (a1 - a2) (b1 - b2) (c1 - c2) (d1 - d2) 
             (e1 - e2) (f1 - f2) (g1 - g2) (h1 - h2)"
  unfolding minus_energy_def somewhere_larger_eq by simp

lemma minus_component_leq:
  assumes "s \<le> x" "x \<le> y"
  shows "modal_depth (x - s) \<le> modal_depth (y - s)" "br_conj_depth (x - s) \<le> br_conj_depth (y - s)"
        "conj_depth (x - s) \<le> conj_depth (y - s)" "st_conj_depth (x - s) \<le> st_conj_depth (y - s)"
        "imm_conj_depth (x - s) \<le> imm_conj_depth (y - s)" "pos_conjuncts (x - s) \<le> pos_conjuncts (y -s)"
        "neg_conjuncts (x - s) \<le> neg_conjuncts (y - s)" "neg_depth (x - s) \<le> neg_depth (y - s)"
proof-
  from assms have "s \<le> y" by (simp del: leq_components)
  with assms leq_components have
    "modal_depth (x - s) \<le> modal_depth (y - s) \<and> br_conj_depth (x - s) \<le> br_conj_depth (y - s) \<and>
    conj_depth (x - s) \<le> conj_depth (y - s) \<and> st_conj_depth (x - s) \<le> st_conj_depth (y - s) \<and>
    imm_conj_depth (x - s) \<le> imm_conj_depth (y - s) \<and> pos_conjuncts (x - s) \<le> pos_conjuncts (y -s) \<and>
    neg_conjuncts (x - s) \<le> neg_conjuncts (y - s) \<and> neg_depth (x - s) \<le> neg_depth (y - s)"
    by (smt (verit, del_insts) add_diff_cancel_enat enat_add_left_cancel_le energy.sel
        leD le_iff_add le_less minus_energy_def)+
  thus
    "modal_depth (x - s) \<le> modal_depth (y - s)" "br_conj_depth (x - s) \<le> br_conj_depth (y - s)"
    "conj_depth (x - s) \<le> conj_depth (y - s)" "st_conj_depth (x - s) \<le> st_conj_depth (y - s)"
    "imm_conj_depth (x - s) \<le> imm_conj_depth (y - s)" "pos_conjuncts (x - s) \<le> pos_conjuncts (y -s)"
    "neg_conjuncts (x - s) \<le> neg_conjuncts (y - s)" "neg_depth (x - s) \<le> neg_depth (y - s)" by auto
qed

lemma enat_diff_mono:
  assumes \<open>(i::enat) \<le> j\<close>
  shows "i - k \<le> j - k"
proof (cases i)
  case (enat iN)
  show ?thesis
  proof (cases j)
    case (enat jN)
    then show ?thesis
      using assms enat_ile by (cases k, fastforce+)
  next
    case infinity
    then show ?thesis using assms by auto
  qed
next
  case infinity
  hence \<open>j = \<infinity>\<close>
    using assms by auto
  then show ?thesis by auto
qed

text \<open>We further show that the subtraction of energies is decreasing.\<close>
lemma energy_diff_mono:
  fixes s :: energy
  shows "mono_on UNIV (\<lambda>x. x - s)"
  unfolding mono_on_def
  by (auto simp add: enat_diff_mono)

lemma gets_smaller:
  fixes s :: energy
  shows "(\<lambda>x. x - s) x \<le> x"
  by (auto)
     (metis add.commute add_diff_cancel_enat enat_diff_mono idiff_infinity idiff_infinity_right le_iff_add not_infinity_eq zero_le)+

lemma mono_subtract: 
  assumes "x \<le> x'"
  shows "(\<lambda>x. x - (E a b c d e f g h)) x \<le> (\<lambda>x. x - (E a b c d e f g h)) x'"
  using assms enat_diff_mono by force

text \<open>We also define abbreviations for performing subtraction.\<close>
abbreviation "subtract_fn a b c d e f g h \<equiv>
  (\<lambda>x. if somewhere_larger x (E a b c d e f g h) then None else Some (x - (E a b c d e f g h)))"

abbreviation "subtract a b c d e f g h \<equiv> Some (subtract_fn a b c d e f g h)"

subsection \<open>Minimum Updates\<close>
text \<open>Next, we define two energy updates that replace the first component with the minimum of two other components.\<close>
definition "min1_6 e \<equiv> case e of E a b c d e f g h \<Rightarrow> Some (E (min a f) b c d e f g h)"
definition "min1_7 e \<equiv> case e of E a b c d e f g h \<Rightarrow> Some (E (min a g) b c d e f g h)"


text \<open>lift order to options\<close>
instantiation option :: (order) order
begin

definition less_eq_option_def[simp]:
  \<open>less_eq_option (optA :: 'a option) optB \<equiv>
    case optA of
      (Some a) \<Rightarrow>
        (case optB of
          (Some b) \<Rightarrow> a \<le> b |
          None \<Rightarrow> False) |
      None \<Rightarrow> True\<close>

definition less_option_def[simp]:
  "less_option (optA :: 'a option) optB \<equiv> (optA \<le> optB \<and> \<not> optB \<le> optA)"

instance proof standard
  fix x y::\<open>'a option\<close>
  show \<open>(x < y) = (x \<le> y \<and> \<not> y \<le> x)\<close> by simp
next
  fix x::\<open>'a option\<close>
  show \<open>x \<le> x\<close>
    by (simp add: option.case_eq_if)
next
  fix x y z::\<open>'a option\<close>
  assume \<open>x \<le> y\<close> \<open>y \<le> z\<close>
  thus \<open>x \<le> z\<close>
    unfolding less_eq_option_def
    by (metis option.case_eq_if order_trans)
next
  fix x y::\<open>'a option\<close>
  assume \<open> x \<le> y\<close> \<open>y \<le> x\<close>
  thus \<open>x = y\<close>
    unfolding less_eq_option_def
    by (smt (z3) inf.absorb_iff2 le_boolD option.case_eq_if option.split_sel order_antisym)
qed

end

text \<open>Again, we prove that these updates only decrease energies.\<close>

lemma min_1_6_simps[simp]:
  shows "modal_depth (the (min1_6 e)) = min (modal_depth e) (pos_conjuncts e)"
        "br_conj_depth (the (min1_6 e)) = br_conj_depth e" 
        "conj_depth (the (min1_6 e)) = conj_depth e"
        "st_conj_depth (the (min1_6 e)) = st_conj_depth e"
        "imm_conj_depth (the (min1_6 e)) = imm_conj_depth e"
        "pos_conjuncts (the (min1_6 e)) = pos_conjuncts e"
        "neg_conjuncts (the (min1_6 e)) = neg_conjuncts e"
        "neg_depth (the (min1_6 e)) = neg_depth e"
  unfolding min1_6_def by (simp_all add: energy.case_eq_if)

lemma min_1_7_simps[simp]:
  shows "modal_depth (the (min1_7 e)) = min (modal_depth e) (neg_conjuncts e)"
        "br_conj_depth (the (min1_7 e)) = br_conj_depth e" 
        "conj_depth (the (min1_7 e)) = conj_depth e"
        "st_conj_depth (the (min1_7 e)) = st_conj_depth e"
        "imm_conj_depth (the (min1_7 e)) = imm_conj_depth e"
        "pos_conjuncts (the (min1_7 e)) = pos_conjuncts e"
        "neg_conjuncts (the (min1_7 e)) = neg_conjuncts e"
        "neg_depth (the (min1_7 e)) = neg_depth e"
  unfolding min1_7_def by (simp_all add: energy.case_eq_if)

lemma min_1_6_some:
  shows \<open>min1_6 e \<noteq> None\<close>
  unfolding min1_6_def
  using energy.case_eq_if by blast

lemma min_1_7_some:
  shows \<open>min1_7 e \<noteq> None\<close>
  unfolding min1_7_def
  using energy.case_eq_if by blast

lemma mono_min_1_6:
  shows "mono (the \<circ> min1_6)"
proof
  fix x y :: energy
  assume "x \<le> y"
  thus "(the \<circ> min1_6) x \<le> (the \<circ> min1_6) y" unfolding leq_components
    using min.mono min_1_6_simps min1_6_def by auto
qed

lemma mono_min_1_7:
  shows "mono (the \<circ> min1_7)"
proof
  fix x y :: energy
  assume "x \<le> y"
  thus "(the \<circ> min1_7) x \<le> (the \<circ> min1_7) y" unfolding leq_components
    using min.mono min_1_7_simps min1_7_def by auto
qed

lemma gets_smaller_min_1_6: 
  shows "the (min1_6 x) \<le> x"
  using min_1_6_simps min_less_iff_conj somewhere_larger_eq by fastforce


lemma gets_smaller_min_1_7: 
  shows "the (min1_7 x) \<le> x"
  using min_1_7_simps min_less_iff_conj somewhere_larger_eq by fastforce

lemma min_1_7_lower_end:
  assumes \<open>(Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) = None\<close>
  shows \<open>neg_depth e = 0\<close>
  using assms
  by (smt (verit) bind.bind_lunit energy.sel ileI1 leq_components min_1_7_some not_gr_zero one_eSuc zero_le)

lemma min_1_7_subtr_simp:
  shows \<open>(Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)
    = (if neg_depth e = 0 then None
        else Some (E (min (modal_depth e) (neg_conjuncts e)) (br_conj_depth e) (conj_depth e) (st_conj_depth e) (imm_conj_depth e) (pos_conjuncts e) (neg_conjuncts e) (neg_depth e - 1)))\<close>
  using min_1_7_lower_end
  by (auto simp add: min1_7_def)

lemma min_1_7_subtr_mono:
  shows \<open>mono (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7)\<close>
proof
  fix e1 e2 :: energy
  assume "e1 \<le> e2"
  thus "(\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) e1
    \<le>  (\<lambda>e. Option.bind ((subtract_fn 0 0 0 0 0 0 0 1) e) min1_7) e2"
    unfolding min_1_7_subtr_simp
    by (auto simp add: min.coboundedI1  min.coboundedI2 enat_diff_mono)
qed

lemma min_1_6_subtr_simp:
  shows \<open>(Option.bind ((subtract_fn 0 1 1 0 0 0 0 0) e) min1_6)
    = (if br_conj_depth e = 0 \<or> conj_depth e = 0 then None
        else Some (E (min (modal_depth e) (pos_conjuncts e)) (br_conj_depth e - 1) (conj_depth e - 1) (st_conj_depth e) (imm_conj_depth e) (pos_conjuncts e) (neg_conjuncts e) (neg_depth e)))\<close>
  by (auto simp add: min1_6_def ileI1 one_eSuc)

instantiation energy :: Sup
begin

definition "Sup ee \<equiv> E (Sup (modal_depth ` ee)) (Sup (br_conj_depth ` ee )) (Sup (conj_depth ` ee)) (Sup (st_conj_depth ` ee))
  (Sup (imm_conj_depth ` ee)) (Sup (pos_conjuncts ` ee)) (Sup (neg_conjuncts ` ee)) (Sup (neg_depth ` ee))"

instance ..
end


end