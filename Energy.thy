text \<open>\newpage\<close>
section \<open>Energy\<close>
theory Energy
  imports "Galois_Energy_Games.Update"
begin
text \<open>Following the paper \cite[p. 5]{bj2023silentStepSpectroscopyArxiv}, we define energies as
      eight-dimensional vectors of natural numbers extended by @{text \<open>\<infinity>\<close>}.
      But deviate from \cite{bj2023silentStepSpectroscopyArxiv} in also defining
      an energy @{text \<open>eneg\<close>} that represents negative energy. This allows us to
      express energy updates (cf. \cite[p. 8]{bj2023silentStepSpectroscopyArxiv}) as total functions\label{deviation:eneg}.\<close>

abbreviation E :: \<open>enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> enat \<Rightarrow> energy\<close> where
  \<open>E md brcd cd scd icd pc nc nd \<equiv> [md, brcd, cd, scd, icd, pc, nc, nd]\<close>

abbreviation modal_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>modal_depth e \<equiv> e!0\<close>
abbreviation br_conj_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>br_conj_depth e \<equiv> e!1\<close>
abbreviation conj_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>conj_depth e \<equiv> e!2\<close>
abbreviation st_conj_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>st_conj_depth e \<equiv> e!3\<close>
abbreviation imm_conj_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>imm_conj_depth e \<equiv> e!4\<close>
abbreviation pos_conjuncts :: \<open>energy \<Rightarrow> enat\<close> where \<open>pos_conjuncts e \<equiv> e!5\<close>
abbreviation neg_conjuncts :: \<open>energy \<Rightarrow> enat\<close> where \<open>neg_conjuncts e \<equiv> e!6\<close>
abbreviation neg_depth :: \<open>energy \<Rightarrow> enat\<close> where \<open>neg_depth e \<equiv> e!7\<close>


(*
lemma energy_components:
  assumes \<open>length e = 2\<close>
  shows \<open>\<exists> md brcd. e = [md, brcd]\<close>
  using assms sledgehammer
  by (metis (no_types, lifting) One_nat_def Suc_1 length_0_conv length_Suc_conv)
  by (metis length_0_conv length_Suc_conv numeral_2_eq_2)
*)

lemma eight_def: \<open>8 = (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))))\<close> by simp

lemma vector_8_comps:
  shows \<open>length v = 8 \<longleftrightarrow> (\<exists> v0 v1 v2 v3 v4 v5 v6 v7. v = [v0, v1, v2, v3, v4, v5, v6, v7])\<close>
  unfolding eight_def length_Suc_conv
  by auto

lemma energy_components:
  assumes \<open>length e = 8\<close>
  shows \<open>\<exists> md brcd cd scd icd pc nc nd. e = E md brcd cd scd icd pc nc nd\<close>
  using assms vector_8_comps
  by blast

lemma leq_components[simp]:
  assumes \<open>length e1 = 8\<close> \<open>length e2 = 8\<close>
  shows \<open>e1 e\<le> e2 \<equiv>
    modal_depth e1 \<le> modal_depth e2 \<and> br_conj_depth e1 \<le> br_conj_depth e2 \<and>
    conj_depth e1 \<le> conj_depth e2 \<and> st_conj_depth e1 \<le> st_conj_depth e2 \<and>
    imm_conj_depth e1 \<le> imm_conj_depth e2 \<and> pos_conjuncts e1 \<le> pos_conjuncts e2 \<and>
    neg_conjuncts e1 \<le> neg_conjuncts e2 \<and> neg_depth e1 \<le> neg_depth e2\<close>
  using assms energy_components[OF assms(1)] energy_components[OF assms(2)]
  unfolding energy_leq_def eight_def
  by (smt (z3) One_nat_def Suc_1 Suc_mono Suc_numeral le_less_Suc_eq le_numeral_extra(3) less_2_cases less_SucE less_SucI semiring_norm(2,5,8))

lemma energy_leq_cases:
  assumes
    \<open>length e1 = 8\<close> \<open>length e2 = 8\<close>
    \<open>modal_depth e1 \<le> modal_depth e2\<close> \<open>br_conj_depth e1 \<le> br_conj_depth e2\<close>
    \<open>conj_depth e1 \<le> conj_depth e2\<close> \<open>st_conj_depth e1 \<le> st_conj_depth e2\<close>
    \<open>imm_conj_depth e1 \<le> imm_conj_depth e2\<close> \<open>pos_conjuncts e1 \<le> pos_conjuncts e2\<close>
    \<open>neg_conjuncts e1 \<le> neg_conjuncts e2\<close> \<open>neg_depth e1 \<le> neg_depth e2\<close>
  shows \<open>e1 e\<le> e2\<close> using assms unfolding leq_components[OF assms(1,2)] by blast

text \<open>We then use this order to define a predicate that decides if an @{term \<open>e1\<close>}
      may be subtracted from another @{term \<open>e2\<close>} without the result being negative.
      We encode this by @{term \<open>e1\<close>} being @{text \<open>somewhere_larger\<close>} than @{term \<open>e2\<close>}.\<close>

abbreviation somewhere_larger where \<open>somewhere_larger e1 e2 \<equiv> \<not>(e2 e\<le> e1)\<close>

lemma somewhere_larger_eq:
  assumes
    \<open>length e1 = 8\<close> \<open>length e2 = 8\<close>
    \<open>somewhere_larger e1 e2\<close>
  shows
    \<open>modal_depth e1 < modal_depth e2 \<or> br_conj_depth e1 < br_conj_depth e2
     \<or> conj_depth e1 < conj_depth e2 \<or> st_conj_depth e1 < st_conj_depth e2
     \<or> imm_conj_depth e1 < imm_conj_depth e2 \<or> pos_conjuncts e1 < pos_conjuncts e2
     \<or> neg_conjuncts e1 < neg_conjuncts e2 \<or> neg_depth e1 < neg_depth e2\<close>
  using assms by auto

lemma enat_diff_mono:
  assumes \<open>(i::enat) \<le> j\<close>
  shows \<open>i - k \<le> j - k\<close>
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

subsection \<open>Minimum Updates\<close>
text \<open>Next, we define two energy updates that replace the first component with the minimum of two other components.\<close>
definition \<open>min1_6 \<equiv> Some [min_set {1,6}, zero, zero, zero, zero, zero, zero, zero]\<close>
definition \<open>min1_7 \<equiv> Some [min_set {1,7}, zero, zero, zero, zero, zero, zero, zero]\<close>

text \<open>Abbreviations for identity update.\<close>
abbreviation \<open>id_up \<equiv> Some [zero, zero, zero, zero, zero, zero, zero, zero]\<close>

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
  \<open>less_option (optA :: 'a option) optB \<equiv> (optA \<le> optB \<and> \<not> optB \<le> optA)\<close>

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

lemma min_1_6_some:
  shows \<open>min1_6 \<noteq> None\<close>
  unfolding min1_6_def by blast

lemma min_1_7_some:
  shows \<open>min1_7 \<noteq> None\<close>
  unfolding min1_7_def by blast

end