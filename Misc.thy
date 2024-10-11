section \<open>Misc\<close>
theory Misc
  imports Main
begin
text \<open>This section formalizes @{text \<open>pairs\<close>}, which is used to
      give an alternate definition for the energy level of a play.\<close>
fun pairs :: \<open>'a list \<Rightarrow> ('a \<times> 'a) list\<close> where
  \<open>pairs p = (if length p \<le> 1 then [] else (hd p, hd (tl p)) # pairs (tl p))\<close>

lemma pairs_is_zip:
  shows \<open>pairs p \<equiv> zip (p) (tl p)\<close>
  by (induct p, simp_all, smt (verit, ccfv_threshold) One_nat_def Suc_lessI pairs.elims length_0_conv length_Suc_conv length_greater_0_conv linorder_not_less list.collapse list.sel(3) nat_neq_iff zip.simps(1) zip_Cons_Cons)

(* some intuition on this definition*)
lemma %invisible \<open>pairs [1,2,3] = [(1,2), (2,3)]\<close> by simp
lemma %invisible empty_pair: \<open>pairs [] = []\<close> by simp
lemma %invisible single_pair: \<open>pairs [x] = []\<close> by simp
lemma %invisible pairs_append_single: \<open>pairs (p @ [gn]) = (if length p \<ge> 1 then (pairs p) @ [(last p, gn)] else [])\<close> 
  by (induct p, simp_all add: not_less_eq_eq)

end