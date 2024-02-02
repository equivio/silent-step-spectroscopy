section \<open>Misc\<close>
theory Misc
  imports Main
begin
fun pairs :: "'a list \<Rightarrow> ('a \<times> 'a) list" where
  "pairs p = (if length p \<le> 1 then [] else (hd p, hd (tl p)) # pairs (tl p))"

lemma pairs_is_zip:
  shows "pairs p \<equiv> zip (p) (tl p)"
  by (induct p, simp_all, smt (verit, ccfv_threshold) One_nat_def Suc_lessI pairs.elims length_0_conv length_Suc_conv length_greater_0_conv linorder_not_less list.collapse list.sel(3) nat_neq_iff zip.simps(1) zip_Cons_Cons)

(* some intuition on this definition*)
lemma %invisible "pairs [1,2,3] = [(1,2), (2,3)]" by simp
lemma %invisible empty_pair: "pairs [] = []" by simp
lemma %invisible single_pair: "pairs [x] = []" by simp
lemma %invisible pairs_append_single: "pairs (p @ [gn]) = (if length p \<ge> 1 then (pairs p) @ [(last p, gn)] else [])" 
  by (induct p, simp_all add: not_less_eq_eq)

end