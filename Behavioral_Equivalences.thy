theory Behavioral_Equivalences
imports Main
begin

locale lts = 
fixes step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto> _ _\<close> [70,70,70] 80)
begin

abbreviation derivatives :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's set\<close> where
  \<open>derivatives p \<alpha> \<equiv> {p'. p \<mapsto> \<alpha> p'}\<close>

end

locale lts_tau =
lts step
for step :: \<open>'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool\<close> (\<open>_ \<mapsto> _ _\<close> [70,70,70] 80) +
  fixes
    \<tau> :: 'a and
    \<epsilon> :: "'b"
begin

inductive silent_reachable :: \<open>'s \<Rightarrow> 's \<Rightarrow> bool\<close> (infix \<open>\<Zsurj>\<close> 80) where
  refl: \<open>p \<Zsurj> p\<close> |
  step: \<open>p \<Zsurj> p''\<close> if \<open>p \<mapsto> \<tau> p'\<close> \<open>p' \<Zsurj> p''\<close>
  
thm silent_reachable.induct
thm silent_reachable.refl
thm HOL.refl

lemma silent_reachable_trans:
  assumes
    \<open>p \<Zsurj> p'\<close>
    \<open>p' \<Zsurj> p''\<close>
  shows
    \<open>p \<Zsurj> p''\<close>
using assms silent_reachable.step
by (induct, blast+)


end

end