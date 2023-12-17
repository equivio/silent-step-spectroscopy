theory LTS
  imports Main
begin

locale LTS =
  fixes step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
begin
abbreviation step_set ("_ \<mapsto>S _ _" [70,70,70] 80) where "P \<mapsto>S \<alpha> Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<mapsto> \<alpha> q"
end

locale LTS_Tau =
  LTS step
    for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
    fixes \<tau> :: 'a
begin

abbreviation non_tau_step ("_ \<mapsto>a _ _" [70,70,70] 80) where
  "p \<mapsto>a \<alpha> q \<equiv> (if \<alpha> = \<tau> then p = q else p \<mapsto>\<alpha> q)" 

inductive silent_reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>" 80)
  where
    "p \<Zsurj> p" |
    "p \<Zsurj> p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj> p''"

abbreviation silent_reachable_set (infix "\<Zsurj>S" 80) where "P \<Zsurj>S Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<Zsurj> q"
abbreviation non_tau_step_set ("_ \<mapsto>aS _ _" [70,70,70] 80) where "P \<mapsto>aS \<alpha> Q \<equiv> \<forall>p \<in> P. \<forall>q \<in> Q. p \<mapsto>a \<alpha> q"

end (* locale LTS_Tau *)

locale Inhabited_LTS = LTS step
  for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
  fixes left :: 's
    and right :: 's
  assumes "(left::'s) \<noteq> (right::'s)"

locale Inhabited_Tau_LTS = Inhabited_LTS step left right + LTS_Tau step \<tau>
  for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)
  and left :: 's
  and right :: 's
  and \<tau> :: 'a

end (* theory LTS *)