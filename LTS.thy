theory LTS
  imports Main
begin

locale LTS =
  fixes step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80)

locale LTS_Tau =
  LTS step
    for step :: "'s \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool" ("_ \<mapsto> _ _" [70,70,70] 80) +
  fixes \<tau> :: 'a
begin

inductive silent_reachable :: "'s \<Rightarrow> 's \<Rightarrow> bool"  (infix "\<Zsurj>" 80)
  where
    "p \<Zsurj> p" |
    "p \<Zsurj> p''" if "p \<mapsto> \<tau> p'" and "p' \<Zsurj> p''"

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