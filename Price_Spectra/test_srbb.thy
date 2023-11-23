theory test_srbb
  imports 
Main 
"../HML/HML_SRBB"
"HOL-Library.Extended_Nat"

begin

context LTS_Tau
begin

function sr_depth:: "('a, 'i)HML \<Rightarrow> enat" and
  sr_depth_chi:: "('a, 'i)HML_neg \<Rightarrow> enat" where
"sr_depth HML_true = 0" |
"sr_depth (HML_poss _ \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_silent \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_internal \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_conj I F) = (if finite {sr_depth_chi(F i)|i. i \<in> I} then Max ({0} \<union> {sr_depth_chi(F i)|i. i \<in> I})
else \<infinity>)" |
"sr_depth_chi (HML_just \<phi>) = (if (\<exists>\<psi>. \<phi> = HML_internal \<psi>) then 1 + sr_depth \<phi> else sr_depth \<phi>)" |
"sr_depth_chi (HML_not \<phi>) = sr_depth \<phi>"

  by ((metis HML.exhaust HML_neg.exhaust obj_sumE), simp+)

termination sorry

(*The nat set has a supremum in nat*)
definition has_supr :: "nat set \<Rightarrow> bool" where
  "has_supr S \<equiv> (\<exists>sup. (\<forall>x \<in> S. x \<le> sup) \<and> (\<forall>y. \<forall>x \<in> S. x \<le> y \<longrightarrow> sup \<le> y))"


fun sr_depth_srbb:: "('a, 'i)HML \<Rightarrow> enat" where
"sr_depth_srbb \<phi> = (if is_hml_srbb \<phi> then sr_depth \<phi> else \<infinity>)"
end
end