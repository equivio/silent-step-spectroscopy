theory test_srbb
  imports 
Main 
"../HML/HML_SRBB"
"HOL-Library.Extended_Nat"

begin

context LTS_Tau
begin

function sr_depth:: "('a, 'i)HML \<Rightarrow> nat" and
  sr_depth_chi:: "('a, 'i)HML_neg \<Rightarrow> nat" where
"sr_depth HML_true = 0" |
"sr_depth (HML_poss _ \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_silent \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_internal \<phi>) = sr_depth \<phi>" |
"sr_depth (HML_conj I F) = Max ({0} \<union> {sr_depth_chi(F i)|i. i \<in> I})" |
"sr_depth_chi (HML_just (HML_internal \<phi>)) = 1 + sr_depth \<phi>" |
"sr_depth_chi (HML_just \<phi>) = sr_depth \<phi>" |
"sr_depth_chi (HML_not \<phi>) = sr_depth \<phi>"

                      apply (metis HML.exhaust HML_neg.exhaust obj_sumE)
                      apply simp+
  sorry
termination sorry

fun sr_depth_srbb:: "('a, 'i)HML \<Rightarrow> enat" where
"sr_depth_srbb \<phi> = (if is_hml_srbb \<phi> then sr_depth \<phi> else \<infinity>)"
end
end