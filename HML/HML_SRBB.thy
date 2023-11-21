theory HML_SRBB
imports Main HML
begin

context LTS_Tau
begin
inductive is_hml_srbb :: "('a, 'i) HML \<Rightarrow> bool" 
  and is_hml_chi :: "('a, 'i) HML  \<Rightarrow> bool" where
srbb_true: "is_hml_srbb (HML_true)" |
srbb_eps: "is_hml_srbb (HML_internal \<phi>)" if "is_hml_chi \<phi>"|
srbb_conj: "is_hml_srbb (HML_conj I F)" if 
"\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_not (HML_internal \<phi>)) \<or> ((F i)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi \<phi>)" |

chi_poss: "is_hml_chi (HML_poss \<alpha> \<phi>)" if "is_hml_srbb \<phi>" |
(*\<And>{\<psi>, \<psi>, ...} with \<psi> ::= \<not>\<langle>\<epsilon>\<rangle>\<phi> | \<langle>\<epsilon>\<rangle>\<phi>*)
chi_conj: "is_hml_chi (HML_conj I F)" if 
"(\<forall>i \<in> I. (\<exists>\<phi>. ((F i)) = (HML_not (HML_internal \<phi>)) \<or> ((F i)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi \<phi>))" |
(*\<And>{\<langle>\<alpha>\<rangle>\<phi>, \<psi>, \<psi>, ...}*)
chi_conj_bb: "is_hml_chi (HML_conj I F)" if
"((\<exists>i \<in> I. \<exists>\<alpha> \<phi>. (F i) = (HML_just (HML_poss \<alpha> \<phi>)) \<and> is_hml_chi \<phi>
    \<and> (\<forall>j \<in> I. \<exists>\<alpha> \<phi>. (F j) = (HML_just (HML_poss \<alpha> \<phi>)) \<longrightarrow> i = j) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> 
      (\<exists>\<phi>. ((F j)) = (HML_not (HML_internal \<phi>)) \<or> ((F j)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi \<phi>))))" |
(*\<And>{(\<tau>)\<phi>, \<psi>, \<psi>, ...}*)
chi_conj_bb_tau: "is_hml_chi (HML_conj I F)" if
"((\<exists>i \<in> I. \<exists>\<phi>. (F i) = (HML_just (HML_internal \<phi>)) \<and> is_hml_chi \<phi>
    \<and> (\<forall>j \<in> I. \<exists>\<alpha> \<phi>. (F j) = (HML_just (HML_poss \<alpha> \<phi>)) \<longrightarrow> i = j) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> 
      (\<exists>\<phi>. ((F j)) = (HML_not (HML_internal \<phi>)) \<or> ((F j)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi \<phi>))))" |
(*\<And>{\<not>\<langle>\<tau>\<rangle>T, \<psi>, \<psi>, ...}*)
chi_conj_sr: "is_hml_chi (HML_conj I F)" if
"(\<exists>i \<in> I. (F i) = (HML_not (HML_silent HML_true))
    \<and> (\<forall>j \<in> I. (F j) = (HML_not (HML_silent HML_true))) 
    \<and> (\<forall>j \<in> I. i \<noteq> j \<longrightarrow> (\<exists>\<phi>. ((F j)) = (HML_not (HML_internal \<phi>)) \<or> ((F j)) = HML_just (HML_internal \<phi>) \<and> is_hml_chi \<phi>)))"

find_theorems is_hml_srbb

find_theorems is_hml_chi

definition HML_SRBB :: \<open>('a, 'i) HML set\<close> where
\<open>HML_SRBB \<equiv> {\<phi>. is_hml_srbb \<phi>}\<close>

end

end