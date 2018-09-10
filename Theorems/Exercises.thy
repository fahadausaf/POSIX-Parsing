theory Exercises
  imports Spec "~~/src/HOL/Library/Infinite_Set"
begin

section {* Some Fun Facts *}

fun
 zeroable :: "rexp \<Rightarrow> bool"
where
  "zeroable (ZERO) \<longleftrightarrow> True"
| "zeroable (ONE) \<longleftrightarrow> False"
| "zeroable (CHAR c) \<longleftrightarrow> False"
| "zeroable (ALT r1 r2) \<longleftrightarrow> zeroable r1 \<and> zeroable r2"
| "zeroable (SEQ r1 r2) \<longleftrightarrow> zeroable r1 \<or> zeroable r2"
| "zeroable (STAR r) \<longleftrightarrow> False"

lemma zeroable_correctness:
  shows "zeroable r \<longleftrightarrow> L r = {}"
by(induct r)(auto simp add: Sequ_def)


fun
 atmostempty :: "rexp \<Rightarrow> bool"
where
  "atmostempty (ZERO) \<longleftrightarrow> True"
| "atmostempty (ONE) \<longleftrightarrow> True"
| "atmostempty (CHAR c) \<longleftrightarrow> False"
| "atmostempty (ALT r1 r2) \<longleftrightarrow> atmostempty r1 \<and> atmostempty r2"
| "atmostempty (SEQ r1 r2) \<longleftrightarrow> 
     zeroable r1 \<or> zeroable r2 \<or> (atmostempty r1 \<and> atmostempty r2)"
| "atmostempty (STAR r) = atmostempty r"



fun
 somechars :: "rexp \<Rightarrow> bool"
where
  "somechars (ZERO) \<longleftrightarrow> False"
| "somechars (ONE) \<longleftrightarrow> False"
| "somechars (CHAR c) \<longleftrightarrow> True"
| "somechars (ALT r1 r2) \<longleftrightarrow> somechars r1 \<or> somechars r2"
| "somechars (SEQ r1 r2) \<longleftrightarrow> 
      (\<not> zeroable r1 \<and> somechars r2) \<or> (\<not> zeroable r2 \<and> somechars r1) \<or> 
      (somechars r1 \<and> nullable r2) \<or> (somechars r2 \<and> nullable r1)"
| "somechars (STAR r) \<longleftrightarrow> somechars r"

lemma somechars_correctness:
  shows "somechars r \<longleftrightarrow> (\<exists>s. s \<noteq> [] \<and> s \<in> L r)"
apply(induct r)
apply(simp_all add: zeroable_correctness nullable_correctness Sequ_def)
using Nil_is_append_conv apply blast
apply blast
apply(auto)
using Star_cstring
  by (metis concat_eq_Nil_conv) 

lemma atmostempty_correctness_aux:
  shows "atmostempty r \<longleftrightarrow> \<not> somechars r"
apply(induct r)
apply(simp_all)
apply(auto simp add: zeroable_correctness nullable_correctness somechars_correctness)
done

lemma atmostempty_correctness:
  shows "atmostempty r \<longleftrightarrow> L r \<subseteq> {[]}"
by(auto simp add: atmostempty_correctness_aux somechars_correctness)

fun
 leastsinglechar :: "rexp \<Rightarrow> bool"
where
  "leastsinglechar (ZERO) \<longleftrightarrow> False"
| "leastsinglechar (ONE) \<longleftrightarrow> False"
| "leastsinglechar (CHAR c) \<longleftrightarrow> True"
| "leastsinglechar (ALT r1 r2) \<longleftrightarrow> leastsinglechar r1 \<or> leastsinglechar r2"
| "leastsinglechar (SEQ r1 r2) \<longleftrightarrow> 
      (if (zeroable r1 \<or> zeroable r2) then False
       else ((nullable r1 \<and> leastsinglechar r2) \<or> (nullable r2 \<and> leastsinglechar r1)))"
| "leastsinglechar (STAR r) \<longleftrightarrow> leastsinglechar r"

lemma leastsinglechar_correctness:
  "leastsinglechar r \<longleftrightarrow> (\<exists>c. [c] \<in> L r)"
  apply(induct r)
  apply(simp)
  apply(simp)
  apply(simp)
  prefer 2
  apply(simp)
  apply(blast)
  prefer 2
  apply(simp)
  using Star.step Star_decomp apply fastforce
  apply(simp add: Sequ_def zeroable_correctness nullable_correctness)
  by (metis append_Nil append_is_Nil_conv butlast_append butlast_snoc)

fun
 infinitestrings :: "rexp \<Rightarrow> bool"
where
  "infinitestrings (ZERO) = False"
| "infinitestrings (ONE) = False"
| "infinitestrings (CHAR c) = False"
| "infinitestrings (ALT r1 r2) = (infinitestrings r1 \<or> infinitestrings r2)"
| "infinitestrings (SEQ r1 r2) \<longleftrightarrow> 
      (\<not> zeroable r1 \<and> infinitestrings r2) \<or> (\<not> zeroable r2 \<and> infinitestrings r1)"
| "infinitestrings (STAR r) = (\<not> atmostempty r)"





lemma Star_atmostempty:
  assumes "A \<subseteq> {[]}"
  shows "A\<star> \<subseteq> {[]}"
using assms
using Star_cstring concat_eq_Nil_conv empty_iff insert_iff subsetI subset_singletonD by fastforce

lemma Star_empty_string_finite:
  shows "finite ({[]}\<star>)"
using Star_atmostempty infinite_super by auto

lemma Star_empty_finite:
  shows "finite ({}\<star>)"
using Star_atmostempty infinite_super by auto

lemma Star_concat_replicate:
  assumes "s \<in> A"
  shows "concat (replicate n s) \<in> A\<star>"
using assms
by (induct n) (auto)


lemma concat_replicate_inj:
  assumes "concat (replicate n s) = concat (replicate m s)" "s \<noteq> []"
  shows "n = m"
using assms
apply(induct n arbitrary: m)
apply(auto)[1]
apply(auto)
apply(case_tac m)
apply(clarify)
apply(simp only: replicate.simps concat.simps)
apply blast
by simp

lemma A0:
  assumes "finite (A ;; B)" "B \<noteq> {}"
  shows "finite A"
apply(subgoal_tac "\<exists>s. s \<in> B")
apply(erule exE)
apply(subgoal_tac "finite {s1 @ s |s1. s1 \<in> A}")
apply(rule_tac f="\<lambda>s1. s1 @ s" in finite_imageD)
apply(simp add: image_def)
apply(smt Collect_cong)
apply(simp add: inj_on_def)
apply(rule_tac B="A ;; B" in finite_subset)
apply(auto simp add: Sequ_def)[1]
apply(rule assms(1))
using assms(2) by auto

lemma A1:
  assumes "finite (A ;; B)" "A \<noteq> {}"
  shows "finite B"
apply(subgoal_tac "\<exists>s. s \<in> A")
apply(erule exE)
apply(subgoal_tac "finite {s @ s1 |s1. s1 \<in> B}")
apply(rule_tac f="\<lambda>s1. s @ s1" in finite_imageD)
apply(simp add: image_def)
apply(smt Collect_cong)
apply(simp add: inj_on_def)
apply(rule_tac B="A ;; B" in finite_subset)
apply(auto simp add: Sequ_def)[1]
apply(rule assms(1))
using assms(2) by auto

lemma Sequ_Prod_finite:
  assumes "A \<noteq> {}" "B \<noteq> {}"
  shows "finite (A ;; B) \<longleftrightarrow> (finite (A \<times> B))"
apply(rule iffI)
apply(rule finite_cartesian_product)
apply(erule A0)
apply(rule assms(2))
apply(erule A1)
apply(rule assms(1))
apply(simp add: Sequ_def)
apply(rule finite_image_set2)
apply(drule finite_cartesian_productD1)
apply(rule assms(2))
apply(simp)
apply(drule finite_cartesian_productD2)
apply(rule assms(1))
apply(simp)
done


lemma Star_non_empty_string_infinite:
  assumes "s \<in> A" " s \<noteq> []"
  shows "infinite (A\<star>)"
proof -
  have "inj (\<lambda>n. concat (replicate n s))" 
  using assms(2) concat_replicate_inj
    by(auto simp add: inj_on_def)
  moreover
  have "infinite (UNIV::nat set)" by simp
  ultimately
  have "infinite ((\<lambda>n. concat (replicate n s)) ` UNIV)"
   by (simp add: range_inj_infinite)
  moreover
  have "((\<lambda>n. concat (replicate n s)) ` UNIV) \<subseteq> (A\<star>)"
    using Star_concat_replicate assms(1) by auto
  ultimately show "infinite (A\<star>)" 
  using infinite_super by auto
qed

lemma infinitestrings_correctness:
  shows "infinitestrings r \<longleftrightarrow> infinite (L r)"
apply(induct r)
apply(simp_all)
apply(simp add: zeroable_correctness)
apply(rule iffI)
apply(erule disjE)
apply(subst Sequ_Prod_finite)
apply(auto)[2]
using finite_cartesian_productD2 apply blast
apply(subst Sequ_Prod_finite)
apply(auto)[2]
using finite_cartesian_productD1 apply blast
apply(subgoal_tac "L r1 \<noteq> {} \<and> L r2 \<noteq> {}")
prefer 2
apply(auto simp add: Sequ_def)[1]
apply(subst (asm) Sequ_Prod_finite)
apply(auto)[2]
apply(auto)[1]
apply(simp add: atmostempty_correctness)
apply(rule iffI)
apply (metis Star_empty_finite Star_empty_string_finite subset_singletonD)
using Star_non_empty_string_infinite apply blast
done

unused_thms

end