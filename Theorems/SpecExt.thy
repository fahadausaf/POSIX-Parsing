   
theory SpecExt
  imports Main "~~/src/HOL/Library/Sublist"
begin

section {* Sequential Composition of Languages *}

definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ ;; _" [100,100] 100)
where 
  "A ;; B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"

text {* Two Simple Properties about Sequential Composition *}

lemma Sequ_empty_string [simp]:
  shows "A ;; {[]} = A"
  and   "{[]} ;; A = A"
by (simp_all add: Sequ_def)

lemma Sequ_empty [simp]:
  shows "A ;; {} = {}"
  and   "{} ;; A = {}"
by (simp_all add: Sequ_def)

lemma Sequ_assoc:
  shows "(A ;; B) ;; C = A ;; (B ;; C)"
apply(auto simp add: Sequ_def)
apply blast
by (metis append_assoc)

lemma Sequ_Union_in:
  shows "(A ;; (\<Union>x\<in> B. C x)) = (\<Union>x\<in> B. A ;; C x)" 
by (auto simp add: Sequ_def)

section {* Semantic Derivative (Left Quotient) of Languages *}

definition
  Der :: "char \<Rightarrow> string set \<Rightarrow> string set"
where
  "Der c A \<equiv> {s. c # s \<in> A}"

definition
  Ders :: "string \<Rightarrow> string set \<Rightarrow> string set"
where
  "Ders s A \<equiv> {s'. s @ s' \<in> A}"

lemma Der_null [simp]:
  shows "Der c {} = {}"
unfolding Der_def
by auto

lemma Der_empty [simp]:
  shows "Der c {[]} = {}"
unfolding Der_def
by auto

lemma Der_char [simp]:
  shows "Der c {[d]} = (if c = d then {[]} else {})"
unfolding Der_def
by auto

lemma Der_union [simp]:
  shows "Der c (A \<union> B) = Der c A \<union> Der c B"
unfolding Der_def
by auto

lemma Der_UNION [simp]: 
  shows "Der c (\<Union>x\<in>A. B x) = (\<Union>x\<in>A. Der c (B x))"
by (auto simp add: Der_def)

lemma Der_Sequ [simp]:
  shows "Der c (A ;; B) = (Der c A) ;; B \<union> (if [] \<in> A then Der c B else {})"
unfolding Der_def Sequ_def
  by (auto simp add: Cons_eq_append_conv)


section {* Kleene Star for Languages *}

inductive_set
  Star :: "string set \<Rightarrow> string set" ("_\<star>" [101] 102)
  for A :: "string set"
where
  start[intro]: "[] \<in> A\<star>"
| step[intro]:  "\<lbrakk>s1 \<in> A; s2 \<in> A\<star>\<rbrakk> \<Longrightarrow> s1 @ s2 \<in> A\<star>"

(* Arden's lemma *)

lemma Star_cases:
  shows "A\<star> = {[]} \<union> A ;; A\<star>"
unfolding Sequ_def
by (auto) (metis Star.simps)

lemma Star_decomp: 
  assumes "c # x \<in> A\<star>" 
  shows "\<exists>s1 s2. x = s1 @ s2 \<and> c # s1 \<in> A \<and> s2 \<in> A\<star>"
using assms
by (induct x\<equiv>"c # x" rule: Star.induct) 
   (auto simp add: append_eq_Cons_conv)

lemma Star_Der_Sequ: 
  shows "Der c (A\<star>) \<subseteq> (Der c A) ;; A\<star>"
unfolding Der_def Sequ_def
by(auto simp add: Star_decomp)


lemma Der_star [simp]:
  shows "Der c (A\<star>) = (Der c A) ;; A\<star>"
proof -    
  have "Der c (A\<star>) = Der c ({[]} \<union> A ;; A\<star>)"  
    by (simp only: Star_cases[symmetric])
  also have "... = Der c (A ;; A\<star>)"
    by (simp only: Der_union Der_empty) (simp)
  also have "... = (Der c A) ;; A\<star> \<union> (if [] \<in> A then Der c (A\<star>) else {})"
    by simp
  also have "... =  (Der c A) ;; A\<star>"
    using Star_Der_Sequ by auto
  finally show "Der c (A\<star>) = (Der c A) ;; A\<star>" .
qed

section {* Power operation for Sets *}

fun 
  Pow :: "string set \<Rightarrow> nat \<Rightarrow> string set" ("_ \<up> _" [101, 102] 101)
where
   "A \<up> 0 = {[]}"
|  "A \<up> (Suc n) = A ;; (A \<up> n)"

lemma Pow_empty [simp]:
  shows "[] \<in> A \<up> n \<longleftrightarrow> (n = 0 \<or> [] \<in> A)"
by(induct n) (auto simp add: Sequ_def)

lemma Pow_Suc_rev:
  "A \<up> (Suc n) =  (A \<up> n) ;; A"
apply(induct n arbitrary: A)
apply(simp_all)
by (metis Sequ_assoc)


lemma Pow_decomp: 
  assumes "c # x \<in> A \<up> n" 
  shows "\<exists>s1 s2. x = s1 @ s2 \<and> c # s1 \<in> A \<and> s2 \<in> A \<up> (n - 1)"
using assms
apply(induct n) 
apply(auto simp add: Cons_eq_append_conv Sequ_def)
apply(case_tac n)
apply(auto simp add: Sequ_def)
apply(blast)
done

lemma Star_Pow:
  assumes "s \<in> A\<star>"
  shows "\<exists>n. s \<in> A \<up> n"
using assms
apply(induct)
apply(auto)
apply(rule_tac x="Suc n" in exI)
apply(auto simp add: Sequ_def)
done

lemma Pow_Star:
  assumes "s \<in> A \<up> n"
  shows "s \<in> A\<star>"
using assms
apply(induct n arbitrary: s)
apply(auto simp add: Sequ_def)
done

lemma Der_Pow_0:
  shows "Der c (A \<up> 0) = {}"
by(simp add: Der_def)

lemma Der_Pow_Suc:
  shows "Der c (A \<up> (Suc n)) = (Der c A) ;; (A \<up> n)"
unfolding Der_def Sequ_def 
apply(auto simp add: Cons_eq_append_conv Sequ_def dest!: Pow_decomp)
apply(case_tac n)
apply(force simp add: Sequ_def)+
done

lemma Der_Pow [simp]:
  shows "Der c (A \<up> n) = (if n = 0 then {} else (Der c A) ;; (A \<up> (n - 1)))"
apply(case_tac n)
apply(simp_all del: Pow.simps add: Der_Pow_0 Der_Pow_Suc)
done

lemma Der_Pow_Sequ [simp]:
  shows "Der c (A ;; A \<up> n) = (Der c A) ;; (A \<up> n)"
by (simp only: Pow.simps[symmetric] Der_Pow) (simp)


lemma Pow_Sequ_Un:
  assumes "0 < x"
  shows "(\<Union>n \<in> {..x}. (A \<up> n)) = ({[]} \<union> (\<Union>n \<in> {..x - Suc 0}. A ;; (A \<up> n)))"
using assms
apply(auto simp add: Sequ_def)
apply(smt Pow.elims Sequ_def Suc_le_mono Suc_pred atMost_iff empty_iff insert_iff mem_Collect_eq)
apply(rule_tac x="Suc xa" in bexI)
apply(auto simp add: Sequ_def)
done

lemma Pow_Sequ_Un2:
  assumes "0 < x"
  shows "(\<Union>n \<in> {x..}. (A \<up> n)) = (\<Union>n \<in> {x - Suc 0..}. A ;; (A \<up> n))"
using assms
apply(auto simp add: Sequ_def)
apply(case_tac n)
apply(auto simp add: Sequ_def)
apply fastforce
apply(case_tac x)
apply(auto)
apply(rule_tac x="Suc xa" in bexI)
apply(auto simp add: Sequ_def)
done

section {* Regular Expressions *}

datatype rexp =
  ZERO
| ONE
| CHAR char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp
| UPNTIMES rexp nat
| NTIMES rexp nat
| FROMNTIMES rexp nat
| NMTIMES rexp nat nat

section {* Semantics of Regular Expressions *}
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (ZERO) = {}"
| "L (ONE) = {[]}"
| "L (CHAR c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"
| "L (STAR r) = (L r)\<star>"
| "L (UPNTIMES r n) = (\<Union>i\<in>{..n} . (L r) \<up> i)"
| "L (NTIMES r n) = (L r) \<up> n"
| "L (FROMNTIMES r n) = (\<Union>i\<in>{n..} . (L r) \<up> i)"
| "L (NMTIMES r n m) = (\<Union>i\<in>{n..m} . (L r) \<up> i)" 

section {* Nullable, Derivatives *}

fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (ZERO) = False"
| "nullable (ONE) = True"
| "nullable (CHAR c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (STAR r) = True"
| "nullable (UPNTIMES r n) = True"
| "nullable (NTIMES r n) = (if n = 0 then True else nullable r)"
| "nullable (FROMNTIMES r n) = (if n = 0 then True else nullable r)"
| "nullable (NMTIMES r n m) = (if m < n then False else (if n = 0 then True else nullable r))"

fun
 der :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "der c (ZERO) = ZERO"
| "der c (ONE) = ZERO"
| "der c (CHAR d) = (if c = d then ONE else ZERO)"
| "der c (ALT r1 r2) = ALT (der c r1) (der c r2)"
| "der c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2)"
| "der c (STAR r) = SEQ (der c r) (STAR r)"
| "der c (UPNTIMES r n) = (if n = 0 then ZERO else SEQ (der c r) (UPNTIMES r (n - 1)))"
| "der c (NTIMES r n) = (if n = 0 then ZERO else SEQ (der c r) (NTIMES r (n - 1)))"
| "der c (FROMNTIMES r n) = 
     (if n = 0 
      then SEQ (der c r) (STAR r)
      else SEQ (der c r) (FROMNTIMES r (n - 1)))"
| "der c (NMTIMES r n m) = 
     (if m < n then ZERO 
      else (if n = 0 then (if m = 0 then ZERO else 
                           SEQ (der c r) (UPNTIMES r (m - 1))) else 
                           SEQ (der c r) (NMTIMES r (n - 1) (m - 1))))" 

fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
by(induct r) (auto simp add: Sequ_def) 


lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
apply(induct r) 
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
prefer 2
apply(simp add: nullable_correctness del: Der_UNION)
apply(simp add: nullable_correctness del: Der_UNION)
apply(rule impI)
apply(subst Sequ_Union_in)
apply(subst Der_Pow_Sequ[symmetric])
apply(subst Pow.simps[symmetric])
apply(subst Der_UNION[symmetric])
apply(subst Pow_Sequ_Un)
apply(simp)
apply(simp only: Der_union Der_empty)
    apply(simp)
(* FROMNTIMES *)    
   apply(simp add: nullable_correctness del: Der_UNION)
  apply(rule conjI)
prefer 2    
apply(subst Sequ_Union_in)
apply(subst Der_Pow_Sequ[symmetric])
apply(subst Pow.simps[symmetric])
apply(case_tac x2)
prefer 2
apply(subst Pow_Sequ_Un2)
apply(simp)
apply(simp)
    apply(auto simp add: Sequ_def Der_def)[1]
   apply(auto simp add: Sequ_def split: if_splits)[1]
  using Star_Pow apply fastforce
  using Pow_Star apply blast
(* NMTIMES *)    
apply(simp add: nullable_correctness del: Der_UNION)
apply(rule impI)
apply(rule conjI)
apply(rule impI)
apply(subst Sequ_Union_in)
apply(subst Der_Pow_Sequ[symmetric])
apply(subst Pow.simps[symmetric])
apply(subst Der_UNION[symmetric])
apply(case_tac x3a)
apply(simp)
apply(clarify)
apply(auto simp add: Sequ_def Der_def Cons_eq_append_conv)[1]
apply(rule_tac x="Suc xa" in bexI)
apply(auto simp add: Sequ_def)[2]
apply (metis append_Cons)
apply (metis (no_types, hide_lams) Pow_decomp atMost_iff diff_Suc_eq_diff_pred diff_is_0_eq)
apply(rule impI)+
apply(subst Sequ_Union_in)
apply(subst Der_Pow_Sequ[symmetric])
apply(subst Pow.simps[symmetric])
apply(subst Der_UNION[symmetric])
apply(case_tac x2)
apply(simp)
apply(simp del: Pow.simps)
apply(auto simp add: Sequ_def Der_def)
apply (metis One_nat_def Suc_le_D Suc_le_mono atLeastAtMost_iff diff_Suc_1 not_le)
by fastforce



lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
by (induct s arbitrary: r)
   (simp_all add: Ders_def der_correctness Der_def)


section {* Values *}

datatype val = 
  Void
| Char char
| Seq val val
| Right val
| Left val
| Stars "val list"


section {* The string behind a value *}

fun 
  flat :: "val \<Rightarrow> string"
where
  "flat (Void) = []"
| "flat (Char c) = [c]"
| "flat (Left v) = flat v"
| "flat (Right v) = flat v"
| "flat (Seq v1 v2) = (flat v1) @ (flat v2)"
| "flat (Stars []) = []"
| "flat (Stars (v#vs)) = (flat v) @ (flat (Stars vs))" 

abbreviation
  "flats vs \<equiv> concat (map flat vs)"

lemma flat_Stars [simp]:
 "flat (Stars vs) = flats vs"
by (induct vs) (auto)

lemma Star_concat:
  assumes "\<forall>s \<in> set ss. s \<in> A"  
  shows "concat ss \<in> A\<star>"
using assms by (induct ss) (auto)

lemma Star_cstring:
  assumes "s \<in> A\<star>"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A \<and> s \<noteq> [])"
using assms
apply(induct rule: Star.induct)
apply(auto)[1]
apply(rule_tac x="[]" in exI)
apply(simp)
apply(erule exE)
apply(clarify)
apply(case_tac "s1 = []")
apply(rule_tac x="ss" in exI)
apply(simp)
apply(rule_tac x="s1#ss" in exI)
apply(simp)
done

lemma Aux:
  assumes "\<forall>s\<in>set ss. s = []"
  shows "concat ss = []"
using assms
by (induct ss) (auto)

lemma Pow_cstring_nonempty:
  assumes "s \<in> A \<up> n"
  shows "\<exists>ss. concat ss = s \<and> length ss \<le> n \<and> (\<forall>s \<in> set ss. s \<in> A \<and> s \<noteq> [])"
using assms
apply(induct n arbitrary: s)
apply(auto)
apply(simp add: Sequ_def)
apply(erule exE)+
apply(clarify)
apply(drule_tac x="s2" in meta_spec)
apply(simp)
apply(clarify)
apply(case_tac "s1 = []")
apply(simp)
apply(rule_tac x="ss" in exI)
apply(simp)
apply(rule_tac x="s1 # ss" in exI)
apply(simp)
done

lemma Pow_cstring:
  assumes "s \<in> A \<up> n"
  shows "\<exists>ss1 ss2. concat (ss1 @ ss2) = s \<and> length (ss1 @ ss2) = n \<and> 
         (\<forall>s \<in> set ss1. s \<in> A \<and> s \<noteq> []) \<and> (\<forall>s \<in> set ss2. s \<in> A \<and> s = [])"
using assms
apply(induct n arbitrary: s)
apply(auto)[1]
apply(simp only: Pow_Suc_rev)
apply(simp add: Sequ_def)
apply(erule exE)+
apply(clarify)
apply(drule_tac x="s1" in meta_spec)
apply(simp)
apply(erule exE)+
apply(clarify)
apply(case_tac "s2 = []")
apply(simp)
apply(rule_tac x="ss1" in exI)
apply(rule_tac x="s2#ss2" in exI)
apply(simp)
apply(rule_tac x="ss1 @ [s2]" in exI)
apply(rule_tac x="ss2" in exI)
apply(simp)
apply(subst Aux)
apply(auto)[1]
apply(subst Aux)
apply(auto)[1]
apply(simp)
done


section {* Lexical Values *}



inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<Turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<Turnstile> v1 : r1; \<Turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile>  Seq v1 v2 : SEQ r1 r2"
| "\<Turnstile> v1 : r1 \<Longrightarrow> \<Turnstile> Left v1 : ALT r1 r2"
| "\<Turnstile> v2 : r2 \<Longrightarrow> \<Turnstile> Right v2 : ALT r1 r2"
| "\<Turnstile> Void : ONE"
| "\<Turnstile> Char c : CHAR c"
| "\<lbrakk>\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v \<noteq> []\<rbrakk> \<Longrightarrow> \<Turnstile> Stars vs : STAR r"
| "\<lbrakk>\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v \<noteq> []; length vs \<le> n\<rbrakk> \<Longrightarrow> \<Turnstile> Stars vs : UPNTIMES r n"
| "\<lbrakk>\<forall>v \<in> set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []; 
    \<forall>v \<in> set vs2. \<Turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<Turnstile> Stars (vs1 @ vs2) : NTIMES r n"
| "\<lbrakk>\<forall>v \<in> set vs1. \<Turnstile> v : r  \<and> flat v \<noteq> []; 
    \<forall>v \<in> set vs2. \<Turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n\<rbrakk> \<Longrightarrow> \<Turnstile> Stars (vs1 @ vs2) : FROMNTIMES r n"
| "\<lbrakk>\<forall>v \<in> set vs. \<Turnstile> v : r  \<and> flat v \<noteq> []; length vs > n\<rbrakk> \<Longrightarrow> \<Turnstile> Stars vs : FROMNTIMES r n"
| "\<lbrakk>\<forall>v \<in> set vs1. \<Turnstile> v : r \<and> flat v \<noteq> [];
    \<forall>v \<in> set vs2. \<Turnstile> v : r \<and> flat v = []; 
    length (vs1 @ vs2) = n; length (vs1 @ vs2) \<le> m\<rbrakk> \<Longrightarrow> \<Turnstile> Stars (vs1 @ vs2) : NMTIMES r n m"
| "\<lbrakk>\<forall>v \<in> set vs. \<Turnstile> v : r \<and> flat v \<noteq> [];
    length vs > n; length vs \<le> m\<rbrakk> \<Longrightarrow> \<Turnstile> Stars vs : NMTIMES r n m"

  
inductive_cases Prf_elims:
  "\<Turnstile> v : ZERO"
  "\<Turnstile> v : SEQ r1 r2"
  "\<Turnstile> v : ALT r1 r2"
  "\<Turnstile> v : ONE"
  "\<Turnstile> v : CHAR c"
  "\<Turnstile> vs : STAR r"
  "\<Turnstile> vs : UPNTIMES r n"
  "\<Turnstile> vs : NTIMES r n"
  "\<Turnstile> vs : FROMNTIMES r n"
  "\<Turnstile> vs : NMTIMES r n m"

lemma Prf_Stars_appendE:
  assumes "\<Turnstile> Stars (vs1 @ vs2) : STAR r"
  shows "\<Turnstile> Stars vs1 : STAR r \<and> \<Turnstile> Stars vs2 : STAR r" 
using assms
by (auto intro: Prf.intros elim!: Prf_elims)



lemma flats_empty:
  assumes "(\<forall>v\<in>set vs. flat v = [])"
  shows "flats vs = []"
using assms
by(induct vs) (simp_all)

lemma Star_cval:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> (\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> [])"
using assms
apply(induct ss)
apply(auto)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(case_tac "flat v = []")
apply(rule_tac x="vs" in exI)
apply(simp)
apply(rule_tac x="v#vs" in exI)
apply(simp)
done


lemma flats_cval:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs1 vs2. flats (vs1 @ vs2) = concat ss \<and> length (vs1 @ vs2) = length ss \<and> 
          (\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []) \<and>
          (\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = [])"
using assms
apply(induct ss rule: rev_induct)
apply(rule_tac x="[]" in exI)+
apply(simp)
apply(simp)
apply(clarify)
apply(case_tac "flat v = []")
apply(rule_tac x="vs1" in exI)
apply(rule_tac x="v#vs2" in exI)
apply(simp)
apply(rule_tac x="vs1 @ [v]" in exI)
apply(rule_tac x="vs2" in exI)
apply(simp)
apply(subst (asm) (2) flats_empty)
apply(simp)
apply(simp)
done

lemma flats_cval_nonempty:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs. flats vs = concat ss \<and> length vs \<le> length ss \<and> 
          (\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> [])" 
using assms
apply(induct ss)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(simp)
apply(clarify)
apply(case_tac "flat v = []")
apply(rule_tac x="vs" in exI)
apply(simp)
apply(rule_tac x="v # vs" in exI)
apply(simp)
done

lemma Pow_flats:
  assumes "\<forall>v \<in> set vs. flat v \<in> A"
  shows "flats vs \<in> A \<up> length vs"
using assms
by(induct vs)(auto simp add: Sequ_def)

lemma Pow_flats_appends:
  assumes "\<forall>v \<in> set vs1. flat v \<in> A" "\<forall>v \<in> set vs2. flat v \<in> A"
  shows "flats vs1 @ flats vs2 \<in> A \<up> (length vs1 + length vs2)"
using assms
apply(induct vs1)
apply(auto simp add: Sequ_def Pow_flats)
done

lemma L_flat_Prf1:
  assumes "\<Turnstile> v : r" 
  shows "flat v \<in> L r"
using assms
apply(induct) 
apply(auto simp add: Sequ_def Star_concat Pow_flats)
apply(meson Pow_flats atMost_iff)
using Pow_flats_appends apply blast
using Pow_flats_appends apply blast
apply (meson Pow_flats atLeast_iff less_imp_le)
apply(rule_tac x="length vs1 + length vs2" in  bexI)
apply(meson Pow_flats_appends atLeastAtMost_iff)
apply(simp)
apply(meson Pow_flats atLeastAtMost_iff less_or_eq_imp_le)
done

lemma L_flat_Prf2:
  assumes "s \<in> L r" 
  shows "\<exists>v. \<Turnstile> v : r \<and> flat v = s"
using assms
proof(induct r arbitrary: s)
  case (STAR r s)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (STAR r)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> L r \<and> s \<noteq> []"
  using Star_cstring by auto  
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> []"
  using IH Star_cval by metis 
  then show "\<exists>v. \<Turnstile> v : STAR r \<and> flat v = s"
  using Prf.intros(6) flat_Stars by blast
next 
  case (SEQ r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : SEQ r1 r2 \<and> flat v = s"
  unfolding Sequ_def L.simps by (fastforce intro: Prf.intros)
next
  case (ALT r1 r2 s)
  then show "\<exists>v. \<Turnstile> v : ALT r1 r2 \<and> flat v = s"
  unfolding L.simps by (fastforce intro: Prf.intros)
next
  case (NTIMES r n)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (NTIMES r n)" by fact
  then obtain ss1 ss2 where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = n" 
    "\<forall>s \<in> set ss1. s \<in> L r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> L r \<and> s = []"
  using Pow_cstring by force
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = n" 
      "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = []"
  using IH flats_cval 
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<Turnstile> v : NTIMES r n \<and> flat v = s"
  using Prf.intros(8) flat_Stars by blast
next 
  case (FROMNTIMES r n)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (FROMNTIMES r n)" by fact 
  then obtain ss1 ss2 k where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = k"  "n \<le> k"
    "\<forall>s \<in> set ss1. s \<in> L r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> L r \<and> s = []"
    using Pow_cstring by force 
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = k" "n \<le> k"
      "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = []"
  using IH flats_cval 
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<Turnstile> v : FROMNTIMES r n \<and> flat v = s"
  apply(case_tac "length vs1 \<le> n")
  apply(rule_tac x="Stars (vs1 @ take (n - length vs1) vs2)" in exI)
  apply(simp)
  apply(subgoal_tac "flats (take (n - length vs1) vs2) = []")
  prefer 2
  apply (meson flats_empty in_set_takeD)
  apply(clarify)
    apply(rule conjI)
      apply(rule Prf.intros)
        apply(simp)
       apply (meson in_set_takeD)
      apply(simp)
     apply(simp)
     apply (simp add: flats_empty)
      apply(rule_tac x="Stars vs1" in exI)
  apply(simp)
    apply(rule conjI)
     apply(rule Prf.intros(10))
      apply(auto)
  done    
next 
  case (NMTIMES r n m)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (NMTIMES r n m)" by fact 
  then obtain ss1 ss2 k where "concat (ss1 @ ss2) = s" "length (ss1 @ ss2) = k" "n \<le> k" "k \<le> m" 
    "\<forall>s \<in> set ss1. s \<in> L r \<and> s \<noteq> []" "\<forall>s \<in> set ss2. s \<in> L r \<and> s = []"
  using Pow_cstring by (auto, blast)
  then obtain vs1 vs2 where "flats (vs1 @ vs2) = s" "length (vs1 @ vs2) = k" "n \<le> k" "k \<le> m"
      "\<forall>v\<in>set vs1. \<Turnstile> v : r \<and> flat v \<noteq> []" "\<forall>v\<in>set vs2. \<Turnstile> v : r \<and> flat v = []"
  using IH flats_cval 
  apply -
  apply(drule_tac x="ss1 @ ss2" in meta_spec)
  apply(drule_tac x="r" in meta_spec)
  apply(drule meta_mp)
  apply(simp)
  apply (metis Un_iff)
  apply(clarify)
  apply(drule_tac x="vs1" in meta_spec)
  apply(drule_tac x="vs2" in meta_spec)
  apply(simp)
  done
  then show "\<exists>v. \<Turnstile> v : NMTIMES r n m \<and> flat v = s"
    apply(case_tac "length vs1 \<le> n")
  apply(rule_tac x="Stars (vs1 @ take (n - length vs1) vs2)" in exI)
  apply(simp)
  apply(subgoal_tac "flats (take (n - length vs1) vs2) = []")
  prefer 2
  apply (meson flats_empty in_set_takeD)
  apply(clarify)
    apply(rule conjI)
      apply(rule Prf.intros)
        apply(simp)
       apply (meson in_set_takeD)
      apply(simp)
     apply(simp)
     apply (simp add: flats_empty)
      apply(rule_tac x="Stars vs1" in exI)
  apply(simp)
    apply(rule conjI)
     apply(rule Prf.intros)
      apply(auto)
  done    
next 
  case (UPNTIMES r n s)
  have IH: "\<And>s. s \<in> L r \<Longrightarrow> \<exists>v. \<Turnstile> v : r \<and> flat v = s" by fact
  have "s \<in> L (UPNTIMES r n)" by fact
  then obtain ss where "concat ss = s" "\<forall>s \<in> set ss. s \<in> L r \<and> s \<noteq> []" "length ss \<le> n"
  using Pow_cstring_nonempty by force
  then obtain vs where "flats vs = s" "\<forall>v\<in>set vs. \<Turnstile> v : r \<and> flat v \<noteq> []" "length vs \<le> n"
  using IH flats_cval_nonempty by (smt order.trans) 
  then show "\<exists>v. \<Turnstile> v : UPNTIMES r n \<and> flat v = s"
  using Prf.intros(7) flat_Stars by blast
qed (auto intro: Prf.intros)


lemma L_flat_Prf:
  shows "L(r) = {flat v | v. \<Turnstile> v : r}"
using L_flat_Prf1 L_flat_Prf2 by blast



section {* Sets of Lexical Values *}

text {*
  Shows that lexical values are finite for a given regex and string.
*}

definition
  LV :: "rexp \<Rightarrow> string \<Rightarrow> val set"
where  "LV r s \<equiv> {v. \<Turnstile> v : r \<and> flat v = s}"

lemma LV_simps:
  shows "LV ZERO s = {}"
  and   "LV ONE s = (if s = [] then {Void} else {})"
  and   "LV (CHAR c) s = (if s = [c] then {Char c} else {})"
  and   "LV (ALT r1 r2) s = Left ` LV r1 s \<union> Right ` LV r2 s"
unfolding LV_def
apply(auto intro: Prf.intros elim: Prf.cases)
done

abbreviation
  "Prefixes s \<equiv> {s'. prefix s' s}"

abbreviation
  "Suffixes s \<equiv> {s'. suffix s' s}"

abbreviation
  "SSuffixes s \<equiv> {s'. strict_suffix s' s}"

lemma Suffixes_cons [simp]:
  shows "Suffixes (c # s) = Suffixes s \<union> {c # s}"
by (auto simp add: suffix_def Cons_eq_append_conv)


lemma finite_Suffixes: 
  shows "finite (Suffixes s)"
by (induct s) (simp_all)

lemma finite_SSuffixes: 
  shows "finite (SSuffixes s)"
proof -
  have "SSuffixes s \<subseteq> Suffixes s"
   unfolding suffix_def strict_suffix_def by auto
  then show "finite (SSuffixes s)"
   using finite_Suffixes finite_subset by blast
qed

lemma finite_Prefixes: 
  shows "finite (Prefixes s)"
proof -
  have "finite (Suffixes (rev s))" 
    by (rule finite_Suffixes)
  then have "finite (rev ` Suffixes (rev s))" by simp
  moreover
  have "rev ` (Suffixes (rev s)) = Prefixes s"
  unfolding suffix_def prefix_def image_def
   by (auto)(metis rev_append rev_rev_ident)+
  ultimately show "finite (Prefixes s)" by simp
qed

definition
  "Stars_Cons V Vs \<equiv> {Stars (v # vs) | v vs. v \<in> V \<and> Stars vs \<in> Vs}"
  
definition
  "Stars_Append Vs1 Vs2 \<equiv> {Stars (vs1 @ vs2) | vs1 vs2. Stars vs1 \<in> Vs1 \<and> Stars vs2 \<in> Vs2}"

fun Stars_Pow :: "val set \<Rightarrow> nat \<Rightarrow> val set"
where  
  "Stars_Pow Vs 0 = {Stars []}"
| "Stars_Pow Vs (Suc n) = Stars_Cons Vs (Stars_Pow Vs n)"
  
lemma finite_Stars_Cons:
  assumes "finite V" "finite Vs"
  shows "finite (Stars_Cons V Vs)"
  using assms  
proof -
  from assms(2) have "finite (Stars -` Vs)"
    by(simp add: finite_vimageI inj_on_def) 
  with assms(1) have "finite (V \<times> (Stars -` Vs))"
    by(simp)
  then have "finite ((\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs)))"
    by simp
  moreover have "Stars_Cons V Vs = (\<lambda>(v, vs). Stars (v # vs)) ` (V \<times> (Stars -` Vs))"
    unfolding Stars_Cons_def by auto    
  ultimately show "finite (Stars_Cons V Vs)"   
    by simp
qed

lemma finite_Stars_Append:
  assumes "finite Vs1" "finite Vs2"
  shows "finite (Stars_Append Vs1 Vs2)"
  using assms  
proof -
  define UVs1 where "UVs1 \<equiv> Stars -` Vs1"
  define UVs2 where "UVs2 \<equiv> Stars -` Vs2"  
  from assms have "finite UVs1" "finite UVs2"
    unfolding UVs1_def UVs2_def
    by(simp_all add: finite_vimageI inj_on_def) 
  then have "finite ((\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2))"
    by simp
  moreover 
    have "Stars_Append Vs1 Vs2 = (\<lambda>(vs1, vs2). Stars (vs1 @ vs2)) ` (UVs1 \<times> UVs2)"
    unfolding Stars_Append_def UVs1_def UVs2_def by auto    
  ultimately show "finite (Stars_Append Vs1 Vs2)"   
    by simp
qed 
 
lemma finite_Stars_Pow:
  assumes "finite Vs"
  shows "finite (Stars_Pow Vs n)"    
by (induct n) (simp_all add: finite_Stars_Cons assms)
    
lemma LV_STAR_finite:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (STAR r) s)"
proof(induct s rule: length_induct)
  fix s::"char list"
  assume "\<forall>s'. length s' < length s \<longrightarrow> finite (LV (STAR r) s')"
  then have IH: "\<forall>s' \<in> SSuffixes s. finite (LV (STAR r) s')"
    apply(auto simp add: strict_suffix_def suffix_def)
    by force    
  define f where "f \<equiv> \<lambda>(v, vs). Stars (v # vs)"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r s'"
  define S2 where "S2 \<equiv> \<Union>s2 \<in> SSuffixes s. LV (STAR r) s2"
  have "finite S1" using assms
    unfolding S1_def by (simp_all add: finite_Prefixes)
  moreover 
  with IH have "finite S2" unfolding S2_def
    by (auto simp add: finite_SSuffixes)
  ultimately 
  have "finite ({Stars []} \<union> Stars_Cons S1 S2)" 
    by (simp add: finite_Stars_Cons)
  moreover 
  have "LV (STAR r) s \<subseteq> {Stars []} \<union> (Stars_Cons S1 S2)" 
  unfolding S1_def S2_def f_def LV_def Stars_Cons_def
  unfolding prefix_def strict_suffix_def 
  unfolding image_def
  apply(auto)
  apply(case_tac x)
  apply(auto elim: Prf_elims)
  apply(erule Prf_elims)
  apply(auto)
  apply(case_tac vs)
  apply(auto intro: Prf.intros)  
  apply(rule exI)
  apply(rule conjI)
  apply(rule_tac x="flats list" in exI)
   apply(rule conjI)
  apply(simp add: suffix_def)
  apply(blast)
  using Prf.intros(6) flat_Stars by blast  
  ultimately
  show "finite (LV (STAR r) s)" by (simp add: finite_subset)
qed  
    
lemma LV_UPNTIMES_STAR:
  "LV (UPNTIMES r n) s \<subseteq> LV (STAR r) s"
by(auto simp add: LV_def intro: Prf.intros elim: Prf_elims)

lemma LV_NTIMES_3:
  shows "LV (NTIMES r (Suc n)) [] = (\<lambda>(v,vs). Stars (v#vs)) ` (LV r [] \<times> (Stars -` (LV (NTIMES r n) [])))"
unfolding LV_def
apply(auto elim!: Prf_elims simp add: image_def)
apply(case_tac vs1)
apply(auto)
apply(case_tac vs2)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
apply(auto)
  done 
    
lemma LV_FROMNTIMES_3:
  shows "LV (FROMNTIMES r (Suc n)) [] = 
    (\<lambda>(v,vs). Stars (v#vs)) ` (LV r [] \<times> (Stars -` (LV (FROMNTIMES r n) [])))"
unfolding LV_def
apply(auto elim!: Prf_elims simp add: image_def)
apply(case_tac vs1)
apply(auto)
apply(case_tac vs2)
apply(auto)
apply(subst append.simps(1)[symmetric])
apply(rule Prf.intros)
     apply(auto)
  apply (metis le_imp_less_Suc length_greater_0_conv less_antisym list.exhaust list.set_intros(1) not_less_eq zero_le)
  prefer 2
  using nth_mem apply blast
  apply(case_tac vs1)
  apply (smt Groups.add_ac(2) Prf.intros(9) add.right_neutral add_Suc_right append.simps(1) insert_iff length_append list.set(2) list.size(3) list.size(4))
    apply(auto)
done     
  
lemma LV_NTIMES_4:
 "LV (NTIMES r n) [] = Stars_Pow (LV r []) n" 
  apply(induct n)
   apply(simp add: LV_def)    
   apply(auto elim!: Prf_elims simp add: image_def)[1]
   apply(subst append.simps[symmetric])
    apply(rule Prf.intros)
      apply(simp_all)
    apply(simp add: LV_NTIMES_3 image_def Stars_Cons_def)
  apply blast
 done   

lemma LV_NTIMES_5:
  "LV (NTIMES r n) s \<subseteq> Stars_Append (LV (STAR r) s) (\<Union>i\<le>n. LV (NTIMES r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
  apply(auto simp add: Stars_Append_def)
  apply(rule_tac x="vs1" in exI)
  apply(rule_tac x="vs2" in exI)  
  apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
    apply(simp)
      done
      
lemma ttty:
 "LV (FROMNTIMES r n) [] = Stars_Pow (LV r []) n" 
  apply(induct n)
   apply(simp add: LV_def)    
   apply(auto elim: Prf_elims simp add: image_def)[1]
   prefer 2
    apply(subst append.simps[symmetric])
    apply(rule Prf.intros)
      apply(simp_all)
   apply(erule Prf_elims) 
    apply(case_tac vs1)
     apply(simp)
    apply(simp)
   apply(case_tac x)
    apply(simp_all)
    apply(simp add: LV_FROMNTIMES_3 image_def Stars_Cons_def)
  apply blast
 done     

lemma LV_FROMNTIMES_5:
  "LV (FROMNTIMES r n) s \<subseteq> Stars_Append (LV (STAR r) s) (\<Union>i\<le>n. LV (FROMNTIMES r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
  apply(auto simp add: Stars_Append_def)
  apply(rule_tac x="vs1" in exI)
  apply(rule_tac x="vs2" in exI)  
  apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
     apply(simp)
      apply(rule_tac x="vs" in exI)
    apply(rule_tac x="[]" in exI) 
    apply(auto)
    by (metis Prf.intros(9) append_Nil atMost_iff empty_iff le_imp_less_Suc less_antisym list.set(1) nth_mem zero_le)

lemma LV_FROMNTIMES_6:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (FROMNTIMES r n) s)"
  apply(rule finite_subset)
   apply(rule LV_FROMNTIMES_5)
  apply(rule finite_Stars_Append)
    apply(rule LV_STAR_finite)
   apply(rule assms)
  apply(rule finite_UN_I)
   apply(auto)
  by (simp add: assms finite_Stars_Pow ttty)
    
lemma LV_NMTIMES_5:
  "LV (NMTIMES r n m) s \<subseteq> Stars_Append (LV (STAR r) s) (\<Union>i\<le>n. LV (FROMNTIMES r i) [])"
apply(auto simp add: LV_def)
apply(auto elim!: Prf_elims)
  apply(auto simp add: Stars_Append_def)
  apply(rule_tac x="vs1" in exI)
  apply(rule_tac x="vs2" in exI)  
  apply(auto)
    using Prf.intros(6) apply(auto)
      apply(rule_tac x="length vs2" in bexI)
    thm Prf.intros
      apply(subst append.simps(1)[symmetric])
    apply(rule Prf.intros)
      apply(auto)[1]
      apply(auto)[1]
     apply(simp)
     apply(simp)
      apply(rule_tac x="vs" in exI)
    apply(rule_tac x="[]" in exI) 
    apply(auto)
    by (metis Prf.intros(9) append_Nil atMost_iff empty_iff le_imp_less_Suc less_antisym list.set(1) nth_mem zero_le)

lemma LV_NMTIMES_6:
  assumes "\<forall>s. finite (LV r s)"
  shows "finite (LV (NMTIMES r n m) s)"
  apply(rule finite_subset)
   apply(rule LV_NMTIMES_5)
  apply(rule finite_Stars_Append)
    apply(rule LV_STAR_finite)
   apply(rule assms)
  apply(rule finite_UN_I)
   apply(auto)
  by (simp add: assms finite_Stars_Pow ttty)
        
    
lemma LV_finite:
  shows "finite (LV r s)"
proof(induct r arbitrary: s)
  case (ZERO s) 
  show "finite (LV ZERO s)" by (simp add: LV_simps)
next
  case (ONE s)
  show "finite (LV ONE s)" by (simp add: LV_simps)
next
  case (CHAR c s)
  show "finite (LV (CHAR c) s)" by (simp add: LV_simps)
next 
  case (ALT r1 r2 s)
  then show "finite (LV (ALT r1 r2) s)" by (simp add: LV_simps)
next 
  case (SEQ r1 r2 s)
  define f where "f \<equiv> \<lambda>(v1, v2). Seq v1 v2"
  define S1 where "S1 \<equiv> \<Union>s' \<in> Prefixes s. LV r1 s'"
  define S2 where "S2 \<equiv> \<Union>s' \<in> Suffixes s. LV r2 s'"
  have IHs: "\<And>s. finite (LV r1 s)" "\<And>s. finite (LV r2 s)" by fact+
  then have "finite S1" "finite S2" unfolding S1_def S2_def
    by (simp_all add: finite_Prefixes finite_Suffixes)
  moreover
  have "LV (SEQ r1 r2) s \<subseteq> f ` (S1 \<times> S2)"
    unfolding f_def S1_def S2_def 
    unfolding LV_def image_def prefix_def suffix_def
    apply (auto elim!: Prf_elims)
    by (metis (mono_tags, lifting) mem_Collect_eq)
  ultimately 
  show "finite (LV (SEQ r1 r2) s)"
    by (simp add: finite_subset)
next
  case (STAR r s)
  then show "finite (LV (STAR r) s)" by (simp add: LV_STAR_finite)
next 
  case (UPNTIMES r n s)
  have "\<And>s. finite (LV r s)" by fact
  then show "finite (LV (UPNTIMES r n) s)"
  by (meson LV_STAR_finite LV_UPNTIMES_STAR rev_finite_subset)
next 
  case (FROMNTIMES r n s)
  have "\<And>s. finite (LV r s)" by fact
  then show "finite (LV (FROMNTIMES r n) s)"
    by (simp add: LV_FROMNTIMES_6)
next 
  case (NTIMES r n s)
  have "\<And>s. finite (LV r s)" by fact
  then show "finite (LV (NTIMES r n) s)"
    by (metis (no_types, lifting) LV_NTIMES_4 LV_NTIMES_5 LV_STAR_finite finite_Stars_Append finite_Stars_Pow finite_UN_I finite_atMost finite_subset)
next
  case (NMTIMES r n m s)
  have "\<And>s. finite (LV r s)" by fact
  then show "finite (LV (NMTIMES r n m) s)"
    by (simp add: LV_NMTIMES_6)         
qed



section {* Our POSIX Definition *}

inductive 
  Posix :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  Posix_ONE: "[] \<in> ONE \<rightarrow> Void"
| Posix_CHAR: "[c] \<in> (CHAR c) \<rightarrow> (Char c)"
| Posix_ALT1: "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| Posix_ALT2: "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> L(r1)\<rbrakk> \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| Posix_SEQ: "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"
| Posix_STAR1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> STAR r \<rightarrow> Stars (v # vs)"
| Posix_STAR2: "[] \<in> STAR r \<rightarrow> Stars []"
| Posix_NTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> NTIMES r (n - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> NTIMES r n \<rightarrow> Stars (v # vs)"
| Posix_NTIMES2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> NTIMES r n \<rightarrow> Stars vs"  
| Posix_UPNTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> UPNTIMES r (n - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (UPNTIMES r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> UPNTIMES r n \<rightarrow> Stars (v # vs)"
| Posix_UPNTIMES2: "[] \<in> UPNTIMES r n \<rightarrow> Stars []"
| Posix_FROMNTIMES2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n\<rbrakk>
    \<Longrightarrow> [] \<in> FROMNTIMES r n \<rightarrow> Stars vs"
| Posix_FROMNTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> FROMNTIMES r (n - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (FROMNTIMES r (n - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> FROMNTIMES r n \<rightarrow> Stars (v # vs)"  
| Posix_FROMNTIMES3: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> FROMNTIMES r 0 \<rightarrow> Stars (v # vs)"  
| Posix_NMTIMES2: "\<lbrakk>\<forall>v \<in> set vs. [] \<in> r \<rightarrow> v; length vs = n; n \<le> m\<rbrakk>
    \<Longrightarrow> [] \<in> NMTIMES r n m \<rightarrow> Stars vs"  
| Posix_NMTIMES1: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> NMTIMES r (n - 1) (m - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < n; n \<le> m;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (NMTIMES r (n - 1) (m - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> NMTIMES r n m \<rightarrow> Stars (v # vs)"  
| Posix_NMTIMES3: "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> UPNTIMES r (m - 1) \<rightarrow> Stars vs; flat v \<noteq> []; 0 < m;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (UPNTIMES r (m - 1)))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> NMTIMES r 0 m \<rightarrow> Stars (v # vs)"    
  
inductive_cases Posix_elims:
  "s \<in> ZERO \<rightarrow> v"
  "s \<in> ONE \<rightarrow> v"
  "s \<in> CHAR c \<rightarrow> v"
  "s \<in> ALT r1 r2 \<rightarrow> v"
  "s \<in> SEQ r1 r2 \<rightarrow> v"
  "s \<in> STAR r \<rightarrow> v"
  "s \<in> NTIMES r n \<rightarrow> v"
  "s \<in> UPNTIMES r n \<rightarrow> v"
  "s \<in> FROMNTIMES r n \<rightarrow> v"
  "s \<in> NMTIMES r n m \<rightarrow> v"
  
lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> L r" "flat v = s"
using assms
  apply(induct s r v rule: Posix.induct)
                    apply(auto simp add: Sequ_def)[18]
            apply(case_tac n)
             apply(simp)
  apply(simp add: Sequ_def)
            apply(auto)[1]
           apply(simp)
  apply(clarify)
  apply(rule_tac x="Suc x" in bexI)
  apply(simp add: Sequ_def)
            apply(auto)[5]
  using nth_mem nullable.simps(9) nullable_correctness apply auto[1]
  apply simp
       apply(simp)
       apply(clarify)
       apply(rule_tac x="Suc x" in bexI)
        apply(simp add: Sequ_def)
          apply(auto)[3]
    defer
     apply(simp)
  apply fastforce
    apply(simp)
   apply(simp)
    apply(clarify)
   apply(rule_tac x="Suc x" in bexI)
    apply(auto simp add: Sequ_def)[2]
   apply(simp)
    apply(simp)
    apply(clarify)
     apply(rule_tac x="Suc x" in bexI)
    apply(auto simp add: Sequ_def)[2]
   apply(simp)
  apply(simp add: Star.step Star_Pow)
done  
    
text {*
  Our Posix definition determines a unique value.
*}
  
lemma List_eq_zipI:
  assumes "\<forall>(v1, v2) \<in> set (zip vs1 vs2). v1 = v2" 
  and "length vs1 = length vs2"
  shows "vs1 = vs2"  
 using assms
  apply(induct vs1 arbitrary: vs2)
   apply(case_tac vs2)
   apply(simp)    
   apply(simp)
   apply(case_tac vs2)
   apply(simp)
  apply(simp)
done    

lemma Posix_determ:
  assumes "s \<in> r \<rightarrow> v1" "s \<in> r \<rightarrow> v2"
  shows "v1 = v2"
using assms
proof (induct s r v1 arbitrary: v2 rule: Posix.induct)
  case (Posix_ONE v2)
  have "[] \<in> ONE \<rightarrow> v2" by fact
  then show "Void = v2" by cases auto
next 
  case (Posix_CHAR c v2)
  have "[c] \<in> CHAR c \<rightarrow> v2" by fact
  then show "Char c = v2" by cases auto
next 
  case (Posix_ALT1 s r1 v r2 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<in> r1 \<rightarrow> v" by fact
  then have "s \<in> L r1" by (simp add: Posix1)
  ultimately obtain v' where eq: "v2 = Left v'" "s \<in> r1 \<rightarrow> v'" by cases auto 
  moreover
  have IH: "\<And>v2. s \<in> r1 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Left v = v2" using eq by simp
next 
  case (Posix_ALT2 s r2 v r1 v2)
  have "s \<in> ALT r1 r2 \<rightarrow> v2" by fact
  moreover
  have "s \<notin> L r1" by fact
  ultimately obtain v' where eq: "v2 = Right v'" "s \<in> r2 \<rightarrow> v'" 
    by cases (auto simp add: Posix1) 
  moreover
  have IH: "\<And>v2. s \<in> r2 \<rightarrow> v2 \<Longrightarrow> v = v2" by fact
  ultimately have "v = v'" by simp
  then show "Right v = v2" using eq by simp
next
  case (Posix_SEQ s1 r1 v1 s2 r2 v2 v')
  have "(s1 @ s2) \<in> SEQ r1 r2 \<rightarrow> v'" 
       "s1 \<in> r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by fact+
  then obtain v1' v2' where "v' = Seq v1' v2'" "s1 \<in> r1 \<rightarrow> v1'" "s2 \<in> r2 \<rightarrow> v2'"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) by fastforce+
  moreover
  have IHs: "\<And>v1'. s1 \<in> r1 \<rightarrow> v1' \<Longrightarrow> v1 = v1'"
            "\<And>v2'. s2 \<in> r2 \<rightarrow> v2' \<Longrightarrow> v2 = v2'" by fact+
  ultimately show "Seq v1 v2 = v'" by simp
next
  case (Posix_STAR1 s1 r v s2 vs v2)
  have "(s1 @ s2) \<in> STAR r \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> STAR r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (STAR r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
  using Posix1(1) apply fastforce
  apply (metis Posix1(1) Posix_STAR1.hyps(6) append_Nil append_Nil2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> STAR r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_STAR2 r v2)
  have "[] \<in> STAR r \<rightarrow> v2" by fact
  then show "Stars [] = v2" by cases (auto simp add: Posix1)
next
  case (Posix_NTIMES2 vs r n v2)
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
     apply(auto)
     apply (simp add: Posix1(2))
    apply(rule List_eq_zipI)
     apply(auto)
    by (meson in_set_zipE)
next
  case (Posix_NTIMES1 s1 r v s2 n vs v2)
  have "(s1 @ s2) \<in> NTIMES r n \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> NTIMES r (n - 1) \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (NTIMES r (n - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (NTIMES r (n - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) apply fastforce
    apply (metis One_nat_def Posix1(1) Posix_NTIMES1.hyps(7) append.right_neutral append_self_conv2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> NTIMES r (n - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_UPNTIMES1 s1 r v s2 n vs v2)
  have "(s1 @ s2) \<in> UPNTIMES r n \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> UPNTIMES r (n - 1) \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (UPNTIMES r (n - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (UPNTIMES r (n - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) apply fastforce
    apply (metis One_nat_def Posix1(1) Posix_UPNTIMES1.hyps(7) append.right_neutral append_self_conv2)
  using Posix1(2) by blast
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> UPNTIMES r (n - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto
next
  case (Posix_UPNTIMES2 r n v2)
  then show "Stars [] = v2"
    apply(erule_tac Posix_elims)
     apply(auto)
    by (simp add: Posix1(2))
next
  case (Posix_FROMNTIMES1 s1 r v s2 n vs v2)
  have "(s1 @ s2) \<in> FROMNTIMES r n \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> FROMNTIMES r (n - 1) \<rightarrow> Stars vs" "flat v \<noteq> []" "0 < n"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (FROMNTIMES r (n - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (FROMNTIMES r (n - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) Posix1(2) apply blast 
     apply(case_tac n)
      apply(simp)
      apply(simp)
    apply(drule_tac x="va" in meta_spec)
    apply(drule_tac x="vs" in meta_spec)
    apply(simp)
     apply(drule meta_mp)
    apply (metis L.simps(9) Posix1(1) UN_E append.right_neutral append_Nil diff_Suc_1 local.Posix_FROMNTIMES1(4) val.inject(5))
    apply (metis L.simps(9) Posix1(1) UN_E append.right_neutral append_Nil)
    by (metis One_nat_def Posix1(1) Posix_FROMNTIMES1.hyps(7) self_append_conv self_append_conv2)
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> FROMNTIMES r (n - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto    
next
  case (Posix_FROMNTIMES2 vs r n v2)  
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
     apply(auto)
    apply(rule List_eq_zipI)
     apply(auto)
      apply(meson in_set_zipE)
     apply (simp add: Posix1(2))
    using Posix1(2) by blast
next
  case (Posix_FROMNTIMES3 s1 r v s2 vs v2)  
    have "(s1 @ s2) \<in> FROMNTIMES r 0 \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> STAR r \<rightarrow> Stars vs" "flat v \<noteq> []"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (STAR r) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(2) apply fastforce
    using Posix1(1) apply fastforce
    by (metis Posix1(1) Posix_FROMNTIMES3.hyps(6) append.right_neutral append_Nil)
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> STAR r \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto     
next    
  case (Posix_NMTIMES1 s1 r v s2 n m vs v2)
  have "(s1 @ s2) \<in> NMTIMES r n m \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> NMTIMES r (n - 1) (m - 1) \<rightarrow> Stars vs" "flat v \<noteq> []" 
       "0 < n" "n \<le> m"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (NMTIMES r (n - 1) (m - 1)))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" 
    "s2 \<in> (NMTIMES r (n - 1) (m - 1)) \<rightarrow> (Stars vs')"
  apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(1) Posix1(2) apply blast 
     apply(case_tac n)
      apply(simp)
     apply(simp)
       apply(case_tac m)
      apply(simp)
     apply(simp)
    apply(drule_tac x="va" in meta_spec)
    apply(drule_tac x="vs" in meta_spec)
    apply(simp)
     apply(drule meta_mp)
      apply(drule Posix1(1))
      apply(drule Posix1(1))
      apply(drule Posix1(1))
      apply(frule Posix1(1))
      apply(simp)
    using Posix_NMTIMES1.hyps(4) apply force
     apply (metis L.simps(10) Posix1(1) UN_E append_Nil2 append_self_conv2)
    by (metis One_nat_def Posix1(1) Posix_NMTIMES1.hyps(8) append.right_neutral append_Nil)      
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> NMTIMES r (n - 1) (m - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto     
next
  case (Posix_NMTIMES2 vs r n m v2)
  then show "Stars vs = v2"
    apply(erule_tac Posix_elims)
      apply(simp)
      apply(rule List_eq_zipI)
       apply(auto)
      apply (meson in_set_zipE)
    apply (simp add: Posix1(2))
    apply(erule_tac Posix_elims)
     apply(auto)
    apply (simp add: Posix1(2))+
    done  
next
  case (Posix_NMTIMES3 s1 r v s2 m vs v2)
   have "(s1 @ s2) \<in> NMTIMES r 0 m \<rightarrow> v2" 
       "s1 \<in> r \<rightarrow> v" "s2 \<in> UPNTIMES r (m - 1) \<rightarrow> Stars vs" "flat v \<noteq> []" "0 < m"
       "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (UPNTIMES r (m - 1 )))" by fact+
  then obtain v' vs' where "v2 = Stars (v' # vs')" "s1 \<in> r \<rightarrow> v'" "s2 \<in> (UPNTIMES r (m - 1)) \<rightarrow> (Stars vs')"
    apply(cases) apply (auto simp add: append_eq_append_conv2)
    using Posix1(2) apply blast
    apply (smt L.simps(7) Posix1(1) UN_E append_eq_append_conv2)
    by (metis One_nat_def Posix1(1) Posix_NMTIMES3.hyps(7) append.right_neutral append_Nil)
  moreover
  have IHs: "\<And>v2. s1 \<in> r \<rightarrow> v2 \<Longrightarrow> v = v2"
            "\<And>v2. s2 \<in> UPNTIMES r (m - 1) \<rightarrow> v2 \<Longrightarrow> Stars vs = v2" by fact+
  ultimately show "Stars (v # vs) = v2" by auto  
qed


text {*
  Our POSIX value is a lexical value.
*}

lemma Posix_LV:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> LV r s"
using assms unfolding LV_def
apply(induct rule: Posix.induct)
            apply(auto simp add: intro!: Prf.intros elim!: Prf_elims)[7]
     defer
  defer
     apply(auto simp add: intro!: Prf.intros elim!: Prf_elims)[2]
  apply (metis (mono_tags, lifting) Prf.intros(9) append_Nil empty_iff flat_Stars flats_empty list.set(1) mem_Collect_eq)
     apply(simp)
     apply(clarify)
     apply(case_tac n)
      apply(simp)
     apply(simp)
     apply(erule Prf_elims)
      apply(simp)
  apply(subst append.simps(2)[symmetric])
      apply(rule Prf.intros) 
        apply(simp)
       apply(simp)
      apply(simp)
     apply(simp)
     apply(rule Prf.intros)  
      apply(simp)
     apply(simp)
    apply(simp)
   apply(clarify)
   apply(erule Prf_elims)
      apply(simp)
  apply(rule Prf.intros)  
       apply(simp)
     apply(simp)
  (* NTIMES *)
   prefer 4
   apply(simp)
   apply(case_tac n)
    apply(simp)
   apply(simp)
   apply(clarify)
   apply(rotate_tac 5)
   apply(erule Prf_elims)
   apply(simp)
  apply(subst append.simps(2)[symmetric])
      apply(rule Prf.intros) 
        apply(simp)
       apply(simp)
   apply(simp)
  prefer 4
  apply(simp)
  apply (metis Prf.intros(8) length_removeAll_less less_irrefl_nat removeAll.simps(1) self_append_conv2)
  (* NMTIMES *)
  apply(simp)
  apply (metis Prf.intros(11) append_Nil empty_iff list.set(1))
  apply(simp)
  apply(clarify)
  apply(rotate_tac 6)
  apply(erule Prf_elims)
   apply(simp)
  apply(subst append.simps(2)[symmetric])
      apply(rule Prf.intros) 
        apply(simp)
       apply(simp)
  apply(simp)
  apply(simp)
  apply(rule Prf.intros) 
        apply(simp)
  apply(simp)
  apply(simp)
  apply(simp)
  apply(clarify)
  apply(rotate_tac 6)
  apply(erule Prf_elims)
   apply(simp)
      apply(rule Prf.intros) 
        apply(simp)
       apply(simp)
  apply(simp)
done    
  
end