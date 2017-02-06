   
theory Re
  imports "Main" 
begin


section {* Sequential Composition of Sets *}
m
definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ ;; _" [100,100] 100)
where 
  "A ;; B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"

text {* Two Simple Properties about Sequential Composition *}

lemma seq_empty [simp]:
  shows "A ;; {[]} = A"
  and   "{[]} ;; A = A"
by (simp_all add: Sequ_def)

lemma seq_null [simp]:
  shows "A ;; {} = {}"
  and   "{} ;; A = {}"
by (simp_all add: Sequ_def)

section {* Regular Expressions *}

datatype rexp =
  NULL
| EMPTY
| CHAR char
| SEQ rexp rexp
| ALT rexp rexp

section {* Semantics of Regular Expressions *}
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (NULL) = {}"
| "L (EMPTY) = {[]}"
| "L (CHAR c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"

fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (NULL) = False"
| "nullable (EMPTY) = True"
| "nullable (CHAR c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"

lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
apply (induct r) 
apply(auto simp add: Sequ_def) 
done

section {* Values *}

datatype val = 
  Void
| Char char
| Seq val val
| Right val
| Left val

section {* The string behind a value *}

fun 
  flat :: "val \<Rightarrow> string"
where
  "flat(Void) = []"
| "flat(Char c) = [c]"
| "flat(Left v) = flat(v)"
| "flat(Right v) = flat(v)"
| "flat(Seq v1 v2) = flat(v1) @ flat(v2)"

section {* Relation between values and regular expressions *}

inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : SEQ r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : ALT r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : ALT r1 r2"
| "\<turnstile> Void : EMPTY"
| "\<turnstile> Char c : CHAR c"

lemma not_nullable_flat:
  assumes "\<turnstile> v : r" "\<not>nullable r"
  shows "flat v \<noteq> []"
using assms
apply(induct)
apply(auto)
done

lemma Prf_flat_L:
  assumes "\<turnstile> v : r" shows "flat v \<in> L r"
using assms
apply(induct v r rule: Prf.induct)
apply(auto simp add: Sequ_def)
done

lemma L_flat_Prf:
  "L(r) = {flat v | v. \<turnstile> v : r}"
apply(induct r)
apply(auto dest: Prf_flat_L simp add: Sequ_def)
apply (metis Prf.intros(4) flat.simps(1))
apply (metis Prf.intros(5) flat.simps(2))
apply (metis Prf.intros(1) flat.simps(5))
apply (metis Prf.intros(2) flat.simps(3))
apply (metis Prf.intros(3) flat.simps(4))
apply(erule Prf.cases)
apply(auto)
done

section {* Greedy Ordering according to Frisch/Cardelli *}

inductive 
  GrOrd :: "val \<Rightarrow> val \<Rightarrow> bool" ("_ gr\<succ> _")
where 
  "v1 gr\<succ> v1' \<Longrightarrow> (Seq v1 v2) gr\<succ> (Seq v1' v2')"
| "v2 gr\<succ> v2' \<Longrightarrow> (Seq v1 v2) gr\<succ> (Seq v1 v2')"
| "v1 gr\<succ> v2 \<Longrightarrow> (Left v1) gr\<succ> (Left v2)"
| "v1 gr\<succ> v2 \<Longrightarrow> (Right v1) gr\<succ> (Right v2)"
| "(Left v2) gr\<succ>(Right v1)"
| "(Char c) gr\<succ> (Char c)"
| "(Void) gr\<succ> (Void)"

lemma Gr_refl:
  assumes "\<turnstile> v : r"
  shows "v gr\<succ> v"
using assms
apply(induct)
apply(auto intro: GrOrd.intros)
done

lemma Gr_total:
  assumes "\<turnstile> v1 : r" "\<turnstile> v2 : r"
  shows "v1 gr\<succ> v2 \<or> v2 gr\<succ> v1"
using assms
apply(induct v1 r arbitrary: v2 rule: Prf.induct)
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis GrOrd.intros(1) GrOrd.intros(2))
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)
apply(clarify)
apply (metis GrOrd.intros(3))
apply(clarify)
apply (metis GrOrd.intros(5))
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)
apply(clarify)
apply (metis GrOrd.intros(5))
apply(clarify)
apply (metis GrOrd.intros(4))
apply(erule Prf.cases)
apply(simp_all)
apply (metis GrOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)
apply (metis GrOrd.intros(6))
done

lemma Gr_trans: 
  assumes "v1 gr\<succ> v2" "v2 gr\<succ> v3" 
  and     "\<turnstile> v1 : r" "\<turnstile> v2 : r" "\<turnstile> v3 : r"
  shows "v1 gr\<succ> v3"
using assms
apply(induct r arbitrary: v1 v2 v3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
defer
(* ALT case *)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(3))
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(5))
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(5))
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(4))
(* SEQ case *)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(clarify)
apply (metis GrOrd.intros(1))
apply (metis GrOrd.intros(1))
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(1))
by (metis GrOrd.intros(1) Gr_refl)


section {* Values Sets *}

definition prefix :: "string \<Rightarrow> string \<Rightarrow> bool" ("_ \<sqsubseteq> _" [100, 100] 100)
where
  "s1 \<sqsubseteq> s2 \<equiv> \<exists>s3. s1 @ s3 = s2"

definition sprefix :: "string \<Rightarrow> string \<Rightarrow> bool" ("_ \<sqsubset> _" [100, 100] 100)
where
  "s1 \<sqsubset> s2 \<equiv> (s1 \<sqsubseteq> s2 \<and> s1 \<noteq> s2)"

lemma length_sprefix:
  "s1 \<sqsubset> s2 \<Longrightarrow> length s1 < length s2"
unfolding sprefix_def prefix_def
by (auto)

definition Prefixes :: "string \<Rightarrow> string set" where
  "Prefixes s \<equiv> {sp. sp \<sqsubseteq> s}"

definition Suffixes :: "string \<Rightarrow> string set" where
  "Suffixes s \<equiv> rev ` (Prefixes (rev s))"

lemma Suffixes_in: 
  "\<exists>s1. s1 @ s2 = s3 \<Longrightarrow> s2 \<in> Suffixes s3"
unfolding Suffixes_def Prefixes_def prefix_def image_def
apply(auto)
by (metis rev_rev_ident)

lemma Prefixes_Cons:
  "Prefixes (c # s) = {[]} \<union> {c # sp | sp. sp \<in> Prefixes s}"
unfolding Prefixes_def prefix_def
apply(auto simp add: append_eq_Cons_conv) 
done

lemma finite_Prefixes:
  "finite (Prefixes s)"
apply(induct s)
apply(auto simp add: Prefixes_def prefix_def)[1]
apply(simp add: Prefixes_Cons)
done

lemma finite_Suffixes:
  "finite (Suffixes s)"
unfolding Suffixes_def
apply(rule finite_imageI)
apply(rule finite_Prefixes)
done

lemma prefix_Cons:
  "((c # s1) \<sqsubseteq> (c # s2)) = (s1 \<sqsubseteq> s2)"
apply(auto simp add: prefix_def)
done

lemma prefix_append:
  "((s @ s1) \<sqsubseteq> (s @ s2)) = (s1 \<sqsubseteq> s2)"
apply(induct s)
apply(simp)
apply(simp add: prefix_Cons)
done


definition Values :: "rexp \<Rightarrow> string \<Rightarrow> val set" where
  "Values r s \<equiv> {v. \<turnstile> v : r \<and> flat v \<sqsubseteq> s}"

definition rest :: "val \<Rightarrow> string \<Rightarrow> string" where
  "rest v s \<equiv> drop (length (flat v)) s"

lemma rest_flat:
  assumes "flat v1 \<sqsubseteq> s"
  shows "flat v1 @ rest v1 s = s"
using assms
apply(auto simp add: rest_def prefix_def)
done


lemma rest_Suffixes:
  "rest v s \<in> Suffixes s"
unfolding rest_def
by (metis Suffixes_in append_take_drop_id)


lemma Values_recs:
  "Values (NULL) s = {}"
  "Values (EMPTY) s = {Void}"
  "Values (CHAR c) s = (if [c] \<sqsubseteq> s then {Char c} else {})" 
  "Values (ALT r1 r2) s = {Left v | v. v \<in> Values r1 s} \<union> {Right v | v. v \<in> Values r2 s}"
  "Values (SEQ r1 r2) s = {Seq v1 v2 | v1 v2. v1 \<in> Values r1 s \<and> v2 \<in> Values r2 (rest v1 s)}"
unfolding Values_def
apply(auto)
(*NULL*)
apply(erule Prf.cases)
apply(simp_all)[5]
(*EMPTY*)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule Prf.intros)
apply (metis append_Nil prefix_def)
(*CHAR*)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule Prf.intros)
apply(erule Prf.cases)
apply(simp_all)[5]
(*ALT*)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
(*SEQ*)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (simp add: append_eq_conv_conj prefix_def rest_def)
apply (metis Prf.intros(1))
apply (simp add: append_eq_conv_conj prefix_def rest_def)
done

lemma Values_finite:
  "finite (Values r s)"
apply(induct r arbitrary: s)
apply(simp_all add: Values_recs)
thm finite_surj
apply(rule_tac f="\<lambda>(x, y). Seq x y" and 
               A="{(v1, v2) | v1 v2. v1 \<in> Values r1 s \<and> v2 \<in> Values r2 (rest v1 s)}" in finite_surj)
prefer 2
apply(auto)[1]
apply(rule_tac B="\<Union>sp \<in> Suffixes s. {(v1, v2). v1 \<in> Values r1 s \<and> v2 \<in> Values r2 sp}" in finite_subset)
apply(auto)[1]
apply (metis rest_Suffixes)
apply(rule finite_UN_I)
apply(rule finite_Suffixes)
apply(simp)
done

section {* Sulzmann functions *}

fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(EMPTY) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"

section {* Derivatives *}

fun
 der :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "der c (NULL) = NULL"
| "der c (EMPTY) = NULL"
| "der c (CHAR c') = (if c = c' then EMPTY else NULL)"
| "der c (ALT r1 r2) = ALT (der c r1) (der c r2)"
| "der c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2)"

fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


section {* Injection function *}

fun injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval (EMPTY) c Void = Char c"
| "injval (CHAR d) c Void = Char d"
| "injval (CHAR d) c (Char c') = Seq (Char d) (Char c')"
| "injval (ALT r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (ALT r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (SEQ r1 r2) c (Char c') = Seq (Char c) (Char c')"
| "injval (SEQ r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"

fun 
  lex :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "lex r [] = (if nullable r then Some(mkeps r) else None)"
| "lex r (c#s) = (case (lex (der c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"

fun 
  lex2 :: "rexp \<Rightarrow> string \<Rightarrow> val"
where
  "lex2 r [] = mkeps r"
| "lex2 r (c#s) = injval r c (lex2 (der c r) s)"


section {* Projection function *}

fun projval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "projval (CHAR d) c _ = Void"
| "projval (ALT r1 r2) c (Left v1) = Left (projval r1 c v1)"
| "projval (ALT r1 r2) c (Right v2) = Right (projval r2 c v2)"
| "projval (SEQ r1 r2) c (Seq v1 v2) = 
     (if flat v1 = [] then Right(projval r2 c v2) 
      else if nullable r1 then Left (Seq (projval r1 c v1) v2)
                          else Seq (projval r1 c v1) v2)"



lemma mkeps_nullable:
  assumes "nullable(r)" 
  shows "\<turnstile> mkeps r : r"
using assms
apply(induct rule: nullable.induct)
apply(auto intro: Prf.intros)
done

lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
apply(induct rule: nullable.induct)
apply(auto)
done

lemma v3:
  assumes "\<turnstile> v : der c r" 
  shows "\<turnstile> (injval r c v) : r"
using assms
apply(induct arbitrary: v rule: der.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "c = c'")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(5))
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply (metis Prf.intros(1))
apply(auto)[1]
apply (metis Prf.intros(1) mkeps_nullable)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(rule Prf.intros)
apply(auto)[2]
done

lemma v3_proj:
  assumes "\<turnstile> v : r" and "\<exists>s. (flat v) = c # s"
  shows "\<turnstile> (projval r c v) : der c r"
using assms
apply(induct rule: Prf.induct)
prefer 4
apply(simp)
prefer 4
apply(simp)
apply (metis Prf.intros(4))
prefer 2
apply(simp)
apply (metis Prf.intros(2))
prefer 2
apply(simp)
apply (metis Prf.intros(3))
apply(auto)
apply(rule Prf.intros)
apply(simp)
apply (metis Prf_flat_L nullable_correctness)
apply(rule Prf.intros)
apply(rule Prf.intros)
apply (metis Cons_eq_append_conv)
apply(simp)
apply(rule Prf.intros)
apply (metis Cons_eq_append_conv)
apply(simp)
done

lemma v4:
  assumes "\<turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct arbitrary: v rule: der.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "c = c'")
apply(simp)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(simp only: injval.simps flat.simps)
apply(auto)[1]
apply (metis mkeps_flat)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
done

lemma v4_proj:
  assumes "\<turnstile> v : r" and "\<exists>s. (flat v) = c # s"
  shows "c # flat (projval r c v) = flat v"
using assms
apply(induct rule: Prf.induct)
prefer 4
apply(simp)
prefer 4
apply(simp)
prefer 2
apply(simp)
prefer 2
apply(simp)
apply(auto)
by (metis Cons_eq_append_conv)

lemma v4_proj2:
  assumes "\<turnstile> v : r" and "(flat v) = c # s"
  shows "flat (projval r c v) = s"
using assms
by (metis list.inject v4_proj)


section {* Alternative Posix definition *}

inductive 
  PMatch :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  "[] \<in> EMPTY \<rightarrow> Void"
| "[c] \<in> (CHAR c) \<rightarrow> (Char c)"
| "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> L(r1)\<rbrakk> \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> s3 @ s4 = s2 \<and> (s1 @ s3) \<in> L r1 \<and> s4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"


lemma PMatch_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r)
apply(auto)
apply (metis PMatch.intros(1))
apply(subst append.simps(1)[symmetric])
apply (rule PMatch.intros)
apply(simp)
apply(simp)
apply(auto)[1]
apply (rule PMatch.intros)
apply(simp)
apply (rule PMatch.intros)
apply(simp)
apply (rule PMatch.intros)
apply(simp)
by (metis nullable_correctness)


lemma PMatch1:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r" "flat v = s"
using assms
apply(induct s r v rule: PMatch.induct)
apply(auto)
apply (metis Prf.intros(4))
apply (metis Prf.intros(5))
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
apply (metis Prf.intros(1))
done

lemma PMatch_Values:
  assumes "s \<in> r \<rightarrow> v"
  shows "v \<in> Values r s"
using assms
apply(simp add: Values_def PMatch1)
by (metis append_Nil2 prefix_def)

lemma PMatch2:
  assumes "s \<in> (der c r) \<rightarrow> v"
  shows "(c#s) \<in> r \<rightarrow> (injval r c v)"
using assms
apply(induct c r arbitrary: s v rule: der.induct)
apply(auto)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(case_tac "c = c'")
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply (metis PMatch.intros(2))
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(erule PMatch.cases)
apply(simp_all)[5]
apply (metis PMatch.intros(3))
apply(clarify)
apply(rule PMatch.intros)
apply metis
apply(simp add: L_flat_Prf)
apply(auto)[1]
thm v3_proj
apply(frule_tac c="c" in v3_proj)
apply metis
apply(drule_tac x="projval r1 c v" in spec)
apply(drule mp)
apply (metis v4_proj2)
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
defer
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(clarify)
apply(subst append.simps(2)[symmetric])
apply(rule PMatch.intros)
apply metis
apply metis
apply(auto)[1]
apply(simp add: L_flat_Prf)
apply(auto)[1]
apply(frule_tac c="c" in v3_proj)
apply metis
apply(drule_tac x="s3" in spec)
apply(drule mp)
apply(rule_tac x="projval r1 c v" in exI)
apply(rule conjI)
apply (metis v4_proj2)
apply(simp)
apply metis
(* nullable case *)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(clarify)
apply(subst append.simps(2)[symmetric])
apply(rule PMatch.intros)
apply metis
apply metis
apply(auto)[1]
apply(simp add: L_flat_Prf)
apply(auto)[1]
apply(frule_tac c="c" in v3_proj)
apply metis
apply(drule_tac x="s3" in spec)
apply(drule mp)
apply (metis v4_proj2)
apply(simp)
(* interesting case *)
apply(clarify)
apply(simp)
thm L.simps
apply(subst (asm) L.simps(4)[symmetric])
apply(simp only: L_flat_Prf)
apply(simp)
apply(subst append.simps(1)[symmetric])
apply(rule PMatch.intros)
apply (metis PMatch_mkeps)
apply metis
apply(auto)
apply(simp only: L_flat_Prf)
apply(simp)
apply(auto)
apply(drule_tac x="Seq (projval r1 c v) vb" in spec)
apply(drule mp)
apply(simp)
apply (metis append_Cons butlast_snoc last_snoc neq_Nil_conv rotate1.simps(2) v4_proj2)
apply(subgoal_tac "\<turnstile> projval r1 c v : der c r1")
apply (metis Prf.intros(1))
apply(rule v3_proj)
apply(simp)
by (metis Cons_eq_append_conv)

lemma lex_correct1:
  assumes "s \<notin> L r"
  shows "lex r s = None"
using assms
apply(induct s arbitrary: r)
apply(simp)
apply (metis nullable_correctness)
apply(auto)
apply(drule_tac x="der a r" in meta_spec)
apply(drule meta_mp)
apply(auto)
apply(simp add: L_flat_Prf)
by (metis v3 v4)


lemma lex_correct2:
  assumes "s \<in> L r"
  shows "\<exists>v. lex r s = Some(v) \<and> \<turnstile> v : r \<and> flat v = s"
using assms
apply(induct s arbitrary: r)
apply(simp)
apply (metis mkeps_flat mkeps_nullable nullable_correctness)
apply(drule_tac x="der a r" in meta_spec)
apply(drule meta_mp)
apply(simp add: L_flat_Prf)
apply(auto)
apply (metis v3_proj v4_proj2)
apply (metis v3)
apply(rule v4)
by metis

lemma lex_correct3:
  assumes "s \<in> L r"
  shows "\<exists>v. lex r s = Some(v) \<and> s \<in> r \<rightarrow> v"
using assms
apply(induct s arbitrary: r)
apply(simp)
apply (metis PMatch_mkeps nullable_correctness)
apply(drule_tac x="der a r" in meta_spec)
apply(drule meta_mp)
apply(simp add: L_flat_Prf)
apply(auto)
apply (metis v3_proj v4_proj2)
apply(rule PMatch2)
apply(simp)
done

lemma lex_correct4:
  assumes "s \<in> L r"
  shows "s \<in> r \<rightarrow> (lex2 r s)"
using assms
apply(induct s arbitrary: r)
apply(simp)
apply (metis PMatch_mkeps nullable_correctness)
apply(simp)
apply(rule PMatch2)
apply(drule_tac x="der a r" in meta_spec)
apply(drule meta_mp)
apply(simp add: L_flat_Prf)
apply(auto)
apply (metis v3_proj v4_proj2)
done

lemma 
  "lex2 (ALT (CHAR a) (ALT (CHAR b) (SEQ (CHAR a) (CHAR b)))) [a,b] = Right (Right (Seq (Char a) (Char b)))"
apply(simp)
done


section {* Sulzmann's Ordering of values *}


inductive ValOrd :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<succ>_ _" [100, 100, 100] 100)
where
  "v2 \<succ>r2 v2' \<Longrightarrow> (Seq v1 v2) \<succ>(SEQ r1 r2) (Seq v1 v2')" 
| "\<lbrakk>v1 \<succ>r1 v1'; v1 \<noteq> v1'\<rbrakk> \<Longrightarrow> (Seq v1 v2) \<succ>(SEQ r1 r2) (Seq v1' v2')" 
| "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) \<succ>(ALT r1 r2) (Right v2)"
| "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) \<succ>(ALT r1 r2) (Left v1)"
| "v2 \<succ>r2 v2' \<Longrightarrow> (Right v2) \<succ>(ALT r1 r2) (Right v2')"
| "v1 \<succ>r1 v1' \<Longrightarrow> (Left v1) \<succ>(ALT r1 r2) (Left v1')"
| "Void \<succ>EMPTY Void"
| "(Char c) \<succ>(CHAR c) (Char c)"

inductive ValOrd2 :: "val \<Rightarrow> val \<Rightarrow> bool" ("_ 2\<succ> _" [100, 100] 100)
where
  "v2 2\<succ> v2' \<Longrightarrow> (Seq v1 v2) 2\<succ> (Seq v1 v2')" 
| "\<lbrakk>v1 2\<succ> v1'; v1 \<noteq> v1'\<rbrakk> \<Longrightarrow> (Seq v1 v2) 2\<succ> (Seq v1' v2')" 
| "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) 2\<succ> (Right v2)"
| "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) 2\<succ> (Left v1)"
| "v2 2\<succ> v2' \<Longrightarrow> (Right v2) 2\<succ> (Right v2')"
| "v1 2\<succ> v1' \<Longrightarrow> (Left v1) 2\<succ> (Left v1')"
| "Void 2\<succ> Void"
| "(Char c) 2\<succ> (Char c)"

lemma Ord1:
  "v1 \<succ>r v2 \<Longrightarrow> v1 2\<succ> v2"
apply(induct rule: ValOrd.induct)
apply(auto intro: ValOrd2.intros)
done

lemma Ord2:
  "v1 2\<succ> v2 \<Longrightarrow> \<exists>r. v1 \<succ>r v2"
apply(induct v1 v2 rule: ValOrd2.induct)
apply(auto intro: ValOrd.intros)
done

lemma Ord3:
  "\<lbrakk>v1 2\<succ> v2; \<turnstile> v1 : r\<rbrakk> \<Longrightarrow> v1 \<succ>r v2"
apply(induct v1 v2 arbitrary: r rule: ValOrd2.induct)
apply(auto intro: ValOrd.intros elim: Prf.cases)
done

section {* Posix definition *}

definition POSIX :: "val \<Rightarrow> rexp \<Rightarrow> bool" 
where
  "POSIX v r \<equiv> (\<turnstile> v : r \<and> (\<forall>v'. (\<turnstile> v' : r \<and> flat v' \<sqsubseteq> flat v) \<longrightarrow> v \<succ>r v'))"

lemma ValOrd_refl:
  assumes "\<turnstile> v : r"
  shows "v \<succ>r v"
using assms
apply(induct)
apply(auto intro: ValOrd.intros)
done

lemma ValOrd_total:
  shows "\<lbrakk>\<turnstile> v1 : r; \<turnstile> v2 : r\<rbrakk>  \<Longrightarrow> v1 \<succ>r v2 \<or> v2 \<succ>r v1"
apply(induct r arbitrary: v1 v2)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(case_tac "v1a = v1b")
apply(simp)
apply(rule ValOrd.intros(1))
apply (metis ValOrd.intros(1))
apply(rule ValOrd.intros(2))
apply(auto)[2]
apply(erule contrapos_np)
apply(rule ValOrd.intros(2))
apply(auto)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Ord1 Ord3 Prf.intros(2) ValOrd2.intros(6))
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply (metis le_eq_less_or_eq neq_iff)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply (metis le_eq_less_or_eq neq_iff)
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
by metis

lemma ValOrd_anti:
  shows "\<lbrakk>\<turnstile> v1 : r; \<turnstile> v2 : r; v1 \<succ>r v2; v2 \<succ>r v1\<rbrakk> \<Longrightarrow> v1 = v2"
apply(induct r arbitrary: v1 v2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(erule ValOrd.cases)
apply(simp_all)[8]
done

lemma POSIX_ALT_I1:
  assumes "POSIX v1 r1" 
  shows "POSIX (Left v1) (ALT r1 r2)"
using assms
unfolding POSIX_def
apply(auto)
apply (metis Prf.intros(2))
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd.intros)
apply(auto)
apply(rule ValOrd.intros)
by (metis le_eq_less_or_eq length_sprefix sprefix_def)

lemma POSIX_ALT_I2:
  assumes "POSIX v2 r2" "\<forall>v'. \<turnstile> v' : r1 \<longrightarrow> length (flat v2) > length (flat v')"
  shows "POSIX (Right v2) (ALT r1 r2)"
using assms
unfolding POSIX_def
apply(auto)
apply (metis Prf.intros)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd.intros)
apply metis
apply(rule ValOrd.intros)
apply metis
done

section {* tryout with all-mkeps *}

fun 
  alleps :: "rexp \<Rightarrow> val set"
where
  "alleps(NULL) = {}"
| "alleps(EMPTY) = {Void}"
| "alleps(CHAR c) = {}"
| "alleps(SEQ r1 r2) = {Seq v1 v2 | v1 v2. v1 \<in> alleps r1 \<and> v2 \<in> alleps r2}"
| "alleps(ALT r1 r2) = {Left v1 | v1. v1 \<in> alleps r1} \<union> {Right v2 | v2. v2 \<in> alleps r2}"

fun injall :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val set"
where
  "injall (EMPTY) c Void = {}"
| "injall (CHAR d) c Void = (if c = d then {Char d} else {})"
| "injall (ALT r1 r2) c (Left v1) = {Left v | v. v \<in> injall r1 c v1}"
| "injall (ALT r1 r2) c (Right v2) = {Right v | v. v \<in> injall r2 c v2}"
| "injall (SEQ r1 r2) c (Seq v1 v2) = {Seq v v2 | v. v \<in> injall r1 c v1}"
| "injall (SEQ r1 r2) c (Left (Seq v1 v2)) = {Seq v v2 | v. v \<in> injall r1 c v1}"
| "injall (SEQ r1 r2) c (Right v2) = {Seq v v' | v v'. v \<in> alleps r1 \<and> v' \<in> injall r2 c v2}"

fun 
  allvals :: "rexp \<Rightarrow> string \<Rightarrow> val set"
where
  "allvals r [] = alleps r"
| "allvals r (c#s) = {v | v v'. v \<in> injall r c v' \<and> v' \<in> allvals (der c r) s}"

lemma q1: 
  assumes "v \<in> alleps r"
  shows "\<turnstile> v : r \<and> flat v = []"
using assms
apply(induct r arbitrary: v)
apply(auto intro: Prf.intros)
done


lemma allvals_NULL:
  shows "allvals (NULL) s = {}"
apply(induct_tac s)
apply(simp)
apply(simp)
done

lemma allvals_EMPTY:
  shows "allvals (EMPTY) [] = {Void}"
  and   "s \<noteq> [] \<Longrightarrow> allvals (EMPTY) s = {}"
apply(simp)
apply(case_tac s)
apply(simp)
apply(simp add: allvals_NULL)
done

lemma allvals_CHAR:
  shows "allvals (CHAR c) [c] = {Char c}"
  and   "s \<noteq> [c] \<Longrightarrow> allvals (CHAR c) s = {}"
apply(simp)
apply(case_tac s)
apply(simp)
apply(case_tac "c = a")
apply(simp add: allvals_EMPTY)
apply(simp add: allvals_NULL)
done

lemma allvals_ALT:
  shows "allvals (ALT r1 r2) s = {Left v1 | v1. v1 \<in> allvals r1 s} \<union>
                                 {Right v2 | v2. v2 \<in> allvals r2 s}"
apply(induct s arbitrary: r1 r2)
apply(simp)
apply(simp)
apply(auto)
apply blast
apply(rule_tac x="Left v'" in exI)
apply(simp)
apply(rule_tac x="Right v'" in exI)
apply(simp)
done

lemma allvals_SEQ_Nil:
  "allvals (SEQ r1 r2) [] = {Seq v1 v2 | v1 v2. v1 \<in> allvals r1 [] \<and> v2 \<in> allvals r2 []}"
by simp

lemma allvals_SEQ:
  shows "allvals (SEQ r1 r2) s = {Seq v1 v2 | v1 v2 s1 s2. 
      s = s1 @ s2 \<and> v1 \<in> allvals r1 s1 \<and> v2 \<in> allvals r2 s2}"
using assms
apply(induct s arbitrary: r1 r2)
apply(simp)
apply(simp)
apply(auto)
apply(simp_all add: allvals_ALT)
apply(auto)
apply (metis (mono_tags, lifting) allvals.simps(2) append_Cons mem_Collect_eq)
apply fastforce
prefer 2
apply(rule_tac x="a#s1" in exI)
apply(rule_tac x="s2" in exI)
apply(simp)
apply(fastforce)
prefer 2
apply(subst (asm) Cons_eq_append_conv)
apply(auto)[1]
using Prf_flat_L nullable_correctness q1 apply fastforce
apply(rule_tac x="Seq v' v2" in exI)
apply(simp)
apply(rule_tac x="ys'" in exI)
apply(rule_tac x="s2" in exI)
apply(simp)
apply(subst (asm) Cons_eq_append_conv)
apply(auto)[1]
apply(rule_tac x="Right v'" in exI)
apply(simp)
apply(rule_tac x="Left (Seq v' v2)" in exI)
apply(simp)
apply(auto)[1]
done

lemma q11:
  assumes "nullable r" "\<turnstile> v : r" "flat v = []"
  shows "v \<in> alleps r"
using assms
apply(induct r arbitrary: v)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(subgoal_tac "nullable r2a")
apply(auto)
using not_nullable_flat apply auto[1]
 apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(subgoal_tac "nullable r1a")
apply(auto)
using not_nullable_flat apply auto[1]
done

lemma q33:
  assumes "nullable r"
  shows "alleps r = {v. \<turnstile> v : r \<and> flat v = []}"
using assms
apply(auto) 
apply (simp_all add: q1)
by (simp add: q11)


lemma k0:
  assumes "\<turnstile> v : der a r" "v' \<in> injall r a v"
  shows "flat v' = a # flat v"
using assms
apply(induct a r arbitrary: v v' rule: der.induct)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(case_tac "c = c'")
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
apply(auto)[1]
apply(case_tac "nullable r1")
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
using q1 apply blast
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
done

lemma k:
  assumes "\<turnstile> v' : der a r" "v \<in> injall r a v'"
  shows "\<turnstile> v : r"
using assms
apply(induct a r arbitrary: v v' rule: der.induct)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(case_tac "c = c'")
apply(erule Prf.cases)
apply(simp_all)
apply(rule Prf.intros)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(auto intro: Prf.intros)[1]
apply(auto intro: Prf.intros)[1]
apply(case_tac "nullable r1")
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(auto intro: Prf.intros)[1]
using Prf.intros(1) q1 apply blast
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
using Prf.intros(1) by auto



lemma q22: 
  assumes "v \<in> allvals r s"
  shows "\<turnstile> v : r \<and> s \<in> L (r) \<and> flat v = s"
using assms
apply(induct s arbitrary: v r)
apply(auto)
apply(simp_all add: q1)
using Prf_flat_L q1 apply fastforce
apply(drule_tac x="v'" in meta_spec)
apply(drule_tac x="der a r" in meta_spec)
apply(simp)
apply(clarify)
apply(rule k)
apply(assumption)
apply(assumption)
apply(drule_tac x="v'" in meta_spec)
apply(drule_tac x="der a r" in meta_spec)
apply(simp)
apply(clarify)
using Prf_flat_L v3 v4 apply fastforce
apply(drule_tac x="v'" in meta_spec)
apply(drule_tac x="der a r" in meta_spec)
apply(simp)
apply(clarify)
using k0 by blast

lemma ra:
  assumes "v \<in> allvals r1 s"
  shows "Left v \<in> allvals (ALT r1 r2) s"
using assms
apply(induct s arbitrary: r1 r2 v)
apply(simp)
apply(auto)
apply(rule_tac x="Left v'" in exI)
apply(simp)
done

lemma rb:
  assumes "v \<in> allvals r2 s"
  shows "Right v \<in> allvals (ALT r1 r2) s"
using assms
apply(induct s arbitrary: r1 r2 v)
apply(simp)
apply(auto)
apply(rule_tac x="Right v'" in exI)
apply(simp)
done

lemma r1:
  assumes "v1 \<in> alleps r1" "v2 \<in> allvals r2 s2"
  shows "Seq v1 v2 \<in> allvals (SEQ r1 r2) s2"
using assms
apply(induct s2 arbitrary: r1 r2 v1 v2)
apply(simp)
apply(simp)
apply(auto)
apply(rule_tac x="Right v'" in exI)
apply(simp)
apply(rule rb)
apply(simp)
using not_nullable_flat q1 by blast

lemma r2:
  assumes "v1 \<in> allvals r1 s1" "v2 \<in> allvals r2 s2"
  shows "Seq v1 v2 \<in> allvals (SEQ r1 r2) (s1 @ s2)"
using assms
apply(induct s1 arbitrary: r1 r2 v1 v2 s2)
apply(simp)
apply(rule r1) 
apply(simp)
apply(simp)
apply(simp)
apply(auto)
apply(drule_tac x="der a r1" in meta_spec)
apply(drule_tac x="r2" in meta_spec)
apply(drule_tac x="v'" in meta_spec)
apply(drule_tac x="v2" in meta_spec)
apply(drule_tac x="s2" in meta_spec)
apply(simp)
apply(rule_tac x="Left (Seq v' v2)" in exI)
apply(simp)
apply(rule ra)
apply(simp)
apply(drule_tac x="der a r1" in meta_spec)
apply(drule_tac x="r2" in meta_spec)
apply(drule_tac x="v'" in meta_spec)
apply(drule_tac x="v2" in meta_spec)
apply(drule_tac x="s2" in meta_spec)
apply(simp)
apply(rule_tac x="Seq v' v2" in exI)
apply(simp)
done

lemma q22a: 
  assumes " s \<in> L (r)"
  shows "\<exists>v. v \<in> allvals r s \<and> flat v = s"
using assms
apply(induct r arbitrary: s)
apply(auto)
apply(simp add: Sequ_def)
apply(auto)
apply(drule_tac x="s1" in meta_spec) 
apply(drule_tac x="s2" in meta_spec) 
apply(auto)
apply(rule_tac x="Seq v va" in exI)
apply(simp)
apply(rule r2)
apply(simp)
apply(simp)
apply(drule_tac x="s" in meta_spec) 
apply(simp)
apply(auto)
apply(rule_tac x="Left v" in exI)
apply(simp)
apply(rule ra)
apply(simp)
apply(drule_tac x="s" in meta_spec) 
apply(drule_tac x="s" in meta_spec) 
apply(simp)
apply(auto)
apply(rule_tac x="Right v" in exI)
apply(simp)
apply(rule rb)
apply(simp)
done

lemma q22b: 
  assumes " s \<in> L (r)" "\<turnstile> v : r" "flat v = s"
  shows "v \<in> allvals r s"
using assms
apply(induct r arbitrary: s v)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(simp add: Sequ_def)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(simp add: append_eq_append_conv2)
apply(auto)
apply (metis Prf_flat_L append_assoc r2)
apply (metis Prf_flat_L r2)
apply(erule Prf.cases)
apply(simp_all)
apply(auto intro: ra rb)[2]
apply(rule rb)
apply (simp add: Prf_flat_L)
apply(erule Prf.cases)
apply(simp_all)
apply(auto intro: ra rb)[2]
apply(rule ra)
by (simp add: Prf_flat_L)


lemma q2:
  assumes "s \<in> L(r)" 
  shows "allvals r s = {v. \<turnstile> v : r \<and> s \<in> L (r) \<and> flat v = s}"
using assms
apply(auto)
apply (simp add: q22)
apply (simp add: q22)
by (simp add: q22b)

lemma r3a:
  assumes "v' \<in> allvals (SEQ r1 r2) (s1 @ s2)" 
          "(s1 @ s2) \<in> L (SEQ r1 r2)"
  shows "\<exists>v1 v2. v' = Seq v1 v2 \<and> v1 \<in> allvals r1 s1 \<and> v2 \<in> allvals r2 s2" 
using assms
apply(subst (asm) q2)
apply(auto)
apply(erule_tac Prf.cases)
apply(simp_all)
apply(rule conjI)
apply(simp add: append_eq_append_conv2)
apply(auto)
apply(subst q2)
oops

lemma r3:
  assumes "Seq v1 v2 \<in> allvals (SEQ r1 r2) (s1 @ s2)" 
          "flat v1 = s1" "flat v2 = s2"
          "(s1 @ s2) \<in> L (SEQ r1 r2)"
  shows "v1 \<in> allvals r1 s1"  "v2 \<in> allvals r2 s2" 
using assms
apply(subst (asm) q2)
apply(auto)
apply(erule_tac Prf.cases)
apply(simp_all)
apply(subst q2)
apply(auto)
using Prf_flat_L apply blast
using Prf_flat_L apply blast
using assms
apply(subst (asm) q2)
apply(auto)
apply(erule_tac Prf.cases)
apply(simp_all)
apply(subst q2)
apply(auto)
using Prf_flat_L apply blast
using Prf_flat_L apply blast
done


definition POSIX2 :: "val \<Rightarrow> rexp \<Rightarrow> string \<Rightarrow> bool" 
where
  "POSIX2 v r s \<equiv> (\<turnstile> v : r \<and> flat v = s \<and> (\<forall>v'\<in>allvals r s. v \<succ>r v'))"




lemma k1:
  assumes "nullable r"
  shows "POSIX2 v r [] \<Longrightarrow> \<forall>v' \<in> alleps r. v \<succ>r v'"
using assms
apply(induct r arbitrary: v)
apply(simp_all)
apply(simp add: POSIX2_def)
apply(auto)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
done

lemma k2:
  assumes "s \<in> L r"
  shows "POSIX2 v r s \<Longrightarrow> \<forall>v' \<in> allvals r s. v \<succ>r v'"
using assms
apply(induct s arbitrary: r v)
apply(simp)
apply(rule k1)
apply (simp add: nullable_correctness)
apply(simp)
apply(simp)
apply(auto)
apply(simp only: POSIX2_def)
apply(simp)
apply(clarify)
apply(drule_tac x="x" in spec)
apply(drule mp)
apply(auto)
done

lemma pos:
  assumes "s \<in> r \<rightarrow> v" 
  shows "v \<in> allvals r s"
using assms
apply(subst q2)
using PMatch1(1) PMatch1(2) Prf_flat_L apply blast
apply(simp)
using PMatch1(1) PMatch1(2) Prf_flat_L by blast

lemma mkeps_val:
  assumes "nullable r"
  shows "mkeps r \<in> alleps r"
using assms
apply(induct r)
apply(auto)
done

lemma injval_injall:
  assumes "\<turnstile> v : der a r"
  shows "injval r a v \<in> injall r a v"
using assms
apply(induct a r arbitrary: v rule: der.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(case_tac "c = c'")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
using mkeps_val apply blast
apply(erule Prf.cases)
apply(simp_all)
done


lemma mkeps_val1:
  assumes "nullable r" "v \<succ>r mkeps r" "flat v = []" "\<turnstile> v : r"
  shows "v = mkeps r"
using assms
apply(induct r arbitrary: v)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule Prf.cases)
apply(auto)
apply(erule Prf.cases)
apply(auto)
apply(erule Prf.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule Prf.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply(erule Prf.cases)
apply(auto)
apply(erule ValOrd.cases)
apply(auto)
apply (simp add: not_nullable_flat)
apply(erule ValOrd.cases)
apply(auto)
done

lemma sulzmann_our:
  assumes "v \<in> alleps r" "nullable r"
  shows "mkeps r \<succ>r v"
using assms
apply(induct r arbitrary: v)
apply(simp_all)
apply(rule ValOrd.intros)
apply(auto)[1]
apply(case_tac "mkeps r1 = v1")
apply(simp)
apply(rule ValOrd.intros)
apply(blast)
apply(rule ValOrd.intros)
apply(blast)
apply(simp)
apply(auto)
apply(rule ValOrd.intros)
apply(blast)
apply(rule ValOrd.intros)
apply(blast)
apply(rule ValOrd.intros)
using not_nullable_flat q1 apply blast
apply(rule ValOrd.intros)
using q1 apply auto[1]
apply(rule ValOrd.intros)
apply (simp add: q1)
apply(rule ValOrd.intros)
apply(blast)
done

lemma destruct:
  assumes "\<forall>s3. s1 @ s3 \<in> L r1 \<longrightarrow> s3 = [] \<or> (\<forall>s4. s3 @ s4 = s2 \<longrightarrow> s4 \<notin> L r2)"
  and "s1 \<in> L r1" "s2 \<in> L r2" "(s1' @ s2') \<sqsubseteq> (s1 @ s2)"
  and "s1'@ s2' \<in> L (SEQ r1 r2)"  "s1' \<in> L r1"
  shows "s1' \<sqsubseteq> s1"
using assms
apply(simp add: prefix_def)
apply(auto)
apply(simp add: append_eq_append_conv2)
apply(auto)
apply(simp add: Sequ_def)
apply(auto)
apply(drule_tac x="us" in spec)
apply(simp)
apply(auto)
apply(simp add: append_eq_append_conv2)
apply(auto)
oops

lemma inj_ord:
  assumes "v1 \<succ>(der a r) v2" "s \<in> (der a r) \<rightarrow> v1" "s' \<in> L (der a r)" 
          "v1 \<in> allvals (der a r) s" "v2 \<in> allvals (der a r) s'" "s' \<sqsubseteq> s" 
  shows "injval r a v1 \<succ>r injval r a v2"
using assms
apply(induct a r arbitrary: s s' v1 v2 rule: der.induct)
apply(simp_all)
(*apply(simp add: allvals_NULL)
apply(simp add: allvals_NULL)*)
apply(case_tac "c = c'")
apply(simp)
apply(case_tac "s = []")
apply(subgoal_tac "s' = []")
prefer 2
using allvals_EMPTY(2) apply blast
apply(simp add: allvals_EMPTY)
apply(rule ValOrd.intros)
apply(simp add: allvals_EMPTY)
apply(simp)
(*apply(simp add: allvals_NULL)*)
(* ALT case *)
apply(simp add: allvals_ALT)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(erule PMatch.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(subst v4)
apply(simp)
apply (simp add: q22)
apply(subst v4)
apply(simp)
apply (simp add: q22)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(subst v4)
apply (simp add: q22)
apply(subst v4)
apply (simp add: q22)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(erule PMatch.cases)
apply(simp_all)
using q22 apply auto[1]
apply(erule PMatch.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
using q22 apply auto[1]
apply(erule PMatch.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(subst v4)
apply (simp add: q22)
apply(subst v4)
apply (simp add: q22)
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(subst v4)
apply (simp add: q22)
apply(subst v4)
apply (simp add: q22)
apply(simp)
using q22 apply auto[1]
apply(erule PMatch.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(rule ValOrd.intros)
using q22 apply auto[1]
(* seq case *)
apply(case_tac "nullable r1")
apply(simp)
prefer 2
apply(simp)
apply(simp add: allvals_SEQ)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
apply(rule ValOrd.intros)
apply(simp)
apply(rule ValOrd.intros)
apply(erule PMatch.cases)
apply(simp_all)
apply(clarify)
apply(rotate_tac 1)
apply(drule_tac x="s1b" in meta_spec)
apply(rotate_tac 13)
apply(drule_tac x="s1a" in meta_spec)
apply(drule_tac x="v1c" in meta_spec)
apply(drule_tac x="v1'" in meta_spec)
apply(simp)
apply(subgoal_tac "s1 = s1b")
prefer 2
apply (metis PMatch1(2) q22)
apply(simp)
apply(clarify)
apply(drule destruct)
apply (metis PMatch1(2) q22)
apply (metis PMatch1(2) q22)
apply(assumption)
apply (metis PMatch1(2) q22)
apply (metis PMatch1(2) q22)
apply(subgoal_tac "s2a = s2b")
prefer 2
apply (metis PMatch1(2) q22)
apply(drule destruct)
apply (metis PMatch1(2) q22)
apply (metis PMatch1(2) q22)
apply(assumption)
back
apply (metis PMatch1(2) q22)
apply (metis PMatch1(2) q22)



apply(simp add: allvals_ALT)
apply(auto)
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
apply(rule ValOrd.intros)
apply(blast)
apply(rule ValOrd.intros)
apply(clarify)
apply(simp add: allvals_SEQ)
apply(auto)[1]
apply(erule PMatch.cases)
apply(simp_all)
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)
apply(auto)
apply(drule_tac x="s1b" in meta_spec)
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="v1'a" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(subgoal_tac "s1 = s1b")
apply(simp)
apply (metis PMatch1(2) q22)
apply(drule_tac meta_mp)
apply(subgoal_tac "s1a = s1b")
apply(simp)
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply(subgoal_tac "s2 = s2a")
apply(simp)
apply(clarify)
prefer 2
using q22 apply blast
using q22 apply blast
using q22 apply blast
apply(subgoal_tac "usa = []")
apply(simp)
prefer 2
using q22 apply blast
prefer 3
apply(simp)
prefer 4
apply(erule PMatch.cases)
apply(simp_all)
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)
apply(auto)
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
apply(simp)
prefer 5
apply(erule PMatch.cases)
apply(simp_all)
apply(clarify)
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
apply(simp add: allvals_SEQ)
apply(auto)[1]
apply (simp add: q22)
apply(simp add: allvals_SEQ)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply (simp add: q22)
thm PMatch2
apply(drule PMatch2)


lemma sulzmann_our:
  assumes "\<forall>v' \<in> allvals r s. v \<succ>r v'" "s \<in> L r" "\<turnstile> v : r" "flat v = s"
  shows "s \<in> r \<rightarrow> v"
using assms
apply(induct s arbitrary: r v)
apply(simp_all)
apply(subst (asm) q33)
apply (simp add: nullable_correctness)
apply(simp)
apply(drule_tac x="mkeps r" in spec)
apply(drule mp)
apply(rule conjI)
using mkeps_val not_nullable_flat q1 apply blast
using mkeps_flat not_nullable_flat apply blast
apply(subgoal_tac "nullable r")
apply(drule mkeps_val1)
apply(assumption)
apply(simp)
apply(simp)
apply(simp)
using PMatch_mkeps not_nullable_flat apply blast
using not_nullable_flat apply blast
apply(drule_tac x="der a r" in meta_spec)
apply(drule_tac x="projval r a v" in meta_spec)
apply(drule meta_mp)
defer
apply(drule meta_mp)
using Prf_flat_L v3_proj v4_proj2 apply blast
apply(drule meta_mp)
using v3_proj apply blast
apply(drule meta_mp)
apply (simp add: v4_proj2)
defer
apply(rule ballI)
apply(drule_tac x="injval r a x" in spec)
apply(auto)
apply(drule_tac x="x" in spec)
apply(drule mp)
apply(rule injval_injall)
using q22 apply blast
apply(simp)
(* HERE *)


lemma our_sulzmann:
  assumes "s \<in> r \<rightarrow> v" "v' \<in> allvals r s"
  shows "v \<succ>r v'"
using assms
apply(induct r arbitrary: s v v')
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
(* SEQ - case *)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(clarify)
apply(subst (asm) (3) q2)
apply(simp add: Sequ_def)
apply(rule_tac x="s1" in exI)
apply(rule_tac x="s2" in exI)
apply(simp)
apply(rule conjI)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(simp)
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "v1 = v1a")
apply(simp)
apply(rule ValOrd.intros)
apply(rotate_tac 1)
apply(drule_tac x="s2" in meta_spec)
apply(drule_tac x="v2" in meta_spec)
apply(drule_tac x="v2a" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(subst q2)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(rule conjI)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply (simp add: PMatch1(2))
apply(simp)
apply(rule ValOrd.intros)
prefer 2
apply(simp)
apply(drule_tac x="s1" in meta_spec)
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="v1a" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(subst q2)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(simp)
apply(rule conjI)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(subst (asm) append_eq_append_conv2)
apply(auto)[1]
using Prf_flat_L apply fastforce

apply(drule_tac x="us" in spec)
apply(auto)[1]

using Prf_flat_L apply fastforce
using Prf_flat_L apply blast
apply(drule_tac meta_mp)
apply(subst q2)
using Prf_flat_L apply fastforce
apply(simp)
using Prf_flat_L apply fastforce
apply(simp)
apply(drule_tac x="flat v1a" in meta_spec)
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule meta_mp)
apply(subst q2)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(simp)
apply(rule conjI)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(drule_tac x="[]" in spec)
apply(auto)[1]

using Prf_flat_L apply fast
apply(drule_tac x="us" in spec)
apply(simp)

apply (simp add: Prf_flat_L)
apply(simp)
thm PMatch1
qed
done
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)
apply(rule ValOrd.intros)
apply(drule_tac x="v1" in meta_spec)
apply(drule meta_mp)
apply(subst q2)
apply (simp add: Prf_flat_L)
apply(simp)
apply (simp add: Prf_flat_L)
apply(simp)
apply(rule ValOrd.intros)
apply(auto)[1]
apply (simp add: PMatch1(2))
apply (simp add: PMatch1(2))
apply(subst (asm) (2) q2)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)
prefer 2
apply(rule ValOrd.intros)
using q22b apply blast
apply(rule ValOrd.intros)
apply(auto)
using Prf_flat_L apply blast
apply(subst (asm) (3) q2)
apply(simp add: Sequ_def)
apply(rule_tac x="s1" in exI)
apply(rule_tac x="s2" in exI)
apply(simp)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)
apply(auto simp add: Sequ_def)[1]
apply(case_tac "v1 = v1a")
apply(simp)
apply(rule ValOrd.intros)
apply(rotate_tac 3)
apply(drule_tac x="v2a" in meta_spec)
apply(drule_tac meta_mp)
apply(subst q2)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(rule conjI)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply (metis PMatch1(2) same_append_eq)
apply(simp)
apply(rule ValOrd.intros)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(subst q2)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
apply(simp)
apply(rule conjI)
using PMatch1(1) PMatch1(2) Prf_flat_L apply fastforce
prefer 2
apply(simp)
prefer 2
apply(simp)
apply(rotate_tac 7)
apply(drule sym)
apply(simp)
apply(subst (asm) (2) append_eq_append_conv2)
apply(auto)[1]
apply(frule_tac x="us" in spec)
apply(auto)[1]
prefer 2
apply(drule_tac x="flat v2a" in spec)
apply(auto)[1]

apply(subgoal_tac "flat v2a = s2")
apply(simp)

apply(simp add: append_eq_append_conv2)
apply(auto)
prefer 2
apply blast
prefer 2
apply (metis Prf_flat_L append_self_conv2)
prefer 4



lemma our_sulzmann:
  assumes "s \<in> r \<rightarrow> v"
  shows "POSIX2 v r s"
using assms
apply(induct s r v)
apply(auto)
apply(simp add: POSIX2_def)
using Prf.intros(4) ValOrd.intros(7) apply blast
apply(simp add: POSIX2_def)
apply (simp add: Prf.intros(5) ValOrd.intros(8))
apply(simp add: POSIX2_def)
apply(auto)
apply(rule Prf.intros)
apply(simp)
apply(subgoal_tac "(\<exists>x1. x = Left x1) \<or> (\<exists>x1. x = Right x1)")
apply(auto)[1]
apply(rule ValOrd.intros)
apply(drule_tac x="x1" in bspec)
apply(subst (asm) q2)
apply (simp add: Prf_flat_L)
apply(simp)
apply(subst q2)
apply (simp add: Prf_flat_L)
apply(auto)[1]
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)
apply (simp add: Prf_flat_L)
apply(rule ValOrd.intros)
apply(subst (asm) (2) q2)
apply (simp add: Prf_flat_L)
apply(auto)[1]
defer
apply(simp add: POSIX2_def)
apply(auto)[1]
apply(rule Prf.intros)
apply (simp add: Prf_flat_L)
apply(subgoal_tac "(\<exists>x1. x = Left x1) \<or> (\<exists>x1. x = Right x1)")
apply(auto)[1]
apply(rule ValOrd.intros)
apply(subst (asm) (2) q2)
apply (simp add: Prf_flat_L)
apply(auto)[1]
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
using Prf_flat_L apply force
apply(rule ValOrd.intros)
apply(drule_tac x="x1" in bspec)
apply(subst (asm) q2)
apply (simp add: Prf_flat_L)
apply(auto)[1]
apply(subst q2)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)
defer
apply(auto)[1]
apply(simp add: POSIX2_def)
apply(auto intro: Prf.intros)[1]
apply(subgoal_tac "(\<exists>x1 x2. x = Seq x1 x2 \<and> flat v1 @ flat v2 = flat x1 @ flat x2)")
apply(auto)[1]
apply(case_tac "v1 = x1")
apply(simp)
apply(rule ValOrd.intros)
apply(rotate_tac 6)
apply(drule_tac x="x2" in bspec)
apply(subst (asm) q2)
apply (simp add: Sequ_def Prf_flat_L)

using Prf_flat_L apply blast
apply(auto)[1]
apply(rotate_tac 6)
apply(erule Prf.cases)
apply(simp_all)
apply(subst q2)
apply (simp add: Prf_flat_L)
apply(auto)[1]
apply(auto simp add: Sequ_def)
using Prf_flat_L apply blast
apply(rule ValOrd.intros)
apply(rotate_tac 5)
apply(drule_tac x="x1" in bspec)
apply(rotate_tac 1)
apply(subst (asm) q2)
apply (simp add: Sequ_def Prf_flat_L)
using Prf_flat_L apply blast
apply(auto)[1]
apply(subst q2)
apply (simp add: Sequ_def Prf_flat_L)
apply(auto)[1]
apply(rotate_tac 7)
apply(erule Prf.cases)
apply(simp_all)
apply (simp add: Sequ_def Prf_flat_L)
apply(rotate_tac 7)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto simp add: Sequ_def)[1]
using Prf_flat_L apply fastforce
apply(simp add: append_eq_append_conv2)
apply(auto simp add: Sequ_def)[1]

apply(auto)[1]

apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)
apply(simp add: POSIX2_def)

lemma "s \<in> L(r) \<Longrightarrow> \<exists>v. POSIX2 v r s"
apply(induct r arbitrary: s)
apply(auto)
apply(rule_tac x="Void" in exI)
apply(simp add: POSIX2_def)
apply (simp add: Prf.intros(4) ValOrd.intros(7))
apply(rule_tac x="Char x" in exI)
apply(simp add: POSIX2_def)
apply (simp add: Prf.intros(5) ValOrd.intros(8))
defer
apply(drule_tac x="s" in meta_spec)
apply(auto)[1]
apply(rule_tac x="Left v" in exI)
apply(simp add: POSIX2_def)
apply(auto)[1]
using Prf.intros(2) apply blast

apply(case_tac s)
apply(simp)
apply(auto)[1]
apply (simp add: ValOrd.intros(6))
apply(rule ValOrd.intros)

thm PMatch.intros[no_vars]

lemma POSIX_PMatch:
  assumes "s \<in> r \<rightarrow> v" "v' \<in> Values r s"
  shows "v \<succ>r v' \<or> length (flat v') < length (flat v)" 
using assms
apply(induct r arbitrary: s v v' rule: rexp.induct)
apply(simp_all add: Values_recs)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(simp add: prefix_def)
apply (metis ValOrd.intros(8))
apply(auto)[1]
defer
apply(auto)[1]
apply(erule PMatch.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(6))
apply (metis (no_types, lifting) PMatch1(2) Prf_flat_L Values_def length_sprefix mem_Collect_eq sprefix_def)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply (metis (no_types, lifting) PMatch1(2) ValOrd.intros(3) Values_def length_sprefix mem_Collect_eq order_refl sprefix_def)
apply (metis ValOrd.intros(5))
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(auto)
apply(case_tac "v1a = v1")
apply(simp)
apply(rule ValOrd.intros(1))
apply (metis PMatch1(2) append_Nil comm_monoid_diff_class.diff_cancel drop_0 drop_all drop_append order_refl rest_def)
apply(rule ValOrd.intros(2))
apply(auto)
apply(drule_tac x="s1" in meta_spec)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac x="v1" in meta_spec)
apply(auto)
apply(drule meta_mp)
defer
apply(auto)[1]
apply(frule PMatch1)
apply(drule PMatch1(2))
apply(frule PMatch1)
apply(drule PMatch1(2))
apply(auto)[1]
apply(simp add: Values_def)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply(rotate_tac 10)
apply(drule sym)
apply(simp)
apply(simp add: rest_def)
apply(case_tac "s3a = []")
apply(auto)[1]


apply (metis ValOrd.intros(6))
apply (metis (no_types, lifting) PMatch1(2) ValOrd.intros(3) Values_def length_sprefix mem_Collect_eq order_refl sprefix_def)
apply(auto)[1]
apply (metis (no_types, lifting) PMatch1(2) Prf_flat_L Values_def length_sprefix mem_Collect_eq sprefix_def)
apply (metis ValOrd.intros(5))
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule PMatch.cases)
apply(simp_all)[5]
defer
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(clarify)
apply(simp add: L_flat_Prf)

apply(clarify)
apply (metis ValOrd.intros(8))
apply (metis POSIX_ALT_I1)
apply(rule POSIX_ALT_I2)
apply(simp)
apply(auto)[1]
apply(simp add: POSIX_def)
apply(frule PMatch1(1))
apply(frule PMatch1(2))
apply(simp)


lemma POSIX_PMatch:
  assumes "s \<in> r \<rightarrow> v" 
  shows "POSIX v r" 
using assms
apply(induct arbitrary: rule: PMatch.induct)
apply(auto)
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(4))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply (metis POSIX_ALT_I1)
apply(rule POSIX_ALT_I2)
apply(simp)
apply(auto)[1]
apply(simp add: POSIX_def)
apply(frule PMatch1(1))
apply(frule PMatch1(2))
apply(simp)



lemma ValOrd_PMatch:
  assumes "s \<in> r \<rightarrow> v1" "\<turnstile> v2 : r" "flat v2 = s"
  shows "v1 \<succ>r v2"
using assms
apply(induct arbitrary: v2 rule: PMatch.induct)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis ValOrd.intros(6))
apply(clarify)
apply (metis PMatch1(2) ValOrd.intros(3) order_refl)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis Prf_flat_L)
apply (metis ValOrd.intros(5))
(* Seq case *)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(case_tac "v1 = v1a")
apply(auto)
apply (metis PMatch1(2) ValOrd.intros(1) same_append_eq)
apply(rule ValOrd.intros(2))
apply(auto)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
prefer 2
apply(simp)
apply(simp add: append_eq_append_conv2)
apply(auto)
apply (metis Prf_flat_L)
apply(case_tac "us = []")
apply(simp)
apply(drule_tac x="us" in spec)
apply(drule mp)

thm L_flat_Prf
apply(simp add: L_flat_Prf)
thm append_eq_append_conv2
apply(simp add: append_eq_append_conv2)
apply(auto)
apply(drule_tac x="us" in spec)
apply(drule mp)
apply metis
apply (metis append_Nil2)
apply(case_tac "us = []")
apply(auto)
apply(drule_tac x="s2" in spec)
apply(drule mp)

apply(auto)[1]
apply(drule_tac x="v1a" in meta_spec)
apply(simp)

lemma refl_on_ValOrd:
  "refl_on (Values r s) {(v1, v2). v1 \<succ>r v2 \<and> v1 \<in> Values r s \<and> v2 \<in> Values r s}"
unfolding refl_on_def
apply(auto)
apply(rule ValOrd_refl)
apply(simp add: Values_def)
done


section {* Posix definition *}

definition POSIX :: "val \<Rightarrow> rexp \<Rightarrow> bool" 
where
  "POSIX v r \<equiv> (\<turnstile> v : r \<and> (\<forall>v'. (\<turnstile> v' : r \<and> flat v = flat v') \<longrightarrow> v \<succ>r v'))"

definition POSIX2 :: "val \<Rightarrow> rexp \<Rightarrow> bool" 
where
  "POSIX2 v r \<equiv> (\<turnstile> v : r \<and> (\<forall>v'. (\<turnstile> v' : r \<and> flat v = flat v') \<longrightarrow> v 2\<succ> v'))"

lemma "POSIX v r = POSIX2 v r"
unfolding POSIX_def POSIX2_def
apply(auto)
apply(rule Ord1)
apply(auto)
apply(rule Ord3)
apply(auto)
done

section {* POSIX for some constructors *}

lemma POSIX_SEQ1:
  assumes "POSIX (Seq v1 v2) (SEQ r1 r2)" "\<turnstile> v1 : r1" "\<turnstile> v2 : r2"
  shows "POSIX v1 r1"
using assms
unfolding POSIX_def
apply(auto)
apply(drule_tac x="Seq v' v2" in spec)
apply(simp)
apply(erule impE)
apply(rule Prf.intros)
apply(simp)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)
apply(clarify)
by (metis ValOrd_refl)

lemma POSIX_SEQ2:
  assumes "POSIX (Seq v1 v2) (SEQ r1 r2)" "\<turnstile> v1 : r1" "\<turnstile> v2 : r2" 
  shows "POSIX v2 r2"
using assms
unfolding POSIX_def
apply(auto)
apply(drule_tac x="Seq v1 v'" in spec)
apply(simp)
apply(erule impE)
apply(rule Prf.intros)
apply(simp)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)
done

lemma POSIX_ALT2:
  assumes "POSIX (Left v1) (ALT r1 r2)"
  shows "POSIX v1 r1"
using assms
unfolding POSIX_def
apply(auto)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(drule_tac x="Left v'" in spec)
apply(simp)
apply(drule mp)
apply(rule Prf.intros)
apply(auto)
apply(erule ValOrd.cases)
apply(simp_all)
done

lemma POSIX_ALT1a:
  assumes "POSIX (Right v2) (ALT r1 r2)"
  shows "POSIX v2 r2"
using assms
unfolding POSIX_def
apply(auto)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(drule_tac x="Right v'" in spec)
apply(simp)
apply(drule mp)
apply(rule Prf.intros)
apply(auto)
apply(erule ValOrd.cases)
apply(simp_all)
done

lemma POSIX_ALT1b:
  assumes "POSIX (Right v2) (ALT r1 r2)"
  shows "(\<forall>v'. (\<turnstile> v' : r2 \<and> flat v' = flat v2) \<longrightarrow> v2 \<succ>r2 v')"
using assms
apply(drule_tac POSIX_ALT1a)
unfolding POSIX_def
apply(auto)
done

lemma POSIX_ALT_I1:
  assumes "POSIX v1 r1" 
  shows "POSIX (Left v1) (ALT r1 r2)"
using assms
unfolding POSIX_def
apply(auto)
apply (metis Prf.intros(2))
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd.intros)
apply(auto)
apply(rule ValOrd.intros)
by simp

lemma POSIX_ALT_I2:
  assumes "POSIX v2 r2" "\<forall>v'. \<turnstile> v' : r1 \<longrightarrow> length (flat v2) > length (flat v')"
  shows "POSIX (Right v2) (ALT r1 r2)"
using assms
unfolding POSIX_def
apply(auto)
apply (metis Prf.intros)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd.intros)
apply metis
done

lemma mkeps_POSIX:
  assumes "nullable r"
  shows "POSIX (mkeps r) r"
using assms
apply(induct r)
apply(auto)[1]
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(4))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros)
apply(simp)
apply(auto)[1]
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis mkeps.simps(2) mkeps_nullable nullable.simps(5))
apply(rotate_tac 6)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (simp add: mkeps_flat)
apply(case_tac "mkeps r1a = v1")
apply(simp)
apply (metis ValOrd.intros(1))
apply (rule ValOrd.intros(2))
apply metis
apply(simp)
(* ALT case *)
thm mkeps.simps
apply(simp)
apply(erule disjE)
apply(simp)
apply (metis POSIX_ALT_I1)
(* *)
apply(auto)[1]
thm  POSIX_ALT_I1
apply (metis POSIX_ALT_I1)
apply(simp (no_asm) add: POSIX_def)
apply(auto)[1]
apply(rule Prf.intros(3))
apply(simp only: POSIX_def)
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
thm mkeps_flat
apply(simp add: mkeps_flat)
apply(auto)[1]
thm Prf_flat_L nullable_correctness
apply (metis Prf_flat_L nullable_correctness)
apply(rule ValOrd.intros)
apply(subst (asm) POSIX_def)
apply(clarify)
apply(drule_tac x="v2" in spec)
by simp



text {*
  Injection value is related to r
*}



text {*
  The string behind the injection value is an added c
*}


lemma injval_inj: "inj_on (injval r c) {v. \<turnstile> v : der c r}"
apply(induct c r rule: der.induct)
unfolding inj_on_def
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis list.distinct(1) mkeps_flat v4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(rotate_tac 6)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis list.distinct(1) mkeps_flat v4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
done

lemma Values_nullable:
  assumes "nullable r1"
  shows "mkeps r1 \<in> Values r1 s"
using assms
apply(induct r1 arbitrary: s)
apply(simp_all)
apply(simp add: Values_recs)
apply(simp add: Values_recs)
apply(simp add: Values_recs)
apply(auto)[1]
done

lemma Values_injval:
  assumes "v \<in> Values (der c r) s"
  shows "injval r c v \<in> Values r (c#s)"
using assms
apply(induct c r arbitrary: v s rule: der.induct)
apply(simp add: Values_recs)
apply(simp add: Values_recs)
apply(case_tac "c = c'")
apply(simp)
apply(simp add: Values_recs)
apply(simp add: prefix_def)
apply(simp)
apply(simp add: Values_recs)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(case_tac "nullable r1")
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(simp add: rest_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp add: Values_def)
apply(rule Values_nullable)
apply(assumption)
apply(simp add: rest_def)
apply(subst mkeps_flat)
apply(assumption)
apply(simp)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(simp add: rest_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp add: Values_def)
done

lemma Values_projval:
  assumes "v \<in> Values r (c#s)" "\<exists>s. flat v = c # s"
  shows "projval r c v \<in> Values (der c r) s"
using assms
apply(induct r arbitrary: v s c rule: rexp.induct)
apply(simp add: Values_recs)
apply(simp add: Values_recs)
apply(case_tac "c = char")
apply(simp)
apply(simp add: Values_recs)
apply(simp)
apply(simp add: Values_recs)
apply(simp add: prefix_def)
apply(case_tac "nullable rexp1")
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(simp add: rest_def)
apply (metis hd_Cons_tl hd_append2 list.sel(1))
apply(simp add: rest_def)
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(subst v4_proj2)
apply(simp add: Values_def)
apply(assumption)
apply(simp)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(auto simp add: Values_def not_nullable_flat)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(simp add: rest_def)
apply(subst v4_proj2)
apply(simp add: Values_def)
apply(assumption)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
done


definition "MValue v r s \<equiv> (v \<in> Values r s \<and> (\<forall>v' \<in> Values r s. v 2\<succ> v'))"

lemma MValue_ALTE:
  assumes "MValue v (ALT r1 r2) s"
  shows "(\<exists>vl. v = Left vl \<and> MValue vl r1 s \<and> (\<forall>vr \<in> Values r2 s. length (flat vr) \<le> length (flat vl))) \<or> 
         (\<exists>vr. v = Right vr \<and> MValue vr r2 s \<and> (\<forall>vl \<in> Values r1 s. length (flat vl) < length (flat vr)))"
using assms
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(auto)
apply(drule_tac x="Left x" in bspec)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
apply(drule_tac x="Right vr" in bspec)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
apply(drule_tac x="Right x" in bspec)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
apply(drule_tac x="Left vl" in bspec)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
done

lemma MValue_ALTI1:
  assumes "MValue vl r1 s"  "\<forall>vr \<in> Values r2 s. length (flat vr) \<le> length (flat vl)"
  shows "MValue (Left vl) (ALT r1 r2) s"
using assms
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(auto)
apply(rule ValOrd2.intros)
apply metis
apply(rule ValOrd2.intros)
apply metis
done

lemma MValue_ALTI2:
  assumes "MValue vr r2 s"  "\<forall>vl \<in> Values r1 s. length (flat vl) < length (flat vr)"
  shows "MValue (Right vr) (ALT r1 r2) s"
using assms
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(auto)
apply(rule ValOrd2.intros)
apply metis
apply(rule ValOrd2.intros)
apply metis
done

lemma t: "(c#xs = c#ys) \<Longrightarrow> xs = ys"
by (metis list.sel(3))

lemma t2: "(xs = ys) \<Longrightarrow> (c#xs) = (c#ys)"
by (metis)

lemma "\<not>(nullable r) \<Longrightarrow> \<not>(\<exists>v. \<turnstile> v : r \<and> flat v = [])"
by (metis Prf_flat_L nullable_correctness)


lemma LeftRight:
  assumes "(Left v1) \<succ>(der c (ALT r1 r2)) (Right v2)"
  and "\<turnstile> v1 : der c r1" "\<turnstile> v2 : der c r2" 
  shows "(injval (ALT r1 r2) c (Left v1)) \<succ>(ALT r1 r2) (injval (ALT r1 r2) c (Right v2))"
using assms
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd.intros)
apply(clarify)
apply(subst v4)
apply(simp)
apply(subst v4)
apply(simp)
apply(simp)
done

lemma RightLeft:
  assumes "(Right v1) \<succ>(der c (ALT r1 r2)) (Left v2)"
  and "\<turnstile> v1 : der c r2" "\<turnstile> v2 : der c r1" 
  shows "(injval (ALT r1 r2) c (Right v1)) \<succ>(ALT r1 r2) (injval (ALT r1 r2) c (Left v2))"
using assms
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd.intros)
apply(clarify)
apply(subst v4)
apply(simp)
apply(subst v4)
apply(simp)
apply(simp)
done

lemma h: 
  assumes "nullable r1" "\<turnstile> v1 : der c r1"
  shows "injval r1 c v1 \<succ>r1 mkeps r1"
using assms
apply(induct r1 arbitrary: v1 rule: der.induct)
apply(simp)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(auto)[1]
apply (metis ValOrd.intros(6))
apply (metis ValOrd.intros(6))
apply (metis ValOrd.intros(3) le_add2 list.size(3) mkeps_flat monoid_add_class.add.right_neutral)
apply(auto)[1]
apply (metis ValOrd.intros(4) length_greater_0_conv list.distinct(1) list.size(3) mkeps_flat v4)
apply (metis ValOrd.intros(4) length_greater_0_conv list.distinct(1) list.size(3) mkeps_flat v4)
apply (metis ValOrd.intros(5))
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis ValOrd.intros(2) list.distinct(1) mkeps_flat v4)
apply(clarify)
by (metis ValOrd.intros(1))

lemma LeftRightSeq:
  assumes "(Left (Seq v1 v2)) \<succ>(der c (SEQ r1 r2)) (Right v3)"
  and "nullable r1" "\<turnstile> v1 : der c r1"
  shows "(injval (SEQ r1 r2) c (Seq v1 v2)) \<succ>(SEQ r1 r2) (injval (SEQ r1 r2) c (Right v2))"
using assms
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(simp)
apply(rule ValOrd.intros(2))
prefer 2
apply (metis list.distinct(1) mkeps_flat v4)
by (metis h)

lemma rr1: 
  assumes "\<turnstile> v : r" "\<not>nullable r" 
  shows "flat v \<noteq> []"
using assms
by (metis Prf_flat_L nullable_correctness)

(* HERE *)

lemma Prf_inj_test:
  assumes "v1 \<succ>(der c r) v2" 
          "v1 \<in> Values (der c r) s"
          "v2 \<in> Values (der c r) s"
          "injval r c v1 \<in> Values r (c#s)"
          "injval r c v2 \<in> Values r (c#s)"
  shows "(injval r c v1) 2\<succ>  (injval r c v2)"
using assms
apply(induct c r arbitrary: v1 v2 s rule: der.induct)
(* NULL case *)
apply(simp add: Values_recs)
(* EMPTY case *)
apply(simp add: Values_recs)
(* CHAR case *)
apply(case_tac "c = c'")
apply(simp)
apply(simp add: Values_recs)
apply (metis ValOrd2.intros(8))
apply(simp add: Values_recs)
(* ALT case *)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply (metis ValOrd2.intros(6))
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd2.intros)
apply(subst v4)
apply(simp add: Values_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd2.intros)
apply(subst v4)
apply(simp add: Values_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply (metis ValOrd2.intros(5))
(* SEQ case*)
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
defer
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(rule ValOrd2.intros)
apply(simp)
apply (metis Ord1)
apply(clarify)
apply(rule ValOrd2.intros)
apply(subgoal_tac "rest v1 (flat v1 @ flat v2) = flat v2")
apply(simp)
apply(subgoal_tac "rest (injval r1 c v1) (c # flat v1 @ flat v2) = flat v2")
apply(simp)
oops

lemma Prf_inj_test:
  assumes "v1 \<succ>(der c r) v2" 
          "v1 \<in> Values (der c r) s"
          "v2 \<in> Values (der c r) s"
          "injval r c v1 \<in> Values r (c#s)"
          "injval r c v2 \<in> Values r (c#s)"
  shows "(injval r c v1) 2\<succ>  (injval r c v2)"
using assms
apply(induct c r arbitrary: v1 v2 s rule: der.induct)
(* NULL case *)
apply(simp add: Values_recs)
(* EMPTY case *)
apply(simp add: Values_recs)
(* CHAR case *)
apply(case_tac "c = c'")
apply(simp)
apply(simp add: Values_recs)
apply (metis ValOrd2.intros(8))
apply(simp add: Values_recs)
(* ALT case *)
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply (metis ValOrd2.intros(6))
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd2.intros)
apply(subst v4)
apply(simp add: Values_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd2.intros)
apply(subst v4)
apply(simp add: Values_def)
apply(subst v4)
apply(simp add: Values_def)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply (metis ValOrd2.intros(5))
(* SEQ case*)
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
defer
apply(simp)
apply(simp add: Values_recs)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(rule ValOrd2.intros)
apply(simp)
apply (metis Ord1)
apply(clarify)
apply(rule ValOrd2.intros)
apply metis
using injval_inj
apply(simp add: Values_def inj_on_def)
apply metis
apply(simp add: Values_recs)
apply(auto)[1]
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply (metis Ord1 ValOrd2.intros(1))
apply(clarify)
apply(rule ValOrd2.intros(2))
apply metis
using injval_inj
apply(simp add: Values_def inj_on_def)
apply metis
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd2.intros(2))
thm h
apply(rule Ord1)
apply(rule h)
apply(simp)
apply(simp add: Values_def)
apply(simp add: Values_def)
apply (metis list.distinct(1) mkeps_flat v4)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(simp add: Values_def)
defer
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(rule ValOrd2.intros(1))
apply(rotate_tac 1)
apply(drule_tac x="v2" in meta_spec)
apply(rotate_tac 8)
apply(drule_tac x="v2'" in meta_spec)
apply(rotate_tac 8)
oops

lemma POSIX_der:
  assumes "POSIX v (der c r)" "\<turnstile> v : der c r"
  shows "POSIX (injval r c v) r"
using assms
unfolding POSIX_def
apply(auto)
thm v3
apply (erule v3)
thm v4
apply(subst (asm) v4)
apply(assumption)
apply(drule_tac x="projval r c v'" in spec)
apply(drule mp)
apply(rule conjI)
thm v3_proj
apply(rule v3_proj)
apply(simp)
apply(rule_tac x="flat v" in exI)
apply(simp)
thm t
apply(rule_tac c="c" in  t)
apply(simp)
thm v4_proj
apply(subst v4_proj)
apply(simp)
apply(rule_tac x="flat v" in exI)
apply(simp)
apply(simp)
oops

lemma POSIX_der:
  assumes "POSIX v (der c r)" "\<turnstile> v : der c r"
  shows "POSIX (injval r c v) r"
using assms
apply(induct c r arbitrary: v rule: der.induct)
(* null case*)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
(* empty case *)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
(* char case *)
apply(simp add: POSIX_def)
apply(case_tac "c = c'")
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
(* alt case *)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(simp (no_asm) add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(2) v3)
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis POSIX_ALT2 POSIX_def ValOrd.intros(6))
apply (metis ValOrd.intros(3) order_refl)
apply(simp (no_asm) add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(3) v3)
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
defer
apply (metis POSIX_ALT1a POSIX_def ValOrd.intros(5))
prefer 2
apply(subst (asm) (5) POSIX_def)
apply(auto)[1]
apply(rotate_tac 5)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(subst (asm) v4)
apply(simp)
apply(drule_tac x="Left (projval r1a c v1)" in spec)
apply(clarify)
apply(drule mp)
apply(rule conjI)
apply (metis Prf.intros(2) v3_proj)
apply(simp)
apply (metis v4_proj2)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply (metis less_not_refl v4_proj2)
(* seq case *)
apply(case_tac "nullable r1")
defer
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(1) v3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(subst (asm) (3) v4)
apply(simp)
apply(simp)
apply(subgoal_tac "flat v1a \<noteq> []")
prefer 2
apply (metis Prf_flat_L nullable_correctness)
apply(subgoal_tac "\<exists>s. flat v1a = c # s")
prefer 2
apply (metis append_eq_Cons_conv)
apply(auto)[1]
oops


lemma POSIX_ex: "\<turnstile> v : r \<Longrightarrow> \<exists>v. POSIX v r"
apply(induct r arbitrary: v)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule_tac x="Void" in exI)
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(4))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule_tac x="Char c" in exI)
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="v2" in meta_spec)
apply(auto)[1]
defer
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply (metis POSIX_ALT_I1)
apply (metis POSIX_ALT_I1 POSIX_ALT_I2)
apply(case_tac "nullable r1a")
apply(rule_tac x="Seq (mkeps r1a) va" in exI)
apply(auto simp add: POSIX_def)[1]
apply (metis Prf.intros(1) mkeps_nullable)
apply(simp add: mkeps_flat)
apply(rotate_tac 7)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "mkeps r1 = v1a")
apply(simp)
apply (rule ValOrd.intros(1))
apply (metis append_Nil mkeps_flat)
apply (rule ValOrd.intros(2))
apply(drule mkeps_POSIX)
apply(simp add: POSIX_def)
oops

lemma POSIX_ex2: "\<turnstile> v : r \<Longrightarrow> \<exists>v. POSIX v r \<and> \<turnstile> v : r"
apply(induct r arbitrary: v)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule_tac x="Void" in exI)
apply(simp add: POSIX_def)
apply(auto)[1]
oops

lemma POSIX_ALT_cases:
  assumes "\<turnstile> v : (ALT r1 r2)" "POSIX v (ALT r1 r2)"
  shows "(\<exists>v1. v = Left v1 \<and> POSIX v1 r1) \<or> (\<exists>v2. v = Right v2 \<and> POSIX v2 r2)"
using assms
apply(erule_tac Prf.cases)
apply(simp_all)
unfolding POSIX_def
apply(auto)
apply (metis POSIX_ALT2 POSIX_def assms(2))
by (metis POSIX_ALT1b assms(2))

lemma POSIX_ALT_cases2:
  assumes "POSIX v (ALT r1 r2)" "\<turnstile> v : (ALT r1 r2)" 
  shows "(\<exists>v1. v = Left v1 \<and> POSIX v1 r1) \<or> (\<exists>v2. v = Right v2 \<and> POSIX v2 r2)"
using assms POSIX_ALT_cases by auto

lemma Prf_flat_empty:
  assumes "\<turnstile> v : r" "flat v = []"
  shows "nullable r"
using assms
apply(induct)
apply(auto)
done

lemma POSIX_proj:
  assumes "POSIX v r" "\<turnstile> v : r" "\<exists>s. flat v = c#s"
  shows "POSIX (projval r c v) (der c r)"
using assms
apply(induct r c v arbitrary: rule: projval.induct)
defer
defer
defer
defer
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
oops

lemma POSIX_proj:
  assumes "POSIX v r" "\<turnstile> v : r" "\<exists>s. flat v = c#s"
  shows "POSIX (projval r c v) (der c r)"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
oops

lemma POSIX_proj:
  assumes "POSIX v r" "\<turnstile> v : r" "\<exists>s. flat v = c#s"
  shows "POSIX (projval r c v) (der c r)"
using assms
apply(induct r c v arbitrary: rule: projval.induct)
defer
defer
defer
defer
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
oops

lemma Prf_inj:
  assumes "v1 \<succ>(der c r) v2" "\<turnstile> v1 : der c r" "\<turnstile> v2 : der c r" "flat v1 = flat v2"
  shows "(injval r c v1) \<succ>r (injval r c v2)"
using assms
apply(induct arbitrary: v1 v2 rule: der.induct)
(* NULL case *)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
(* EMPTY case *)
apply(erule ValOrd.cases)
apply(simp_all)[8]
(* CHAR case *)
apply(case_tac "c = c'")
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd.intros)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
(* ALT case *)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(rule ValOrd.intros)
apply(subst v4)
apply(clarify)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(subst v4)
apply(clarify)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(rule ValOrd.intros)
apply(clarify)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
(* SEQ case*)
apply(simp)
apply(case_tac "nullable r1")
defer
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all)[8]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(rule ValOrd.intros)
apply(simp)
oops


text {*
  Injection followed by projection is the identity.
*}

lemma proj_inj_id:
  assumes "\<turnstile> v : der c r" 
  shows "projval r c (injval r c v) = v"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "c = char")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
defer
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "nullable rexp1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply (metis list.distinct(1) v4)
apply(auto)[1]
apply (metis mkeps_flat)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(simp add: v4)
done

text {* 

  HERE: Crucial lemma that does not go through in the sequence case. 

*}
lemma v5:
  assumes "\<turnstile> v : der c r" "POSIX v (der c r)"
  shows "POSIX (injval r c v) r"
using assms
apply(induct arbitrary: v rule: der.induct)
(* NULL case *)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
(* EMPTY case *)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
(* CHAR case *)
apply(simp)
apply(case_tac "c = c'")
apply(auto simp add: POSIX_def)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
oops