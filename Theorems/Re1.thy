   
theory Re1
  imports "Main" 
begin


section {* Sequential Composition of Sets *}

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

fun SEQS :: "rexp \<Rightarrow> rexp list \<Rightarrow> rexp"
where
  "SEQS r [] = r"
| "SEQS r (r'#rs) = SEQ r (SEQS r' rs)"

section {* Semantics of Regular Expressions *}
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (NULL) = {}"
| "L (EMPTY) = {[]}"
| "L (CHAR c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"

fun zeroable where
  "zeroable NULL = True"
| "zeroable EMPTY = False"
| "zeroable (CHAR c) = False"
| "zeroable (ALT r1 r2) = (zeroable r1 \<and> zeroable r2)"
| "zeroable (SEQ r1 r2) = (zeroable r1 \<or> zeroable r2)"

lemma L_ALT_cases:
  "L (ALT r1 r2) \<noteq> {} \<Longrightarrow> (L r1 \<noteq> {}) \<or> (L r1 = {} \<and> L r2 \<noteq> {})"
by(auto)

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


fun Seqs :: "val \<Rightarrow> val list \<Rightarrow> val"
where
  "Seqs v [] = v"
| "Seqs v (v'#vs) = Seqs (Seq v v') vs"

section {* The string behind a value *}

fun flat :: "val \<Rightarrow> string"
where
  "flat(Void) = []"
| "flat(Char c) = [c]"
| "flat(Left v) = flat(v)"
| "flat(Right v) = flat(v)"
| "flat(Seq v1 v2) = flat(v1) @ flat(v2)"

fun flats :: "val \<Rightarrow> string list"
where
  "flats(Void) = [[]]"
| "flats(Char c) = [[c]]"
| "flats(Left v) = flats(v)"
| "flats(Right v) = flats(v)"
| "flats(Seq v1 v2) = (flats v1) @ (flats v2)"

value "flats(Seq(Char c)(Char b))"

section {* Relation between values and regular expressions *}


inductive Prfs :: "string \<Rightarrow> val \<Rightarrow> rexp \<Rightarrow> bool" ("\<Turnstile>_ _ : _" [100, 100, 100] 100)
where
 "\<lbrakk>\<Turnstile>s1 v1 : r1; \<Turnstile>s2 v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile>(s1 @ s2) (Seq v1 v2) : SEQ r1 r2"
| "\<Turnstile>s v1 : r1 \<Longrightarrow> \<Turnstile>s (Left v1) : ALT r1 r2"
| "\<Turnstile>s v2 : r2 \<Longrightarrow> \<Turnstile>s (Right v2) : ALT r1 r2"
| "\<Turnstile>[] Void : EMPTY"
| "\<Turnstile>[c] (Char c) : CHAR c"

lemma Prfs_flat:
  "\<Turnstile>s v : r \<Longrightarrow> flat v = s"
apply(induct s v r rule: Prfs.induct)
apply(auto)
done

inductive Prfn :: "nat \<Rightarrow> val \<Rightarrow> rexp \<Rightarrow> bool" ("\<TTurnstile>_ _ : _" [100, 100, 100] 100)
where
 "\<lbrakk>\<TTurnstile>n1 v1 : r1; \<TTurnstile>n2 v2 : r2\<rbrakk> \<Longrightarrow> \<TTurnstile>(n1 + n2) (Seq v1 v2) : SEQ r1 r2"
| "\<TTurnstile>n v1 : r1 \<Longrightarrow> \<TTurnstile>n (Left v1) : ALT r1 r2"
| "\<TTurnstile>n v2 : r2 \<Longrightarrow> \<TTurnstile>n (Right v2) : ALT r1 r2"
| "\<TTurnstile>0 Void : EMPTY"
| "\<TTurnstile>1 (Char c) : CHAR c"

lemma Prfn_flat:
  "\<TTurnstile>n v : r \<Longrightarrow> length (flat v) = n"
apply(induct rule: Prfn.induct)
apply(auto)
done

inductive Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : SEQ r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : ALT r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : ALT r1 r2"
| "\<turnstile> Void : EMPTY"
| "\<turnstile> Char c : CHAR c"

lemma Prf_Prfn:
  shows "\<turnstile> v : r \<Longrightarrow> \<TTurnstile>(length (flat v)) v : r"
apply(induct v r rule: Prf.induct)
apply(auto intro: Prfn.intros)
by (metis One_nat_def Prfn.intros(5))

lemma Prfn_Prf:
  shows "\<TTurnstile>n v : r \<Longrightarrow> \<turnstile> v : r"
apply(induct n v r rule: Prfn.induct)
apply(auto intro: Prf.intros)
done

lemma Prf_Prfs:
  shows "\<turnstile> v : r \<Longrightarrow> \<Turnstile>(flat v) v : r"
apply(induct v r rule: Prf.induct)
apply(auto intro: Prfs.intros)
done

lemma Prfs_Prf:
  shows "\<Turnstile>s v : r \<Longrightarrow> \<turnstile> v : r"
apply(induct s v r rule: Prfs.induct)
apply(auto intro: Prf.intros)
done

lemma not_nullable_flat:
  assumes "\<turnstile> v : r" "\<not>nullable r"
  shows "flat v \<noteq> []"
using assms
apply(induct)
apply(auto)
done


fun mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(EMPTY) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"

lemma mkeps_nullable:
  assumes "nullable(r)" shows "\<turnstile> mkeps r : r"
using assms
apply(induct rule: nullable.induct)
apply(auto intro: Prf.intros)
done

lemma mkeps_nullable_n:
  assumes "nullable(r)" shows "\<TTurnstile>0 (mkeps r) : r"
using assms
apply(induct rule: nullable.induct)
apply(auto intro: Prfn.intros)
apply(drule Prfn.intros(1))
apply(assumption)
apply(simp)
done

lemma mkeps_nullable_s:
  assumes "nullable(r)" shows "\<Turnstile>[] (mkeps r) : r"
using assms
apply(induct rule: nullable.induct)
apply(auto intro: Prfs.intros)
apply(drule Prfs.intros(1))
apply(assumption)
apply(simp)
done

lemma mkeps_flat:
  assumes "nullable(r)" shows "flat (mkeps r) = []"
using assms
apply(induct rule: nullable.induct)
apply(auto)
done

text {*
  The value mkeps returns is always the correct POSIX
  value.
*}

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

section {* Greedy Ordering according to Frisch/Cardelli *}

inductive GrOrd :: "val \<Rightarrow> val \<Rightarrow> bool" ("_ \<prec> _")
where 
  "v1 \<prec> v1' \<Longrightarrow> (Seq v1 v2) \<prec> (Seq v1' v2')"
| "v2 \<prec> v2' \<Longrightarrow> (Seq v1 v2) \<prec> (Seq v1 v2')"
| "v1 \<prec> v2 \<Longrightarrow> (Left v1) \<prec> (Left v2)"
| "v1 \<prec> v2 \<Longrightarrow> (Right v1) \<prec> (Right v2)"
| "(Right v1) \<prec> (Left v2)"
| "(Char c) \<prec> (Char c)"
| "(Void) \<prec> (Void)"

lemma Gr_refl:
  assumes "\<turnstile> v : r"
  shows "v \<prec> v"
using assms
apply(induct)
apply(auto intro: GrOrd.intros)
done

lemma Gr_total:
  assumes "\<turnstile> v1 : r" "\<turnstile> v2 : r"
  shows "v1 \<prec> v2 \<or> v2 \<prec> v1"
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
  assumes "v1 \<prec> v2" "v2 \<prec> v3" "\<turnstile> v1 : r" "\<turnstile> v2 : r" "\<turnstile> v3 : r"
  shows "v1 \<prec> v3"
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
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(5))
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(5))
apply(clarify)
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply(erule GrOrd.cases)
apply(simp_all (no_asm_use))[7]
apply (metis GrOrd.intros(4))
(* seq case *)
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

definition
  GrMaxM :: "val set => val" where
  "GrMaxM S == SOME v.  v \<in> S \<and> (\<forall>v' \<in> S. v' \<prec> v)"

definition
  "GrMax r s \<equiv> GrMaxM {v. \<turnstile> v : r \<and> flat v = s}"

inductive ValOrd3 :: "val \<Rightarrow> val \<Rightarrow> bool" ("_ 3\<succ> _" [100, 100] 100)
where
  "v2 3\<succ> v2' \<Longrightarrow> (Seq v1 v2) 3\<succ> (Seq v1 v2')" 
| "v1 3\<succ> v1' \<Longrightarrow> (Seq v1 v2) 3\<succ> (Seq v1' v2')" 
| "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) 3\<succ> (Right v2)"
| "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) 3\<succ> (Left v1)"
| "v2 3\<succ> v2' \<Longrightarrow> (Right v2) 3\<succ> (Right v2')"
| "v1 3\<succ> v1' \<Longrightarrow> (Left v1) 3\<succ> (Left v1')"
| "Void 3\<succ> Void"
| "(Char c) 3\<succ> (Char c)"


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

inductive ValOrdStr :: "string \<Rightarrow> val \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile> _ \<succ>_" [100, 100, 100] 100)
where
  "\<lbrakk>s \<turnstile> v1 \<succ> v1'; rest v1 s \<turnstile> v2 \<succ> v2'\<rbrakk> \<Longrightarrow> s \<turnstile> (Seq v1 v2) \<succ> (Seq v1' v2')" 
| "\<lbrakk>flat v2 \<sqsubseteq> flat v1; flat v1 \<sqsubseteq> s\<rbrakk> \<Longrightarrow> s \<turnstile> (Left v1) \<succ> (Right v2)"
| "\<lbrakk>flat v1 \<sqsubset> flat v2; flat v2 \<sqsubseteq> s\<rbrakk> \<Longrightarrow> s \<turnstile> (Right v2) \<succ> (Left v1)"
| "s \<turnstile> v2 \<succ> v2' \<Longrightarrow> s \<turnstile> (Right v2) \<succ> (Right v2')"
| "s \<turnstile> v1 \<succ> v1' \<Longrightarrow> s \<turnstile> (Left v1) \<succ> (Left v1')"
| "s \<turnstile> Void \<succ> Void"
| "(c#s) \<turnstile> (Char c) \<succ> (Char c)"

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


lemma ValOrd_refl:
  assumes "\<turnstile> v : r"
  shows "v \<succ>r v"
using assms
apply(induct)
apply(auto intro: ValOrd.intros)
done

lemma 
  "flat Void = []"
  "flat (Seq Void Void) = []"
apply(simp_all)
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

lemma refl_on_ValOrd:
  "refl_on (Values r s) {(v1, v2). v1 \<succ>r v2 \<and> v1 \<in> Values r s \<and> v2 \<in> Values r s}"
unfolding refl_on_def
apply(auto)
apply(rule ValOrd_refl)
apply(simp add: Values_def)
done

(*
inductive ValOrd3 :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ 3\<succ>_ _" [100, 100, 100] 100)
where
  "\<lbrakk>v2 3\<succ>r2 v2'; \<turnstile> v1 : r1\<rbrakk> \<Longrightarrow> (Seq v1 v2) 3\<succ>(SEQ r1 r2) (Seq v1 v2')" 
| "\<lbrakk>v1 3\<succ>r1 v1'; v1 \<noteq> v1'; flat v2 = flat v2'; \<turnstile> v2 : r2; \<turnstile> v2' : r2\<rbrakk> 
      \<Longrightarrow> (Seq v1 v2) 3\<succ>(SEQ r1 r2) (Seq v1' v2')" 
| "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) 3\<succ>(ALT r1 r2) (Right v2)"
| "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) 3\<succ>(ALT r1 r2) (Left v1)"
| "v2 3\<succ>r2 v2' \<Longrightarrow> (Right v2) 3\<succ>(ALT r1 r2) (Right v2')"
| "v1 3\<succ>r1 v1' \<Longrightarrow> (Left v1) 3\<succ>(ALT r1 r2) (Left v1')"
| "Void 3\<succ>EMPTY Void"
| "(Char c) 3\<succ>(CHAR c) (Char c)"
*)

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

definition POSIXs :: "val \<Rightarrow> rexp \<Rightarrow> string \<Rightarrow> bool" 
where
  "POSIXs v r s \<equiv> (\<Turnstile>s v : r \<and> (\<forall>v'. (\<Turnstile>s v' : r \<longrightarrow> v 2\<succ> v')))"

definition POSIXn :: "val \<Rightarrow> rexp \<Rightarrow> nat \<Rightarrow> bool" 
where
  "POSIXn v r n \<equiv> (\<TTurnstile>n v : r \<and> (\<forall>v'. (\<TTurnstile>n v' : r \<longrightarrow> v 2\<succ> v')))"

lemma "POSIXn v r (length (flat v)) \<Longrightarrow> POSIX2 v r"
unfolding POSIXn_def POSIX2_def
apply(auto)
apply (metis Prfn_Prf)
by (metis Prf_Prfn)

lemma Prfs_POSIX:
  "POSIXs v r s \<Longrightarrow> \<Turnstile>s v: r \<and> flat v = s"
apply(simp add: POSIXs_def)
by (metis Prfs_flat)


lemma "POSIXs v r (flat v) =  POSIX2 v r"
unfolding POSIXs_def POSIX2_def
apply(auto)
apply (metis Prfs_Prf)
apply (metis Prf_Prfs)
apply (metis Prf_Prfs)
by (metis Prfs_Prf Prfs_flat)

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

lemma POSIXn_SEQ1:
  assumes "POSIXn (Seq v1 v2) (SEQ r1 r2) (n1 + n2)" "\<TTurnstile>n1 v1 : r1" "\<TTurnstile>n2 v2 : r2"
  shows "POSIXn v1 r1 n1"
using assms
unfolding POSIXn_def
apply(auto)
apply(drule_tac x="Seq v' v2" in spec)
apply(erule impE)
apply(rule Prfn.intros)
apply(simp)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
apply(clarify)
by (metis Ord1 Prfn_Prf ValOrd_refl)

lemma POSIXs_SEQ1:
  assumes "POSIXs (Seq v1 v2) (SEQ r1 r2) (s1 @ s2)" "\<Turnstile>s1 v1 : r1" "\<Turnstile>s2 v2 : r2"
  shows "POSIXs v1 r1 s1"
using assms
unfolding POSIXs_def
apply(auto)
apply(drule_tac x="Seq v' v2" in spec)
apply(erule impE)
apply(rule Prfs.intros)
apply(simp)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
apply(clarify)
by (metis Ord1 Prfs_Prf ValOrd_refl)

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

lemma POSIXn_SEQ2:
  assumes "POSIXn (Seq v1 v2) (SEQ r1 r2) (n1 + n2)" "\<TTurnstile>n1 v1 : r1" "\<TTurnstile>n2 v2 : r2" 
  shows "POSIXn v2 r2 n2"
using assms
unfolding POSIXn_def
apply(auto)
apply(drule_tac x="Seq v1 v'" in spec)
apply(erule impE)
apply(rule Prfn.intros)
apply(simp)
apply(simp)
apply(erule ValOrd2.cases)
apply(simp_all)
done

lemma POSIXs_SEQ2:
  assumes "POSIXs (Seq v1 v2) (SEQ r1 r2) (s1 @ s2)" "\<Turnstile>s1 v1 : r1" "\<Turnstile>s2 v2 : r2" 
  shows "POSIXs v2 r2 s2"
using assms
unfolding POSIXs_def
apply(auto)
apply(drule_tac x="Seq v1 v'" in spec)
apply(erule impE)
apply(rule Prfs.intros)
apply(simp)
apply(simp)
apply(erule ValOrd2.cases)
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

lemma POSIXn_ALT2:
  assumes "POSIXn (Left v1) (ALT r1 r2) n"
  shows "POSIXn v1 r1 n"
using assms
unfolding POSIXn_def
apply(auto)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(drule_tac x="Left v'" in spec)
apply(drule mp)
apply(rule Prfn.intros)
apply(auto)
apply(erule ValOrd2.cases)
apply(simp_all)
done

lemma POSIXs_ALT2:
  assumes "POSIXs (Left v1) (ALT r1 r2) s"
  shows "POSIXs v1 r1 s"
using assms
unfolding POSIXs_def
apply(auto)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(drule_tac x="Left v'" in spec)
apply(drule mp)
apply(rule Prfs.intros)
apply(auto)
apply(erule ValOrd2.cases)
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

lemma POSIXn_ALT1a:
  assumes "POSIXn (Right v2) (ALT r1 r2) n"
  shows "POSIXn v2 r2 n"
using assms
unfolding POSIXn_def
apply(auto)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(drule_tac x="Right v'" in spec)
apply(drule mp)
apply(rule Prfn.intros)
apply(auto)
apply(erule ValOrd2.cases)
apply(simp_all)
done

lemma POSIXs_ALT1a:
  assumes "POSIXs (Right v2) (ALT r1 r2) s"
  shows "POSIXs v2 r2 s"
using assms
unfolding POSIXs_def
apply(auto)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(drule_tac x="Right v'" in spec)
apply(drule mp)
apply(rule Prfs.intros)
apply(auto)
apply(erule ValOrd2.cases)
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

lemma POSIXn_ALT1b:
  assumes "POSIXn (Right v2) (ALT r1 r2) n"
  shows "(\<forall>v'. (\<TTurnstile>n v' : r2 \<longrightarrow> v2 2\<succ> v'))"
using assms
apply(drule_tac POSIXn_ALT1a)
unfolding POSIXn_def
apply(auto)
done

lemma POSIXs_ALT1b:
  assumes "POSIXs (Right v2) (ALT r1 r2) s"
  shows "(\<forall>v'. (\<Turnstile>s v' : r2 \<longrightarrow> v2 2\<succ> v'))"
using assms
apply(drule_tac POSIXs_ALT1a)
unfolding POSIXs_def
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

lemma POSIXn_ALT_I1:
  assumes "POSIXn v1 r1 n" 
  shows "POSIXn (Left v1) (ALT r1 r2) n"
using assms
unfolding POSIXn_def
apply(auto)
apply (metis Prfn.intros(2))
apply(rotate_tac 2)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd2.intros)
apply(auto)
apply(rule ValOrd2.intros)
by (metis Prfn_flat order_refl)

lemma POSIXs_ALT_I1:
  assumes "POSIXs v1 r1 s" 
  shows "POSIXs (Left v1) (ALT r1 r2) s"
using assms
unfolding POSIXs_def
apply(auto)
apply (metis Prfs.intros(2))
apply(rotate_tac 2)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd2.intros)
apply(auto)
apply(rule ValOrd2.intros)
by (metis Prfs_flat order_refl)

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

lemma POSIXs_ALT_I2:
  assumes "POSIXs v2 r2 s" "\<forall>s' v'. \<Turnstile>s' v' : r1 \<longrightarrow> length s > length s'"
  shows "POSIXs (Right v2) (ALT r1 r2) s"
using assms
unfolding POSIXs_def
apply(auto)
apply (metis Prfs.intros)
apply(rotate_tac 3)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto)
apply(rule ValOrd2.intros)
apply metis
done

lemma 
  "\<lbrakk>POSIX (mkeps r2) r2; nullable r2; \<not> nullable r1\<rbrakk>
   \<Longrightarrow> POSIX (Right (mkeps r2)) (ALT r1 r2)" 
apply(auto simp add: POSIX_def)
apply(rule Prf.intros(3))
apply(auto)
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: mkeps_flat)
apply(auto)[1]
apply (metis Prf_flat_L nullable_correctness)
apply(rule ValOrd.intros)
apply(auto)
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

fun
 red :: "char \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "red c (NULL) = NULL"
| "red c (EMPTY) = CHAR c"
| "red c (CHAR c') = SEQ (CHAR c) (CHAR c')"
| "red c (ALT r1 r2) = ALT (red c r1) (red c r2)"
| "red c (SEQ r1 r2) = 
     (if nullable r1
      then ALT (SEQ (red c r1) r2) (red c r2)
      else SEQ (red c r1) r2)"

lemma L_der:
  shows "L (der c r) = {s. c#s \<in> L r}"
apply(induct r)
apply(simp_all)
apply(simp add: Sequ_def)
apply(auto)[1]
apply (metis append_Cons)
apply (metis append_Nil nullable_correctness)
apply (metis append_eq_Cons_conv)
apply (metis append_Cons)
apply (metis Cons_eq_append_conv nullable_correctness)
apply(auto)
done

lemma L_red:
  shows "L (red c r) = {c#s | s. s \<in> L r}"
apply(induct r)
apply(simp_all)
apply(simp add: Sequ_def)
apply(simp add: Sequ_def)
apply(auto)[1]
apply (metis append_Nil nullable_correctness)
apply (metis append_Cons)
apply (metis append_Cons)
apply(auto)
done

lemma L_red_der:
  "L(red c (der c r)) = {c#s | s. c#s \<in> L r}"
apply(simp add: L_red)
apply(simp add: L_der)
done

lemma L_der_red:
  "L(der c (red c r)) = L r"
apply(simp add: L_der)
apply(simp add: L_red)
done

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

text {*
  Injection value is related to r
*}

lemma v3:
  assumes "\<turnstile> v : der c r" shows "\<turnstile> (injval r c v) : r"
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

lemma v3_red:
  assumes "\<turnstile> v : r" shows "\<turnstile> (injval (red c r) c v) : (red c r)"
using assms
apply(induct c r arbitrary: v rule: red.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(1) Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
prefer 2
apply (metis Prf.intros(1))
oops

lemma v3s:
  assumes "\<Turnstile>s v : der c r" shows "\<Turnstile>(c#s) (injval r c v) : r"
using assms
apply(induct arbitrary: s v rule: der.induct)
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(case_tac "c = c'")
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply (metis Prfs.intros(5))
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply (metis Prfs.intros(2))
apply (metis Prfs.intros(3))
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto)[1]
apply (metis Prfs.intros(1) append_Cons)
apply(auto)[1]
apply (metis Prfs.intros(1) append_Nil mkeps_nullable_s)
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto)[1]
by (metis Prfs.intros(1) append_Cons)

lemma v3n:
  assumes "\<TTurnstile>n v : der c r" shows "\<TTurnstile>(Suc n) (injval r c v) : r"
using assms
apply(induct arbitrary: n v rule: der.induct)
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(case_tac "c = c'")
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply (metis One_nat_def Prfn.intros(5))
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply (metis Prfn.intros(2))
apply (metis Prfn.intros(3))
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(auto)[1]
apply (metis Prfn.intros(1) add.commute add_Suc_right)
apply(auto)[1]
apply (metis Prfn.intros(1) mkeps_nullable_n plus_nat.add_0)
apply(simp)
apply(erule Prfn.cases)
apply(simp_all)[5]
apply(auto)[1]
by (metis Prfn.intros(1) add_Suc)

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

lemma v3s_proj:
  assumes "\<Turnstile>(c#s) v : r"
  shows "\<Turnstile>s (projval r c v) : der c r"
using assms
apply(induct s\<equiv>"c#s" v r arbitrary: s rule: Prfs.induct)
prefer 4
apply(simp)
apply (metis Prfs.intros(4))
prefer 2
apply(simp)
apply (metis Prfs.intros(2))
prefer 2
apply(simp)
apply (metis Prfs.intros(3))
apply(auto)
apply(rule Prfs.intros)
apply (metis Prfs_flat append_Nil)
prefer 2
apply(rule Prfs.intros)
apply(subst (asm) append_eq_Cons_conv)
apply(auto)[1]
apply (metis Prfs_flat)
apply(rule Prfs.intros)
apply metis
apply(simp)
apply(subst (asm) append_eq_Cons_conv)
apply(auto)[1]
apply (metis Prf_flat_L Prfs_Prf nullable_correctness)
apply (metis Prfs_flat list.distinct(1))
apply(subst (asm) append_eq_Cons_conv)
apply(auto)[1]
apply (metis Prfs_flat)
by (metis Prfs.intros(1))

text {*
  The string behind the injection value is an added c
*}

lemma v4s:
  assumes "\<Turnstile>s v : der c r" shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct arbitrary: s v rule: der.induct)
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "c = c'")
apply(simp)
apply(auto)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prfs.cases)
apply(simp_all (no_asm_use))[5]
apply(auto)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(clarify)
apply(simp only: injval.simps flat.simps)
apply(auto)[1]
apply (metis mkeps_flat)
apply(simp)
apply(erule Prfs.cases)
apply(simp_all)[5]
done

lemma v4:
  assumes "\<turnstile> v : der c r" shows "flat (injval r c v) = c # (flat v)"
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
apply(case_tac "c = x")
apply(simp)
apply(simp add: Values_recs)
apply(simp)
apply(simp add: Values_recs)
apply(simp add: prefix_def)
apply(case_tac "nullable x1")
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

lemma 
  assumes "MValue v1 r1 s"
  shows "MValue (Seq v1 v2) (SEQ r1 r2) s


lemma MValue_SEQE:
  assumes "MValue v (SEQ r1 r2) s"
  shows "(\<exists>v1 v2. MValue v1 r1 s \<and> MValue v2 r2 (rest v1 s) \<and> v = Seq v1 v2)"
using assms
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(erule conjE)
apply(erule exE)+
apply(erule conjE)+
apply(simp)
apply(auto)
apply(drule_tac x="Seq x v2" in spec)
apply(drule mp)
apply(rule_tac x="x" in exI)
apply(rule_tac x="v2" in exI)
apply(simp)
oops


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

lemma MValue_injval:
  assumes "MValue v (der c r) s"
  shows "MValue (injval r c v) r (c#s)"
using assms
apply(induct c r arbitrary: v s rule: der.induct)
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(case_tac "c = c'")
apply(simp)
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(simp add: prefix_def)
apply(rule ValOrd2.intros)
apply(simp)
apply(simp add: MValue_def)
apply(simp add: Values_recs)
apply(simp)
apply(drule MValue_ALTE)
apply(erule disjE)
apply(auto)[1]
apply(rule MValue_ALTI1)
apply(simp)
apply(subst v4)
apply(simp add: MValue_def Values_def)
apply(rule ballI)
apply(simp)
apply(case_tac "flat vr = []")
apply(simp)
apply(drule_tac x="projval r2 c vr" in bspec)
apply(rule Values_projval)
apply(simp)
apply(simp add: Values_def prefix_def)
apply(auto)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(simp add: Values_def prefix_def)
apply(auto)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(subst (asm) v4_proj2)
apply(assumption)
apply(assumption)
apply(simp)
apply(auto)[1]
apply(rule MValue_ALTI2)
apply(simp)
apply(subst v4)
apply(simp add: MValue_def Values_def)
apply(rule ballI)
apply(simp)
apply(case_tac "flat vl = []")
apply(simp)
apply(drule_tac x="projval r1 c vl" in bspec)
apply(rule Values_projval)
apply(simp)
apply(simp add: Values_def prefix_def)
apply(auto)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(simp add: Values_def prefix_def)
apply(auto)[1]
apply(simp add: append_eq_Cons_conv)
apply(auto)[1]
apply(subst (asm) v4_proj2)
apply(simp add: MValue_def Values_def)
apply(assumption)
apply(assumption)
apply(case_tac "nullable r1")
defer
apply(simp)
apply(frule MValue_SEQE)
apply(auto)[1]


apply(simp add: MValue_def)
apply(simp add: Values_recs)

lemma nullable_red:
  "\<not>nullable (red c r)"
apply(induct r)
apply(auto)
done

lemma twq:
  assumes "\<turnstile> v : r" 
  shows "\<turnstile> injval r c v : red c r"
using assms
apply(induct)
apply(auto)
oops

lemma injval_inj_red: "inj_on (injval (red c r) c) {v. \<turnstile> v : r}"
using injval_inj
apply(auto simp add: inj_on_def)
apply(drule_tac x="red c r" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="x" in spec)
apply(drule mp)
oops

lemma 
  assumes "POSIXs v (der c r) s" 
  shows "POSIXs (injval r c v) r (c # s)"
using assms
apply(induct c r arbitrary: v s rule: der.induct)
apply(auto simp add: POSIXs_def)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(auto simp add: POSIXs_def)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(case_tac "c = c'")
apply(auto simp add: POSIXs_def)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply (metis Prfs.intros(5))
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply (metis ValOrd2.intros(8))
apply(auto simp add: POSIXs_def)[1]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(frule Prfs_POSIX)
apply(drule conjunct1)
apply(erule Prfs.cases)
apply(simp_all)[5]
apply(rule POSIXs_ALT_I1)
apply (metis POSIXs_ALT2)
apply(rule POSIXs_ALT_I2)
apply (metis POSIXs_ALT1a)
apply(frule POSIXs_ALT1b)
apply(auto)
apply(frule POSIXs_ALT1a)
(* HERE *)
oops

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

section {* TESTTEST *}

inductive ValOrdA :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ A\<succ>_ _" [100, 100, 100] 100)
where
  "v2 A\<succ>r2 v2' \<Longrightarrow> (Seq v1 v2) A\<succ>(SEQ r1 r2) (Seq v1 v2')" 
| "v1 A\<succ>r1 v1' \<Longrightarrow> (Seq v1 v2) A\<succ>(SEQ r1 r2) (Seq v1' v2')" 
| "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) A\<succ>(ALT r1 r2) (Right v2)"
| "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) A\<succ>(ALT r1 r2) (Left v1)"
| "v2 A\<succ>r2 v2' \<Longrightarrow> (Right v2) A\<succ>(ALT r1 r2) (Right v2')"
| "v1 A\<succ>r1 v1' \<Longrightarrow> (Left v1) A\<succ>(ALT r1 r2) (Left v1')"
| "Void A\<succ>EMPTY Void"
| "(Char c) A\<succ>(CHAR c) (Char c)"

inductive ValOrd4 :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ 4\<succ> _ _" [100, 100] 100)
where
  (*"v1 4\<succ>(der c r) v1' \<Longrightarrow> (injval r c v1) 4\<succ>r (injval r c v1')" 
| "\<lbrakk>v1 4\<succ>r v2; v2 4\<succ>r v3\<rbrakk> \<Longrightarrow> v1 4\<succ>r v3" 
|*) 
  "\<lbrakk>v1 4\<succ>r1 v1'; flat v2 = flat v2'; \<turnstile> v2 : r2; \<turnstile> v2' : r2\<rbrakk> \<Longrightarrow> (Seq v1 v2) 4\<succ>(SEQ r1 r2)  (Seq v1' v2')"
| "\<lbrakk>v2 4\<succ>r2 v2'; \<turnstile> v1 : r1\<rbrakk> \<Longrightarrow> (Seq v1 v2) 4\<succ>(SEQ r1 r2)  (Seq v1 v2')"
| "\<lbrakk>flat v1 = flat v2; \<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> (Left v1) 4\<succ>(ALT r1 r2) (Right v2)"
| "v2 4\<succ>r2 v2' \<Longrightarrow> (Right v2) 4\<succ>(ALT r1 r2) (Right v2')"
| "v1 4\<succ>r1 v1' \<Longrightarrow> (Left v1) 4\<succ>(ALT r1 r2) (Left v1')"
| "Void 4\<succ>(EMPTY) Void"
| "(Char c) 4\<succ>(CHAR c) (Char c)"

lemma ValOrd4_Prf:
  assumes "v1 4\<succ>r v2"
  shows "\<turnstile> v1 : r \<and> \<turnstile> v2 : r"
using assms
apply(induct v1 r v2)
apply(auto intro: Prf.intros)
done

lemma ValOrd4_flat:
  assumes "v1 4\<succ>r v2"
  shows "flat v1 = flat v2"
using assms
apply(induct v1 r v2)
apply(simp_all)
done

lemma ValOrd4_refl:
  assumes "\<turnstile> v : r"
  shows "v 4\<succ>r v"
using assms
apply(induct v r)
apply(auto intro: ValOrd4.intros)
done

lemma 
  assumes "v1 4\<succ>r v2" "v2 4\<succ>r v3" 
  shows "v1 A\<succ>r v3"
using assms
apply(induct v1 r v2 arbitrary: v3)
apply(rotate_tac 5)
apply(erule ValOrd4.cases)
apply(simp_all)
apply(clarify)
apply (metis ValOrdA.intros(2))
apply(clarify)
apply (metis ValOrd4_refl ValOrdA.intros(2))
apply(rotate_tac 3)
apply(erule ValOrd4.cases)
apply(simp_all)
apply(clarify)

apply (metis ValOrdA.intros(2))
apply (metis ValOrdA.intros(1))
apply (metis ValOrdA.intros(3) order_refl)
apply (auto intro: ValOrdA.intros)
done

lemma 
  assumes "v1 4\<succ>r v2"
  shows "v1 A\<succ>r v2"
using assms
apply(induct v1 r v2 arbitrary:)
apply (metis ValOrdA.intros(2))
apply (metis ValOrdA.intros(1))
apply (metis ValOrdA.intros(3) order_refl)
apply (auto intro: ValOrdA.intros)
done

lemma 
  assumes "v1 \<succ>r v2" "\<turnstile> v1 : r" "\<turnstile> v2 : r" "flat v1 = flat v2"
  shows "v1 4\<succ>r v2"
using assms
apply(induct v1 r v2 arbitrary:)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply (metis ValOrd4.intros(4) ValOrd4_flat ValOrd4_refl)
apply(simp)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)

lemma 
  assumes "v1 \<succ>r v2" "\<turnstile> v1 : r" "\<turnstile> v2 : r" "flat v1 = flat v2"
  shows "v1 4\<succ>r v2"
using assms
apply(induct v1 r v2 arbitrary:)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)
apply (metis ValOrd4.intros(4) ValOrd4_flat ValOrd4_refl)
apply(simp)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[5]
apply(clarify)


apply(simp)
apply(erule Prf.cases)




lemma rr2: "hd (flats v) \<noteq> [] \<Longrightarrow> flats v \<noteq> []"
apply(induct v)
apply(auto)
done

lemma rr3: "flats v = [] \<Longrightarrow> flat v = []"
apply(induct v)
apply(auto)
done

lemma POSIXs_der:
  assumes "POSIXs v (der c r) s" "\<Turnstile>s v : der c r"
  shows "POSIXs (injval r c v) r (c#s)"
using assms
unfolding POSIXs_def
apply(auto)
thm v3s 
apply (erule v3s)
apply(drule_tac x="projval r c v'" in spec)
apply(drule mp)
thm v3s_proj
apply(rule v3s_proj)
apply(simp)
thm v3s_proj
apply(drule v3s_proj)
oops

term Values
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
apply(drule_tac x="s" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(simp)
apply(simp add: rest_def mkeps_flat)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(simp)
apply(clarify)
apply(simp add: prefix_Cons)
apply(subgoal_tac "((flat v1c) @ (flat v2b)) \<sqsubseteq> (flat v2)")
prefer 2
apply(simp add: prefix_def)
apply(auto)[1]
(* HEREHERE *)


lemma Prf_inj_test:
  assumes "v1 \<succ>r v2" 
          "v1 \<in> Values r s"
          "v2 \<in> Values r s"
          "injval r c v1 \<in> Values (red c r) (c#s)"
          "injval r c v2 \<in> Values (red c r) (c#s)"
  shows "(injval r c v1) \<succ>(red c r)  (injval r c v2)"
using assms
apply(induct v1 r v2 arbitrary: s rule: ValOrd.induct)
apply(simp add: Values_recs)
apply (metis ValOrd.intros(1))
apply(simp add: Values_recs)
apply(rule ValOrd.intros(2))
apply(metis)
defer
apply(simp add: Values_recs)
apply(rule ValOrd.intros)
apply(subst v4)
apply(simp add: Values_def)
apply(subst v4)
apply(simp add: Values_def)
using injval_inj_red
apply(simp add: Values_def inj_on_def)
apply(rule notI)
apply(drule_tac x="r1" in meta_spec)
apply(drule_tac x="c" in meta_spec)
apply(drule_tac x="injval r1 c v1" in spec)
apply(simp)

apply(drule_tac x="c" in meta_spec)

apply metis
apply (metis ValOrd.intros(1))



done
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
apply(drule_tac x="s" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(simp)
apply(simp add: rest_def mkeps_flat)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(simp)
apply(clarify)
apply(simp add: prefix_Cons)
apply(subgoal_tac "((flat v1c) @ (flat v2b)) \<sqsubseteq> (flat v2)")
prefer 2
apply(simp add: prefix_def)
apply(auto)[1]
(* HEREHERE *)

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
apply(drule_tac x="s" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(drule_tac meta_mp)
apply(simp add: rest_def mkeps_flat)
apply(simp)
apply(simp add: rest_def mkeps_flat)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(subst (asm) (5) v4)
apply(simp)
apply(simp)
apply(clarify)
apply(simp add: prefix_Cons)
apply(subgoal_tac "((flat v1c) @ (flat v2b)) \<sqsubseteq> (flat v2)")
prefer 2
apply(simp add: prefix_def)
apply(auto)[1]
(* HEREHERE *)

apply(subst (asm) (7) v4)
apply(simp)


(* HEREHERE *)

apply(simp add: Values_def)
apply(simp add: Values_recs)
apply(simp add: Values_recs)
done

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
thm  Prf_inj_test
apply(drule_tac r="r" in Prf_inj_test)
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

apply metis
apply(simp)
apply(simp)
apply(erule disjE)
apply(simp)

apply(drule_tac x="v2" in spec)

lemma POSIX_ex2: "\<turnstile> v : r \<Longrightarrow> \<exists>v. POSIX v r \<and> \<turnstile> v : r"
apply(induct r arbitrary: v)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule_tac x="Void" in exI)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply (metis Prf.intros(4))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule_tac x="Char c" in exI)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)[1]
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="v2" in meta_spec)
apply(auto)[1]
apply(simp add: POSIX_def)
apply(auto)[1]
apply(rule ccontr)
apply(simp)
apply(drule_tac x="Seq v va" in spec)
apply(drule mp)
defer
apply (metis Prf.intros(1))
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
apply (metis ValOrd.intros(7))
apply(erule_tac [!] exE)
prefer 3
apply(frule POSIX_SEQ1)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "flat v1 = []")
apply(subgoal_tac "nullable r1")
apply(simp)
prefer 2
apply(rule_tac v="v1" in Prf_flat_empty)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(frule POSIX_SEQ2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(drule meta_mp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ccontr)
apply(subgoal_tac "\<turnstile> val.Right (projval r2 c v2) : (ALT (SEQ (der c r1) r2) (der c r2))")
apply(rotate_tac 11)
apply(frule POSIX_ex)
apply(erule exE)
apply(drule POSIX_ALT_cases2)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(drule v3_proj)
apply(simp)
apply(simp)
apply(drule POSIX_ex)
apply(erule exE)
apply(frule POSIX_ALT_cases2)
apply(simp)
apply(simp)
apply(erule 
prefer 2
apply(case_tac "nullable r1")
prefer 2
apply(simp)
apply(rotate_tac 1)
apply(drule meta_mp)
apply(rule POSIX_SEQ1)
apply(assumption)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rotate_tac 7)
apply(drule meta_mp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rotate_tac 7)
apply(drule meta_mp)
apply (metis Cons_eq_append_conv)


apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: POSIX_def)
apply(simp)
apply(simp)
apply(simp_all)[5]
apply(simp add: POSIX_def)


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
apply (metis ValOrd.intros(7))

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
apply (metis ValOrd.intros(7))
apply(erule_tac [!] exE)
prefer 3
apply(frule POSIX_SEQ1)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "flat v1 = []")
apply(subgoal_tac "nullable r1")
apply(simp)
prefer 2
apply(rule_tac v="v1" in Prf_flat_empty)
apply(erule Prf.cases)
apply(simp_all)[5]


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
apply (metis ValOrd.intros(7))
apply(erule_tac [!] exE)
prefer 3
apply(frule POSIX_SEQ1)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(case_tac "flat v1 = []")
apply(subgoal_tac "nullable r1")
apply(simp)
prefer 2
apply(rule_tac v="v1" in Prf_flat_empty)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
apply(rule ccontr)
apply(drule v3_proj)
apply(simp)
apply(simp)
apply(drule POSIX_ex)
apply(erule exE)
apply(frule POSIX_ALT_cases2)
apply(simp)
apply(simp)
apply(erule 
prefer 2
apply(case_tac "nullable r1")
prefer 2
apply(simp)
apply(rotate_tac 1)
apply(drule meta_mp)
apply(rule POSIX_SEQ1)
apply(assumption)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rotate_tac 7)
apply(drule meta_mp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rotate_tac 7)
apply(drule meta_mp)
apply (metis Cons_eq_append_conv)


apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp add: POSIX_def)
apply(simp)
apply(simp)
apply(simp_all)[5]
apply(simp add: POSIX_def)

done
(* NULL case *)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(7))
apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(simp)
prefer 2
apply(simp)
apply(frule POSIX_ALT1a)
apply(drule meta_mp)
apply(simp)
apply(drule meta_mp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule POSIX_ALT_I2)
apply(assumption)
apply(auto)[1]

thm v4_proj2
prefer 2
apply(subst (asm) (13) POSIX_def)

apply(drule_tac x="projval v2" in spec)
apply(auto)[1]
apply(drule mp)
apply(rule conjI)
apply(simp)
apply(simp)

apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
prefer 2
apply(clarify)
apply(subst (asm) (2) POSIX_def)

apply (metis ValOrd.intros(5))
apply(clarify)
apply(simp)
apply(rotate_tac 3)
apply(drule_tac c="c" in t2)
apply(subst (asm) v4_proj)
apply(simp)
apply(simp)
thm contrapos_np contrapos_nn
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply(subst  v4_proj2)
apply(simp)
apply(simp)
apply(subgoal_tac "\<not>(length (flat v1) < length (flat (projval r2a c v2a)))")
prefer 2
apply(erule contrapos_nn)
apply (metis nat_less_le v4_proj2)
apply(simp)

apply(blast)
thm contrapos_nn

apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(rule ValOrd.intros)
apply(drule meta_mp)
apply(auto)[1]
apply (metis POSIX_ALT2 POSIX_def flat.simps(3))
apply metis
apply(clarify)
apply(rule ValOrd.intros)
apply(simp)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(rule ValOrd.intros)
apply(simp)

apply(drule meta_mp)
apply(auto)[1]
apply (metis POSIX_ALT2 POSIX_def flat.simps(3))
apply metis
apply(clarify)
apply(rule ValOrd.intros)
apply(simp)


done
(* EMPTY case *)
apply(simp add: POSIX_def)
apply(auto)[1]
apply(rotate_tac 3)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(drule_tac c="c" in t2)
apply(subst (asm) v4_proj)
apply(auto)[2]

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


unfolding POSIX_def
apply(auto)
thm v4

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
apply(simp)
apply(rule ValOrd.intros(2))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
defer
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all del: injval.simps)[8]
apply(simp)
apply(clarify)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(rule ValOrd.intros(2))




done


txt {*
done
(* nullable case - unfinished *)
apply(simp)
apply(erule ValOrd.cases)
apply(simp_all del: injval.simps)[8]
apply(simp)
apply(clarify)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(simp)
apply(rule ValOrd.intros(2))
oops
*}
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

lemma "L r \<noteq> {} \<Longrightarrow> \<exists>v. POSIX3 v r"
apply(induct r)
apply(simp)
apply(simp add: POSIX3_def)
apply(rule_tac x="Void" in exI)
apply(auto)[1]
apply (metis Prf.intros(4))
apply (metis POSIX3_def flat.simps(1) mkeps.simps(1) mkeps_POSIX3 nullable.simps(2) order_refl)
apply(simp add: POSIX3_def)
apply(rule_tac x="Char char" in exI)
apply(auto)[1]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[5]
apply (metis ValOrd.intros(8))
apply(simp add: Sequ_def)
apply(auto)[1]
apply(drule meta_mp)
apply(auto)[2]
apply(drule meta_mp)
apply(auto)[2]
apply(rule_tac x="Seq v va" in exI)
apply(simp (no_asm) add: POSIX3_def)
apply(auto)[1]
apply (metis POSIX3_def Prf.intros(1))
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply(case_tac "v  \<succ>r1a v1")
apply(rule ValOrd.intros(2))
apply(simp)
apply(case_tac "v = v1")
apply(rule ValOrd.intros(1))
apply(simp)
apply(simp)
apply (metis ValOrd_refl)
apply(simp add: POSIX3_def)
oops

lemma "\<exists>v. POSIX v r"
apply(induct r)
apply(rule exI)
apply(simp add: POSIX_def)
apply (metis (full_types) Prf_flat_L der.simps(1) der.simps(2) der.simps(3) flat.simps(1) nullable.simps(1) nullable_correctness proj_inj_id projval.simps(1) v3 v4)
apply(rule_tac x = "Void" in exI)
apply(simp add: POSIX_def)
apply (metis POSIX_def flat.simps(1) mkeps.simps(1) mkeps_POSIX nullable.simps(2))
apply(rule_tac x = "Char char" in exI)
apply(simp add: POSIX_def)
apply(auto) [1]
apply(erule Prf.cases)
apply(simp_all) [5]
apply (metis ValOrd.intros(8))
defer
apply(auto)
apply (metis POSIX_ALT_I1)
(* maybe it is too early to instantiate this existential quantifier *)
(* potentially this is the wrong POSIX value *)
apply(case_tac "r1 = NULL")
apply(simp add: POSIX_def)
apply(auto)[1]
apply (metis L.simps(1) L.simps(4) Prf_flat_L mkeps_flat nullable.simps(1) nullable.simps(2) nullable_correctness seq_null(2))
apply(case_tac "r1 = EMPTY")
apply(rule_tac x = "Seq Void va" in exI )
apply(simp (no_asm) add: POSIX_def)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)
apply(rule ValOrd.intros(2))
apply(rule ValOrd.intros)
apply(case_tac "\<exists>c. r1 = CHAR c")
apply(auto)
apply(rule_tac x = "Seq (Char c) va" in exI )
apply(simp (no_asm) add: POSIX_def)
apply(auto)
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)
apply(auto)[1]
apply(rule ValOrd.intros(2))
apply(rule ValOrd.intros)
apply(case_tac "\<exists>r1a r1b. r1 = ALT r1a r1b")
apply(auto)
oops (* not sure if this can be proved by induction *)

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
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[5]
(* base cases done *)
(* ALT case *)
apply(erule Prf.cases)
apply(simp_all)[5]
using POSIX_ALT POSIX_ALT_I1 apply blast
apply(clarify)
apply(simp)
apply(rule POSIX_ALT_I2)
apply(drule POSIX_ALT1a)
apply metis
apply(auto)[1]
apply(subst v4)
apply(assumption)
apply(simp)
apply(drule POSIX_ALT1a)
apply(rotate_tac 1)
apply(drule_tac x="v2" in meta_spec)
apply(simp)

apply(rotate_tac 4)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(rule ValOrd.intros)
apply(simp)
apply(subst (asm) v4)
apply(assumption)
apply(clarify)
thm POSIX_ALT1a POSIX_ALT1b POSIX_ALT_I2
apply(subst (asm) v4)
apply(auto simp add: POSIX_def)[1]
apply(subgoal_tac "POSIX v2 (der c r2)")
prefer 2
apply(auto simp add: POSIX_def)[1]
apply (metis POSIX_ALT1a POSIX_def flat.simps(4))
apply(frule POSIX_ALT1a)
apply(drule POSIX_ALT1b)
apply(rule POSIX_ALT_I2)
apply(rotate_tac 1)
apply(drule_tac x="v2" in meta_spec)
apply(simp)
apply(subgoal_tac "\<turnstile> Right (injval r2 c v2) : (ALT r1 r2)")
prefer 2
apply (metis Prf.intros(3) v3)
apply auto[1]
apply(subst v4)
apply(auto)[2]
apply(subst (asm) (4) POSIX_def)
apply(subst (asm) v4)
apply(drule_tac x="v2" in meta_spec)
apply(simp)

apply(auto)[2]

thm POSIX_ALT_I2
apply(rule POSIX_ALT_I2)

apply(rule ccontr)
apply(auto simp add: POSIX_def)[1]

apply(rule allI)
apply(rule impI)
apply(erule conjE)
thm POSIX_ALT_I2
apply(frule POSIX_ALT1a)
apply(drule POSIX_ALT1b)
apply(rule POSIX_ALT_I2)
apply auto[1]
apply(subst v4)
apply(auto)[2]
apply(rotate_tac 1)
apply(drule_tac x="v2" in meta_spec)
apply(simp)
apply(subst (asm) (4) POSIX_def)
apply(subst (asm) v4)
apply(auto)[2]
(* stuck in the ALT case *)
