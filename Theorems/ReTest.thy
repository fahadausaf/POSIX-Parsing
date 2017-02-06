   
theory ReTest
  imports "Main" 
begin


section {* Sequential Composition of Sets *}

definition
  Sequ :: "string set \<Rightarrow> string set \<Rightarrow> string set" ("_ ;; _" [100,100] 100)
where 
  "A ;; B = {s1 @ s2 | s1 s2. s1 \<in> A \<and> s2 \<in> B}"

fun spow where
  "spow s 0 = []"
| "spow s (Suc n) = s @ spow s n"

text {* Two Simple Properties about Sequential Composition *}

lemma seq_empty [simp]:
  shows "A ;; {[]} = A"
  and   "{[]} ;; A = A"
by (simp_all add: Sequ_def)

lemma seq_null [simp]:
  shows "A ;; {} = {}"
  and   "{} ;; A = {}"
by (simp_all add: Sequ_def)

definition
  Der :: "char \<Rightarrow> string set \<Rightarrow> string set"
where
  "Der c A \<equiv> {s. [c] @ s \<in> A}"

definition 
  Ders :: "string \<Rightarrow> string set \<Rightarrow> string set"
where  
  "Ders s A \<equiv> {s' | s'. s @ s' \<in> A}"

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

lemma Der_seq [simp]:
  shows "Der c (A ;; B) = (Der c A) ;; B \<union> (if [] \<in> A then Der c B else {})"
unfolding Der_def Sequ_def
apply (auto simp add: Cons_eq_append_conv)
done

lemma seq_image:
  assumes "\<forall>s1 s2. f (s1 @ s2) = (f s1) @ (f s2)"
  shows "f ` (A ;; B) = (f ` A) ;; (f ` B)"
apply(auto simp add: Sequ_def image_def)
apply(rule_tac x="f s1" in exI)
apply(rule_tac x="f s2" in exI)
using assms
apply(auto)
apply(rule_tac x="xa @ xb" in exI)
using assms
apply(auto)
done

section {* Kleene Star for Sets *}

inductive_set
  Star :: "string set \<Rightarrow> string set" ("_\<star>" [101] 102)
  for A :: "string set"
where
  start[intro]: "[] \<in> A\<star>"
| step[intro]:  "\<lbrakk>s1 \<in> A; s2 \<in> A\<star>\<rbrakk> \<Longrightarrow> s1 @ s2 \<in> A\<star>"

lemma star_cases:
  shows "A\<star> = {[]} \<union> A ;; A\<star>"
unfolding Sequ_def
by (auto) (metis Star.simps)


fun 
  pow :: "string set \<Rightarrow> nat \<Rightarrow> string set" ("_ \<up> _" [100,100] 100)
where
  "A \<up> 0 = {[]}"
| "A \<up> (Suc n) = A ;; (A \<up> n)"  

lemma star1: 
  shows "s \<in> A\<star> \<Longrightarrow> \<exists>n. s \<in> A \<up> n"
  apply(induct rule: Star.induct)
  apply (metis pow.simps(1) insertI1)
  apply(auto)
  apply(rule_tac x="Suc n" in exI)
  apply(auto simp add: Sequ_def)
  done

lemma star2:
  shows "s \<in> A \<up> n \<Longrightarrow> s \<in> A\<star>"
  apply(induct n arbitrary: s)
  apply (metis pow.simps(1) Star.simps empty_iff insertE)
  apply(auto simp add: Sequ_def)
  done

lemma star3:
  shows "A\<star> = (\<Union>i. A \<up> i)"
using star1 star2
apply(auto)
done

lemma star4:
  shows "s \<in> A \<up> n \<Longrightarrow> \<exists>ss. s = concat ss \<and> (\<forall>s' \<in> set ss. s' \<in> A)"
  apply(induct n arbitrary: s)
  apply(auto simp add: Sequ_def)
  apply(rule_tac x="[]" in exI)
  apply(auto)
  apply(drule_tac x="s2" in meta_spec)
  apply(auto)
by (metis concat.simps(2) insertE set_simps(2))

lemma star5:
  assumes "f [] = []"
  assumes "\<forall>s1 s2. f (s1 @ s2) = (f s1) @ (f s2)"
  shows "(f ` A) \<up> n = f ` (A \<up> n)"
apply(induct n)
apply(simp add: assms)
apply(simp)
apply(subst seq_image[OF assms(2)])
apply(simp)
done

lemma star6:
  assumes "f [] = []"
  assumes "\<forall>s1 s2. f (s1 @ s2) = (f s1) @ (f s2)"
  shows "(f ` A)\<star> = f ` (A\<star>)"
apply(simp add: star3)
apply(simp add: image_UN)
apply(subst star5[OF assms])
apply(simp)
done

lemma star_decomp: 
  assumes a: "c # x \<in> A\<star>" 
  shows "\<exists>a b. x = a @ b \<and> c # a \<in> A \<and> b \<in> A\<star>"
using a
by (induct x\<equiv>"c # x" rule: Star.induct) 
   (auto simp add: append_eq_Cons_conv)

lemma Der_star [simp]:
  shows "Der c (A\<star>) = (Der c A) ;; A\<star>"
proof -    
  have "Der c (A\<star>) = Der c ({[]} \<union> A ;; A\<star>)"
    
    by (simp only: star_cases[symmetric])
  also have "... = Der c (A ;; A\<star>)"
    by (simp only: Der_union Der_empty) (simp)
  also have "... = (Der c A) ;; A\<star> \<union> (if [] \<in> A then Der c (A\<star>) else {})"
    by simp
  also have "... =  (Der c A) ;; A\<star>"
    unfolding Sequ_def Der_def
    by (auto dest: star_decomp)
  finally show "Der c (A\<star>) = (Der c A) ;; A\<star>" .
qed



section {* Regular Expressions *}

datatype rexp =
  NULL
| EMPTY
| CHAR char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp

section {* Semantics of Regular Expressions *}
 
fun
  L :: "rexp \<Rightarrow> string set"
where
  "L (NULL) = {}"
| "L (EMPTY) = {[]}"
| "L (CHAR c) = {[c]}"
| "L (SEQ r1 r2) = (L r1) ;; (L r2)"
| "L (ALT r1 r2) = (L r1) \<union> (L r2)"
| "L (STAR r) = (L r)\<star>"

fun
 nullable :: "rexp \<Rightarrow> bool"
where
  "nullable (NULL) = False"
| "nullable (EMPTY) = True"
| "nullable (CHAR c) = False"
| "nullable (ALT r1 r2) = (nullable r1 \<or> nullable r2)"
| "nullable (SEQ r1 r2) = (nullable r1 \<and> nullable r2)"
| "nullable (STAR r) = True"

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

lemma [simp]:
 "flat (Stars vs) = concat (map flat vs)"
apply(induct vs)
apply(auto)
done

section {* Relation between values and regular expressions *}

inductive 
  NPrf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<Turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<Turnstile> v1 : r1; \<Turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<Turnstile> Seq v1 v2 : SEQ r1 r2"
| "\<Turnstile> v1 : r1 \<Longrightarrow> \<Turnstile> Left v1 : ALT r1 r2"
| "\<Turnstile> v2 : r2 \<Longrightarrow> \<Turnstile> Right v2 : ALT r1 r2"
| "\<Turnstile> Void : EMPTY"
| "\<Turnstile> Char c : CHAR c"
| "\<Turnstile> Stars [] : STAR r"
| "\<lbrakk>\<Turnstile> v : r; \<Turnstile> Stars vs : STAR r; flat v \<noteq> []\<rbrakk> \<Longrightarrow> \<Turnstile> Stars (v # vs) : STAR r"

inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : SEQ r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : ALT r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : ALT r1 r2"
| "\<turnstile> Void : EMPTY"
| "\<turnstile> Char c : CHAR c"
| "\<turnstile> Stars [] : STAR r"
| "\<lbrakk>\<turnstile> v : r; \<turnstile> Stars vs : STAR r\<rbrakk> \<Longrightarrow> \<turnstile> Stars (v # vs) : STAR r"

lemma NPrf_imp_Prf:
  assumes "\<Turnstile> v : r" 
  shows "\<turnstile> v : r"
using assms
apply(induct)
apply(auto intro: Prf.intros)
done

lemma NPrf_Prf_val:
  shows "\<turnstile> v : r \<Longrightarrow> \<exists>v'. flat v' = flat v \<and> \<Turnstile> v' : r"
  and   "\<turnstile> Stars vs : r \<Longrightarrow> \<exists>vs'. flat (Stars vs') = flat (Stars vs) \<and> \<Turnstile> Stars vs' : r"
using assms
apply(induct v and vs arbitrary: r and r rule: val.inducts)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule_tac x="Void" in exI)
apply(simp)
apply(rule NPrf.intros)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule_tac x="Char c" in exI)
apply(simp)
apply(rule NPrf.intros)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply(drule_tac x="r1" in meta_spec)
apply(drule_tac x="r2" in meta_spec)
apply(simp)
apply(auto)[1]
apply(rule_tac x="Seq v' v'a" in exI)
apply(simp)
apply (metis NPrf.intros(1))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(drule_tac x="r2" in meta_spec)
apply(simp)
apply(auto)[1]
apply(rule_tac x="Right v'" in exI)
apply(simp)
apply (metis NPrf.intros)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(drule_tac x="r1" in meta_spec)
apply(simp)
apply(auto)[1]
apply(rule_tac x="Left v'" in exI)
apply(simp)
apply (metis NPrf.intros)
apply(drule_tac x="r" in meta_spec)
apply(simp)
apply(auto)[1]
apply(rule_tac x="Stars vs'" in exI)
apply(simp)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis NPrf.intros(6))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply(drule_tac x="ra" in meta_spec)
apply(simp)
apply(drule_tac x="STAR ra" in meta_spec)
apply(simp)
apply(auto)
apply(case_tac "flat v = []")
apply(rule_tac x="vs'" in exI)
apply(simp)
apply(rule_tac x="v' # vs'" in exI)
apply(simp)
apply(rule NPrf.intros)
apply(auto)
done

lemma NPrf_Prf:
  shows "{flat v | v. \<turnstile> v : r} = {flat v | v. \<Turnstile> v : r}"
apply(auto)
apply (metis NPrf_Prf_val(1))
by (metis NPrf_imp_Prf)


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

lemma NPrf_flat_L:
  assumes "\<Turnstile> v : r" shows "flat v \<in> L r"
using assms
by (metis NPrf_imp_Prf Prf_flat_L)

lemma Prf_Stars:
  assumes "\<forall>v \<in> set vs. \<turnstile> v : r"
  shows "\<turnstile> Stars vs : STAR r"
using assms
apply(induct vs)
apply (metis Prf.intros(6))
by (metis Prf.intros(7) insert_iff set_simps(2))

lemma Star_string:
  assumes "s \<in> A\<star>"
  shows "\<exists>ss. concat ss = s \<and> (\<forall>s \<in> set ss. s \<in> A)"
using assms
apply(induct rule: Star.induct)
apply(auto)
apply(rule_tac x="[]" in exI)
apply(simp)
apply(rule_tac x="s1#ss" in exI)
apply(simp)
done

lemma Star_val:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<turnstile> v : r"
  shows "\<exists>vs. concat (map flat vs) = concat ss \<and> (\<forall>v\<in>set vs. \<turnstile> v : r)"
using assms
apply(induct ss)
apply(auto)
apply (metis empty_iff list.set(1))
by (metis concat.simps(2) list.simps(9) set_ConsD)

lemma Star_valN:
  assumes "\<forall>s\<in>set ss. \<exists>v. s = flat v \<and> \<Turnstile> v : r"
  shows "\<exists>vs. concat (map flat vs) = concat ss \<and> (\<forall>v\<in>set vs. \<Turnstile> v : r)"
using assms
apply(induct ss)
apply(auto)
apply (metis empty_iff list.set(1))
by (metis concat.simps(2) list.simps(9) set_ConsD)

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
apply(subgoal_tac "\<exists>vs::val list. concat (map flat vs) = x \<and> (\<forall>v \<in> set vs. \<turnstile> v : r)")
apply(auto)[1]
apply(rule_tac x="Stars vs" in exI)
apply(simp)
apply(rule Prf_Stars)
apply(simp)
apply(drule Star_string)
apply(auto)
apply(rule Star_val)
apply(simp)
done

lemma L_flat_NPrf:
  "L(r) = {flat v | v. \<Turnstile> v : r}"
by (metis L_flat_Prf NPrf_Prf)

text {* nicer proofs by Fahad *}

lemma Prf_Star_flat_L:
  assumes "\<turnstile> v : STAR r" shows "flat v \<in> (L r)\<star>"
using assms
apply(induct v r\<equiv>"STAR r" arbitrary: r rule: Prf.induct)
apply(auto)
apply(simp add: star3)
apply(auto)
apply(rule_tac x="Suc x" in exI)
apply(auto simp add: Sequ_def)
apply(rule_tac x="flat v" in exI)
apply(rule_tac x="flat (Stars vs)" in exI)
apply(auto)
by (metis Prf_flat_L)

lemma L_flat_Prf2:
  "L(r) = {flat v | v. \<turnstile> v : r}"
apply(induct r)
apply(auto)
using L.simps(1) Prf_flat_L 
apply(blast)
using Prf.intros(4) 
apply(force)
using L.simps(2) Prf_flat_L 
apply(blast)
using Prf.intros(5) apply force
using L.simps(3) Prf_flat_L apply blast
using L_flat_Prf apply auto[1]
apply (smt L.simps(4) Sequ_def mem_Collect_eq)
using Prf_flat_L 
apply(fastforce)
apply(metis Prf.intros(2) flat.simps(3))
apply(metis Prf.intros(3) flat.simps(4))
apply(erule Prf.cases)
apply(simp)
apply(simp)
apply(auto)
using L_flat_Prf apply auto[1]
apply (smt Collect_cong L.simps(6) mem_Collect_eq)
using Prf_Star_flat_L 
apply(fastforce)
done


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

definition SPrefixes :: "string \<Rightarrow> string set" where
  "SPrefixes s \<equiv> {sp. sp \<sqsubset> s}"

definition SSuffixes :: "string \<Rightarrow> string set" where
  "SSuffixes s \<equiv> rev ` (SPrefixes (rev s))"

lemma Suffixes_in: 
  "\<exists>s1. s1 @ s2 = s3 \<Longrightarrow> s2 \<in> Suffixes s3"
unfolding Suffixes_def Prefixes_def prefix_def image_def
apply(auto)
by (metis rev_rev_ident)

lemma SSuffixes_in: 
  "\<exists>s1. s1 \<noteq> [] \<and> s1 @ s2 = s3 \<Longrightarrow> s2 \<in> SSuffixes s3"
unfolding SSuffixes_def Suffixes_def SPrefixes_def Prefixes_def sprefix_def prefix_def image_def
apply(auto)
by (metis append_self_conv rev.simps(1) rev_rev_ident)

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

definition SValues :: "rexp \<Rightarrow> string \<Rightarrow> val set" where
  "SValues r s \<equiv> {v. \<turnstile> v : r \<and> flat v = s}"


definition NValues :: "rexp \<Rightarrow> string \<Rightarrow> val set" where
  "NValues r s \<equiv> {v. \<Turnstile> v : r \<and> flat v \<sqsubseteq> s}"

lemma NValues_STAR_Nil:
  "NValues (STAR r) [] = {Stars []}"
apply(auto simp add: NValues_def prefix_def)
apply(erule NPrf.cases)
apply(auto)
by (metis NPrf.intros(6))


definition rest :: "val \<Rightarrow> string \<Rightarrow> string" where
  "rest v s \<equiv> drop (length (flat v)) s"

lemma rest_Nil:
  "rest v [] = []"
apply(simp add: rest_def)
done

lemma rest_Suffixes:
  "rest v s \<in> Suffixes s"
unfolding rest_def
by (metis Suffixes_in append_take_drop_id)

lemma rest_SSuffixes:
  assumes "flat v \<noteq> []" "s \<noteq> []"
  shows "rest v s \<in> SSuffixes s"
using assms
unfolding rest_def
thm SSuffixes_in
apply(rule_tac SSuffixes_in)
apply(rule_tac x="take (length (flat v)) s" in exI)
apply(simp add: sprefix_def)
done


lemma Values_recs:
  "Values (NULL) s = {}"
  "Values (EMPTY) s = {Void}"
  "Values (CHAR c) s = (if [c] \<sqsubseteq> s then {Char c} else {})" 
  "Values (ALT r1 r2) s = {Left v | v. v \<in> Values r1 s} \<union> {Right v | v. v \<in> Values r2 s}"
  "Values (SEQ r1 r2) s = {Seq v1 v2 | v1 v2. v1 \<in> Values r1 s \<and> v2 \<in> Values r2 (rest v1 s)}"
  "Values (STAR r) s = 
      {Stars []} \<union> {Stars (v # vs) | v vs. v \<in> Values r s \<and> Stars vs \<in> Values (STAR r) (rest v s)}"
unfolding Values_def
apply(auto)
(*NULL*)
apply(erule Prf.cases)
apply(simp_all)[7]
(*EMPTY*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule Prf.intros)
apply (metis append_Nil prefix_def)
(*CHAR*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule Prf.intros)
apply(erule Prf.cases)
apply(simp_all)[7]
(*ALT*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
(*SEQ*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (simp add: append_eq_conv_conj prefix_def rest_def)
apply (metis Prf.intros(1))
apply (simp add: append_eq_conv_conj prefix_def rest_def)
(*STAR*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule conjI)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: prefix_def)
apply(auto)[1]
apply (metis append_eq_conv_conj rest_def)
apply (metis Prf.intros(6))
apply (metis append_Nil prefix_def)
apply (metis Prf.intros(7))
by (metis append_eq_conv_conj prefix_append prefix_def rest_def)

lemma NValues_recs:
  "NValues (NULL) s = {}"
  "NValues (EMPTY) s = {Void}"
  "NValues (CHAR c) s = (if [c] \<sqsubseteq> s then {Char c} else {})" 
  "NValues (ALT r1 r2) s = {Left v | v. v \<in> NValues r1 s} \<union> {Right v | v. v \<in> NValues r2 s}"
  "NValues (SEQ r1 r2) s = {Seq v1 v2 | v1 v2. v1 \<in> NValues r1 s \<and> v2 \<in> NValues r2 (rest v1 s)}"
  "NValues (STAR r) s = 
  {Stars []} \<union> {Stars (v # vs) | v vs. v \<in> NValues r s \<and> flat v \<noteq> [] \<and>  Stars vs \<in> NValues (STAR r) (rest v s)}"
unfolding NValues_def
apply(auto)
(*NULL*)
apply(erule NPrf.cases)
apply(simp_all)[7]
(*EMPTY*)
apply(erule NPrf.cases)
apply(simp_all)[7]
apply(rule NPrf.intros)
apply (metis append_Nil prefix_def)
(*CHAR*)
apply(erule NPrf.cases)
apply(simp_all)[7]
apply(rule NPrf.intros)
apply(erule NPrf.cases)
apply(simp_all)[7]
(*ALT*)
apply(erule NPrf.cases)
apply(simp_all)[7]
apply (metis NPrf.intros(2))
apply (metis NPrf.intros(3))
(*SEQ*)
apply(erule NPrf.cases)
apply(simp_all)[7]
apply (simp add: append_eq_conv_conj prefix_def rest_def)
apply (metis NPrf.intros(1))
apply (simp add: append_eq_conv_conj prefix_def rest_def)
(*STAR*)
apply(erule NPrf.cases)
apply(simp_all)
apply(rule conjI)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: prefix_def)
apply(auto)[1]
apply (metis append_eq_conv_conj rest_def)
apply (metis NPrf.intros(6))
apply (metis append_Nil prefix_def)
apply (metis NPrf.intros(7))
by (metis append_eq_conv_conj prefix_append prefix_def rest_def)

lemma SValues_recs:
 "SValues (NULL) s = {}"
 "SValues (EMPTY) s = (if s = [] then {Void} else {})"
 "SValues (CHAR c) s = (if [c] = s then {Char c} else {})" 
 "SValues (ALT r1 r2) s = {Left v | v. v \<in> SValues r1 s} \<union> {Right v | v. v \<in> SValues r2 s}"
 "SValues (SEQ r1 r2) s = {Seq v1 v2 | v1 v2. \<exists>s1 s2. s = s1 @ s2 \<and> v1 \<in> SValues r1 s1 \<and> v2 \<in> SValues r2 s2}"
 "SValues (STAR r) s = (if s = [] then {Stars []} else {}) \<union> 
   {Stars (v # vs) | v vs. \<exists>s1 s2. s = s1 @ s2 \<and> v \<in> SValues r s1 \<and> Stars vs \<in> SValues (STAR r) s2}"
unfolding SValues_def
apply(auto)
(*NULL*)
apply(erule Prf.cases)
apply(simp_all)[7]
(*EMPTY*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule Prf.intros)
apply(erule Prf.cases)
apply(simp_all)[7]
(*CHAR*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(5))
apply(erule Prf.cases)
apply(simp_all)[7]
(*ALT*)
apply(erule Prf.cases)
apply(simp_all)[7]
apply metis
apply(erule Prf.intros)
apply(erule Prf.intros)
(* SEQ case *)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(1))
(* STAR case *)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule Prf.intros)
apply (metis Prf.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(7))
by (metis Prf.intros(7))

lemma finite_image_set2:
  "finite {x. P x} \<Longrightarrow> finite {y. Q y} \<Longrightarrow> finite {(x, y) | x y. P x \<and> Q y}"
  by (rule finite_subset [where B = "\<Union>x \<in> {x. P x}. \<Union>y \<in> {y. Q y}. {(x, y)}"]) auto


lemma NValues_finite_aux:
  "(\<lambda>(r, s). finite (NValues r s)) (r, s)"
apply(rule wf_induct[of "measure size <*lex*> measure length",where P="\<lambda>(r, s). finite (NValues r s)"])
apply (metis wf_lex_prod wf_measure)
apply(auto)
apply(case_tac a)
apply(simp_all)
apply(simp add: NValues_recs)
apply(simp add: NValues_recs)
apply(simp add: NValues_recs)
apply(simp add: NValues_recs)
apply(rule_tac f="\<lambda>(x, y). Seq x y" and 
               A="{(v1, v2) | v1 v2. v1 \<in> NValues rexp1 b \<and> v2 \<in> NValues rexp2 (rest v1 b)}" in finite_surj)
prefer 2
apply(auto)[1]
apply(rule_tac B="\<Union>sp \<in> Suffixes b. {(v1, v2). v1 \<in> NValues rexp1 b \<and> v2 \<in> NValues rexp2 sp}" in finite_subset)
apply(auto)[1]
apply (metis rest_Suffixes)
apply(rule finite_UN_I)
apply(rule finite_Suffixes)
apply(simp)
apply(simp add: NValues_recs)
apply(clarify)
apply(subst NValues_recs)
apply(simp)
apply(rule_tac f="\<lambda>(v, vs). Stars (v # vs)" and 
               A="{(v, vs) | v vs. v \<in> NValues rexp b \<and> (flat v \<noteq> [] \<and> Stars vs \<in> NValues (STAR rexp) (rest v b))}" in finite_surj)
prefer 2
apply(auto)[1]
apply(auto)
apply(case_tac b)
apply(simp)
defer
apply(rule_tac B="\<Union>sp \<in> SSuffixes b. {(v, vs) | v vs. v \<in> NValues rexp b \<and> Stars vs \<in> NValues (STAR rexp) sp}" in finite_subset)
apply(auto)[1]
apply(rule_tac x="rest aa (a # list)" in bexI)
apply(simp)
apply (rule rest_SSuffixes)
apply(simp)
apply(simp)
apply(rule finite_UN_I)
defer
apply(frule_tac x="rexp" in spec)
apply(drule_tac x="b" in spec)
apply(drule conjunct1)
apply(drule mp)
apply(simp)
apply(drule_tac x="STAR rexp" in spec)
apply(drule_tac x="sp" in spec)
apply(drule conjunct2)
apply(drule mp)
apply(simp)
apply(simp add: prefix_def SPrefixes_def SSuffixes_def)
apply(auto)[1]
apply (metis length_Cons length_rev length_sprefix rev.simps(2))
apply(simp)
apply(rule finite_cartesian_product)
apply(simp)
apply(rule_tac f="Stars" in finite_imageD)
prefer 2
apply(auto simp add: inj_on_def)[1]
apply (metis finite_subset image_Collect_subsetI)
apply(simp add: rest_Nil)
apply(simp add: NValues_STAR_Nil)
apply(rule_tac B="{(v, vs). v \<in> NValues rexp [] \<and> vs = []}" in finite_subset)
apply(auto)[1]
apply(simp)
apply(rule_tac B="Suffixes b" in finite_subset)
apply(auto simp add: SSuffixes_def Suffixes_def Prefixes_def SPrefixes_def sprefix_def)[1]
by (metis finite_Suffixes)

lemma NValues_finite:
  "finite (NValues r s)"
using NValues_finite_aux
apply(simp)
done

section {* Sulzmann functions *}

fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(EMPTY) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(STAR r) = Stars []"

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
| "der c (STAR r) = SEQ (der c r) (STAR r)"

fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
apply(induct r) 
apply(simp_all add: nullable_correctness)
done

lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
apply(induct s arbitrary: r) 
apply(simp add: Ders_def)
apply(simp)
apply(subst der_correctness)
apply(simp add: Ders_def Der_def)
done

section {* Injection function *}

fun injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval (CHAR d) c Void = Char d"
| "injval (ALT r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (ALT r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (SEQ r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (STAR r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 

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
| "projval (STAR r) c (Stars (v # vs)) = Seq (projval r c v) (Stars vs)"



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
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(case_tac "c = c'")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(5))
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf.intros(2))
apply (metis Prf.intros(3))
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply (metis Prf.intros(1))
apply(auto)[1]
apply (metis Prf.intros(1) mkeps_nullable)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply(rule Prf.intros)
apply(auto)[2]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply (metis Prf.intros(6) Prf.intros(7))
by (metis Prf.intros(7))

lemma v3_proj:
  assumes "\<Turnstile> v : r" and "\<exists>s. (flat v) = c # s"
  shows "\<Turnstile> (projval r c v) : der c r"
using assms
apply(induct rule: NPrf.induct)
prefer 4
apply(simp)
prefer 4
apply(simp)
apply (metis NPrf.intros(4))
prefer 2
apply(simp)
apply (metis NPrf.intros(2))
prefer 2
apply(simp)
apply (metis NPrf.intros(3))
apply(auto)
apply(rule NPrf.intros)
apply(simp)
apply (metis NPrf_imp_Prf not_nullable_flat)
apply(rule NPrf.intros)
apply(rule NPrf.intros)
apply (metis Cons_eq_append_conv)
apply(simp)
apply(rule NPrf.intros)
apply (metis Cons_eq_append_conv)
apply(simp)
(* Stars case *)
apply(rule NPrf.intros)
apply (metis Cons_eq_append_conv)
apply(auto)
done

lemma v4:
  assumes "\<turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct arbitrary: v rule: der.induct)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(case_tac "c = c'")
apply(simp)
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(case_tac "nullable r1")
apply(simp)
apply(erule Prf.cases)
apply(simp_all (no_asm_use))[7]
apply(auto)[1]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(simp only: injval.simps flat.simps)
apply(auto)[1]
apply (metis mkeps_flat)
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(simp)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
done

lemma v4_proj:
  assumes "\<Turnstile> v : r" and "\<exists>s. (flat v) = c # s"
  shows "c # flat (projval r c v) = flat v"
using assms
apply(induct rule: NPrf.induct)
prefer 4
apply(simp)
prefer 4
apply(simp)
prefer 2
apply(simp)
prefer 2
apply(simp)
apply(auto)
apply (metis Cons_eq_append_conv)
apply(simp add: append_eq_Cons_conv)
apply(auto)
done

lemma v4_proj2:
  assumes "\<Turnstile> v : r" and "(flat v) = c # s"
  shows "flat (projval r c v) = s"
using assms
by (metis list.inject v4_proj)


definition 
  PC31 :: "string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC31 s r r' \<equiv> s \<notin> L r"

definition 
  PC41 :: "string \<Rightarrow> string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC41 s s' r r' \<equiv> (\<forall>x. (s @ x \<in> L r \<longrightarrow> s' \<in> {x} ;; L r' \<longrightarrow> x = []))"


lemma
 L1: "\<not>(nullable r1) \<longrightarrow> [] \<in> L r2 \<longrightarrow> PC31 [] r1 r2" and
 L2: "s1 \<in> L(r1) \<longrightarrow> [] \<in> L(r2) \<longrightarrow> PC41 s1 [] r1 r2" and
 L3: "s2 \<in> L(der c r2) \<longrightarrow> PC31 s2 (der c r1) (der c r2) \<longrightarrow> PC31 (c#s2) r1 r2" and
 L4: "s1 \<in> L(der c r1) \<longrightarrow> s2 \<in> L(r2) \<longrightarrow> PC41 s1 s2 (der c r1) r2 \<longrightarrow> PC41 (c#s1) s2 r1 r2" and
 L5: "nullable(r1) \<longrightarrow> s2 \<in> L(der c r2) \<longrightarrow> PC31 s2 (SEQ (der c r1) r2) (der c r2) \<longrightarrow> PC41 [] (c#s2) r1 r2" and
 L6: "s0 \<in> L(der c r0) \<longrightarrow>  s \<in> L(STAR r0) \<longrightarrow>  PC41 s0 s (der c r0) (STAR r0) \<longrightarrow> PC41 (c#s0) s r0 (STAR r0)" and
 L7: "s' \<in> L(r') \<longrightarrow> s' \<in> L(r) \<longrightarrow> \<not>PC31 s' r r'" and
 L8: "s \<in> L(r) \<longrightarrow> s' \<in> L(r') \<longrightarrow> s @ x \<in> L(r) \<longrightarrow> s' \<in> {x} ;; (L(r') ;; {y}) \<longrightarrow>  x \<noteq> [] \<longrightarrow> \<not>PC41 s s' r r'"
apply(auto simp add: PC31_def PC41_def)[1]
apply (metis nullable_correctness)
apply(auto simp add: PC31_def PC41_def)[1]
apply(simp add: Sequ_def)
apply(auto simp add: PC31_def PC41_def)[1]
apply(simp add: der_correctness Der_def)
apply(auto simp add: PC31_def PC41_def)[1]
apply(simp add: der_correctness Der_def Sequ_def)
apply(auto simp add: PC31_def PC41_def)[1]
apply(simp add: Sequ_def)
apply(simp add: der_correctness Der_def)
apply(auto)[1]
apply (metis append_eq_Cons_conv)
apply(auto simp add: PC31_def PC41_def)[1]
apply(simp add: Sequ_def)
apply(simp add: der_correctness Der_def)
apply(auto simp add: PC31_def PC41_def)[1]
apply(rule impI)+
apply(rule notI)
(* 8 fails *)
oops

definition 
  PC32 :: "string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC32 s r r' \<equiv> \<forall>y. s \<notin> (L r ;; {y})"

definition 
  PC42 :: "string \<Rightarrow> string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC42 s s' r r' \<equiv> (\<forall>x. (s @ x \<in> L r \<longrightarrow> (\<exists>y. s' \<in> {x} ;; (L r' ;; {y})) \<longrightarrow> x = []))"


lemma
 L1: "\<not>(nullable r1) \<longrightarrow> [] \<in> L r2 \<longrightarrow> PC32 [] r1 r2" and
 L2: "s1 \<in> L(r1) \<longrightarrow> [] \<in> L(r2) \<longrightarrow> PC42 s1 [] r1 r2" and
 L3: "s2 \<in> L(der c r2) \<longrightarrow> PC32 s2 (der c r1) (der c r2) \<longrightarrow> PC32 (c#s2) r1 r2" and
 L4: "s1 \<in> L(der c r1) \<longrightarrow> s2 \<in> L(r2) \<longrightarrow> PC42 s1 s2 (der c r1) r2 \<longrightarrow> PC42 (c#s1) s2 r1 r2" and
 L5: "nullable(r1) \<longrightarrow> s2 \<in> L(der c r2) \<longrightarrow> PC32 s2 (SEQ (der c r1) r2) (der c r2) \<longrightarrow> PC42 [] (c#s2) r1 r2" and
 L6: "s0 \<in> L(der c r0) \<longrightarrow>  s \<in> L(STAR r0) \<longrightarrow>  PC42 s0 s (der c r0) (STAR r0) \<longrightarrow> PC42 (c#s0) s r0 (STAR r0)" and
 L7: "s' \<in> L(r') \<longrightarrow> s' \<in> L(r) \<longrightarrow> \<not>PC32 s' r r'" and
 L8: "s \<in> L(r) \<longrightarrow> s' \<in> L(r') \<longrightarrow> s @ x \<in> L(r) \<longrightarrow> s' \<in> {x} ;; (L(r') ;; {y}) \<longrightarrow>  x \<noteq> [] \<longrightarrow> \<not>PC42 s s' r r'"
apply(auto simp add: PC32_def PC42_def)[1]
apply(simp add: Sequ_def)
apply (metis nullable_correctness)
apply(auto simp add: PC32_def PC42_def Sequ_def)[1]
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def)[1]
apply(simp add: Cons_eq_append_conv)
apply(auto)[1]
defer
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def)[1]
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def nullable_correctness)[1]
apply (metis append_Cons append_assoc hd_Cons_tl list.discI list.inject)
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def)[1]
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def)[1]
apply(auto simp add: PC32_def PC42_def Sequ_def der_correctness Der_def)[1]
oops

definition 
  PC33 :: "string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC33 s r r' \<equiv> s \<notin> L r"

definition 
  PC43 :: "string \<Rightarrow> string \<Rightarrow> rexp \<Rightarrow> rexp \<Rightarrow> bool"
where
  "PC43 s s' r r' \<equiv> (\<forall>x. (s @ x \<in> L r \<longrightarrow> (\<exists>y. s' \<in> {x} ;; (L r' ;; {y})) \<longrightarrow> x = []))"

lemma
 L1: "\<not>(nullable r1) \<longrightarrow> [] \<in> L r2 \<longrightarrow> PC33 [] r1 r2" and
 L2: "s1 \<in> L(r1) \<longrightarrow> [] \<in> L(r2) \<longrightarrow> PC43 s1 [] r1 r2" and
 L3: "s2 \<in> L(der c r2) \<longrightarrow> PC33 s2 (der c r1) (der c r2) \<longrightarrow> PC33 (c#s2) r1 r2" and
 L4: "s1 \<in> L(der c r1) \<longrightarrow> s2 \<in> L(r2) \<longrightarrow> PC43 s1 s2 (der c r1) r2 \<longrightarrow> PC43 (c#s1) s2 r1 r2" and
 L5: "nullable(r1) \<longrightarrow> s2 \<in> L(der c r2) \<longrightarrow> PC33 s2 (SEQ (der c r1) r2) (der c r2) \<longrightarrow> PC43 [] (c#s2) r1 r2" and
 L6: "s0 \<in> L(der c r0) \<longrightarrow>  s \<in> L(STAR r0) \<longrightarrow>  PC43 s0 s (der c r0) (STAR r0) \<longrightarrow> PC43 (c#s0) s r0 (STAR r0)" and
 L7: "s' \<in> L(r') \<longrightarrow> s' \<in> L(r) \<longrightarrow> \<not>PC33 s' r r'" and
 L8: "s \<in> L(r) \<longrightarrow> s' \<in> L(r') \<longrightarrow> s @ x \<in> L(r) \<longrightarrow> s' \<in> {x} ;; (L(r') ;; {y}) \<longrightarrow>  x \<noteq> [] \<longrightarrow> \<not>PC43 s s' r r'"
apply(auto simp add: PC33_def PC43_def)[1]
apply (metis nullable_correctness)
apply(auto simp add: PC33_def PC43_def)[1]
apply(simp add: Sequ_def)
apply(auto simp add: PC33_def PC43_def)[1]
apply(simp add: der_correctness Der_def)
apply(auto simp add: PC33_def PC43_def)[1]
apply(simp add: der_correctness Der_def Sequ_def)
apply metis
(* 5 *)
apply(auto simp add: PC33_def PC43_def)[1]
apply(simp add: Sequ_def)
apply(simp add: der_correctness Der_def)
apply(auto)[1]
defer
apply(auto simp add: PC33_def PC43_def)[1]
apply(simp add: Sequ_def)
apply(simp add: der_correctness Der_def)
apply metis
apply(auto simp add: PC33_def PC43_def)[1]
apply(auto simp add: PC33_def PC43_def)[1]
(* 5 fails *)
apply(simp add: Cons_eq_append_conv)
apply(auto)[1]
apply(drule_tac x="ys'" in spec)
apply(simp)
oops

section {* Roy's Definition *}

inductive 
  Roy :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<rhd> _ : _" [100, 100] 100)
where
  "\<rhd> Void : EMPTY"
| "\<rhd> Char c : CHAR c"
| "\<rhd> v : r1 \<Longrightarrow> \<rhd> Left v : ALT r1 r2"
| "\<lbrakk>\<rhd> v : r2; flat v \<notin> L r1\<rbrakk> \<Longrightarrow> \<rhd> Right v : ALT r1 r2"
| "\<lbrakk>\<rhd> v1 : r1; \<rhd> v2 : r2; \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = flat v2 \<and> (flat v1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)\<rbrakk> \<Longrightarrow>
      \<rhd> Seq v1 v2 : SEQ r1 r2"
| "\<lbrakk>\<rhd> v : r; \<rhd> Stars vs : STAR r; flat v \<noteq> []; 
   \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = flat (Stars vs) \<and> (flat v @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk> \<Longrightarrow>
      \<rhd> Stars (v#vs) : STAR r"
| "\<rhd> Stars [] : STAR r"

lemma drop_append:
  assumes "s1 \<sqsubseteq> s2"
  shows "s1 @ drop (length s1) s2 = s2"
using assms
apply(simp add: prefix_def)
apply(auto)
done

lemma royA: 
  assumes "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = flat v2 \<and> (flat v1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)"
  shows "\<forall>s. (s \<in> L(ders (flat v1) r1) \<and> 
              s \<sqsubseteq> (flat v2) \<and> drop (length s) (flat v2) \<in> L r2 \<longrightarrow> s = [])" 
using assms
apply -
apply(rule allI)
apply(rule impI)
apply(simp add: ders_correctness)
apply(simp add: Ders_def)
thm rest_def
apply(drule_tac x="s" in spec)
apply(simp)
apply(erule disjE)
apply(simp)
apply(drule_tac x="drop (length s) (flat v2)" in spec)
apply(simp add: drop_append)
done

lemma royB:
  assumes "\<forall>s. (s \<in> L(ders (flat v1) r1) \<and> 
              s \<sqsubseteq> (flat v2) \<and> drop (length s) (flat v2) \<in> L r2 \<longrightarrow> s = [])"
  shows "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = flat v2 \<and> (flat v1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" 
using assms
apply -
apply(auto simp add: prefix_def ders_correctness Ders_def)
by (metis append_eq_conv_conj)

lemma royC: 
  assumes "\<forall>s t. (s \<in> L(ders (flat v1) r1) \<and> 
                s \<sqsubseteq> (flat v2 @ t) \<and> drop (length s) (flat v2 @ t) \<in> L r2 \<longrightarrow> s = [])" 
  shows "\<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = flat v2 \<and> (flat v1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)"
using assms
apply -
apply(rule royB)
apply(rule allI)
apply(drule_tac x="s" in spec)
apply(drule_tac x="[]" in spec)
apply(simp)
done

inductive 
  Roy2 :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("2\<rhd> _ : _" [100, 100] 100)
where
  "2\<rhd> Void : EMPTY"
| "2\<rhd> Char c : CHAR c"
| "2\<rhd> v : r1 \<Longrightarrow> 2\<rhd> Left v : ALT r1 r2"
| "\<lbrakk>2\<rhd> v : r2; \<forall>t. flat v \<notin> (L r1 ;; {t})\<rbrakk> \<Longrightarrow> 2\<rhd> Right v : ALT r1 r2"
| "\<lbrakk>2\<rhd> v1 : r1; 2\<rhd> v2 : r2;
    \<forall>s. ((flat v1 @ s \<in> L r1) \<and> 
         (\<exists>t. s \<sqsubseteq> (flat v2 @ t) \<and> drop (length s) (flat v2) \<in> (L r2 ;; {t}))) \<longrightarrow> s = []\<rbrakk> \<Longrightarrow>
    2\<rhd> Seq v1 v2 : SEQ r1 r2"
| "\<lbrakk>2\<rhd> v : r; 2\<rhd> Stars vs : STAR r; flat v \<noteq> []; 
    \<forall>s. ((flat v @ s \<in> L r) \<and> 
       (\<exists>t. s \<sqsubseteq> (flat (Stars vs) @ t) \<and> drop (length s) (flat (Stars vs)) \<in> (L (STAR r) ;; {t}))) \<longrightarrow> s = []\<rbrakk>
    \<Longrightarrow> 2\<rhd> Stars (v#vs) : STAR r"
| "2\<rhd> Stars [] : STAR r"

lemma Roy2_props:
  assumes "2\<rhd> v : r"
  shows "\<turnstile> v : r"
using assms
apply(induct)
apply(auto intro: Prf.intros)
done

lemma Roy_mkeps_nullable:
  assumes "nullable(r)" 
  shows "2\<rhd> (mkeps r) : r"
using assms
apply(induct rule: nullable.induct)
apply(auto intro: Roy2.intros)
apply(rule Roy2.intros)
apply(simp_all)
apply(simp add: mkeps_flat)
apply(simp add: Sequ_def)
apply (metis nullable_correctness)
apply(rule Roy2.intros)
apply(simp_all)
apply(rule allI)
apply(rule impI)
apply(auto simp add: Sequ_def)
apply(simp add: mkeps_flat)
apply(auto simp add: prefix_def)
done

section {* Alternative Posix definition *}

inductive 
  PMatch :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  "[] \<in> EMPTY \<rightarrow> Void"
| "[c] \<in> (CHAR c) \<rightarrow> (Char c)"
| "s \<in> r1 \<rightarrow> v \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| "\<lbrakk>s \<in> r2 \<rightarrow> v; s \<notin> L(r1)\<rbrakk> \<Longrightarrow> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r1 \<and> s\<^sub>4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"
| "\<lbrakk>s1 \<in> r \<rightarrow> v; s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> (s1 @ s2) \<in> STAR r \<rightarrow> Stars (v # vs)"
| "[] \<in> STAR r \<rightarrow> Stars []"

inductive 
  PMatchX :: "string \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("\<turnstile> _ \<in> _ \<rightarrow> _" [100, 100, 100] 100)
where
  "\<turnstile> s \<in> EMPTY \<rightarrow> Void"
| "\<turnstile> (c # s) \<in> (CHAR c) \<rightarrow> (Char c)"
| "\<turnstile> s \<in> r1 \<rightarrow> v \<Longrightarrow> \<turnstile> s \<in> (ALT r1 r2) \<rightarrow> (Left v)"
| "\<lbrakk>\<turnstile> s \<in> r2 \<rightarrow> v; \<not>(\<exists>s'. s' \<sqsubseteq> s \<and> flat v \<sqsubseteq> s' \<and> s' \<in> L(r1))\<rbrakk> \<Longrightarrow> \<turnstile> s \<in> (ALT r1 r2) \<rightarrow> (Right v)"
| "\<lbrakk>s1 \<in> r1 \<rightarrow> v1; \<turnstile> s2 \<in> r2 \<rightarrow> v2;
    \<not>(\<exists>s3 s4. s3 \<noteq> [] \<and> (s3 @ s4) \<sqsubseteq> s2 \<and> (s1 @ s3) \<in> L r1 \<and> s4 \<in> L r2)\<rbrakk> \<Longrightarrow> 
    \<turnstile> (s1 @ s2) \<in> (SEQ r1 r2) \<rightarrow> (Seq v1 v2)"
| "\<lbrakk>s1 \<in> r \<rightarrow> v; \<turnstile> s2 \<in> STAR r \<rightarrow> Stars vs; flat v \<noteq> [];
    \<not>(\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> (s\<^sub>3 @ s\<^sub>4) \<sqsubseteq> s2 \<and> (s1 @ s\<^sub>3) \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))\<rbrakk>
    \<Longrightarrow> \<turnstile> (s1 @ s2) \<in> STAR r \<rightarrow> Stars (v # vs)"
| "\<turnstile> s \<in> STAR r \<rightarrow> Stars []"

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
apply (metis Prf.intros(7))
by (metis Prf.intros(6))


lemma PMatchX1:
  assumes "\<turnstile> s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
using assms
apply(induct s r v rule: PMatchX.induct)
apply(auto simp add: prefix_def intro: Prf.intros)
apply (metis PMatch1(1) Prf.intros(1))
by (metis PMatch1(1) Prf.intros(7))


lemma PMatchX:
  assumes "\<turnstile> s \<in> r \<rightarrow> v"
  shows "flat v \<sqsubseteq> s"
using assms
apply(induct s r v rule: PMatchX.induct)
apply(auto simp add: prefix_def PMatch1)
done

lemma PMatchX_PMatch:
  assumes "\<turnstile> s \<in> r \<rightarrow> v" "flat v = s"
  shows "s \<in> r \<rightarrow> v"
using assms
apply(induct s r v rule: PMatchX.induct)
apply(auto intro: PMatch.intros)
apply(rule PMatch.intros)
apply(simp)
apply (metis PMatchX Prefixes_def mem_Collect_eq)
apply (smt2 PMatch.intros(5) PMatch1(2) PMatchX append_Nil2 append_assoc append_self_conv prefix_def)
by (metis L.simps(6) PMatch.intros(6) PMatch1(2) append_Nil2 append_eq_conv_conj prefix_def)

lemma PMatch_PMatchX:
  assumes "s \<in> r \<rightarrow> v" 
  shows "\<turnstile> s \<in> r \<rightarrow> v"
using assms
apply(induct s r v arbitrary: s' rule: PMatch.induct)
apply(auto intro: PMatchX.intros)
apply(rule PMatchX.intros)
apply(simp)
apply(rule notI)
apply(auto)[1]
apply (metis PMatch1(2) append_eq_conv_conj length_sprefix less_imp_le_nat prefix_def sprefix_def take_all)
apply(rule PMatchX.intros)
apply(simp)
apply(simp)
apply(auto)[1]
oops

lemma 
  assumes "\<rhd> v : r"
  shows "(flat v) \<in> r \<rightarrow> v"
using assms
apply(induct)
apply(auto intro: PMatch.intros)
apply(rule PMatch.intros)
apply(simp)
apply(simp)
apply(simp)
apply(auto)[1]
done

lemma 
  assumes "s \<in> r \<rightarrow> v"
  shows "\<rhd> v : r"
using assms
apply(induct)
apply(auto intro: Roy.intros)
apply (metis PMatch1(2) Roy.intros(4))
apply (metis PMatch1(2) Roy.intros(5))
by (metis L.simps(6) PMatch1(2) Roy.intros(6))


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
apply (metis nullable_correctness)
apply(metis PMatch.intros(7))
done


lemma PMatch1N:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<Turnstile> v : r" 
using assms
apply(induct s r v rule: PMatch.induct)
apply(auto)
apply (metis NPrf.intros(4))
apply (metis NPrf.intros(5))
apply (metis NPrf.intros(2))
apply (metis NPrf.intros(3))
apply (metis NPrf.intros(1))
apply(rule NPrf.intros)
apply(simp)
apply(simp)
apply(simp)
apply(rule NPrf.intros)
done

lemma PMatch_determ:
  shows "\<lbrakk>s \<in> r \<rightarrow> v1; s \<in> r \<rightarrow> v2\<rbrakk> \<Longrightarrow> v1 = v2"
  and   "\<lbrakk>s \<in> (STAR r) \<rightarrow> Stars vs1; s \<in> (STAR r) \<rightarrow> Stars vs2\<rbrakk> \<Longrightarrow> vs1 = vs2"
apply(induct v1 and vs1 arbitrary: s r v2 and s r vs2 rule: val.inducts)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(subgoal_tac "s1 = s1a \<and> s2 = s2a")
apply metis
apply(rule conjI)
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply (metis PMatch1(1) PMatch1(2) Prf_flat_L)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply (metis NPrf_flat_L PMatch1(2) PMatch1N)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply (metis NPrf_flat_L PMatch1(2) PMatch1N)
(* star case *)
defer
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply (metis PMatch1(2))
apply(rotate_tac  3)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(subgoal_tac "s1 = s1a \<and> s2 = s2a")
apply metis
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply (metis L.simps(6) PMatch1(1) PMatch1(2) Prf_flat_L)
apply (metis L.simps(6) PMatch1(1) PMatch1(2) Prf_flat_L)
apply (metis L.simps(6) PMatch1(1) PMatch1(2) Prf_flat_L)
apply (metis L.simps(6) PMatch1(1) PMatch1(2) Prf_flat_L)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply (metis PMatch1(2))
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(subgoal_tac "s1 = s1a \<and> s2 = s2a")
apply(drule_tac x="s1 @ s2" in meta_spec)
apply(drule_tac x="rb" in meta_spec)
apply(drule_tac x="(va#vsa)" in meta_spec)
apply(simp)
apply(drule meta_mp)
apply (metis L.simps(6) PMatch.intros(6))
apply (metis L.simps(6) PMatch.intros(6))
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply (metis L.simps(6) NPrf_flat_L PMatch1(2) PMatch1N)
apply (metis L.simps(6) NPrf_flat_L PMatch1(2) PMatch1N)
apply (metis L.simps(6) NPrf_flat_L PMatch1(2) PMatch1N)
apply (metis L.simps(6) NPrf_flat_L PMatch1(2) PMatch1N)
apply (metis PMatch1(2))
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
by (metis PMatch1(2))


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
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(case_tac "c = c'")
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis PMatch.intros(2))
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis PMatch.intros(3))
apply(clarify)
apply(rule PMatch.intros)
apply metis
apply(simp add: L_flat_NPrf)
apply(auto)[1]
apply(frule_tac c="c" in v3_proj)
apply metis
apply(drule_tac x="projval r1 c v" in spec)
apply(drule mp)
apply (metis v4_proj2)
apply (metis NPrf_imp_Prf)
(* SEQ case *)
apply(case_tac "nullable r1")
apply(simp)
prefer 2
apply(simp)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(subst append.simps(2)[symmetric])
apply(rule PMatch.intros)
apply metis
apply metis
apply(auto)[1]
apply(simp add: der_correctness Der_def)
apply(auto)[1]
(* nullable case *)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[4]
apply(clarify)
apply(simp (no_asm))
apply(subst append.simps(2)[symmetric])
apply(rule PMatch.intros)
apply metis
apply metis
apply(erule contrapos_nn)
apply(erule exE)+
apply(auto)[1]
apply(simp add: L_flat_NPrf)
apply(auto)[1]
thm v3_proj
apply(frule_tac c="c" in v3_proj)
apply metis
apply(rule_tac x="s\<^sub>3" in exI)
apply(simp)
apply (metis NPrf_imp_Prf v4_proj2)
apply(simp)
(* interesting case *)
apply(clarify)
apply(clarify)
apply(simp)
apply(subst (asm) L.simps(4)[symmetric])
apply(simp only: L_flat_Prf)
apply(simp)
apply(subst append.simps(1)[symmetric])
apply(rule PMatch.intros)
apply (metis PMatch_mkeps)
apply metis
apply(auto)
apply(simp only: L_flat_NPrf)
apply(simp)
apply(auto)
apply(drule_tac x="Seq (projval r1 c v) vb" in spec)
apply(drule mp)
apply(simp)

apply (metis append_Cons butlast_snoc list.sel(1) neq_Nil_conv rotate1.simps(2) v4_proj2)
apply(subgoal_tac "\<turnstile> projval r1 c v : der c r1")
apply (metis NPrf_imp_Prf Prf.intros(1))
apply(rule NPrf_imp_Prf)
apply(rule v3_proj)
apply(simp)
apply (metis Cons_eq_append_conv)
(* Stars case *)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(rotate_tac 2)
apply(frule_tac PMatch1)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(subst append.simps(2)[symmetric])
apply(rule PMatch.intros)
apply metis
apply(auto)[1]
apply(rule PMatch.intros)
apply(simp)
apply(simp)
apply(simp)
apply (metis L.simps(6))
apply(subst v4)
apply (metis NPrf_imp_Prf PMatch1N)
apply(simp)
apply(auto)[1]
apply(drule_tac x="s\<^sub>3" in spec)
apply(drule mp)
defer
apply metis
apply(clarify)
apply(drule_tac x="s1" in meta_spec)
apply(drule_tac x="v1" in meta_spec)
apply(simp)
apply(rotate_tac 2)
apply(drule PMatch.intros(6))
apply(rule PMatch.intros(7))
apply (metis PMatch1(1) list.distinct(1) v4)
apply (metis Nil_is_append_conv)
apply(simp)
apply(subst der_correctness)
apply(simp add: Der_def)
done



lemma Sequ_single:
  "(A ;; {t}) = {s @ t | s . s \<in> A}"
apply(simp add: Sequ_def)
done

lemma Sequ_not:
  assumes "\<forall>t. s \<notin> (L(der c r1) ;; {t})" "L r1 \<noteq> {}" 
  shows "\<forall>t. c # s \<notin> (L r1 ;; {t})"
using assms
apply(simp add: der_correctness)
apply(simp add: Der_def)
apply(simp add: Sequ_def)
apply(rule allI)+
apply(rule impI)
apply(simp add: Cons_eq_append_conv)
apply(auto)

oops

lemma PMatch_Roy2:
  assumes "2\<rhd> v : (der c r)" "\<exists>s. c # s \<in> L r"
  shows "2\<rhd> (injval r c v) : r"
using assms
apply(induct c r arbitrary: v rule: der.induct)
apply(auto)
apply(erule Roy2.cases)
apply(simp_all)
apply (metis Roy2.intros(2))
(* alt case *)
apply(erule Roy2.cases)
apply(simp_all)
apply(clarify)
apply (metis Roy2.intros(3))
apply(clarify)
apply(rule Roy2.intros(4))
apply (metis (full_types) Prf_flat_L Roy2_props v3 v4)
apply(subgoal_tac "\<forall>t. c # flat va \<notin> L r1 ;; {t}")
prefer 2
apply(simp add: der_correctness)
apply(simp add: Der_def)
apply(simp add: Sequ_def)
apply(rule allI)+
apply(rule impI)
apply(simp add: Cons_eq_append_conv)
apply(erule disjE)
apply(erule conjE)
prefer 2
apply metis
apply(simp)
apply(drule_tac x="[]" in spec)
apply(drule_tac x="drop 1 t" in spec)
apply(clarify)
apply(simp)
oops 

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
apply(simp add: L_flat_NPrf)
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
apply(simp add: L_flat_NPrf)
apply(auto)
apply (metis v3_proj v4_proj2)
apply(rule PMatch2)
apply(simp)
done

lemma lex_correct4:
  assumes "s \<in> L r"
  shows "\<exists>v. lex r s = Some(v) \<and> \<Turnstile> v : r \<and> flat v = s"
using lex_correct3[OF assms]
apply(auto)
apply (metis PMatch1N)
by (metis PMatch1(2))


lemma lex_correct5:
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
apply(simp add: L_flat_NPrf)
apply(auto)
apply (metis v3_proj v4_proj2)
done

lemma 
  "lex2 (ALT (CHAR a) (ALT (CHAR b) (SEQ (CHAR a) (CHAR b)))) [a,b] = Right (Right (Seq (Char a) (Char b)))"
apply(simp)
done


(* NOT DONE YET *)

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
| "flat (Stars (v # vs)) = [] \<Longrightarrow> (Stars []) \<succ>(STAR r) (Stars (v # vs))"
| "flat (Stars (v # vs)) \<noteq> [] \<Longrightarrow> (Stars (v # vs)) \<succ>(STAR r) (Stars [])"
| "\<lbrakk>v1 \<succ>r v2; v1 \<noteq> v2\<rbrakk> \<Longrightarrow> (Stars (v1 # vs1)) \<succ>(STAR r) (Stars (v2 # vs2))"
| "(Stars vs1) \<succ>(STAR r) (Stars vs2) \<Longrightarrow> (Stars (v # vs1)) \<succ>(STAR r) (Stars (v # vs2))"
| "(Stars []) \<succ>(STAR r) (Stars [])"

lemma PMatch_ValOrd:
  assumes "s \<in> r \<rightarrow> v" "v' \<in> SValues r s"
  shows "v \<succ>r v'"
using assms
apply(induct r arbitrary: v v' s rule: rexp.induct)
apply(simp add: SValues_recs)
apply(simp add: SValues_recs)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(simp add: SValues_recs)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8) empty_iff singletonD)
apply(simp add: SValues_recs)
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply(clarify)
apply(case_tac "v1a = v1")
apply(simp)
apply(rule ValOrd.intros)
apply(rotate_tac 1)
apply(drule_tac x="v2a" in meta_spec)
apply(rotate_tac 8)
apply(drule_tac x="v2" in meta_spec)
apply(drule_tac x="s2a" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: SValues_def)
apply (metis PMatch1(2) same_append_eq)
apply(simp)
apply(rule ValOrd.intros)
apply(drule_tac x="v1a" in meta_spec)
apply(rotate_tac 8)
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac x="s1a" in meta_spec)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply(case_tac "us=[]")
apply(simp)
apply(drule_tac x="us" in spec)
apply(drule mp)
apply(simp add: SValues_def)
apply (metis Prf_flat_L)
apply(erule disjE)
apply(simp)
apply(simp)
apply(simp add: SValues_def)
apply (metis Prf_flat_L)

apply(subst (asm) (2) Values_def)
apply(simp)
apply(clarify)
apply(simp add: rest_def)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply(case_tac "us = []")
apply(simp)
apply(simp add: Values_def)
apply (metis append_Nil2 prefix_def)
apply(drule_tac x="us" in spec)
apply(simp)
apply(drule_tac mp)


oops
(*HERE *)

inductive ValOrd2 :: "val \<Rightarrow> string \<Rightarrow> val \<Rightarrow> bool" ("_ 2\<succ>_ _" [100, 100, 100] 100)
where 
  "v2 2\<succ>s v2' \<Longrightarrow> (Seq v1 v2) 2\<succ>(flat v1 @ s) (Seq v1 v2')" 
| "\<lbrakk>v1 2\<succ>s v1'; v1 \<noteq> v1'\<rbrakk> \<Longrightarrow> (Seq v1 v2) 2\<succ>s (Seq v1' v2')" 
| "(flat v2) \<sqsubseteq> (flat v1) \<Longrightarrow> (Left v1) 2\<succ>(flat v1) (Right v2)"
| "(flat v1) \<sqsubset> (flat v2) \<Longrightarrow> (Right v2) 2\<succ>(flat v2) (Left v1)"
| "v2 2\<succ>s v2' \<Longrightarrow> (Right v2) 2\<succ>s (Right v2')"
| "v1 2\<succ>s v1' \<Longrightarrow> (Left v1) 2\<succ>s (Left v1')" 
| "Void 2\<succ>[] Void"
| "(Char c) 2\<succ>[c] (Char c)" 
| "flat (Stars (v # vs)) = [] \<Longrightarrow> (Stars []) 2\<succ>[] (Stars (v # vs))"
| "flat (Stars (v # vs)) \<noteq> [] \<Longrightarrow> (Stars (v # vs)) 2\<succ>(flat (Stars (v # vs))) (Stars [])"
| "\<lbrakk>v1 2\<succ>s v2; v1 \<noteq> v2\<rbrakk> \<Longrightarrow> (Stars (v1 # vs1)) 2\<succ>s (Stars (v2 # vs2))"
| "(Stars vs1) 2\<succ>s (Stars vs2) \<Longrightarrow> (Stars (v # vs1)) 2\<succ>(flat v @ s) (Stars (v # vs2))"
| "(Stars []) 2\<succ>[] (Stars [])"

lemma ValOrd2_string1:
  assumes "v1 2\<succ>s v2"
  shows "s \<sqsubseteq> flat v1"
using assms
apply(induct)
apply(auto simp add: prefix_def)
apply (metis append_assoc)
by (metis append_assoc)


lemma admissibility:
  assumes "s \<in> r \<rightarrow> v" "\<turnstile> v' : r" 
  shows "(\<forall>s'. (s' \<in> L(r) \<and> s' \<sqsubseteq> s) \<longrightarrow> v 2\<succ>s' v')"
using assms
apply(induct arbitrary: v')
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd2.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd2.intros(8) append_Nil2 prefix_Cons prefix_append prefix_def)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)[1]
apply (metis ValOrd2.intros(6))
apply(rule ValOrd2.intros)
apply(drule_tac x="v1" in meta_spec)
apply(simp)

apply(clarify)
apply (metis PMatch1(2) ValOrd2.intros(3))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)

apply(case_tac "v1 = v1a")
apply(simp)
apply(rotate_tac 3)
apply(drule_tac x="v2a" in meta_spec)
apply(drule meta_mp)
apply(simp)
apply(auto)
apply(rule_tac x="flat v1a @ s'" in exI)
apply (metis PMatch1(2) ValOrd2.intros(1) prefix_append)
apply (metis PMatch1(2) ValOrd2.intros(2) ValOrd2_string1 flat.simps(5))
prefer 4
apply(erule Prf.cases)
apply(simp_all)[7]
prefer 2
apply (metis ValOrd2.intros(5))


apply (metis ValOrd.intros(6))
oops


lemma admissibility:
  assumes "\<turnstile> s \<in> r \<rightarrow> v" "\<turnstile> v' : r" 
  shows "v \<succ>r v'"
using assms
apply(induct arbitrary: v')
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(6))
oops

lemma admissibility:
  assumes "2\<rhd> v : r" "\<turnstile> v' : r" "flat v' \<sqsubseteq> flat v"
  shows "v \<succ>r v'"
using assms
apply(induct arbitrary: v')
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(6))
apply (metis ValOrd.intros(3) length_sprefix less_imp_le_nat order_refl sprefix_def)
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis Prf_flat_L ValOrd.intros(4) length_sprefix seq_empty(1) sprefix_def)
apply (metis ValOrd.intros(5))
oops


lemma admisibility:
  assumes "\<rhd> v : r" "\<turnstile> v' : r"
  shows "v \<succ>r v'"
using assms
apply(induct arbitrary: v')
prefer 5
apply(drule royA)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(case_tac "v1 = v1a")
apply(simp)
apply(rule ValOrd.intros)
apply metis
apply (metis ValOrd.intros(2))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(6))
apply(rule ValOrd.intros)
defer
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(rule ValOrd.intros)
(* seq case goes through *)
oops


lemma admisibility:
  assumes "\<rhd> v : r" "\<turnstile> v' : r" "flat v' \<sqsubseteq> flat v"
  shows "v \<succ>r v'"
using assms
apply(induct arbitrary: v')
prefer 5
apply(drule royA)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply(case_tac "v1 = v1a")
apply(simp)
apply(rule ValOrd.intros)
apply(subst (asm) (3) prefix_def)
apply(erule exE)
apply(simp)
apply (metis prefix_def)
(* the unequal case *)
apply(subgoal_tac "flat v1 \<sqsubset> flat v1a \<or> flat v1a \<sqsubseteq> flat v1")
prefer 2
apply(simp add: prefix_def sprefix_def)
apply (metis append_eq_append_conv2)
apply(erule disjE)
(* first case  flat v1 \<sqsubset> flat v1a *)
apply(subst (asm) sprefix_def)
apply(subst (asm) (5) prefix_def)
apply(clarify)
apply(subgoal_tac "(s3 @ flat v2a) \<sqsubseteq> flat v2")
prefer 2
apply(simp)
apply (metis append_assoc prefix_append)
apply(subgoal_tac "s3 \<noteq> []")
prefer 2
apply (metis append_Nil2)
(* HERE *)
apply(subst (asm) (5) prefix_def)
apply(erule exE)
apply(simp add: ders_correctness Ders_def)
apply(simp add: prefix_def)
apply(clarify)
apply(subst (asm) append_eq_append_conv2)
apply(erule exE)
apply(erule disjE)
apply(clarify)
oops



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
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
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
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(clarify)
apply (metis ValOrd.intros(6))
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply (metis le_eq_less_or_eq neq_iff)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply (metis le_eq_less_or_eq neq_iff)
apply(rule ValOrd.intros)
apply(erule contrapos_np)
apply(rule ValOrd.intros)
apply(metis)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply (metis ValOrd.intros(13))
apply (metis ValOrd.intros(10) ValOrd.intros(9))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply (metis ValOrd.intros(10) ValOrd.intros(9))
apply(case_tac "v = va")
prefer 2
apply (metis ValOrd.intros(11))
apply(simp)
apply(rule ValOrd.intros(12))
apply(erule contrapos_np)
apply(rule ValOrd.intros(12))
oops

lemma Roy_posix:
  assumes "\<rhd> v : r" "\<turnstile> v' : r" "flat v' \<sqsubseteq> flat v"
  shows "v \<succ>r v'"
using assms
apply(induct r arbitrary: v v' rule: rexp.induct)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Roy.cases)
apply(simp_all)
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Roy.cases)
apply(simp_all)
apply (metis ValOrd.intros(8))
prefer 2
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Roy.cases)
apply(simp_all)
apply(clarify)
apply (metis ValOrd.intros(6))
apply(clarify)
apply (metis Prf_flat_L ValOrd.intros(4) length_sprefix sprefix_def)
apply(erule Roy.cases)
apply(simp_all)
apply (metis ValOrd.intros(3) length_sprefix less_imp_le_nat order_refl sprefix_def)
apply(clarify)
apply (metis ValOrd.intros(5))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Roy.cases)
apply(simp_all)
apply(clarify)
apply(case_tac "v1a = v1")
apply(simp)
apply(rule ValOrd.intros)
apply (metis prefix_append)
apply(rule ValOrd.intros)
prefer 2
apply(simp)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto)[1]
apply(drule_tac x="v1a" in meta_spec)
apply(rotate_tac 9)
apply(drule_tac x="v1" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac x="us" in spec)
apply(drule_tac mp)
apply (metis Prf_flat_L)
apply(auto)[1]
oops


lemma ValOrd_anti:
  shows "\<lbrakk>\<turnstile> v1 : r; \<turnstile> v2 : r; v1 \<succ>r v2; v2 \<succ>r v1\<rbrakk> \<Longrightarrow> v1 = v2"
  and   "\<lbrakk>\<turnstile> Stars vs1 : r; \<turnstile> Stars vs2 : r; Stars vs1 \<succ>r Stars vs2; Stars vs2 \<succ>r Stars vs1\<rbrakk>  \<Longrightarrow> vs1 = vs2"
apply(induct v1 and vs1 arbitrary: r v2 and r vs2 rule: val.inducts)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(erule ValOrd.cases)
apply(simp_all)
apply(auto)[1]
prefer 2
oops


(*

lemma ValOrd_PMatch:
  assumes "s \<in> r \<rightarrow> v1" "\<turnstile> v2 : r" "flat v2  \<sqsubseteq> s"
  shows "v1 \<succ>r v2"
using assms
apply(induct r arbitrary: s v1 v2 rule: rexp.induct)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(7))
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(8))
defer
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis ValOrd.intros(6))
apply (metis PMatch1(2) Prf_flat_L ValOrd.intros(4) length_sprefix sprefix_def)
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)[7]
apply (metis PMatch1(2) ValOrd.intros(3) length_sprefix less_imp_le_nat order_refl sprefix_def)
apply(clarify)
apply (metis ValOrd.intros(5))
(* Stars case *)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(erule PMatch.cases)
apply(simp_all)
apply (metis Nil_is_append_conv ValOrd.intros(10) flat.simps(7))
apply (metis ValOrd.intros(13))
apply(clarify)
apply(erule PMatch.cases)
apply(simp_all)
prefer 2
apply(rule ValOrd.intros)
apply(simp add: prefix_def)
apply(rule ValOrd.intros)
apply(drule_tac x="s1" in meta_spec)
apply(drule_tac x="va" in meta_spec)
apply(drule_tac x="v" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp add: prefix_def)
apply(auto)[1]
prefer 3
(* Seq case *)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(erule PMatch.cases)
apply(simp_all)[5]
apply(auto)
apply(case_tac "v1b = v1a")
apply(auto)
apply(simp add: prefix_def)
apply(auto)[1]
apply (metis PMatch1(2) ValOrd.intros(1) same_append_eq)
apply(simp add: prefix_def)
apply(auto)[1]
apply(simp add: append_eq_append_conv2)
apply(auto)
prefer 2
apply (metis ValOrd.intros(2))
prefer 2
apply (metis ValOrd.intros(2))
apply(case_tac "us = []")
apply(simp)
apply (metis ValOrd.intros(2) append_Nil2)
apply(drule_tac x="us" in spec)
apply(simp)
apply(drule_tac mp)
apply (metis Prf_flat_L)
apply(drule_tac x="s1 @ us" in meta_spec)
apply(drule_tac x="v1b" in meta_spec)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)

apply(simp)
apply(drule_tac meta_mp)
apply(simp)
apply(simp)
apply(simp)
apply(clarify)
apply (metis ValOrd.intros(6))
apply(clarify)
apply (metis PMatch1(2) ValOrd.intros(3) length_sprefix less_imp_le_nat order_refl sprefix_def)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis PMatch1(2) Prf_flat_L ValOrd.intros(4) length_sprefix sprefix_def)
apply (metis ValOrd.intros(5))
(* Seq case *)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(case_tac "v1 = v1a")
apply(auto)
apply(simp add: prefix_def)
apply(auto)[1]
apply (metis PMatch1(2) ValOrd.intros(1) same_append_eq)
apply(simp add: prefix_def)
apply(auto)[1]
apply(frule PMatch1)
apply(frule PMatch1(2)[symmetric])
apply(clarify)
apply(simp add: append_eq_append_conv2)
apply(auto)
prefer 2
apply (metis ValOrd.intros(2))
prefer 2
apply (metis ValOrd.intros(2))
apply(case_tac "us = []")
apply(simp)
apply (metis ValOrd.intros(2) append_Nil2)
apply(drule_tac x="us" in spec)
apply(simp)
apply(drule mp)
apply (metis  Prf_flat_L)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp)

lemma ValOrd_PMatch:
  assumes "s \<in> r \<rightarrow> v1" "\<turnstile> v2 : r" "flat v2  \<sqsubseteq> s"
  shows "v1 \<succ>r v2"
using assms
apply(induct arbitrary: v2 rule: .induct)
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
apply (metis PMatch1(2) ValOrd.intros(3) length_sprefix less_imp_le_nat order_refl sprefix_def)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(clarify)
apply (metis PMatch1(2) Prf_flat_L ValOrd.intros(4) length_sprefix sprefix_def)
apply (metis ValOrd.intros(5))
(* Seq case *)
apply(erule Prf.cases)
apply(simp_all)[5]
apply(auto)
apply(case_tac "v1 = v1a")
apply(auto)
apply(simp add: prefix_def)
apply(auto)[1]
apply (metis PMatch1(2) ValOrd.intros(1) same_append_eq)
apply(simp add: prefix_def)
apply(auto)[1]
apply(frule PMatch1)
apply(frule PMatch1(2)[symmetric])
apply(clarify)
apply(simp add: append_eq_append_conv2)
apply(auto)
prefer 2
apply (metis ValOrd.intros(2))
prefer 2
apply (metis ValOrd.intros(2))
apply(case_tac "us = []")
apply(simp)
apply (metis ValOrd.intros(2) append_Nil2)
apply(drule_tac x="us" in spec)
apply(simp)
apply(drule mp)
apply (metis  Prf_flat_L)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
apply(simp)

apply (metis PMatch1(2) ValOrd.intros(1) same_append_eq)
apply(rule ValOrd.intros(2))
apply(auto)
apply(drule_tac x="v1a" in meta_spec)
apply(drule_tac meta_mp)
apply(simp)
apply(drule_tac meta_mp)
prefer 2
apply(simp)
thm append_eq_append_conv
apply(simp add: append_eq_append_conv2)
apply(auto)
apply (metis Prf_flat_L)
apply(case_tac "us = []")
apply(simp)
apply(drule_tac x="us" in spec)
apply(drule mp)


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

thm PMatch.intros[no_vars]

lemma POSIX_PMatch:
  assumes "s \<in> r \<rightarrow> v" "\<turnstile> v' : r"
  shows "length (flat v') \<le> length (flat v)" 
using assms
apply(induct arbitrary: s v v' rule: rexp.induct)
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
*)


end