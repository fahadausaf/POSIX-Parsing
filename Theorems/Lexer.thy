   
theory Lexer
  imports Main
begin


section {* Sequential Composition of Languages *}

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

lemma star_cases:
  shows "A\<star> = {[]} \<union> A ;; A\<star>"
unfolding Sequ_def
by (auto) (metis Star.simps)

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
  ZERO
| ONE
| CHAR char
| SEQ rexp rexp
| ALT rexp rexp
| STAR rexp

fun ALTS :: "rexp list \<Rightarrow> rexp"
where 
  "ALTS [] = ZERO"
| "ALTS [r] = r"
| "ALTS (r # rs) = ALT r (ALTS rs)"

fun SEQS :: "rexp list \<Rightarrow> rexp"
where 
  "SEQS [] = ONE"
| "SEQS [r] = r"
| "SEQS (r # rs) = SEQ r (SEQS rs)"

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

lemma L_ALTS:
  "L (ALTS rs) = (\<Union>r \<in> set rs. L(r))"
by(induct rs rule: ALTS.induct)(simp_all)

lemma L_SEQS:
  "L (SEQS []) = {[]}"
  "L (SEQS (r # rs)) = (L r) ;; (L (SEQS rs))"
apply(simp)
apply(case_tac rs)
apply(simp)
apply(simp)
done


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

fun 
 ders :: "string \<Rightarrow> rexp \<Rightarrow> rexp"
where
  "ders [] r = r"
| "ders (c # s) r = ders s (der c r)"


lemma nullable_correctness:
  shows "nullable r  \<longleftrightarrow> [] \<in> (L r)"
by (induct r) (auto simp add: Sequ_def) 

lemma der_correctness:
  shows "L (der c r) = Der c (L r)"
by (induct r) (simp_all add: nullable_correctness)

lemma ders_correctness:
  shows "L (ders s r) = Ders s (L r)"
apply(induct s arbitrary: r)
apply(simp_all add: Ders_def der_correctness Der_def)
done

lemma ders_ZERO:
  shows "ders s (ZERO) = ZERO"
apply(induct s)
apply(simp_all)
done

lemma ders_ONE:
  shows "ders s (ONE) = (if s = [] then ONE else ZERO)"
apply(induct s)
apply(simp_all add: ders_ZERO)
done

lemma ders_CHAR:
  shows "ders s (CHAR c) = (if s = [c] then ONE else 
                           (if s = [] then (CHAR c) else ZERO))"
apply(induct s)
apply(simp_all add: ders_ZERO ders_ONE)
done

lemma  ders_ALT:
  shows "ders s (ALT r1 r2) = ALT (ders s r1) (ders s r2)"
apply(induct s arbitrary: r1 r2)
apply(simp_all)
done



definition
  delta :: "rexp \<Rightarrow> rexp"
where
  "delta r \<equiv> (if nullable r then ONE else ZERO)"

lemma delta_simp:
  shows "nullable r1 \<Longrightarrow> L (SEQ (delta r1) r2) = L r2"
  and   "\<not>nullable r1 \<Longrightarrow> L (SEQ (delta r1) r2) = {}"
unfolding delta_def
by simp_all

fun str_split :: "string \<Rightarrow> string \<Rightarrow> (string * string) list"
where
  "str_split s1 [] = []"
| "str_split s1 [c] = [(s1, [c])]"
| "str_split s1 (c#s2) = (s1, c#s2) # str_split (s1 @ [c]) s2"

fun ssplit :: "string \<Rightarrow> (string * string) list"
where
  "ssplit s = rev (str_split [] s)"  

fun tsplit :: "string \<Rightarrow> (string * string) list"
where
  "tsplit s = tl (str_split [] s)" 


value "ssplit([])"
value "ssplit([a1])"
value "ssplit([a1, a2])"
value "ssplit([a1, a2, a3])"
value "ssplit([a1, a2, a3, a4])"

value "tsplit([])"
value "tsplit([a1])"
value "tsplit([a1, a2])"
value "tsplit([a1, a2, a3])"
value "tsplit([a1, a2, a3, a4])"

function
  D :: "string \<Rightarrow> rexp \<Rightarrow> rexp" 
where
  "D s (ZERO) = ZERO"
| "D s (ONE) = (if s = [] then ONE else ZERO)"
| "D s (CHAR c) = (if s = [c] then ONE else 
                  (if s = [] then (CHAR c) else ZERO))"
| "D s (ALT r1 r2) = ALT (D s r1) (D s r2)"
| "D s (SEQ r1 r2) = ALTS ((SEQ (D s r1) r2) # [SEQ (delta (D s1 r1)) (D s2 r2). (s1, s2) \<leftarrow> (ssplit s)])"
| "D [] (STAR r) = STAR r"
| "D (c#s) (STAR r) = ALTS (SEQ (D (c#s) r) (STAR r) # 
      [SEQS ((map (\<lambda>c. delta (D [c] r)) s1) @ [D s2 (STAR r)]). (s1, s2) \<leftarrow> (tsplit (c#s))])"
sorry

termination sorry

thm D.simps
thm tl_def

lemma D_Nil:
  shows "D [] r = r"
apply(induct r)
apply(simp_all)
done

lemma D_ALTS:
  shows "D s (ALTS rs) = ALTS [D s r. r \<leftarrow> rs]"
apply(induct rs rule: ALTS.induct)
apply(simp_all)
done

(*
lemma 
  "D [a] (SEQ E F) = ALT (SEQ (D [a] E) F) (SEQ (delta E) (D [a] F))"
apply(simp add: D_Nil)
done

lemma 
  "D [a1, a2] (SEQ E F) = ALT (SEQ (D [a1, a2] E) F)
     (ALT (SEQ (delta (D [a1] E)) (D [a2] F)) (SEQ (delta E) (D [a1, a2] F)))"
apply(simp add: D_Nil)
done
*)
(*
lemma D_Der1:
  shows "L(D [c] r) = L(der c r)"
apply(induct r)
apply(simp)
apply(simp)
apply(simp)
prefer 2
apply(simp)
apply(simp)
apply(auto)[1]
apply(simp add: D_Nil)
apply(simp add: delta_def)
apply(simp add: D_Nil)
apply(simp add: delta_def)
apply(simp add: D_Nil)
apply(simp add: delta_def)
apply(simp)
done

lemma D_Der2:
  shows "L(D [a1, a2] r) = L(der a2 (der a1 r))"
apply(induct r)
apply(simp)
apply(simp)
apply(simp)
prefer 2
apply(simp)
apply(simp)
apply(auto)[1]
apply(simp add: delta_def)
apply(auto split: if_splits)[1]
apply(simp add: der_correctness Der_def D_Der1 D_Nil)
apply(simp add: der_correctness Der_def D_Der1 D_Nil)
apply (simp add: delta_def)
apply(simp add: der_correctness Der_def D_Der1 D_Nil)
apply (simp add: D_Der1 delta_def nullable_correctness)
apply (simp add: D_Der1 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Nil)
apply(simp add: der_correctness Der_def D_Der1 D_Nil)
apply (simp add: D_Der1 delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(auto)[1]
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
apply(simp add: D_Der1 D_Nil delta_def nullable_correctness)
done

lemma D_Der3:
  shows "L(D [a1, a2, a3] r) = L(ders [a1, a2, a3] r)"
apply(induct r)
apply(simp)
apply(simp)
apply(simp)
prefer 2
apply(simp)
apply(simp)
apply(auto)[1]
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
(* star case *)
apply(simp)
apply(auto)[1]
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply(simp add: Sequ_def)
apply(auto)[1]
defer
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
defer
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
defer
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness D_Der1)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
apply (simp add: D_Der2 delta_def nullable_correctness)
apply(simp add: der_correctness Der_def D_Der1 D_Der2 D_Nil)
defer
done

lemma D_Ders:
  shows "L (D (s1 @ s2) r) = L (D s2 (D s1 r))"
apply(induct r arbitrary: s1 s2)
apply(simp)
apply(simp)
apply(simp)
apply(auto)[1]
apply (metis Cons_eq_append_conv append_is_Nil_conv)
apply(simp)
apply(auto)[1]
apply(simp add: L_ALTS D_ALTS)
apply(auto)[1]
apply(simp add: L_ALTS)
oops


lemma D_cons:
  shows "L (D (c # s) r) = L (D s (der c r))"
apply(induct r arbitrary: c s)
apply(simp)
apply(simp)
apply(simp)
apply(simp)
apply(auto)[1]
sorry

lemma D_Zero:
  shows "lang (D s Zero) = lang (derivs s Zero)"
by (induct s) (simp_all)

lemma D_One:
  shows "lang (D s One) = lang (derivs s One)"
by (induct s) (simp_all add: D_Zero[symmetric])

lemma D_Atom:
  shows "lang (D s (Atom c)) = lang (derivs s (Atom c))"
by (induct s) (simp_all add: D_Zero[symmetric] D_One[symmetric])

lemma D_Plus:
  shows "lang (D s (Plus r1 r2)) = lang (derivs s (Plus r1 r2))"
by (induct s arbitrary: r1 r2) (simp_all add: D_empty D_cons)

lemma D_Times:
  shows "lang (D s (Times r1 r2)) = lang (derivs s (Times r1 r2))"
apply(induct s arbitrary: r1 r2) 
apply(simp_all add: D_empty D_cons)
apply(auto simp add: conc_def)[1]
apply(simp only: D_Plus[symmetric])
apply(simp only: D.simps)
apply(simp)
*)


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

lemma flat_Stars [simp]:
 "flat (Stars vs) = concat (map flat vs)"
by (induct vs) (auto)


section {* Relation between values and regular expressions *}

inductive 
  Prf :: "val \<Rightarrow> rexp \<Rightarrow> bool" ("\<turnstile> _ : _" [100, 100] 100)
where
 "\<lbrakk>\<turnstile> v1 : r1; \<turnstile> v2 : r2\<rbrakk> \<Longrightarrow> \<turnstile> Seq v1 v2 : SEQ r1 r2"
| "\<turnstile> v1 : r1 \<Longrightarrow> \<turnstile> Left v1 : ALT r1 r2"
| "\<turnstile> v2 : r2 \<Longrightarrow> \<turnstile> Right v2 : ALT r1 r2"
| "\<turnstile> Void : ONE"
| "\<turnstile> Char c : CHAR c"
| "\<turnstile> Stars [] : STAR r"
| "\<lbrakk>\<turnstile> v : r; \<turnstile> Stars vs : STAR r\<rbrakk> \<Longrightarrow> \<turnstile> Stars (v # vs) : STAR r"

inductive_cases Prf_elims:
  "\<turnstile> v : ZERO"
  "\<turnstile> v : SEQ r1 r2"
  "\<turnstile> v : ALT r1 r2"
  "\<turnstile> v : ONE"
  "\<turnstile> v : CHAR c"
(*  "\<turnstile> vs : STAR r"*)

lemma Prf_flat_L:
  assumes "\<turnstile> v : r" shows "flat v \<in> L r"
using assms
by(induct v r rule: Prf.induct)
  (auto simp add: Sequ_def)

lemma Prf_Stars:
  assumes "\<forall>v \<in> set vs. \<turnstile> v : r"
  shows "\<turnstile> Stars vs : STAR r"
using assms
by(induct vs) (auto intro: Prf.intros)

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

lemma L_flat_Prf1:
  assumes "\<turnstile> v : r" shows "flat v \<in> L r"
using assms
by (induct)(auto simp add: Sequ_def)

lemma L_flat_Prf2:
  assumes "s \<in> L r" shows "\<exists>v. \<turnstile> v : r \<and> flat v = s"
using assms
apply(induct r arbitrary: s)
apply(auto simp add: Sequ_def intro: Prf.intros)
using Prf.intros(1) flat.simps(5) apply blast
using Prf.intros(2) flat.simps(3) apply blast
using Prf.intros(3) flat.simps(4) apply blast
apply(subgoal_tac "\<exists>vs::val list. concat (map flat vs) = s \<and> (\<forall>v \<in> set vs. \<turnstile> v : r)")
apply(auto)[1]
apply(rule_tac x="Stars vs" in exI)
apply(simp)
apply (simp add: Prf_Stars)
apply(drule Star_string)
apply(auto)
apply(rule Star_val)
apply(auto)
done

lemma L_flat_Prf:
  "L(r) = {flat v | v. \<turnstile> v : r}"
using L_flat_Prf1 L_flat_Prf2 by blast


section {* Sulzmann and Lu functions *}

fun 
  mkeps :: "rexp \<Rightarrow> val"
where
  "mkeps(ONE) = Void"
| "mkeps(SEQ r1 r2) = Seq (mkeps r1) (mkeps r2)"
| "mkeps(ALT r1 r2) = (if nullable(r1) then Left (mkeps r1) else Right (mkeps r2))"
| "mkeps(STAR r) = Stars []"

fun injval :: "rexp \<Rightarrow> char \<Rightarrow> val \<Rightarrow> val"
where
  "injval (CHAR d) c Void = Char d"
| "injval (ALT r1 r2) c (Left v1) = Left(injval r1 c v1)"
| "injval (ALT r1 r2) c (Right v2) = Right(injval r2 c v2)"
| "injval (SEQ r1 r2) c (Seq v1 v2) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Left (Seq v1 v2)) = Seq (injval r1 c v1) v2"
| "injval (SEQ r1 r2) c (Right v2) = Seq (mkeps r1) (injval r2 c v2)"
| "injval (STAR r) c (Seq v (Stars vs)) = Stars ((injval r c v) # vs)" 


section {* Mkeps, injval *}

lemma mkeps_nullable:
  assumes "nullable(r)" 
  shows "\<turnstile> mkeps r : r"
using assms
by (induct rule: nullable.induct) 
   (auto intro: Prf.intros)

lemma mkeps_flat:
  assumes "nullable(r)" 
  shows "flat (mkeps r) = []"
using assms
by (induct rule: nullable.induct) (auto)


lemma Prf_injval:
  assumes "\<turnstile> v : der c r" 
  shows "\<turnstile> (injval r c v) : r"
using assms
apply(induct r arbitrary: c v rule: rexp.induct)
apply(auto intro!: Prf.intros mkeps_nullable elim!: Prf_elims split: if_splits)
(* STAR *)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
apply(auto)
apply (metis Prf.intros(6) Prf.intros(7))
by (metis Prf.intros(7))

lemma Prf_injval_flat:
  assumes "\<turnstile> v : der c r" 
  shows "flat (injval r c v) = c # (flat v)"
using assms
apply(induct arbitrary: v rule: der.induct)
apply(auto elim!: Prf_elims split: if_splits)
apply(metis mkeps_flat)
apply(rotate_tac 2)
apply(erule Prf.cases)
apply(simp_all)[7]
done



section {* Our Alternative Posix definition *}

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

inductive_cases Posix_elims:
  "s \<in> ZERO \<rightarrow> v"
  "s \<in> ONE \<rightarrow> v"
  "s \<in> CHAR c \<rightarrow> v"
  "s \<in> ALT r1 r2 \<rightarrow> v"
  "s \<in> SEQ r1 r2 \<rightarrow> v"
  "s \<in> STAR r \<rightarrow> v"

lemma Posix1:
  assumes "s \<in> r \<rightarrow> v"
  shows "s \<in> L r" "flat v = s"
using assms
by (induct s r v rule: Posix.induct)
   (auto simp add: Sequ_def)


lemma Posix1a:
  assumes "s \<in> r \<rightarrow> v"
  shows "\<turnstile> v : r"
using assms
by (induct s r v rule: Posix.induct)(auto intro: Prf.intros)


lemma Posix_mkeps:
  assumes "nullable r"
  shows "[] \<in> r \<rightarrow> mkeps r"
using assms
apply(induct r rule: nullable.induct)
apply(auto intro: Posix.intros simp add: nullable_correctness Sequ_def)
apply(subst append.simps(1)[symmetric])
apply(rule Posix.intros)
apply(auto)
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
qed


lemma Posix_injval:
  assumes "s \<in> (der c r) \<rightarrow> v"
  shows "(c # s) \<in> r \<rightarrow> (injval r c v)"
using assms
proof(induct r arbitrary: s v rule: rexp.induct)
  case ZERO
  have "s \<in> der c ZERO \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ZERO \<rightarrow> (injval ZERO c v)" by simp
next
  case ONE
  have "s \<in> der c ONE \<rightarrow> v" by fact
  then have "s \<in> ZERO \<rightarrow> v" by simp
  then have "False" by cases
  then show "(c # s) \<in> ONE \<rightarrow> (injval ONE c v)" by simp
next 
  case (CHAR d)
  consider (eq) "c = d" | (ineq) "c \<noteq> d" by blast
  then show "(c # s) \<in> (CHAR d) \<rightarrow> (injval (CHAR d) c v)"
  proof (cases)
    case eq
    have "s \<in> der c (CHAR d) \<rightarrow> v" by fact
    then have "s \<in> ONE \<rightarrow> v" using eq by simp
    then have eqs: "s = [] \<and> v = Void" by cases simp
    show "(c # s) \<in> CHAR d \<rightarrow> injval (CHAR d) c v" using eq eqs 
    by (auto intro: Posix.intros)
  next
    case ineq
    have "s \<in> der c (CHAR d) \<rightarrow> v" by fact
    then have "s \<in> ZERO \<rightarrow> v" using ineq by simp
    then have "False" by cases
    then show "(c # s) \<in> CHAR d \<rightarrow> injval (CHAR d) c v" by simp
  qed
next
  case (ALT r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (ALT r1 r2) \<rightarrow> v" by fact
  then have "s \<in> ALT (der c r1) (der c r2) \<rightarrow> v" by simp
  then consider (left) v' where "v = Left v'" "s \<in> der c r1 \<rightarrow> v'" 
              | (right) v' where "v = Right v'" "s \<notin> L (der c r1)" "s \<in> der c r2 \<rightarrow> v'" 
              by cases auto
  then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v"
  proof (cases)
    case left
    have "s \<in> der c r1 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r1 \<rightarrow> injval r1 c v'" using IH1 by simp
    then have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Left v')" by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using left by simp
  next 
    case right
    have "s \<notin> L (der c r1)" by fact
    then have "c # s \<notin> L r1" by (simp add: der_correctness Der_def)
    moreover 
    have "s \<in> der c r2 \<rightarrow> v'" by fact
    then have "(c # s) \<in> r2 \<rightarrow> injval r2 c v'" using IH2 by simp
    ultimately have "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c (Right v')" 
      by (auto intro: Posix.intros)
    then show "(c # s) \<in> ALT r1 r2 \<rightarrow> injval (ALT r1 r2) c v" using right by simp
  qed
next
  case (SEQ r1 r2)
  have IH1: "\<And>s v. s \<in> der c r1 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r1 \<rightarrow> injval r1 c v" by fact
  have IH2: "\<And>s v. s \<in> der c r2 \<rightarrow> v \<Longrightarrow> (c # s) \<in> r2 \<rightarrow> injval r2 c v" by fact
  have "s \<in> der c (SEQ r1 r2) \<rightarrow> v" by fact
  then consider 
        (left_nullable) v1 v2 s1 s2 where 
        "v = Left (Seq v1 v2)"  "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
      | (right_nullable) v1 s1 s2 where 
        "v = Right v1" "s = s1 @ s2"  
        "s \<in> der c r2 \<rightarrow> v1" "nullable r1" "s1 @ s2 \<notin> L (SEQ (der c r1) r2)"
      | (not_nullable) v1 v2 s1 s2 where
        "v = Seq v1 v2" "s = s1 @ s2" 
        "s1 \<in> der c r1 \<rightarrow> v1" "s2 \<in> r2 \<rightarrow> v2" "\<not>nullable r1" 
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)"
        by (force split: if_splits elim!: Posix_elims simp add: Sequ_def der_correctness Der_def)   
  then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" 
    proof (cases)
      case left_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using left_nullable by (rule_tac Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using left_nullable by simp
    next
      case right_nullable
      have "nullable r1" by fact
      then have "[] \<in> r1 \<rightarrow> (mkeps r1)" by (rule Posix_mkeps)
      moreover
      have "s \<in> der c r2 \<rightarrow> v1" by fact
      then have "(c # s) \<in> r2 \<rightarrow> (injval r2 c v1)" using IH2 by simp
      moreover
      have "s1 @ s2 \<notin> L (SEQ (der c r1) r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> [] @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" using right_nullable
        by(auto simp add: der_correctness Der_def append_eq_Cons_conv Sequ_def)
      ultimately have "([] @ (c # s)) \<in> SEQ r1 r2 \<rightarrow> Seq (mkeps r1) (injval r2 c v1)"
      by(rule Posix.intros)
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using right_nullable by simp
    next
      case not_nullable
      have "s1 \<in> der c r1 \<rightarrow> v1" by fact
      then have "(c # s1) \<in> r1 \<rightarrow> injval r1 c v1" using IH1 by simp
      moreover
      have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r1) \<and> s\<^sub>4 \<in> L r2)" by fact
      then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r1 \<and> s\<^sub>4 \<in> L r2)" by (simp add: der_correctness Der_def)
      ultimately have "((c # s1) @ s2) \<in> SEQ r1 r2 \<rightarrow> Seq (injval r1 c v1) v2" using not_nullable 
        by (rule_tac Posix.intros) (simp_all) 
      then show "(c # s) \<in> SEQ r1 r2 \<rightarrow> injval (SEQ r1 r2) c v" using not_nullable by simp
    qed
next
  case (STAR r)
  have IH: "\<And>s v. s \<in> der c r \<rightarrow> v \<Longrightarrow> (c # s) \<in> r \<rightarrow> injval r c v" by fact
  have "s \<in> der c (STAR r) \<rightarrow> v" by fact
  then consider
      (cons) v1 vs s1 s2 where 
        "v = Seq v1 (Stars vs)" "s = s1 @ s2" 
        "s1 \<in> der c r \<rightarrow> v1" "s2 \<in> (STAR r) \<rightarrow> (Stars vs)"
        "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" 
        apply(auto elim!: Posix_elims(1-5) simp add: der_correctness Der_def intro: Posix.intros)
        apply(rotate_tac 3)
        apply(erule_tac Posix_elims(6))
        apply (simp add: Posix.intros(6))
        using Posix.intros(7) by blast
    then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" 
    proof (cases)
      case cons
          have "s1 \<in> der c r \<rightarrow> v1" by fact
          then have "(c # s1) \<in> r \<rightarrow> injval r c v1" using IH by simp
        moreover
          have "s2 \<in> STAR r \<rightarrow> Stars vs" by fact
        moreover 
          have "(c # s1) \<in> r \<rightarrow> injval r c v1" by fact 
          then have "flat (injval r c v1) = (c # s1)" by (rule Posix1)
          then have "flat (injval r c v1) \<noteq> []" by simp
        moreover 
          have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> s1 @ s\<^sub>3 \<in> L (der c r) \<and> s\<^sub>4 \<in> L (STAR r))" by fact
          then have "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s2 \<and> (c # s1) @ s\<^sub>3 \<in> L r \<and> s\<^sub>4 \<in> L (STAR r))" 
            by (simp add: der_correctness Der_def)
        ultimately 
        have "((c # s1) @ s2) \<in> STAR r \<rightarrow> Stars (injval r c v1 # vs)" by (rule Posix.intros)
        then show "(c # s) \<in> STAR r \<rightarrow> injval (STAR r) c v" using cons by(simp)
    qed
qed


section {* The Lexer by Sulzmann and Lu  *}

fun 
  lexer :: "rexp \<Rightarrow> string \<Rightarrow> val option"
where
  "lexer r [] = (if nullable r then Some(mkeps r) else None)"
| "lexer r (c#s) = (case (lexer (der c r) s) of  
                    None \<Rightarrow> None
                  | Some(v) \<Rightarrow> Some(injval r c v))"


lemma lexer_correct_None:
  shows "s \<notin> L r \<longleftrightarrow> lexer r s = None"
apply(induct s arbitrary: r)
apply(simp add: nullable_correctness)
apply(drule_tac x="der a r" in meta_spec)
apply(auto simp add: der_correctness Der_def)
done

lemma lexer_correct_Some:
  shows "s \<in> L r \<longleftrightarrow> (\<exists>v. lexer r s = Some(v) \<and> s \<in> r \<rightarrow> v)"
apply(induct s arbitrary: r)
apply(auto simp add: Posix_mkeps nullable_correctness)[1]
apply(drule_tac x="der a r" in meta_spec)
apply(simp add: der_correctness Der_def)
apply(rule iffI)
apply(auto intro: Posix_injval simp add: Posix1(1))
done 

lemma lexer_correctness:
  shows "(lexer r s = Some v) \<longleftrightarrow> s \<in> r \<rightarrow> v"
  and   "(lexer r s = None) \<longleftrightarrow> \<not>(\<exists>v. s \<in> r \<rightarrow> v)"
using Posix1(1) Posix_determ lexer_correct_None lexer_correct_Some apply fastforce
using Posix1(1) lexer_correct_None lexer_correct_Some by blast


end