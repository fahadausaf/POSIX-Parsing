   
theory Sulzmann
  imports "Lexer" "~~/src/HOL/Library/Multiset"
begin


section {* Sulzmann's "Ordering" of Values *}


inductive ValOrd :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ >_ _" [100, 100, 100] 100)
where
  C2: "v1 >r1 v1' \<Longrightarrow> (Seq v1 v2) >(SEQ r1 r2) (Seq v1' v2')" 
| C1: "v2 >r2 v2' \<Longrightarrow> (Seq v1 v2) >(SEQ r1 r2) (Seq v1 v2')" 
| A1: "length (flat v2) > length (flat v1) \<Longrightarrow> (Right v2) >(ALT r1 r2) (Left v1)"
| A2: "length (flat v1) \<ge> length (flat v2) \<Longrightarrow> (Left v1) >(ALT r1 r2) (Right v2)"
| A3: "v2 >r2 v2' \<Longrightarrow> (Right v2) >(ALT r1 r2) (Right v2')"
| A4: "v1 >r1 v1' \<Longrightarrow> (Left v1) >(ALT r1 r2) (Left v1')"
| K1: "flat (Stars (v # vs)) = [] \<Longrightarrow> (Stars []) >(STAR r) (Stars (v # vs))"
| K2: "flat (Stars (v # vs)) \<noteq> [] \<Longrightarrow> (Stars (v # vs)) >(STAR r) (Stars [])"
| K3: "v1 >r v2 \<Longrightarrow> (Stars (v1 # vs1)) >(STAR r) (Stars (v2 # vs2))"
| K4: "(Stars vs1) >(STAR r) (Stars vs2) \<Longrightarrow> (Stars (v # vs1)) >(STAR r) (Stars (v # vs2))"

definition ValOrdEq :: "val \<Rightarrow> rexp \<Rightarrow> val \<Rightarrow> bool" ("_ \<ge>_ _" [100, 100, 100] 100)
where 
  "v\<^sub>1 \<ge>r v\<^sub>2 \<equiv> v\<^sub>1 = v\<^sub>2 \<or> (v\<^sub>1 >r v\<^sub>2 \<and> flat v\<^sub>1 = flat v\<^sub>2)"

(*


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
*)


section {* Bit-Encodings *}


fun 
  code :: "val \<Rightarrow> rexp \<Rightarrow> bool list"
where
  "code Void ONE = []"
| "code (Char c) (CHAR d) = []"
| "code (Left v) (ALT r1 r2) = False # (code v r1)"
| "code (Right v) (ALT r1 r2) = True # (code v r2)"
| "code (Seq v1 v2) (SEQ r1 r2) = (code v1 r1) @ (code v2 r2)"
| "code (Stars []) (STAR r) = [True]"
| "code (Stars (v # vs)) (STAR r) =  False # (code v r) @ code (Stars vs) (STAR r)"

fun 
  Stars_add :: "val \<Rightarrow> val \<Rightarrow> val"
where
  "Stars_add v (Stars vs) = Stars (v # vs)"

function
  decode' :: "bool list \<Rightarrow> rexp \<Rightarrow> (val * bool list)"
where
  "decode' ds ZERO = (Void, [])"
| "decode' ds ONE = (Void, ds)"
| "decode' ds (CHAR d) = (Char d, ds)"
| "decode' [] (ALT r1 r2) = (Void, [])"
| "decode' (False # ds) (ALT r1 r2) = (let (v, ds') = decode' ds r1 in (Left v, ds'))"
| "decode' (True # ds) (ALT r1 r2) = (let (v, ds') = decode' ds r2 in (Right v, ds'))"
| "decode' ds (SEQ r1 r2) = (let (v1, ds') = decode' ds r1 in
                             let (v2, ds'') = decode' ds' r2 in (Seq v1 v2, ds''))"
| "decode' [] (STAR r) = (Void, [])"
| "decode' (True # ds) (STAR r) = (Stars [], ds)"
| "decode' (False # ds) (STAR r) = (let (v, ds') = decode' ds r in
                                    let (vs, ds'') = decode' ds' (STAR r) 
                                    in (Stars_add v vs, ds''))"
by pat_completeness auto

termination
apply(size_change)
oops

term "inv_image (measure(%cs. size cs) <*lex*> measure(%s. size s)) (%(ds,r). (r,ds))"

lemma decode'_smaller:
  assumes "decode'_dom (ds, r)"
  shows "length (snd (decode' ds r)) \<le> length ds"
using assms
apply(induct ds r)
apply(auto simp add: decode'.psimps split: prod.split)
using dual_order.trans apply blast
by (meson dual_order.trans le_SucI)

termination "decode'"  
apply(relation "inv_image (measure(%cs. size cs) <*lex*> measure(%s. size s)) (%(ds,r). (r,ds))") 
apply(auto dest!: decode'_smaller)
by (metis less_Suc_eq_le snd_conv)

fun 
  decode :: "bool list \<Rightarrow> rexp \<Rightarrow> val option"
where
  "decode ds r = (let (v, ds') = decode' ds r 
                  in (if ds' = [] then Some v else None))"

lemma decode'_code:
  assumes "\<turnstile> v : r"
  shows "decode' ((code v r) @ ds) r = (v, ds)"
using assms
by (induct v r arbitrary: ds) (auto)


lemma decode_code:
  assumes "\<turnstile> v : r"
  shows "decode (code v r) r = Some v"
using assms decode'_code[of _ _ "[]"]
by auto

datatype arexp =
  AZERO
| AONE "bool list"
| ACHAR "bool list" char
| ASEQ "bool list" arexp arexp
| AALT "bool list" arexp arexp
| ASTAR "bool list" arexp

fun fuse :: "bool list \<Rightarrow> arexp \<Rightarrow> arexp" where
  "fuse bs AZERO = AZERO"
| "fuse bs (AONE cs) = AONE (bs @ cs)" 
| "fuse bs (ACHAR cs c) = ACHAR (bs @ cs) c"
| "fuse bs (AALT cs r1 r2) = AALT (bs @ cs) r1 r2"
| "fuse bs (ASEQ cs r1 r2) = ASEQ (bs @ cs) r1 r2"
| "fuse bs (ASTAR cs r) = ASTAR (bs @ cs) r"

fun internalise :: "rexp \<Rightarrow> arexp" where
  "internalise ZERO = AZERO"
| "internalise ONE = AONE []"
| "internalise (CHAR c) = ACHAR [] c"
| "internalise (ALT r1 r2) = AALT [] (fuse [False] (internalise r1)) 
                                     (fuse [True]  (internalise r2))"
| "internalise (SEQ r1 r2) = ASEQ [] (internalise r1) (internalise r2)"
| "internalise (STAR r) = ASTAR [] (internalise r)"

fun retrieve :: "arexp \<Rightarrow> val \<Rightarrow> bool list" where
  "retrieve (AONE bs) Void = bs"
| "retrieve (ACHAR bs c) (Char d) = bs"
| "retrieve (AALT bs r1 r2) (Left v) = bs @ retrieve r1 v"
| "retrieve (AALT bs r1 r2) (Right v) = bs @ retrieve r2 v"
| "retrieve (ASEQ bs r1 r2) (Seq v1 v2) = bs @ retrieve r1 v1 @ retrieve r2 v2"
| "retrieve (ASTAR bs r) (Stars []) = bs @ [True]"
| "retrieve (ASTAR bs r) (Stars (v#vs)) = 
     bs @ [False] @ retrieve r v @ retrieve (ASTAR [] r) (Stars vs)"

fun
 anullable :: "arexp \<Rightarrow> bool"
where
  "anullable (AZERO) = False"
| "anullable (AONE bs) = True"
| "anullable (ACHAR bs c) = False"
| "anullable (AALT bs r1 r2) = (anullable r1 \<or> anullable r2)"
| "anullable (ASEQ bs r1 r2) = (anullable r1 \<and> anullable r2)"
| "anullable (ASTAR bs r) = True"

fun 
  amkeps :: "arexp \<Rightarrow> bool list"
where
  "amkeps(AONE bs) = bs"
| "amkeps(ASEQ bs r1 r2) = bs @ (amkeps r1) @ (amkeps r2)"
| "amkeps(AALT bs r1 r2) = (if anullable(r1) then bs @ (amkeps r1) else bs @ (amkeps r2))"
| "amkeps(ASTAR bs r) = bs @ [True]"


fun
 ader :: "char \<Rightarrow> arexp \<Rightarrow> arexp"
where
  "ader c (AZERO) = AZERO"
| "ader c (AONE bs) = AZERO"
| "ader c (ACHAR bs d) = (if c = d then AONE bs else AZERO)"
| "ader c (AALT bs r1 r2) = AALT bs (ader c r1) (ader c r2)"
| "ader c (ASEQ bs r1 r2) = 
     (if anullable r1
      then AALT bs (ASEQ [] (ader c r1) r2) (fuse (amkeps r1) (ader c r2))
      else ASEQ bs (ader c r1) r2)"
| "ader c (ASTAR bs r) = ASEQ bs (fuse [False] (ader c r)) (ASTAR [] r)"

lemma
  assumes "\<turnstile> v : der c r"
  shows "Some (injval r c v) = decode (retrieve (ader c (internalise r)) v) r"
using assms
apply(induct c r arbitrary: v rule: der.induct)
apply(simp_all)
apply(erule Prf_elims)
apply(erule Prf_elims)
apply(case_tac "c = d")
apply(simp)
apply(erule Prf_elims)
apply(simp)
apply(simp)
apply(erule Prf_elims)
apply(auto split: prod.splits)[1]
oops

end