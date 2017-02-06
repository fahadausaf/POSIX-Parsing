   
theory Bounds
  imports "Lexer" 
begin

definition Size :: "rexp \<Rightarrow> nat"
where "Size r == Max {size (ders s r) | s. True }"

fun bar :: "rexp \<Rightarrow> string \<Rightarrow> rexp" where
  "bar r [] = r"
| "bar r (c # s) = ALT (ders (c # s) r) (bar r s)"

lemma size_ALT:
  "size (ders s (ALT r1 r2)) = Suc (size (ders s r1) + size (ders s r2))"
apply(induct s arbitrary: r1 r2)
apply(simp_all)
done

lemma size_bar_ALT:
  "size (bar (ALT r1 r2) s) = Suc (size (bar r1 s) + size (bar r2 s))"
apply(induct s)
apply(simp)
apply(simp add: size_ALT)
done

lemma size_SEQ:
  "size (ders s (SEQ r1 r2)) \<le> Suc (size (ders s r1)) + size r2 + size (bar (SEQ r1 r2) s)"
apply(induct s arbitrary: r1 r2)
apply(simp_all)
done

(*
lemma size_bar_SEQ:
  "size (bar (SEQ r1 r2) s) \<le> Suc (size (bar r1 s) + size (bar r2 s))"
apply(induct s)
apply(simp)
apply(auto simp add: size_SEQ size_ALT)
apply(rule le_trans)
apply(rule size_SEQ)
done
*)

lemma size_STAR:
  "size (ders s (STAR r)) \<le> Suc (size (bar r s)) + size (STAR r)"
apply(induct s arbitrary: r)
apply(simp)
apply(simp)
apply(rule le_trans)
apply(rule size_SEQ)
apply(simp)
oops

lemma Size_ALT:
  "Size (ALT r1 r2) \<le> Suc (Size r1 + Size r2)"
unfolding Size_def
apply(auto)
apply(simp add: size_ALT)
apply(subgoal_tac "Max {n. \<exists>s. n = Suc (size (ders s r1) + size (ders s r2))} \<ge>
  Suc (Max {n. \<exists>s. n = size (ders s r1) + size (ders s r2)})")
prefer 2
oops



end