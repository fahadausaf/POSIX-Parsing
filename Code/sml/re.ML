
datatype rexp =
   ZERO
 | ONE 
 | CHAR of char
 | ALT of rexp * rexp
 | SEQ of rexp * rexp 
 | STAR of rexp 
 | RECD of string * rexp

datatype value =
   Empty
 | Chr of char
 | Sequ of value * value
 | Left of value
 | Right of value
 | Stars of value list
 | Rec of string * value

(* some helper functions for strings *)   
fun string_repeat s n = String.concat (List.tabulate (n, fn _ => s))

(* some helper functions for rexps *)
fun seq s = case s of
    [] => ONE
  | [c] => CHAR(c)
  | c::cs => SEQ(CHAR(c), seq cs)

fun chr c = CHAR(c)

fun str s = seq(explode s)

fun plus r = SEQ(r, STAR(r))

infix 9 ++
infix 9 --
infix 9 $

fun op ++ (r1, r2) = ALT(r1, r2)

fun op -- (r1, r2) = SEQ(r1, r2)

fun op $ (x, r) = RECD(x, r)

fun alts rs = case rs of
    [] => ZERO
  | [r] => r
  | r::rs => List.foldl (op ++) r rs


(* size of a regular expressions - for testing purposes *)
fun size r = case r of
    ZERO => 1
  | ONE => 1
  | CHAR(_) => 1
  | ALT(r1, r2) => 1 + (size r1) + (size r2)
  | SEQ(r1, r2) => 1 + (size r1) + (size r2)
  | STAR(r) => 1 + (size r)
  | RECD(_, r) => 1 + (size r)

(* nullable function: tests whether the regular 
   expression can recognise the empty string *)
fun nullable r = case r of
    ZERO => false
  | ONE => true
  | CHAR(_) => false
  | ALT(r1, r2) => nullable(r1) orelse nullable(r2)
  | SEQ(r1, r2) => nullable(r1) andalso nullable(r2)
  | STAR(_) => true
  | RECD(_, r) => nullable(r)

(* derivative of a regular expression r w.r.t. a character c *)
fun der c r = case r of
    ZERO => ZERO
  | ONE => ZERO
  | CHAR(d) => if c = d then ONE else ZERO
  | ALT(r1, r2) => ALT(der c r1, der c r2)
  | SEQ(r1, r2) => 
      if nullable r1 then ALT(SEQ(der c r1, r2), der c r2)
      else SEQ(der c r1, r2)
  | STAR(r) => SEQ(der c r, STAR(r))
  | RECD(_, r) => der c r

(* derivative w.r.t. a list of chars (iterates der) *)
fun ders s r = case s of 
    [] => r
  | c::s => ders s (der c r)

(* extracts a string from value *)
fun flatten v = case v of 
    Empty => ""
  | Chr(c) => Char.toString c
  | Left(v) => flatten v
  | Right(v) => flatten v
  | Sequ(v1, v2) => flatten v1 ^ flatten v2
  | Stars(vs) => String.concat (List.map flatten vs)
  | Rec(_, v) => flatten v


(* extracts an environment from a value *)
fun env v = case v of 
    Empty => []
  | Chr(c) => []
  | Left(v) => env v
  | Right(v) => env v
  | Sequ(v1, v2) => env v1 @ env v2
  | Stars(vs) => List.foldr (op @) [] (List.map env vs)
  | Rec(x, v) => (x, flatten v) :: env v

fun string_of_pair (x, s) = "(" ^ x ^ "," ^ s ^ ")"
fun string_of_env xs = String.concatWith "," (List.map string_of_pair xs)


(* the value for a nullable rexp *)
fun mkeps r = case r of 
    ONE => Empty
  | ALT(r1, r2) => 
      if nullable r1 then Left(mkeps r1) else Right(mkeps r2)
  | SEQ(r1, r2) => Sequ(mkeps r1, mkeps r2)
  | STAR(r) => Stars([])
  | RECD(x, r) => Rec(x, mkeps r)

exception Error

(* injection of a char into a value *)
fun inj r c v = case (r, v) of
    (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj r c v1 :: vs)
  | (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj r1 c v1, v2)
  | (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj r1 c v1, v2)
  | (SEQ(r1, r2), Right(v2)) => Sequ(mkeps r1, inj r2 c v2)
  | (ALT(r1, r2), Left(v1)) => Left(inj r1 c v1)
  | (ALT(r1, r2), Right(v2)) => Right(inj r2 c v2)
  | (CHAR(d), Empty) => Chr(d) 
  | (RECD(x, r1), _) => Rec(x, inj r1 c v)
  | _ => (print ("\nr: " ^ PolyML.makestring r ^ "\n");
          print ("v: " ^ PolyML.makestring v ^ "\n");
          raise Error)

(* some "rectification" functions for simplification *)
fun f_id v = v
fun f_right f = fn v => Right(f v)
fun f_left f = fn v => Left(f v)
fun f_alt f1 f2 = fn v => case v of
    Right(v) => Right(f2 v)
  | Left(v) => Left(f1 v)
fun f_seq f1 f2 = fn v => case v of 
  Sequ(v1, v2) => Sequ(f1 v1, f2 v2)
fun f_seq_Empty1 f1 f2 = fn v => Sequ(f1 Empty, f2 v)
fun f_seq_Empty2 f1 f2 = fn v => Sequ(f1 v, f2 Empty)
fun f_rec f = fn v => case v of
    Rec(x, v) => Rec(x, f v)

exception ShouldNotHappen

fun f_error v = raise ShouldNotHappen

(* simplification of regular expressions returning also an 
   rectification function; no simplification under STARs *)
fun simp r = case r of
    ALT(r1, r2) => 
      let val (r1s, f1s) = simp r1  
          val (r2s, f2s) = simp r2 in
        (case (r1s, r2s) of
            (ZERO, _) => (r2s, f_right f2s)
          | (_, ZERO) => (r1s, f_left f1s)
          | (_, _)    => if r1s = r2s then (r1s, f_left f1s)
                         else (ALT (r1s, r2s), f_alt f1s f2s))
      end 
  | SEQ(r1, r2) => 
      let val (r1s, f1s) = simp r1 
          val (r2s, f2s) = simp r2 in
        (case (r1s, r2s) of
          (ZERO, _)  => (ZERO, f_error)
        | (_, ZERO)  => (ZERO, f_error)
        | (ONE, _) => (r2s, f_seq_Empty1 f1s f2s)
        | (_, ONE) => (r1s, f_seq_Empty2 f1s f2s)
        | (_, _)     => (SEQ(r1s, r2s), f_seq f1s f2s))
      end  
  | RECD(x, r1) => 
      let val (r1s, f1s) = simp r1 in
        (RECD(x, r1s), f_rec f1s)
      end
  | r => (r, f_id)

fun der_simp c r = case r of
    ZERO => (ZERO, f_id)
  | ONE => (ZERO, f_id)
  | CHAR(d) => ((if c = d then ONE else ZERO), f_id)
  | ALT(r1, r2) => 
      let 
        val (r1d, f1d) = der_simp c r1 
        val (r2d, f2d) = der_simp c r2 
      in
        case (r1d, r2d) of
          (ZERO, _) => (r2d, f_right f2d)
        | (_, ZERO) => (r1d, f_left f1d)
        | (_, _)    => if r1d = r2d then (r1d, f_left f1d)
                       else (ALT (r1d, r2d), f_alt f1d f2d)
      end
  | SEQ(r1, r2) => 
      if nullable r1 
      then 
        let 
          val (r1d, f1d) = der_simp c r1 
          val (r2d, f2d) = der_simp c r2
          val (r2s, f2s) = simp r2 
        in
          case (r1d, r2s, r2d) of
            (ZERO, _, _)  => (r2d, f_right f2d)
          | (_, ZERO, _)  => (r2d, f_right f2d)
          | (_, _, ZERO)  => (SEQ(r1d, r2s), f_left (f_seq f1d f2s))
          | (ONE, _, _) => (ALT(r2s, r2d), f_alt (f_seq_Empty1 f1d f2s) f2d)
          | (_, ONE, _) => (ALT(r1d, r2d), f_alt (f_seq_Empty2 f1d f2s) f2d)
          | (_, _, _)     => (ALT(SEQ(r1d, r2s), r2d), f_alt (f_seq f1d f2s) f2d)
        end
      else 
        let 
          val (r1d, f1d) = der_simp c r1 
          val (r2s, f2s) = simp r2
        in
          case (r1d, r2s) of
            (ZERO, _) => (ZERO, f_error)
          | (_, ZERO) => (ZERO, f_error)
          | (ONE, _) => (r2s, f_seq_Empty1 f1d f2s)
          | (_, ONE) => (r1d, f_seq_Empty2 f1d f2s)
          | (_, _) => (SEQ(r1d, r2s), f_seq f1d f2s)
  	end	  
  | STAR(r1) => 
      let 
        val (r1d, f1d) = der_simp c r1 
      in
        case r1d of
          ZERO => (ZERO, f_error)
        | ONE => (STAR r1, f_seq_Empty1 f1d f_id)
        | _ => (SEQ(r1d, STAR(r1)), f_seq f1d f_id)
      end
  | RECD(x, r1) => der_simp c r1 



(* matcher function *)
fun matcher r s = nullable(ders (explode s) r)

(* lexing function (produces a value) *)
exception LexError

fun lex r s = case s of 
    [] => if (nullable r) then mkeps r else raise LexError
  | c::cs => inj r c (lex (der c r) cs)

fun lexing r s = lex r (explode s)

(* lexing with simplification *)
fun lex_simp r s = case s of 
    [] => if (nullable r) then mkeps r else raise LexError
  | c::cs => 
    let val (r_simp, f_simp) = simp (der c r) in
      inj r c (f_simp (lex_simp r_simp cs))
    end

fun lexing_simp r s = lex_simp r (explode s)

fun lex_simp2 r s = case s of 
    [] => if (nullable r) then mkeps r else raise LexError
  | c::cs => 
    let val (r_simp, f_simp) = der_simp c r in
      inj r c (f_simp (lex_simp2 r_simp cs))
    end

fun lexing_simp2 r s = lex_simp2 r (explode s)

fun lex_acc r s f = case s of 
    [] => if (nullable r) then f (mkeps r) else raise LexError
  | c::cs => 
    let val (r_simp, f_simp) = simp (der c r) in
      lex_acc r_simp cs (fn v => f (inj r c (f_simp v)))
    end

fun lexing_acc r s  = lex_acc r (explode s) (f_id)

fun lex_acc2 r s f = case s of 
    [] => if (nullable r) then f (mkeps r) else raise LexError
  | c::cs => 
    let val (r_simp, f_simp) = der_simp c r in
      lex_acc2 r_simp cs (fn v => f (inj r c (f_simp v)))
    end

fun lexing_acc2 r s  = lex_acc2 r (explode s) (f_id)


(* Lexing rules for a small WHILE language *)
val sym = alts (List.map chr (explode "abcdefghijklmnopqrstuvwxyz"))
val digit = alts (List.map chr (explode "0123456789"))
val idents =  sym -- STAR(sym ++ digit)
val nums = plus(digit)
val keywords = alts (List.map str ["skip", "while", "do", "if", "then", "else", "read", "write", "true", "false"])
val semicolon = str ";"
val ops = alts (List.map str [":=", "==", "-", "+", "*", "!=", "<", ">", "<=", ">=", "%", "/"])
val whitespace = plus(str " " ++ str "\n" ++ str "\t")
val rparen = str ")"
val lparen = str "("
val begin_paren = str "{"
val end_paren = str "}"


val while_regs = STAR(("k" $ keywords) ++
                      ("i" $ idents) ++
                      ("o" $ ops) ++ 
                      ("n" $ nums) ++ 
                      ("s" $ semicolon) ++ 
                      ("p" $ (lparen ++ rparen)) ++ 
                      ("b" $ (begin_paren ++ end_paren)) ++ 
                      ("w" $ whitespace))



(* Some Tests
  ============ *)

fun time f x =
  let
  val t_start = Timer.startCPUTimer()
  val f_x = (f x; f x; f x; f x; f x; f x; f x; f x; f x; f x)
  val t_end = Time.toReal(#usr(Timer.checkCPUTimer(t_start))) / 10.0
in
  (print ((Real.toString t_end) ^ "\n"); f_x)
end

val prog = "ab";
val reg = ("x" $ ((str "a") -- (str "b")));
print("Simp: " ^ PolyML.makestring (lexing_simp reg prog) ^ "\n");
print("Acc:  " ^ PolyML.makestring (lexing_acc  reg prog) ^ "\n");
print("Env   " ^ string_of_env (env (lexing_acc reg prog)) ^ "\n");

fun fst (x, y) = x;
fun snd (x, y) = y;

val derS = [reg,
            der #"a" reg,
            fst (simp (der #"a" reg)),
            fst (der_simp #"a" reg)];

val vS = [(snd (simp (der #"a" reg))) (Chr(#"b")),
          (snd (der_simp #"a" reg)) (Chr(#"b"))
         ];

print("Ders: \n" ^ 
       String.concatWith "\n" (List.map PolyML.makestring derS)
       ^ "\n\n");
print("Vs: \n" ^ 
       String.concatWith "\n" (List.map PolyML.makestring vS)
       ^ "\n\n");


val prog0 = "read n";
print("Env0 is: \n" ^  string_of_env (env (lexing_acc while_regs prog0)) ^ "\n");

val prog1 = "read  n; write (n)";
print("Env1 is: \n" ^ string_of_env (env (lexing_acc while_regs prog1)) ^ "\n");


val prog2 = String.concatWith "\n" 
  ["i := 2;",
   "max := 100;",
   "while i < max do {",
   "  isprime := 1;",
   "  j := 2;",
   "  while (j * j) <= i + 1  do {",
   "    if i % j == 0 then isprime := 0  else skip;",
   "    j := j + 1",
   "  };",
   " if isprime == 1 then write i else skip;",
   " i := i + 1",
   "}"];


let 
  val tst = (lexing_simp while_regs prog2 = lexing_acc while_regs prog2)
in
  print("Sanity test: >>" ^ (PolyML.makestring tst) ^ "<<\n")
end;

(* loops in ML *)
datatype for = to of int * int
infix to 

val for =
  fn lo to up =>
    (fn f => 
       let fun loop lo = 
         if lo > up then () else (f lo; loop (lo + 1))
       in loop lo end)

fun forby n =
  fn lo to up =>
    (fn f => 
       let fun loop lo = 
         if lo > up then () else (f lo; loop (lo + n))
       in loop lo end)


fun step_simp i = 
  (print ((Int.toString i) ^ ": ") ;
   time (lexing_simp while_regs) (string_repeat prog2 i)) 

fun step_simp2 i = 
  (print ((Int.toString i) ^ ": ") ;
   time (lexing_simp2 while_regs) (string_repeat prog2 i)) 

fun step_acc i = 
  (print ((Int.toString i) ^ ": ") ;
   time (lexing_acc while_regs) (string_repeat prog2 i))

fun step_acc2 i = 
  (print ((Int.toString i) ^ ": ") ;
   time (lexing_acc2 while_regs) (string_repeat prog2 i)) 

val main1 = forby 1000 (1000 to 5000) step_simp;
print "\n";
val main2 = forby 1000 (1000 to 5000) step_simp2;
print "\n";
val main3 = forby 1000 (1000 to 5000) step_acc;
print "\n";
val main4 = forby 1000 (1000 to 5000) step_acc2; 


