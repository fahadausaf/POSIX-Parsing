
type rexp =
   ZERO 
 | ONE 
 | CHAR of char
 | ALT of rexp * rexp
 | SEQ of rexp * rexp 
 | STAR of rexp 
 | RECD of string * rexp;;

type value =
   Empty
 | Chr of char
 | Sequ of value * value
 | Left of value
 | Right of value
 | Stars of value list
 | Rec of string * value;;

let rec string_of_val v = match v with
   Empty -> "Empty"
 | Chr(c) -> String.make 1 c
 | Sequ(v1, v2) -> "Seq(" ^ string_of_val v1 ^ "," ^ string_of_val v2 ^ ")"
 | Left(v1) -> "Left(" ^ string_of_val v1 ^ ")"
 | Right(v1) -> "Right(" ^ string_of_val v1 ^ ")"
 | Stars(vs) -> "[" ^ String.concat "," (List.map string_of_val vs) ^ "]"
 | Rec(x, v1) -> x ^ " $ " ^ string_of_val v1;;


(* some helper functions for strings *)   
let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let string_repeat s n =
  Array.fold_left (^) "" (Array.make n s);;

(* some helper functions for rexps *)
let rec seq s = match s with
    [] -> ONE
  | [c] -> CHAR(c)
  | c::cs -> SEQ(CHAR(c), seq cs);;

let chr c = CHAR(c)

let str s = seq(explode s);;

let plus r = SEQ(r, STAR(r));;

let (++) r1 r2 = ALT(r1, r2);;

let (--) r1 r2 = SEQ(r1, r2);;

let ($) x r = RECD(x, r);;

let alts rs = match rs with 
    [] -> ZERO
  | [r] -> r
  | r::rs -> List.fold_left (++) r rs;;


(* size of a regular expressions - for testing purposes *)
let rec size r = match r with
    ZERO -> 1
  | ONE -> 1
  | CHAR(_) -> 1
  | ALT(r1, r2) -> 1 + (size r1) + (size r2)
  | SEQ(r1, r2) -> 1 + (size r1) + (size r2)
  | STAR(r) -> 1 + (size r)
  | RECD(_, r) -> 1 + (size r);;

(* nullable function: tests whether the regular 
   expression can recognise the empty string *)
let rec nullable r = match r with
    ZERO -> false
  | ONE -> true
  | CHAR(_) -> false
  | ALT(r1, r2) -> nullable(r1) || nullable(r2)
  | SEQ(r1, r2) -> nullable(r1) && nullable(r2)
  | STAR(_) -> true
  | RECD(_, r) -> nullable(r);;

(* derivative of a regular expression r w.r.t. a character c *)
let rec der c r = match r with 
    ZERO -> ZERO
  | ONE -> ZERO
  | CHAR(d) -> if c = d then ONE else ZERO
  | ALT(r1, r2) -> ALT(der c r1, der c r2)
  | SEQ(r1, r2) -> 
      if nullable r1 then ALT(SEQ(der c r1, r2), der c r2)
      else SEQ(der c r1, r2)
  | STAR(r) -> SEQ(der c r, STAR(r))
  | RECD(_, r) -> der c r;;

(* derivative w.r.t. a list of chars (iterates der) *)
let rec ders s r = match s with 
    [] -> r
  | c::s -> ders s (der c r);;

(* extracts a string from value *)
let rec flatten v = match v with 
    Empty -> ""
  | Chr(c) -> String.make 1 c
  | Left(v) -> flatten v
  | Right(v) -> flatten v
  | Sequ(v1, v2) -> flatten v1 ^ flatten v2
  | Stars(vs) -> String.concat "" (List.map flatten vs)
  | Rec(_, v) -> flatten v;;


(* extracts an environment from a value *)
let rec env v = match v with
    Empty -> []
  | Chr(c) -> []
  | Left(v) -> env v
  | Right(v) -> env v
  | Sequ(v1, v2) -> env v1 @ env v2
  | Stars(vs) -> List.flatten (List.map env vs)
  | Rec(x, v) -> (x, flatten v) :: env v;;

let string_of_pair (x, s) = "(" ^ x ^ "," ^ s ^ ")";;
let string_of_env xs = String.concat "," (List.map string_of_pair xs);;


(* the value for a nullable rexp *)
let rec mkeps r = match r with
    ONE -> Empty
  | ALT(r1, r2) -> 
      if nullable r1 then Left(mkeps r1) else Right(mkeps r2)
  | SEQ(r1, r2) -> Sequ(mkeps r1, mkeps r2)
  | STAR(r) -> Stars([])
  | RECD(x, r) -> Rec(x, mkeps r);;


(* injection of a char into a value *)
let rec inj r c v = match r, v with
    STAR(r), Sequ(v1, Stars(vs)) -> Stars(inj r c v1 :: vs)
  | SEQ(r1, r2), Sequ(v1, v2) -> Sequ(inj r1 c v1, v2)
  | SEQ(r1, r2), Left(Sequ(v1, v2)) -> Sequ(inj r1 c v1, v2)
  | SEQ(r1, r2), Right(v2) -> Sequ(mkeps r1, inj r2 c v2)
  | ALT(r1, r2), Left(v1) -> Left(inj r1 c v1)
  | ALT(r1, r2), Right(v2) -> Right(inj r2 c v2)
  | CHAR(d), Empty -> Chr(d) 
  | RECD(x, r1), _ -> Rec(x, inj r1 c v);;

(* some "rectification" functions for simplification *)
let f_id v = v;;
let f_right f = fun v -> Right(f v);;
let f_left f = fun v -> Left(f v);;
let f_alt f1 f2 = fun v -> match v with 
    Right(v) -> Right(f2 v)
  | Left(v) -> Left(f1 v);;
let f_seq f1 f2 = fun v -> match v with 
  Sequ(v1, v2) -> Sequ(f1 v1, f2 v2);;
let f_seq_Empty1 f1 f2 = fun v -> Sequ(f1 Empty, f2 v);;
let f_seq_Empty2 f1 f2 = fun v -> Sequ(f1 v, f2 Empty);;
let f_rec f = fun v -> match v with
    Rec(x, v) -> Rec(x, f v);;

exception ShouldNotHappen
let f_error v = raise ShouldNotHappen

(* simplification of regular expressions returning also an 
   rectification function; no simplification under STARs *)
let rec simp r = match r with
    ALT(r1, r2) -> 
      let (r1s, f1s) = simp r1 in 
      let (r2s, f2s) = simp r2 in
      (match r1s, r2s with
          ZERO, _ -> (r2s, f_right f2s)
        | _, ZERO -> (r1s, f_left f1s)
        | _, _    -> if r1s = r2s then (r1s, f_left f1s)
                     else (ALT (r1s, r2s), f_alt f1s f2s)) 
  | SEQ(r1, r2) -> 
      let (r1s, f1s) = simp r1 in
      let (r2s, f2s) = simp r2 in
      (match r1s, r2s with
          ZERO, _  -> (ZERO, f_error)
        | _, ZERO  -> (ZERO, f_error)
        | ONE, _ -> (r2s, f_seq_Empty1 f1s f2s)
        | _, ONE -> (r1s, f_seq_Empty2 f1s f2s)
        | _, _     -> (SEQ(r1s, r2s), f_seq f1s f2s))
  | RECD(x, r1) -> 
      let (r1s, f1s) = simp r1 in
      (RECD(x, r1s), f_rec f1s)
  | r -> (r, f_id)
;;

let rec der_simp c r = match r with
    ZERO -> (ZERO, f_id)
  | ONE -> (ZERO, f_id)
  | CHAR(d) -> ((if c = d then ONE else ZERO), f_id)
  | ALT(r1, r2) -> 
      let (r1d, f1d) = der_simp c r1 in
      let (r2d, f2d) = der_simp c r2 in
      (match r1d, r2d with
          ZERO, _ -> (r2d, f_right f2d)
        | _, ZERO -> (r1d, f_left f1d)
        | _, _    -> if r1d = r2d then (r1d, f_left f1d)
                     else (ALT (r1d, r2d), f_alt f1d f2d))
  | SEQ(r1, r2) -> 
      if nullable r1 
      then 
        let (r1d, f1d) = der_simp c r1 in 
        let (r2d, f2d) = der_simp c r2 in
        let (r2s, f2s) = simp r2 in
        (match r1d, r2s, r2d with
            ZERO, _, _  -> (r2d, f_right f2d)
          | _, ZERO, _  -> (r2d, f_right f2d)
          | _, _, ZERO  -> (SEQ(r1d, r2s), f_left (f_seq f1d f2s))
          | ONE, _, _ -> (ALT(r2s, r2d), f_alt (f_seq_Empty1 f1d f2s) f2d)
          | _, ONE, _ -> (ALT(r1d, r2d), f_alt (f_seq_Empty2 f1d f2s) f2d)
          | _, _, _     -> (ALT(SEQ(r1d, r2s), r2d), f_alt (f_seq f1d f2s) f2d))
      else 
        let (r1d, f1d) = der_simp c r1 in
        let (r2s, f2s) = simp r2 in
        (match r1d, r2s with
            ZERO, _ -> (ZERO, f_error)
          | _, ZERO -> (ZERO, f_error)
          | ONE, _ -> (r2s, f_seq_Empty1 f1d f2s)
          | _, ONE -> (r1d, f_seq_Empty2 f1d f2s)
          | _, _ -> (SEQ(r1d, r2s), f_seq f1d f2s))	  
  | STAR(r1) -> 
      let (r1d, f1d) = der_simp c r1 in
      (match r1d with
          ZERO -> (ZERO, f_error)
        | ONE -> (STAR r1, f_seq_Empty1 f1d f_id)
        | _ -> (SEQ(r1d, STAR(r1)), f_seq f1d f_id))
  | RECD(x, r1) -> der_simp c r1 


(* matcher function *)
let matcher r s = nullable(ders (explode s) r);;

(* lexing function (produces a value) *)
exception LexError;;

let rec lex r s = match s with
    [] -> if (nullable r) then mkeps r else raise LexError
  | c::cs -> inj r c (lex (der c r) cs);;

let lexing r s = lex r (explode s);;

(* lexing with simplification *)
let rec lex_simp r s = match s with
    [] -> if (nullable r) then mkeps r else raise LexError
  | c::cs -> 
    let (r_simp, f_simp) = simp (der c r) in
    inj r c (f_simp (lex_simp r_simp cs));;

let lexing_simp r s = lex_simp r (explode s);;

let rec lex_simp2 r s = match s with
    [] -> if (nullable r) then mkeps r else raise LexError
  | c::cs -> 
    let (r_simp, f_simp) = der_simp c r in
    inj r c (f_simp (lex_simp2 r_simp cs));;

let lexing_simp2 r s = lex_simp2 r (explode s);;


(* lexing with accumulation *)
let rec lex_acc r s f = match s with
    [] -> if (nullable r) then f (mkeps r) else raise LexError
  | c::cs -> 
    let (r_simp, f_simp) = simp (der c r) in
    lex_acc r_simp cs (fun v -> f (inj r c (f_simp v)));;

let lexing_acc r s = lex_acc r (explode s) (f_id);;

let rec lex_acc2 r s f = match s with
    [] -> if (nullable r) then f (mkeps r) else raise LexError
  | c::cs -> 
    let (r_simp, f_simp) = der_simp c r in
    lex_acc2 r_simp cs (fun v -> f (inj r c (f_simp v)));;

let lexing_acc2 r s = lex_acc2 r (explode s) (f_id);;


(* Lexing rules for a small WHILE language *)
let sym = alts (List.map chr (explode "abcdefghijklmnopqrstuvwxyz"));;
let digit = alts (List.map chr (explode "0123456789"));;
let idents =  sym -- STAR(sym ++ digit);;
let nums = plus(digit);;
let keywords = alts 
   (List.map str ["skip"; "while"; "do"; "if"; "then"; "else"; "read"; "write"; "true"; "false"]);;
let semicolon = str ";"
let ops = alts 
   (List.map str [":="; "=="; "-"; "+"; "*"; "!="; "<"; ">"; "<="; ">="; "%"; "/"]);;
let whitespace = plus(str " " ++ str "\n" ++ str "\t");;
let rparen = str ")";;
let lparen = str "(";;
let begin_paren = str "{";;
let end_paren = str "}";;


let while_regs = STAR(("k" $ keywords) ++
                      ("i" $ idents) ++
                      ("o" $ ops) ++ 
                      ("n" $ nums) ++ 
                      ("s" $ semicolon) ++ 
                      ("p" $ (lparen ++ rparen)) ++ 
                      ("b" $ (begin_paren ++ end_paren)) ++ 
                      ("w" $ whitespace));;



(* Some Tests
  ============ *)

let time f x =
  let t = Sys.time() in
  let f_x = (f x; f x; f x) in
  (print_float ((Sys.time() -. t) /. 3.0); f_x);;


let prog0 = "read n";;

let prog1 = "read  n; write (n)";;
string_of_env (env (lexing_simp while_regs prog1));;


let prog2 = "
i := 2;
max := 100;
while i < max do {
  isprime := 1;
  j := 2;
  while (j * j) <= i + 1  do {
    if i % j == 0 then isprime := 0  else skip;
    j := j + 1
  };
  if isprime == 1 then write i else skip;
  i := i + 1
}";;

let tst1 = (lexing_simp while_regs prog2 = lexing_simp2 while_regs prog2) in
let tst2 = (lexing_simp while_regs prog2 = lexing_acc while_regs prog2) in
let tst3 = (lexing_simp while_regs prog2 = lexing_acc2 while_regs prog2)
in
  print_string ("Sanity test simp vs simp2: >>" ^ (string_of_bool tst1) ^ "<<\n") ;
  print_string ("Sanity test simp vs acc:   >>" ^ (string_of_bool tst2) ^ "<<\n") ;
  print_string ("Sanity test simp vs acc2:  >>" ^ (string_of_bool tst3) ^ "<<") ;
  print_newline ();;



type range = 
  To of int * int;;

let (---) i j = To(i, j);; 

let forby n =
  fun range -> match range with To(lo, up) ->
    (fun f -> 
       let rec loop lo = 
         if lo > up then () else (f lo; loop (lo + n))
       in loop lo);;

let step_simp i = 
  (print_string ((string_of_int i) ^ ": ") ;
   time (lexing_simp while_regs) (string_repeat prog2 i) ;
   print_newline ());;

let step_simp2 i = 
  (print_string ((string_of_int i) ^ ": ") ;
   time (lexing_simp2 while_regs) (string_repeat prog2 i) ;
   print_newline ());;

let step_acc i = 
  (print_string ((string_of_int i) ^ ": ") ;
   time (lexing_acc while_regs) (string_repeat prog2 i) ;
   print_newline ());;

let step_acc2 i = 
  (print_string ((string_of_int i) ^ ": ") ;
   time (lexing_acc2 while_regs) (string_repeat prog2 i) ;
   print_newline ());;

forby 100 (100 --- 700) step_simp;;
print_newline ();;
forby 100 (100 --- 700) step_simp2;;
print_newline ();;
forby 100 (100 --- 700) step_acc;;
print_newline ();;
forby 100 (100 --- 700) step_acc2;;
print_newline ();;
forby 1000 (1000 --- 5000) step_acc;;
print_newline ();;
forby 1000 (1000 --- 5000) step_acc2;;
(*print_newline ();;*)
(* forby 500 (100 --- 5000) step_simp;; *)

