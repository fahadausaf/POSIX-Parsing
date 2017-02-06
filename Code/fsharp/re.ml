
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

(* some helper functions for strings *)   
let explode s = [for c in s -> c];;

let string_repeat s n =  String.replicate n s;;

(* some helper functions for rexps *)
let rec seq s = match s with
  | [] -> ONE
  | [c] -> CHAR(c)
  | c::cs -> SEQ(CHAR(c), seq cs);;

let chr c = CHAR(c)

let str s = seq(explode s);;

let plus r = SEQ(r, STAR(r));;

let (++) r1 r2 = ALT(r1, r2);;

let (--) r1 r2 = SEQ(r1, r2);;

let ($) x r = RECD(x, r);;

let alts rs = match rs with 
  | [] -> ZERO
  | [r] -> r
  | r::rs -> List.fold (++) r rs;;


(* size of a regular expressions - for testing purposes *)
let rec size r = match r with
  | ZERO -> 1
  | ONE -> 1
  | CHAR(_) -> 1
  | ALT(r1, r2) -> 1 + (size r1) + (size r2)
  | SEQ(r1, r2) -> 1 + (size r1) + (size r2)
  | STAR(r) -> 1 + (size r)
  | RECD(_, r) -> 1 + (size r);;

(* nullable function: tests whether the regular 
   expression can recognise the empty string *)
let rec nullable r = match r with
  | ZERO -> false
  | ONE -> true
  | CHAR(_) -> false
  | ALT(r1, r2) -> nullable(r1) || nullable(r2)
  | SEQ(r1, r2) -> nullable(r1) && nullable(r2)
  | STAR(_) -> true
  | RECD(_, r) -> nullable(r);;

(* derivative of a regular expression r w.r.t. a character c *)
let rec der c r = match r with 
  | ZERO -> ZERO
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
  | [] -> r
  | c::s -> ders s (der c r);;

(* extracts a string from value *)
let rec flatten v = match v with 
  | Empty -> ""
  | Chr(c) -> System.Convert.ToString(c)
  | Left(v) -> flatten v
  | Right(v) -> flatten v
  | Sequ(v1, v2) -> flatten v1 ^ flatten v2
  | Stars(vs) -> String.concat "" (List.map flatten vs)
  | Rec(_, v) -> flatten v;;


(* extracts an environment from a value *)
let rec env v = match v with
  | Empty -> []
  | Chr(c) -> []
  | Left(v) -> env v
  | Right(v) -> env v
  | Sequ(v1, v2) -> env v1 @ env v2
  | Stars(vs) -> List.fold (@) [] (List.map env vs)
  | Rec(x, v) -> (x, flatten v) :: env v;;

let string_of_pair (x, s) = "(" ^ x ^ "," ^ s ^ ")";;
let string_of_env xs = String.concat "," (List.map string_of_pair xs);;


(* the value for a nullable rexp *)
let rec mkeps r = match r with
  | ONE -> Empty
  | ALT(r1, r2) -> 
      if nullable r1 then Left(mkeps r1) else Right(mkeps r2)
  | SEQ(r1, r2) -> Sequ(mkeps r1, mkeps r2)
  | STAR(r) -> Stars([])
  | RECD(x, r) -> Rec(x, mkeps r);;


(* injection of a char into a value *)
let rec inj r c v = match r, v with
  | STAR(r), Sequ(v1, Stars(vs)) -> Stars(inj r c v1 :: vs)
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
          ZERO, _  -> (ZERO, f_right f2s)
        | _, ZERO  -> (ZERO, f_left f1s)
        | ONE, _ -> (r2s, f_seq_Empty1 f1s f2s)
        | _, ONE -> (r1s, f_seq_Empty2 f1s f2s)
        | _, _     -> (SEQ(r1s, r2s), f_seq f1s f2s))
  | RECD(x, r1) -> 
      let (r1s, f1s) = simp r1 in
      (RECD(x, r1s), f_rec f1s)
  | r -> (r, f_id)
;;

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




(* Lexing rules for a small WHILE language *)
let sym = alts (List.map chr (explode "abcdefghijklmnopqrstuvwxyz"));;
let digit = alts (List.map chr (explode "0123456789"));;
let idents =  sym -- STAR(sym ++ digit);;
let nums = plus(digit);;
let keywords = alts (List.map str ["skip"; "while"; "do"; "if"; "then"; "else"; "read"; "write"; "true"; "false"]);;
let semicolon = str ";"
let ops = alts (List.map str [":="; "=="; "-"; "+"; "*"; "!="; "<"; ">"; "<="; ">="; "%"; "/"]);;
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
  let t = System.DateTime.Now in
  let f_x = f x in
  (printfn "%O" (System.DateTime.Now - t); f_x);;

let prog0 = "read n";;
string_of_env (env (lexing while_regs prog0));;

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

for i = 1 to 100 do
  printf "%i: " i ;
  time (lexing_simp while_regs) (string_repeat prog2 i);
done;;

