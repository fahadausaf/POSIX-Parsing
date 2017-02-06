import System.Environment
import Data.List
import Text.Printf
import Control.Exception
import System.CPUTime
import Control.Parallel.Strategies
import Control.Monad

lim :: Int
lim = 1
-- lim = 10^6
 
time :: (Num t, NFData t) => t -> IO ()
time y = do
    start <- getCPUTime
    replicateM_ lim $ do
        x <- evaluate $ 1 + y
        rdeepseq x `seq` return ()
    end   <- getCPUTime
    let diff = (fromIntegral (end - start)) / (10^12)
    printf "%0.9f\n" (diff :: Double)
    return ()

data Rexp =
   ZERO 
 | ONE 
 | CHAR Char
 | ALT Rexp Rexp
 | SEQ Rexp Rexp 
 | STAR Rexp 
 | RECD String Rexp deriving (Eq, Show) 

data Value =
   Empty
 | Chr Char
 | Sequ Value Value
 | Lf Value
 | Rg Value
 | Stars [Value]
 | Rec String Value deriving (Eq, Show) 

string_repeat :: String -> Int -> String
string_repeat s n = concat (replicate n s)

sequ :: [Char] -> Rexp
sequ s = case s of
  [] -> ONE
  [c] -> CHAR c
  c:cs -> SEQ (CHAR c) (sequ cs)


str :: String -> Rexp
str s = sequ s

plus :: Rexp -> Rexp
plus r = SEQ r (STAR r)

(\/) :: Rexp -> Rexp -> Rexp 
r1 \/ r2 = ALT r1 r2

(~~) :: Rexp -> Rexp -> Rexp 
r1 ~~ r2 = SEQ r1 r2

($$) :: String -> Rexp -> Rexp 
x $$ r = RECD x r

alts :: [Rexp] -> Rexp
alts rs = case rs of
  [] -> ZERO
  [r] -> r
  r:rs -> foldl (ALT) r rs

size :: Rexp -> Int
size r = case r of
  ZERO -> 1
  ONE -> 1
  CHAR _ -> 1
  ALT r1 r2 -> 1 + (size r1) + (size r2)
  SEQ r1 r2 -> 1 + (size r1) + (size r2)
  STAR r -> 1 + (size r)
  RECD _ r -> 1 + (size r)

nullable :: Rexp -> Bool
nullable r = case r of
  ZERO -> False
  ONE -> True
  CHAR _ -> False
  ALT r1 r2 -> nullable(r1) || nullable(r2)
  SEQ r1 r2 -> nullable(r1) && nullable(r2)
  STAR _ -> True
  RECD _ r -> nullable(r)

der :: Char -> Rexp -> Rexp
der c r = case r of
  ZERO -> ZERO
  ONE -> ZERO
  CHAR d -> if c == d then ONE else ZERO
  ALT r1 r2 -> ALT (der c r1) (der c r2)
  SEQ r1 r2 -> 
      if nullable r1 then ALT (SEQ (der c r1) r2) (der c r2)
      else SEQ (der c r1) r2
  STAR r -> SEQ (der c r) (STAR r)
  RECD _ r -> der c r

ders :: [Char] -> Rexp -> Rexp
ders s r = case s of 
  [] -> r
  c:s -> ders s (der c r)

flatten :: Value -> String
flatten v = case v of 
  Empty -> ""
  Chr c -> [c]
  Lf v -> flatten v
  Rg v -> flatten v
  Sequ v1 v2 -> flatten v1 ++ flatten v2
  Stars vs -> concat (map flatten vs)
  Rec _ v -> flatten v

env :: Value -> [(String, String)]
env v = case v of 
  Empty -> []
  Chr c -> []
  Lf v -> env v
  Rg v -> env v
  Sequ v1 v2 -> env v1 ++ env v2
  Stars vs -> foldl (++) [] (map env vs)
  Rec x v -> (x, flatten v) : env v

string_of_pair :: (String, String) -> String
string_of_pair (x, s) = "(" ++ x ++ "," ++ s ++ ")"

string_of_env :: [(String, String)] -> String
string_of_env xs = intercalate "," (map string_of_pair xs)

mkeps :: Rexp -> Value
mkeps r = case r of 
  ONE -> Empty
  ALT r1 r2 -> 
      if nullable r1 then Lf (mkeps r1) else Rg (mkeps r2)
  SEQ r1 r2 -> Sequ (mkeps r1) (mkeps r2)
  STAR r -> Stars []
  RECD x r -> Rec x (mkeps r)

inj :: Rexp -> Char -> Value -> Value
inj r c v = case (r, v) of
  (STAR r, Sequ v1 (Stars vs)) -> Stars (inj r c v1 : vs)
  (SEQ r1 r2, Sequ v1 v2) -> Sequ (inj r1 c v1) v2
  (SEQ r1 r2, Lf (Sequ v1 v2)) -> Sequ (inj r1 c v1) v2
  (SEQ r1 r2, Rg v2) -> Sequ (mkeps r1) (inj r2 c v2)
  (ALT r1 r2, Lf v1) -> Lf (inj r1 c v1)
  (ALT r1 r2, Rg v2) -> Rg (inj r2 c v2)
  (CHAR d, Empty) -> Chr d 
  (RECD x r1, _) -> Rec x (inj r1 c v)

f_id :: Value -> Value
f_id v = v

f_right :: (Value -> Value) -> Value -> Value
f_right f = \v -> Rg (f v)

f_left :: (Value -> Value) -> Value -> Value
f_left f = \v -> Lf (f v)

f_alt :: (Value -> Value) -> (Value -> Value) -> Value -> Value
f_alt f1 f2 = \v -> case v of
  Rg v -> Rg (f2 v)
  Lf v -> Lf (f1 v)

f_seq :: (Value -> Value) -> (Value -> Value) -> Value -> Value
f_seq f1 f2 = \v -> case v of 
  Sequ v1 v2 -> Sequ (f1 v1) (f2 v2)

f_seq_void1 :: (Value -> Value) -> (Value -> Value) -> Value -> Value
f_seq_void1 f1 f2 = \v -> Sequ (f1 Empty) (f2 v)

f_seq_void2 :: (Value -> Value) -> (Value -> Value) -> Value -> Value
f_seq_void2 f1 f2 = \v -> Sequ(f1 v) (f2 Empty)

f_rec :: (Value -> Value) -> Value -> Value
f_rec f = \v -> case v of
    Rec x v -> Rec x (f v)

simp :: Rexp -> (Rexp, Value -> Value)
simp r = case r of
    ALT r1 r2 -> 
      let (r1s, f1s) = simp r1  
          (r2s, f2s) = simp r2 
      in
        (case (r1s, r2s) of
            (ZERO, _) -> (r2s, f_right f2s)
            (_, ZERO) -> (r1s, f_left f1s)
            (_, _)    -> if r1s == r2s then (r1s, f_left f1s)
                         else (ALT r1s r2s, f_alt f1s f2s))
    SEQ r1 r2 -> 
      let (r1s, f1s) = simp r1 
          (r2s, f2s) = simp r2 
      in
        (case (r1s, r2s) of
          (ZERO, _)  -> (ZERO, f_right f2s)
          (_, ZERO)  -> (ZERO, f_left f1s)
          (ONE, _) -> (r2s, f_seq_void1 f1s f2s)
          (_, ONE) -> (r1s, f_seq_void2 f1s f2s)
          (_, _)     -> (SEQ r1s r2s, f_seq f1s f2s))
    RECD x r1 -> 
      let (r1s, f1s) = simp r1 
      in
        (RECD x r1s, f_rec f1s)
    r -> (r, f_id)

der_simp :: Char -> Rexp -> (Rexp, Value -> Value)
der_simp c r = case r of
    ZERO -> (ZERO, f_id)
    ONE -> (ZERO, f_id)
    CHAR(d) -> ((if c == d then ONE else ZERO), f_id)
    ALT r1 r2 -> 
      let (r1d, f1d) = der_simp c r1
          (r2d, f2d) = der_simp c r2 
      in
        (case (r1d, r2d) of 
          (ZERO, _) -> (r2d, f_right f2d)
          (_, ZERO) -> (r1d, f_left f1d)
          (_, _)    -> if r1d == r2d then (r1d, f_left f1d)
                       else (ALT r1d r2d, f_alt f1d f2d))
    SEQ r1 r2 -> 
      if nullable r1 
      then 
        let (r1d, f1d) = der_simp c r1 
            (r2d, f2d) = der_simp c r2 
            (r2s, f2s) = simp r2 
        in
          (case (r1d, r2s, r2d) of
             (ZERO, _, _)  -> (r2d, f_right f2d)
             (_, ZERO, _)  -> (r2d, f_right f2d)
             (_, _, ZERO)  -> (SEQ r1d r2s, f_left (f_seq f1d f2s))
             (ONE, _, _) -> (ALT r2s r2d, f_alt (f_seq_void1 f1d f2s) f2d)
             (_, ONE, _) -> (ALT r1d r2d, f_alt (f_seq_void2 f1d f2s) f2d)
             (_, _, _)     -> (ALT (SEQ r1d r2s) r2d, f_alt (f_seq f1d f2s) f2d))
      else 
        let (r1d, f1d) = der_simp c r1 
            (r2s, f2s) = simp r2 
        in
          (case (r1d, r2s) of
             (ZERO, _)  -> (ZERO, f_id)
             (_, ZERO)  -> (ZERO, f_id)
             (ONE, _) -> (r2s, f_seq_void1 f1d f2s)
             (_, ONE) -> (r1d, f_seq_void2 f1d f2s)
             (_, _) -> (SEQ r1d r2s, f_seq f1d f2s))	  
    STAR r1 -> 
      let (r1d, f1d) = der_simp c r1 
      in
        (case r1d of
           ZERO -> (ZERO, f_id)
           ONE -> (STAR r1, f_seq_void1 f1d f_id)
           _ -> (SEQ r1d (STAR r1), f_seq f1d f_id))
    RECD x r1 -> der_simp c r1 



matcher :: Rexp -> String -> Bool
matcher r s = nullable (ders s r)

lex0 :: Rexp -> String -> Maybe Value
lex0 r s = case s of 
  [] -> if (nullable r) 
        then Just (mkeps r) 
        else Nothing
  c:cs -> do res <- lex0 (der c r) cs
             return (inj r c res)

lex_simp :: Rexp -> String -> Maybe Value
lex_simp r s = case s of 
  [] -> if (nullable r) 
        then Just (mkeps r) 
        else Nothing
  c:cs -> let 
            (r_simp, f_simp) = simp (der c r)
          in
             do 
               res <- lex_simp r_simp cs
               return (inj r c (f_simp res))

lex_simp2 :: Rexp -> String -> Maybe Value
lex_simp2 r s = case s of 
  [] -> if (nullable r) 
        then Just (mkeps r) 
        else Nothing
  c:cs -> let 
            (r_simp, f_simp) = der_simp c r
          in
             do 
               res <- lex_simp2 r_simp cs
               return (inj r c (f_simp res))

lex_acc :: Rexp -> String -> (Value -> Value) -> Maybe Value
lex_acc r s f = case s of 
  [] -> if (nullable r) 
        then Just (f (mkeps r)) 
        else Nothing
  c:cs -> let 
            (r_simp, f_simp) = simp (der c r)
          in
            lex_acc r_simp cs (\v -> f (inj r c (f_simp v)))

lex_acc2 :: Rexp -> String -> (Value -> Value) -> Maybe Value
lex_acc2 r s f = case s of 
  [] -> if (nullable r) 
        then Just (f (mkeps r)) 
        else Nothing
  c:cs -> let 
            (r_simp, f_simp) = der_simp c r
          in
            lex_acc2 r_simp cs (\v -> f (inj r c (f_simp v)))

sym = alts (map CHAR "abcdefghijklmnopqrstuvwxyz")
digit = alts (map CHAR "0123456789")
idents =  sym ~~ STAR(sym \/ digit)
nums = plus digit
keywords = alts (map str ["skip", "while", "do", "if", "then", "else", "read", "write", "true", "false"])
semicolon = str ";"
ops = alts (map str [":=", "==", "-", "+", "*", "!=", "<", ">", "<=", ">=", "%", "/"])
whitespace = plus(str " " \/ str "\n" \/ str "\t")
rparen = str ")"
lparen = str "("
begin_paren = str "{"
end_paren = str "}"

while_regs = STAR(("k" $$ keywords) \/
                  ("i" $$ idents) \/
                  ("o" $$ ops) \/ 
                  ("n" $$ nums) \/ 
                  ("s" $$ semicolon) \/ 
                  ("p" $$ (lparen \/ rparen)) \/ 
                  ("b" $$ (begin_paren \/ end_paren)) \/ 
                  ("w" $$ whitespace))

prog2 = intercalate "\n" 
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
   "}"]


lexing_simp :: Int -> Int
lexing_simp n = case (lex_simp while_regs (string_repeat prog2 n)) of
  Just result -> 1
  Nothing -> 0

step_simp :: Int -> IO ()
step_simp n = do 
           putStr (show n ++ ": ") 
           time (lexing_simp n)

lexing_simp2 :: Int -> Int
lexing_simp2 n = case (lex_simp2 while_regs (string_repeat prog2 n)) of
  Just result -> 1
  Nothing -> 0

step_simp2 :: Int -> IO ()
step_simp2 n = do 
           putStr (show n ++ ": ") 
           time (lexing_simp2 n)

lexing_acc :: Int -> Int
lexing_acc n = case (lex_acc while_regs (string_repeat prog2 n) f_id) of
  Just result -> 1
  Nothing -> 0

step_acc :: Int -> IO ()
step_acc n = do 
           putStr (show n ++ ": ") 
           time (lexing_acc n)

lexing_acc2 :: Int -> Int
lexing_acc2 n = case (lex_acc2 while_regs (string_repeat prog2 n) f_id) of
  Just result -> 1
  Nothing -> 0

step_acc2 :: Int -> IO ()
step_acc2 n = do 
           putStr (show n ++ ": ") 
           time (lexing_acc2 n)

main :: IO ()
main = do
        forM_  [1000,2000..5000] step_simp
        printf "\n"
        forM_  [1000,2000..5000] step_simp2
        printf "\n"
        forM_  [1000,2000..5000] step_acc
        printf "\n"
        forM_  [1000,2000..5000] step_acc2