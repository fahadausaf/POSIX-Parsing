import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp

abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
case class Rec(x: String, v: Val) extends Val
   
// some convenience for typing in regular expressions
def charlist2rexp(s : List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s : String) : Rexp = charlist2rexp(s.toList)

implicit def RexpOps(r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps(s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
  def $ (r: Rexp) = RECD(s, r)
}

def pretty(r: Rexp) : String = r match {
  case ZERO => "0"
  case ONE => "e"
  case CHAR(c) => c.toString 
  case ALT(r1, r2) => "(" ++ pretty(r1) ++ " | " + pretty(r2) ++ ")"
  case SEQ(r1, r2) => pretty(r1) ++ pretty(r2)
  case STAR(r) => "(" ++ pretty(r) ++ ")*"
  case RECD(x, r) => "(" ++ x ++ " : " ++ pretty(r) ++ ")"
}

def vpretty(v: Val) : String = v match {
  case Empty => "()"
  case Chr(c) => c.toString
  case Left(v) => "Left(" ++ vpretty(v) ++ ")"
  case Right(v) => "Right(" ++ vpretty(v) ++ ")"
  case Sequ(v1, v2) => vpretty(v1) ++ " ~ " ++ vpretty(v2)
  case Stars(vs) => vs.flatMap(vpretty).mkString("[", ",", "]")
  case Rec(x, v) => "(" ++ x ++ ":" ++ vpretty(v) ++ ")"
}


// size of a regular expressions - for testing purposes 
def size(r: Rexp) : Int = r match {
  case ZERO => 1
  case ONE => 1
  case CHAR(_) => 1
  case ALT(r1, r2) => 1 + size(r1) + size(r2)
  case SEQ(r1, r2) => 1 + size(r1) + size(r2)
  case STAR(r) => 1 + size(r)
  case RECD(_, r) => 1 + size(r)
}

// extracts a set of candidate values from a "non-starred" regular expression
def values(r: Rexp) : Set[Val] = r match {
  case ZERO => Set()
  case ONE => Set(Empty)
  case CHAR(c) => Set(Chr(c))
  case ALT(r1, r2) => (for (v1 <- values(r1)) yield Left(v1)) ++ 
                      (for (v2 <- values(r2)) yield Right(v2))
  case SEQ(r1, r2) => for (v1 <- values(r1); v2 <- values(r2)) yield Sequ(v1, v2)
  case STAR(r) => Set(Empty) ++ values(r)   // to do more would cause the set to be infinite
  case RECD(_, r) => values(r)
}

// zeroable function: tests whether the regular 
// expression cannot regognise any string
def zeroable (r: Rexp) : Boolean = r match {
  case ZERO => true
  case ONE => false
  case CHAR(_) => false
  case ALT(r1, r2) => zeroable(r1) && zeroable(r2)
  case SEQ(r1, r2) => zeroable(r1) || zeroable(r2)
  case STAR(_) => false
  case RECD(_, r1) => zeroable(r1)
}


// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case RECD(_, r1) => nullable(r1)
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r) => SEQ(der(c, r), STAR(r))
  case RECD(_, r1) => der(c, r1)
}

// derivative w.r.t. a string (iterates der)
def ders (s: List[Char], r: Rexp) : Rexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
  case Rec(_, v) => flatten(v)
}

def flattens(v: Val) : List[String] = v match {
  case Empty => List("")
  case Chr(c) => List(c.toString)
  case Left(v) => flattens(v)
  case Right(v) => flattens(v)
  case Sequ(v1, v2) => flattens(v1) ::: flattens(v2)
  case Stars(vs) => vs.flatMap(flattens)
  case Rec(_, v) => flattens(v)
}


// extracts an environment from a value
def env(v: Val) : List[(String, String)] = v match {
  case Empty => Nil
  case Chr(c) => Nil
  case Left(v) => env(v)
  case Right(v) => env(v)
  case Sequ(v1, v2) => env(v1) ::: env(v2)
  case Stars(vs) => vs.flatMap(env)
  case Rec(x, v) => (x, flatten(v))::env(v)
}

// injection part
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => Rec(x, mkeps(r))
}


def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(d) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}

def prj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(prj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => 
    if (flatten(v1) == "") Right(prj(r2, c, v2))      
    else { if (nullable(r1)) Left(Sequ(prj(r1, c, v1), v2))
           else Sequ(prj(r1, c, v1), v2)
    }
  case (ALT(r1, r2), Left(v1)) => Left(prj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(prj(r2, c, v2))
  case (CHAR(d), _) => Empty 
  case (RECD(x, r1), _) => Rec(x, prj(r1, c, v))
}


// main lexing function (produces a value)
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)



// some "rectification" functions for simplification
def F_ID(v: Val): Val = v
def F_RIGHT(f: Val => Val) = (v:Val) => Right(f(v))
def F_LEFT(f: Val => Val) = (v:Val) => Left(f(v))
def F_ALT(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Right(v) => Right(f2(v))
  case Left(v) => Left(f1(v))
}
def F_SEQ(f1: Val => Val, f2: Val => Val) = (v:Val) => v match {
  case Sequ(v1, v2) => Sequ(f1(v1), f2(v2))
}
def F_SEQ_Empty1(f1: Val => Val, f2: Val => Val) = (v:Val) => Sequ(f1(Empty), f2(v))
def F_SEQ_Empty2(f1: Val => Val, f2: Val => Val) = (v:Val) => Sequ(f1(v), f2(Empty))
def F_RECD(f: Val => Val) = (v:Val) => v match {
  case Rec(x, v) => Rec(x, f(v))
}
def F_ERROR(v: Val): Val = throw new Exception("error")

// simplification of regular expressions returning also an
// rectification function; no simplification under STAR 
def simp(r: Rexp): (Rexp, Val => Val) = r match {
  case ALT(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (r2s, F_RIGHT(f2s))
      case (_, ZERO) => (r1s, F_LEFT(f1s))
      case _ => if (r1s == r2s) (r1s, F_LEFT(f1s))
                else (ALT (r1s, r2s), F_ALT(f1s, f2s)) 
    }
  }
  case SEQ(r1, r2) => {
    val (r1s, f1s) = simp(r1)
    val (r2s, f2s) = simp(r2)
    (r1s, r2s) match {
      case (ZERO, _) => (ZERO, F_ERROR)
      case (_, ZERO) => (ZERO, F_ERROR)
      case (ONE, _) => (r2s, F_SEQ_Empty1(f1s, f2s))
      case (_, ONE) => (r1s, F_SEQ_Empty2(f1s, f2s))
      case _ => (SEQ(r1s,r2s), F_SEQ(f1s, f2s))
    }
  }
  case RECD(x, r1) => {
    val (r1s, f1s) = simp(r1)
    (RECD(x, r1s), F_RECD(f1s))
  }
  case r => (r, F_ID)
}

def lex_simp(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => {
    val (r_simp, f_simp) = simp(der(c, r))
    inj(r, c, f_simp(lex_simp(r_simp, cs)))
  }
}

def lexing_simp(r: Rexp, s: String) : Val = lex_simp(r, s.toList)

lexing(("a" | "ab") ~ ("b" | ""), "ab")
lexing_simp(("a" | "ab") ~ ("b" | ""), "ab")



// brute force search infrastructure

// enumerates regular expressions until a certain depth
def enum(n: Int, s: String) : Set[Rexp] = n match {
  case 0 => Set(ZERO, ONE) ++ s.toSet.map(CHAR)
  case n => {
    val rs = enum(n - 1, s)
    rs ++
    (for (r1 <- rs; r2 <- rs) yield ALT(r1, r2)) ++
    (for (r1 <- rs; r2 <- rs) yield SEQ(r1, r2))
  }
}

def ordr(v1: Val, r: Rexp, v2: Val) : Boolean = (v1, r, v2) match {
  case (Empty, ONE, Empty) => true
  case (Chr(c1), CHAR(c2), Chr(c3)) if (c1 == c2 && c1 == c3) => true
  case (Left(v1), ALT(r1, r2), Left(v2)) => ordr(v1, r1, v2)
  case (Right(v1), ALT(r1, r2), Right(v2)) => ordr(v1, r2, v2)
  case (Left(v1), ALT(r1, r2), Right(v2)) => flatten(v2).length <= flatten(v1).length
  case (Right(v1), ALT(r1, r2), Left(v2)) => flatten(v2).length < flatten(v1).length
  case (Sequ(v1, v2), SEQ(r1, r2), Sequ(v3, v4)) if (v1 == v3) => ordr(v2, r2, v4)
  case (Sequ(v1, v2), SEQ(r1, r2), Sequ(v3, v4)) if (v1 != v3) => ordr(v1, r1, v3)
  case _ => false
}     

def ord(v1: Val, v2: Val) : Boolean = (v1, v2) match {
  case (Empty, Empty) => true
  case (Chr(c1), Chr(c2)) if (c1 == c2) => true
  case (Left(v1), Left(v2)) => ord(v1, v2)
  case (Right(v1), Right(v2)) => ord(v1, v2)
  case (Left(v1), Right(v2)) => flatten(v2).length <= flatten(v1).length
  case (Right(v1), Left(v2)) => flatten(v2).length < flatten(v1).length
  case (Sequ(v1, v2), Sequ(v3, v4)) if (v1 == v3) => ord(v2, v4)
  case (Sequ(v1, v2), Sequ(v3, v4)) if (v1 != v3) => ord(v1, v3)
  case _ => false
}     

// exhaustively tests values of a regular expression
def vfilter1(f: Rexp => Val => Boolean)(r: Rexp) : Set[(Rexp, Val)] = {
  val vs = values(r)
  for (v <- vs; if (f(r)(v))) yield (r, v)
}

def vfilter2(f: Rexp => Val => Val => Boolean)(r: Rexp) : Set[(Rexp, Val, Val)] = {
  val vs = values(r)
  for (v1 <- vs; v2 <- vs; if (f(r)(v1)(v2))) yield (r, v1, v2)
}

def vfilter3(f: Rexp => Val => Val => Val => Boolean)(r: Rexp) : Set[(Rexp, Val, Val, Val)] = {
  val vs = values(r)
  for (v1 <- vs; v2 <- vs; v3 <- vs; if (f(r)(v1)(v2)(v3))) yield (r, v1, v2, v3)
}

// number of test cases
enum(3, "a").size
enum(2, "ab").size
enum(2, "abc").size
//enum(3, "ab").size

// test for inj/prj
def injprj_test(r:Rexp)(v:Val) : Boolean =
  if (flatten(v) != "") (inj(r, 'a', prj(r, 'a', v)) != v) else false

val injprj_tst = enum(2, "ab").flatMap(vfilter1(injprj_test))
val injprj_smallest = injprj_tst.toList.sortWith { (x,y) => size(x._1) < size(y._1) }.head

prj(CHAR('b'), 'a', Chr('b'))
inj(CHAR('b'), 'a', Empty)

prj(SEQ(ALT(ONE,ONE),CHAR('a')), 'a', Sequ(Right(Empty),Chr('a')))
inj(SEQ(ALT(ONE,ONE),CHAR('a')), 'a', Right(Empty))

// tests for totality
def totality_test(r: Rexp)(v1: Val)(v2: Val) : Boolean =
  !(ord(v1, v2) || ord(v2, v1))

enum(2, "ab").flatMap(vfilter2(totality_test))
enum(3, "a").flatMap(vfilter2(totality_test))


//tests for transitivity (simple transitivity fails)
def transitivity_test(r: Rexp)(v1: Val)(v2: Val)(v3: Val) : Boolean = 
  ord(v1, v2) && ord(v2, v3) && !ord(v1, v3)

val test0 = enum(3, "a").flatMap(vfilter3(transitivity_test))
val test0_smallest = test0.toList.sortWith { (x,y) => size(x._1) < size(y._1) }.head

pretty(test0_smallest._1)
vpretty(test0_smallest._2)
vpretty(test0_smallest._3)
vpretty(test0_smallest._4)

/* Counter example for simple transitivity:

 r = a | ((a | a)(a | e))

 v1 = Left(a)
 v2 = Right(Left(a) ~ Right(()))
 v3 = Right(Right(a) ~ Left(a))

*/ 

def is_seq(v: Val) : Boolean = v match {
  case Seq(_, _) => true
  case _ => false
}

def transitivity_test_extended(r: Rexp)(v1: Val)(v2: Val)(v3: Val) : Boolean = {
  //flatten(v1).size >= flatten(v2).size && 
  //flatten(v2).size >= flatten(v3).size && 
  is_seq(v1) &&
  ord(v1, v2) && ord(v2, v3) && !ord(v1, v3)
}

// smallest(?) example where simple transitivity fails 
val test1 = enum(3, "a").flatMap(vfilter3(transitivity_test_extended))
val test1_smallest = test1.toList.sortWith { (x,y) => size(x._1) < size(y._1) }.head

pretty(test1_smallest._1)
vpretty(test1_smallest._2)
vpretty(test1_smallest._3)
vpretty(test1_smallest._4)

ord(test1_smallest._2, test1_smallest._3)
ord(test1_smallest._3, test1_smallest._4)
ord(test1_smallest._2, test1_smallest._4)
ordr(test1_smallest._3, test1_smallest._1, test1_smallest._4)

/* Counter example for extended transitivity:

 r = ((e | e)(e | a)) | a

 v1 = Left(Right(()) ~ Right(a))
 v2 = Right(a)
 v3 = Left(Left(()) ~ Left(()))

*/ 


// with flatten test
enum(3, "a").flatMap(vfilter3(transitivity_test_extended))

//injection tests
def injection_test(r: Rexp)(c: Char)(v1: Val)(v2: Val) : Boolean = {
  v1 != v2 && 
  ord(v1, v2) && 
  ord(inj(r, c, v2), inj(r, c, v1)) && 
  flatten(v1) == flatten(v2)
}

def injection_testA(r: Rexp)(c: Char)(v1: Val)(v2: Val) : Boolean = {
  v1 != v2 && 
  ord(v1, v2) && 
  ord(inj(r, c, v2), inj(r, c, v1)) && 
  flatten(v1).length == flatten(v2).length
}

def injection_test2(r: Rexp)(c: Char)(v1: Val)(v2: Val) : Boolean = {
  v1 != v2 && 
  ord(v1, v2) && 
  ord(inj(r, c, v2), inj(r, c, v1))
}
def vfilter4(f: Rexp => Char => Val => Val => Boolean)(c: Char)(r: Rexp) : Set[(Rexp, Rexp, Val, Val)] = {
  val r_der = der(c, r)
  val vs = values(r_der)
  for (v1 <- vs; v2 <- vs; if (f(r)(c)(v1)(v2))) yield (r, r_der, v1, v2)
} 

enum(3, "a").flatMap(vfilter4(injection_test)('a'))
enum(3, "a").flatMap(vfilter4(injection_testA)('a'))

val test2 = enum(3, "a").flatMap(vfilter4(injection_test2)('a'))
val test2_smallest = test2.toList.sortWith { (x,y) => size(x._1) < size(y._1) }.head

pretty(test2_smallest._1)
pretty(test2_smallest._2)
vpretty(test2_smallest._3)
vpretty(test2_smallest._4)
vpretty(inj(test2_smallest._1, 'a', test2_smallest._3))
vpretty(inj(test2_smallest._1, 'a', test2_smallest._4))

// Lexing Rules for a Small While Language

def PLUS(r: Rexp) = r ~ r.%
val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = PLUS(DIGIT)
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUS(" " | "\n" | "\t")
val RPAREN: Rexp = ")"
val LPAREN: Rexp = "("
val BEGIN: Rexp = "{"
val END: Rexp = "}"
val STRING: Rexp = "\"" ~ SYM.% ~ "\""


val WHILE_REGS = (("k" $ KEYWORD) | 
                  ("i" $ ID) | 
                  ("o" $ OP) | 
                  ("n" $ NUM) | 
                  ("s" $ SEMI) | 
                  ("str" $ STRING) |
                  ("p" $ (LPAREN | RPAREN)) | 
                  ("b" $ (BEGIN | END)) | 
                  ("w" $ WHITESPACE)).%

/*
val WHILE_REGS = (KEYWORD | 
                  ID | 
                  OP | 
                  NUM | 
                  SEMI | 
                  LPAREN | RPAREN | 
                  BEGIN | END | 
                  WHITESPACE).%
*/

// Some Tests
//============

def time[T](code: => T) = {
  val start = System.nanoTime()
  val result = code
  val end = System.nanoTime()
  println((end - start)/1.0e9)
  result
}

val r1 = ("a" | "ab") ~ ("bcd" | "c")
println(lexing(r1, "abcd"))
println(values(r1).mkString("\n"))
println(values(r1).map(flatten).mkString("\n"))

val r2 = ("" | "a") ~ ("ab" | "b")
println(lexing(r2, "ab"))
println(values(r2).mkString("\n"))
println(values(r2).toList.map(flatten).mkString("\n"))

//Some experiments
//================

val f0 = ("ab" | "b" | "cb")
val f1 = der('a', f0)
val f2 = der('b', f1)
val g2 = mkeps(f2)
val g1 = inj(f1, 'b', g2)
val g0 = inj(f0, 'a', g1)

lex((("" | "a") ~ ("ab" | "b")), "ab".toList)
lex((("" | "a") ~ ("b" | "ab")), "ab".toList)
lex((("" | "a") ~ ("c" | "ab")), "ab".toList)

val reg0 = ("" | "a") ~ ("ab" | "b")
val reg1 = der('a', reg0)
val reg2 = der('b', reg1)
println(List(reg0, reg1, reg2).map(pretty).mkString("\n"))
println(lexing(reg0, "ab"))

val val0 = values(reg0)
val val1 = values(reg1)
val val2 = values(reg2)


// Two Simple Tests
//===================
println("prog0 test")

val prog0 = """read n"""
println(env(lexing_simp(WHILE_REGS, prog0)))

println("prog1 test")

val prog1 = """read  n; write (n)"""
println(env(lexing_simp(WHILE_REGS, prog1)))


// Big Test
//==========
/*
val prog2 = """
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
}"""
*/
val prog2 = """
write "fib";
read n;
minus1 := 0;
minus2 := 1;
while n > 0 do {
  temp := minus2;
  minus2 := minus1 + minus2;
  minus1 := temp;
  n := n - 1
};
write "result";
write minus2
"""

println("Tokens")
println(env(lexing_simp(WHILE_REGS, prog2)))

for (i <- 1 to 80) {
  print(i.toString + ":  ")
  time(lexing_simp(WHILE_REGS, prog2 * i))
}


val a0 = (ONE | "a") ~ (ONE | "ab")
val a1 = der('a', a0)
pretty(a1)
val m = mkeps(a1)
vpretty(m)
val v = inj(a0, 'a', m)
vpretty(v)

val a0 = (ONE | "a") ~ (ONE | "ab")
val a1 = der('a', a0)
pretty(a1)
values(a1).toList
val List(u2,_,u1) = values(a1).toList
vpretty(u1)
vpretty(u2)
vpretty(inj(a0,'a',u1))
vpretty(inj(a0,'a',u2))

lexing(a0, "ab")
val aa = der('a', a0)
pretty(aa)
val ab = der('b', aa)
pretty(ab)
nullable(ab)
val m = mkeps(ab)
vpretty(m)
val vb = inj(aa, 'b', m)
vpretty(vb)
val va = inj(a0, 'a', vb)
vpretty(va)


/* ord is not transitive in general: counter-example
 *
 * (1)  Left(Right(Right(())))
 * (2)  Right(Left(()) ~ Left(()))
 * (3)  Right(Right(()) ~ Right(a))
 *
 * (1) > (2); (2) > (3) but not (1) > (3)
*/
