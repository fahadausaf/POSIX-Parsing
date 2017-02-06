import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   
import scala.io.Source

abstract class Rexp 
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp
case class CRANGE(cs: String) extends Rexp
case class PLUS(r: Rexp) extends Rexp
case class OPT(r: Rexp) extends Rexp
case class NTIMES(r: Rexp, n: Int) extends Rexp

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

def Alts(rs: List[Rexp]) : Rexp = rs match {
  case Nil => ZERO
  case r::Nil => r
  case r::rs => ALT(r, Alts(rs))
}
def ALTS(rs: Rexp*) = Alts(rs.toList)

def Seqs(rs: List[Rexp]) : Rexp = rs match {
  case Nil => ONE
  case r::Nil => r
  case r::rs => SEQ(r, Seqs(rs))
}
def SEQS(rs: Rexp*) = Seqs(rs.toList)


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
  case CRANGE(_) => false
  case PLUS(r) => nullable(r)
  case OPT(_) => true
  case NTIMES(r, n) => if (n == 0) true else nullable(r)
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
  case CRANGE(cs) => if (cs.contains(c)) ONE else ZERO
  case PLUS(r) => SEQ(der(c, r), STAR(r))
  case OPT(r) => ALT(der(c, r), ZERO)
  case NTIMES(r, n) => if (n == 0) ZERO else der(c, SEQ(r, NTIMES(r, n - 1)))
}

// derivative w.r.t. a string (iterates der)
@tailrec
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
  case Stars(vs) => vs.map(flatten(_)).mkString
  case Rec(_, v) => flatten(v)
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
  case PLUS(r) => Stars(List(mkeps(r)))
  case OPT(_) => Right(Empty)
  case NTIMES(r, n) => if (n == 0) Stars(Nil) else Stars(Nil.padTo(n, mkeps(r)))
}


def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
  case (CRANGE(_), Empty) => Chr(c) 
  case (PLUS(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (OPT(r), Left(v1)) => Left(inj(r, c, v1))
  case (NTIMES(r, n), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (NTIMES(r, n), Left(Sequ(v1, Stars(vs)))) => Stars(inj(r, c, v1)::vs)
  case (NTIMES(r, n), Right(Stars(v::vs))) => Stars(mkeps(r)::inj(r, c, v)::vs)
}

// main unsimplified lexing function (produces a value)
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


// Some Tests
//============

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


val r0 = ("a" | "ab") ~ ("b" | "")
println(lexing(r0, "ab"))
println(lexing_simp(r0, "ab"))

val r1 = ("a" | "ab") ~ ("bcd" | "cd")
println(lexing_simp(r1, "abcd"))

println(lexing_simp((("" | "a") ~ ("ab" | "b")), "ab"))
println(lexing_simp((("" | "a") ~ ("b" | "ab")), "ab"))
println(lexing_simp((("" | "a") ~ ("c" | "ab")), "ab"))



// Two Simple Tests for the While Language
//========================================

// Lexing Rules 

def PLUSs(r: Rexp) = r ~ r.%
val SYM = "a" | "b" | "c" | "d" | "e" | "f" | "g" | "h" | "i" | "j" | "k" | "l" | "m" | "n" | "o" | "p" | "q" | "r" | "s" | "t" | "u" | "v" | "w" | "x" | "y" | "z"
val DIGIT = "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
val ID = SYM ~ (SYM | DIGIT).% 
val NUM = PLUSs(DIGIT)
val KEYWORD : Rexp = "skip" | "while" | "do" | "if" | "then" | "else" | "read" | "write" | "true" | "false"
val SEMI: Rexp = ";"
val OP: Rexp = ":=" | "==" | "-" | "+" | "*" | "!=" | "<" | ">" | "<=" | ">=" | "%" | "/"
val WHITESPACE = PLUSs(" " | "\n" | "\t")
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


println("prog0 test")

val prog0 = """read n"""
println(env(lexing_simp(WHILE_REGS, prog0)))

println("prog1 test")

val prog1 = """read  n; write (n)"""
println(env(lexing_simp(WHILE_REGS, prog1)))


// Bigger Test
//=============
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

println("prog2 test - tokens")
println(env(lexing_simp(WHILE_REGS, prog2)))


val prog3 = """
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

println("prog3 test - tokens")
println(env(lexing_simp(WHILE_REGS, prog3)))

/*
for (i <- 1 to 80) {
  print(i.toString + ":  ")
  time(lexing_simp(WHILE_REGS, prog2 * i))
}
*/

// Sulzmann's tests
//==================

val sulzmann = ("a" | "b" | "ab").%

println(lexing_simp(sulzmann, "a" * 10))

for (i <- 1 to 4501 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "a" * i))))
}

for (i <- 1 to 2001 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "ab" * i))))
}


// first benchmark regex 
//=======================

val reWord = CRANGE("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789")

val reWordStar = STAR(reWord)
val reWordPlus = reWord ~ reWordStar
val optionSet1 = "-" | "+" | "."
val optionSet2 = "-" | "."
val atTheRate = "@"
val period = "."
val optionSet3 = "," | ";"
val whitespace = " "

val re01 = reWordPlus
val re02 = STAR(optionSet1 ~ reWordPlus)
val re03 = atTheRate
val re04 = reWordPlus
val re05 = STAR(optionSet2 ~ reWordPlus)
val re06 = period
val re07 = reWordPlus
val re08 = re05

val re09 = optionSet3
val re10 = STAR(whitespace)
val re11 = reWordPlus
val re12 = re02
val re13 = atTheRate
val re14 = reWordPlus
val re15 = re05
val re16 = period
val re17 = reWordPlus
val re18 = re05


val re01_08 = SEQS(re01, re02, re03, re04, re05, re06, re07, re08)
val re09_10 = re09 ~ re10
val re11_18 = re01_08

val re = re01_08 ~ STAR(re09_10 ~ re11_18)


def process(s: String, i: Int) : Unit = {
  println(i + " " + "%.5f".format(time_needed(1, lexing(re, s))))
}

val filename = "../tests/emails.txt"
val filelines = Source.fromFile(filename).getLines.take(76).zipWithIndex


filelines.foreach({ case (s: String, i: Int) => process(s, i) })


