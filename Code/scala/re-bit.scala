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

abstract class ARexp 
case object AZERO extends ARexp
case class AONE(bs: List[Boolean]) extends ARexp
case class ACHAR(bs: List[Boolean], c: Char) extends ARexp
case class AALT(bs: List[Boolean], r1: ARexp, r2: ARexp) extends ARexp 
case class ASEQ(bs: List[Boolean], r1: ARexp, r2: ARexp) extends ARexp 
case class ASTAR(bs: List[Boolean], r: ARexp) extends ARexp 

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

// translation into ARexps
def fuse(bs: List[Boolean], r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(cs) => AONE(bs ++ cs)
  case ACHAR(cs, c) => ACHAR(bs ++ cs, c)
  case AALT(cs, r1, r2) => AALT(bs ++ cs, r1, r2)
  case ASEQ(cs, r1, r2) => ASEQ(bs ++ cs, r1, r2)
  case ASTAR(cs, r) => ASTAR(bs ++ cs, r)
}

def internalise(r: Rexp) : ARexp = r match {
  case ZERO => AZERO
  case ONE => AONE(Nil)
  case CHAR(c) => ACHAR(Nil, c)
  case ALT(r1, r2) => AALT(Nil, fuse(List(false), internalise(r1)), fuse(List(true), internalise(r2)))
  case SEQ(r1, r2) => ASEQ(Nil, internalise(r1), internalise(r2))
  case STAR(r) => ASTAR(Nil, internalise(r))
  case RECD(x, r) => internalise(r)
}

internalise(("a" | "ab") ~ ("b" | ""))


def decode_aux(r: Rexp, bs: List[Boolean]) : (Val, List[Boolean]) = (r, bs) match {
  case (ONE, bs) => (Empty, bs)
  case (CHAR(c), bs) => (Chr(c), bs)
  case (ALT(r1, r2), false::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Left(v), bs1)
  }
  case (ALT(r1, r2), true::bs) => {
    val (v, bs1) = decode_aux(r2, bs)
    (Right(v), bs1)
  }
  case (SEQ(r1, r2), bs) => {
    val (v1, bs1) = decode_aux(r1, bs)
    val (v2, bs2) = decode_aux(r2, bs1)
    (Sequ(v1, v2), bs2)
  }
  case (STAR(r1), false::bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    val (Stars(vs), bs2) = decode_aux(STAR(r1), bs1)
    (Stars(v::vs), bs2)
  }
  case (STAR(_), true::bs) => (Stars(Nil), bs)
  case (RECD(x, r1), bs) => {
    val (v, bs1) = decode_aux(r1, bs)
    (Rec(x, v), bs1)
  }
}

def decode(r: Rexp, bs: List[Boolean]) = decode_aux(r, bs) match {
  case (v, Nil) => v
  case _ => throw new Exception("Not decodable")
}

// nullable function: tests whether the aregular 
// expression can recognise the empty string
def nullable (r: ARexp) : Boolean = r match {
  case AZERO => false
  case AONE(_) => true
  case ACHAR(_,_) => false
  case AALT(_, r1, r2) => nullable(r1) || nullable(r2)
  case ASEQ(_, r1, r2) => nullable(r1) && nullable(r2)
  case ASTAR(_, _) => true
}

def mkepsBC(r: ARexp) : List[Boolean] = r match {
  case AONE(bs) => bs
  case AALT(bs, r1, r2) => 
    if (nullable(r1)) bs ++ mkepsBC(r1) else bs ++ mkepsBC(r2)
  case ASEQ(bs, r1, r2) => bs ++ mkepsBC(r1) ++ mkepsBC(r2)
  case ASTAR(bs, r) => bs ++ List(true)
}

// derivative of a regular expression w.r.t. a character
def der (c: Char, r: ARexp) : ARexp = r match {
  case AZERO => AZERO
  case AONE(_) => AZERO
  case ACHAR(bs, d) => if (c == d) AONE(bs) else AZERO
  case AALT(bs, r1, r2) => AALT(bs, der(c, r1), der(c, r2))
  case ASEQ(bs, r1, r2) => 
    if (nullable(r1)) AALT(bs, ASEQ(Nil, der(c, r1), r2), fuse(mkepsBC(r1), der(c, r2)))
    else ASEQ(bs, der(c, r1), r2)
  case ASTAR(bs, r) => ASEQ(bs, fuse(List(false), der(c, r)), ASTAR(Nil, r))
}

// derivative w.r.t. a string (iterates der)
@tailrec
def ders (s: List[Char], r: ARexp) : ARexp = s match {
  case Nil => r
  case c::s => ders(s, der(c, r))
}

// main unsimplified lexing function (produces a value)
def lex(r: ARexp, s: List[Char]) : List[Boolean] = s match {
  case Nil => if (nullable(r)) mkepsBC(r) else throw new Exception("Not matched")
  case c::cs => lex(der(c, r), cs)
}

def pre_lexing(r: Rexp, s: String) = lex(internalise(r), s.toList)
def lexing(r: Rexp, s: String) : Val = decode(r, lex(internalise(r), s.toList))



def simp(r: ARexp): ARexp = r match {
  case ASEQ(bs1, r1, r2) => (simp(r1), simp(r2)) match {
      case (AZERO, _) => AZERO
      case (_, AZERO) => AZERO
      case (AONE(bs2), r2s) => fuse(bs1 ++ bs2, r2s)
      case (r1s, r2s) => ASEQ(bs1, r1s, r2s)
  }
  case AALT(bs1, r1, r2) => (simp(r1), simp(r2)) match {
      case (AZERO, r2s) => fuse(bs1, r2s)
      case (r1s, AZERO) => fuse(bs1, r1s)
      case (r1s, r2s) => AALT(bs1, r1s, r2s)
  }
  case r => r
}

def lex_simp(r: ARexp, s: List[Char]) : List[Boolean] = s match {
  case Nil => if (nullable(r)) mkepsBC(r) else throw new Exception("Not matched")
  case c::cs => lex(simp(der(c, r)), cs)
}

def lexing_simp(r: Rexp, s: String) : Val = decode(r, lex_simp(internalise(r), s.toList))



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

// Some Tests
//============

def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


val rf = ("a" | "ab") ~ ("ab" | "")
println(pre_lexing(rf, "ab"))
println(lexing(rf, "ab"))
println(lexing_simp(rf, "ab"))

val r0 = ("a" | "ab") ~ ("b" | "")
println(pre_lexing(r0, "ab"))
println(lexing(r0, "ab"))
println(lexing_simp(r0, "ab"))

val r1 = ("a" | "ab") ~ ("bcd" | "cd")
println(lexing(r1, "abcd"))
println(lexing_simp(r1, "abcd"))

println(lexing((("" | "a") ~ ("ab" | "b")), "ab"))
println(lexing_simp((("" | "a") ~ ("ab" | "b")), "ab"))

println(lexing((("" | "a") ~ ("b" | "ab")), "ab"))
println(lexing_simp((("" | "a") ~ ("b" | "ab")), "ab"))

println(lexing((("" | "a") ~ ("c" | "ab")), "ab"))
println(lexing_simp((("" | "a") ~ ("c" | "ab")), "ab"))


// Two Simple Tests for the While Language
//========================================

// Lexing Rules 

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

println("prog0 test")

val prog0 = """read n"""
println(env(lexing(WHILE_REGS, prog0)))
println(env(lexing_simp(WHILE_REGS, prog0)))

println("prog1 test")

val prog1 = """read  n; write (n)"""
println(env(lexing(WHILE_REGS, prog1)))
println(env(lexing_simp(WHILE_REGS, prog1)))


// Sulzmann's tests
//==================

val sulzmann = ("a" | "b" | "ab").%

println(lexing(sulzmann, "a" * 10))
println(lexing_simp(sulzmann, "a" * 10))

for (i <- 1 to 6501 by 500) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "a" * i))))
}

for (i <- 1 to 16 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, lexing_simp(sulzmann, "ab" * i))))
}
