/* lexer without simplification */

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
  case (CHAR(d), Empty) => Chr(c) 
  case (RECD(x, r1), _) => Rec(x, inj(r1, c, v))
}


// main lexing function (produces a value)
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)

// Examples

val K: Rexp = "a" | "b"
val I: Rexp = "ab" | "ba"  

println(lexing((K | I).%, "abab"))

val K2: Rexp = ("key" $ "a" | "b")
val I2: Rexp = ("id" $ ("ab" | "ba"))  

println(lexing((K2 | I2).%, "abaa"))
println(env(lexing((K2 | I2).%, "abaa")))

val r1: Rexp = "abc"
val r2: Rexp = der('a', r1)
val r3: Rexp = der('b', r2)
val r4: Rexp = der('c', r3)
println(r1)
println(r2)
println(r3)
println(r4)


// time keeping
def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}


// first benchmark regex 

val reWord = ALTS("a","b","c","d","e","f","g","h","i","j","k","l","m","n","o","p","q","r","s","t","u","v",
                  "w","x","y","z","A","B","C","D","E","F","G","H","I","J","K","L","M","N","O","P","Q","R",
                  "S","T","U","V","W","X","Y","Z","0","1","2","3","4","5","6","7","8","9")


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
val filelines = Source.fromFile(filename).getLines.take(22).zipWithIndex


filelines.foreach({ case (s: String, i: Int) => process(s, i) })

