import scala.language.implicitConversions    
import scala.language.reflectiveCalls
import scala.annotation.tailrec   
import scala.io.Source
import scala.util.parsing.combinator._

abstract class Rexp 
case object ZERO extends Rexp 
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp {
  override def toString = c.toString 
}
case object ANYCHAR extends Rexp {
  override def toString = "." 
}
case class ALT(r1: Rexp, r2: Rexp) extends Rexp {
  override def toString = "(" + r1.toString + "|" + r2.toString + ")" 
}
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp {
  override def toString = "(" + r1.toString + r2.toString +")"
} 
case class STAR(r: Rexp) extends Rexp 
case class RECD(x: String, r: Rexp) extends Rexp {
  override def toString = "[" + r.toString +"]"
}


abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val
   
// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable (r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ANYCHAR => false
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
  case ANYCHAR => ONE
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
}

// extracts an environment from a value
def env(v: Val, r: Rexp) : List[(String, String)] = (v, r) match {
  case (Empty, ONE) => Nil
  case (Chr(c), CHAR(_)) => Nil
  case (Chr(c), ANYCHAR) => Nil
  case (Left(v), ALT(r1, r2)) => env(v, r1)
  case (Right(v), ALT(r1, r2)) => env(v, r2)
  case (Sequ(v1, v2), SEQ(r1, r2)) => env(v1, r1) ::: env(v2, r2)
  case (Stars(vs), STAR(r)) => vs.flatMap(env(_, r))
  case (v, RECD(x, r)) => (x, flatten(v))::env(v, r)
}

// extracts indices for the underlying strings
def env2(v: Val, r: Rexp, n: Int) : (List[(Int, Int)], Int) = (v, r) match {
  case (Empty, ONE) => (Nil, n)
  case (Chr(c), CHAR(_)) => (Nil, n + 1)
  case (Chr(c), ANYCHAR) => (Nil, n + 1)
  case (Left(v), ALT(r1, r2)) => env2(v, r1, n)
  case (Right(v), ALT(r1, r2)) => env2(v, r2, n)
  case (Sequ(v1, v2), SEQ(r1, r2)) => {
   val (e1, n1) = env2(v1, r1, n) 
   val (e2, n2) = env2(v2, r2, n1)
   (e1 ::: e2, n2)
  }
  case (Stars(Nil), STAR(r)) => (Nil, n)
  case (Stars(v :: vs), STAR(r)) => {
   val (e1, n1) = env2(v, r, n) 
   val (e2, n2) = env2(Stars(vs), STAR(r), n1)
   (e1 ::: e2, n2)
  }
  case (v, RECD(x, r)) => {
    val (e1, n1) = env2(v, r, n)
    ((n, n + flatten(v).length) :: e1, n1)
  }
}

// injection part
def mkeps(r: Rexp) : Val = r match {
  case ONE => Empty
  case ALT(r1, r2) => 
    if (nullable(r1)) Left(mkeps(r1)) else Right(mkeps(r2))
  case SEQ(r1, r2) => Sequ(mkeps(r1), mkeps(r2))
  case STAR(r) => Stars(Nil)
  case RECD(x, r) => mkeps(r)
}

def inj(r: Rexp, c: Char, v: Val) : Val = (r, v) match {
  case (STAR(r), Sequ(v1, Stars(vs))) => Stars(inj(r, c, v1)::vs)
  case (SEQ(r1, r2), Sequ(v1, v2)) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Left(Sequ(v1, v2))) => Sequ(inj(r1, c, v1), v2)
  case (SEQ(r1, r2), Right(v2)) => Sequ(mkeps(r1), inj(r2, c, v2))
  case (ALT(r1, r2), Left(v1)) => Left(inj(r1, c, v1))
  case (ALT(r1, r2), Right(v2)) => Right(inj(r2, c, v2))
  case (CHAR(d), Empty) => Chr(c) 
  case (ANYCHAR, Empty) => Chr(c) 
  case (RECD(x, r1), _) => inj(r1, c, v)
}


// main lexing function (produces a value)
def lex(r: Rexp, s: List[Char]) : Val = s match {
  case Nil => if (nullable(r)) mkeps(r) else throw new Exception("Not matched")
  case c::cs => inj(r, c, lex(der(c, r), cs))
}

def lexing(r: Rexp, s: String) : Val = lex(r, s.toList)



// Regular expression parser

case class Parser(s: String) {
  var i = 0
  
  def peek() = s(i)
  def eat(c: Char) = 
    if (c == s(i)) i = i + 1 else throw new Exception("Expected " + c + " got " + s(i))
  def next() = { i = i + 1; s(i - 1) }
  def more() = s.length - i > 0

  def Regex() : Rexp = {
    val t = Term();
    if (more() && peek() == '|') {
      eat ('|') ; 
      ALT(t, Regex()) 
    } 
    else t
  }

  def Term() : Rexp = {
    var f : Rexp = 
      if (more() && peek() != ')' && peek() != '|') Factor() else ONE;
    while (more() && peek() != ')' && peek() != '|') {
      f = SEQ(f, Factor()) ;
    }
    f
  }

  def Factor() : Rexp = {
    var b = Base();
    while (more() && peek() == '*') {
      eat('*') ;
      b = STAR(b) ;
    }
    while (more() && peek() == '?') {
      eat('?') ;
      b = ALT(b, ONE) ;
    }
    while (more() && peek() == '+') {
      eat('+') ;
      b = SEQ(b, STAR(b)) ;
    }
    b
  }

  def Base() : Rexp = {
    peek() match {
      case '(' => { eat('(') ; val r = Regex(); eat(')') ; RECD("",r) }
      case '.' => { eat('.'); ANYCHAR }
      case _ => CHAR(next())
    }
  }
}

//test case
//println(Parser("a|(bc)*").Regex())


def process_line(line: String) : String = {
  if (line.head == '#') "#" else
    {
      val line_split = line.split("\\t+")
      val reg_str = line_split(1)
      val reg = RECD("", Parser(reg_str).Regex())
      val in_str = if (line_split(2) == "-") "" else line_split(2)
      val res_str = line_split(3)
      val our_val = lexing(reg, in_str)
      val our_result = env2(our_val, reg, 0)._1.mkString("") 
      if (our_result != res_str) 
        { 
          reg_str + ":   " + 
          reg.toString + ": " + 
          in_str + "   \n " + 
          our_result +  
          " => \n" + res_str + " ! " +
          our_val + ":" + reg + "\n" 
        }
      else "*"
    }
}

def process_file(name : String) : Unit = {
  println("\nProcessing " + name)
  val filelines : List[String] = Source.fromFile(name).getLines.toList
  filelines.foreach((s: String) => print(process_line(s)))
}


val files = List("../tests/forced-assoc.txt",
                 "../tests/left-assoc.txt",
                 //"../tests/right-assoc.txt",
                 "../tests/class.txt",
                 "../tests/basic3.txt",
                 "../tests/totest.txt",
                 "../tests/repetition2.txt",
                 "../tests/osx-bsd-critical.txt")

files.foreach(process_file(_))

