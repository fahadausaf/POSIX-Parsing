import scala.annotation.tailrec
import scala.language.implicitConversions
import scala.language.reflectiveCalls 


abstract class Rexp 
case object ZERO extends Rexp 
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp 
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

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
}

// enumerates regular expressions until a certain depth
// using the characters in the string
def generate(n: Int, s: String) : Set[Rexp] = n match {
  case 0 => Set(ZERO, ONE) ++ s.toSet.map(CHAR)
  case n => {
    val rs = generate(n - 1, s)
    rs ++
    (for (r1 <- rs; r2 <- rs) yield ALT(r1, r2)) ++
    (for (r1 <- rs; r2 <- rs) yield SEQ(r1, r2)) ++
    (for (r <- rs) yield STAR(r))
  }
}



abstract class Val
case object Empty extends Val
case class Chr(c: Char) extends Val
case class Sequ(v1: Val, v2: Val) extends Val
case class Left(v: Val) extends Val
case class Right(v: Val) extends Val
case class Stars(vs: List[Val]) extends Val



// extracts a string from value
def flatten(v: Val) : String = v match {
  case Empty => ""
  case Chr(c) => c.toString
  case Left(v) => flatten(v)
  case Right(v) => flatten(v)
  case Sequ(v1, v2) => flatten(v1) + flatten(v2)
  case Stars(vs) => vs.map(flatten).mkString
}

def flat_len(v: Val) : Int = flatten(v).length

// extracts a set of candidate values from a "non-starred" regular expression
def values(r: Rexp) : Set[Val] = r match {
  case ZERO => Set()
  case ONE => Set(Empty)
  case CHAR(c) => Set(Chr(c))
  case ALT(r1, r2) => values(r1).map(Left(_)) ++ values(r2).map(Right(_)) 
  case SEQ(r1, r2) => for (v1 <- values(r1); v2 <- values(r2)) yield Sequ(v1, v2)
  case STAR(r) => values(r).map(v => Stars(List(v))) ++ Set(Stars(Nil))  
    // to do much more would cause the set to be infinite
}


def values_str(r: Rexp, s: String) : Set[Val] =
  values(r).filter(flatten(_) == s)   

val List(val1, val2) = values_str(("ab" | "a") ~ ("c" | "bc"), "abc").toList

// Position
type Pos = List[Int]


def positions(v: Val) : Set[Pos] = v match {
  case Empty => Set(Nil)
  case Chr(c) => Set(Nil)
  case Left(v) => Set(Nil) ++ positions(v).map(0::_) 
  case Right(v) => Set(Nil) ++ positions(v).map(1::_)
  case Sequ(v1, v2) => Set(Nil) ++ positions(v1).map(0::_) ++ positions(v2).map(1::_)
  case Stars(vs) => Set(Nil) ++ vs.zipWithIndex.flatMap{ case (v, n) => positions(v).map(n::_) }
} 

val v1 = Sequ(Chr('a'), Chr('b'))
val ps1 = positions(v1)
val ps1L = positions(Left(v1))
val ps1R = positions(Right(v1))

val v3 = Stars(List(Left(Chr('x')), Right(Left(Chr('y')))))
val v4 = Stars(List(Right(Right(Sequ(Chr('x'), Chr('y'))))))

val ps3 = positions(v3)
val ps4 = positions(v4)

def at(v: Val, ps: List[Int]) : Val = (v, ps) match {
  case (v, Nil) => v
  case (Left(v), 0::ps) => at(v, ps)
  case (Right(v), 1::ps) => at(v, ps)
  case (Sequ(v1, v2), 0::ps) => at(v1, ps)
  case (Sequ(v1, v2), 1::ps) => at(v2, ps)
  case (Stars(vs), n::ps) => at(vs(n), ps)
} 

ps1.map(at(v1, _))
ps1L.map(at(Left(v1), _))
ps1R.map(at(Right(v1), _))


def pflat_len(v: Val, p: Pos) : Int =
  if (positions(v) contains p) flat_len(at(v, p)) else -1
  

// for lexicographic list-orderings
import scala.math.Ordering.Implicits._

def smaller_than(pss: Set[Pos], ps: Pos) : Set[Pos] = 
  pss.filter(_ < ps)


// order from the alternative posix paper
def ordr(v1: Val, p: List[Int], v2: Val) : Boolean = { 
  pflat_len(v1, p) > pflat_len(v2, p) && 
  smaller_than(positions(v1) | positions(v2), p).forall(q => pflat_len(v1, q) == pflat_len(v2, q))
}

//tests
val List(val1, val2) = values_str(("ab" | "a") ~ ("c" | "bc"), "abc").toList

positions(val1).map(p => (p, ordr(val1, p, val2))).filter{ case (_, b) => b == true }
positions(val1)
at(val1, List(0))

smaller_than(positions(val1), List(1, 0))

val List(val1, val2) = values_str("a" ~ (("ab" | "a") ~ ("c" | "bc")), "aabc").toList
positions(val2).map(p => (p, ordr(val2, p, val1))).filter{ case (_, b) => b == true }
