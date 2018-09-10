// NFAs based on Scala's partial functions (returning
// sets of states)


import scala.util.Try


// type abbreviation for partial functions
type :=>[A, B] = PartialFunction[A, B]


// some states for test cases 
abstract class State
case object Q0 extends State
case object Q1 extends State
case object Q2 extends State
case object Q3 extends State
case object Q4 extends State
case object Q5 extends State
case object Q6 extends State


// return empty set when not defined
def applyOrElse[A, B](f: A :=> Set[B], x: A) : Set[B] =
  Try(f(x)) getOrElse Set[B]()



// class for NFAs
case class NFA[A, C](starts: Set[A],            // starting states
                     delta: (A, C) :=> Set[A],  // transitions
                     fins:  A => Boolean) {     // final states 

  // given a state and a character, what is the set of next states?
  // if there is none => empty set
  def next(q: A, c: C) : Set[A] = 
    applyOrElse(delta, (q, c))

  def nexts(qs: Set[A], c: C) : Set[A] =
    qs.flatMap(next(_, c))

  // given some states and a string, what is the set of next states?
  def deltas(qs: Set[A], s: List[C]) : Set[A] = s match {
    case Nil => qs
    case c::cs => deltas(nexts(qs, c), cs)
  }

  // is a string accepted by an NFA?
  def accepts(s: List[C]) : Boolean = 
    deltas(starts, s).exists(fins)

  // depth-first search version of accept
  def search(q: A, s: List[C]) : Boolean = s match {
    case Nil => fins(q)
    case c::cs => next(q, c).exists(search(_, cs)) 
  }

  def accepts2(s: List[C]) : Boolean = 
    starts.exists(search(_, s))

}


// NFA test cases

val trans2 : (State, Char) :=> Set[State] = 
 { case (Q0, 'a') => Set(Q0, Q1)
   case (Q0, 'b') => Set(Q2)
   case (Q1, 'a') => Set(Q1)
   case (Q2, 'b') => Set(Q2)
 }

val nfa2 = NFA(Set[State](Q0), trans2, Set[State](Q2))

nfa2.accepts("aa".toList)             // false
nfa2.accepts("aaaaa".toList)          // false
nfa2.accepts("aaaaab".toList)         // true
nfa2.accepts("aaaaabbb".toList)       // true
nfa2.accepts("aaaaabbbaaa".toList)    // false
nfa2.accepts("ac".toList)             // false

nfa2.accepts2("aa".toList)             // false
nfa2.accepts2("aaaaa".toList)          // false
nfa2.accepts2("aaaaab".toList)         // true
nfa2.accepts2("aaaaabbb".toList)       // true
nfa2.accepts2("aaaaabbbaaa".toList)    // false
nfa2.accepts2("ac".toList)             // false




// epsilon NFAs
// (not explicitly defined, but immediately translated into NFAs)

// fixpoint construction
import scala.annotation.tailrec
@tailrec
def fixpT[A](f: A => A, x: A): A = {
  val fx = f(x)
  if (fx == x) x else fixpT(f, fx) 
}

// translates eNFAs directly into NFAs 
def eNFA[A, C](starts: Set[A], 
	       delta: (A, Option[C]) :=> Set[A], 
	       fins: A => Boolean) : NFA[A, C] = { 

  // epsilon transitions
  def enext(q: A) : Set[A] = 
    applyOrElse(delta, (q, None))

  def enexts(qs: Set[A]) : Set[A] = 
    qs | qs.flatMap(enext(_))

  // epsilon closure
  def ecl(qs: Set[A]) : Set[A] = 
    fixpT(enexts, qs)

  // "normal" transitions
  def next(q: A, c: C) : Set[A] = 
    applyOrElse(delta, (q, Some(c)))

  def nexts(qs: Set[A], c: C) : Set[A] = 
    ecl(ecl(qs).flatMap(next(_, c)))

  NFA(ecl(starts), 
      { case (q, c) => nexts(Set(q), c) }, 
      q => ecl(Set(q)) exists fins)
}





// test cases for eNFAs
val etrans1 : (State, Option[Char]) :=> Set[State] =
  { case (Q0, Some('a')) => Set(Q1)
    case (Q1, None) => Set(Q0)
  }

val enfa1 = eNFA(Set[State](Q0), etrans1, Set[State](Q1))

enfa1.accepts("a".toList)              // true
enfa1.accepts("".toList)               // false
enfa1.accepts("aaaaa".toList)          // true
enfa1.accepts("aaaaab".toList)         // false
enfa1.accepts("aaaaabbb".toList)       // false
enfa1.accepts("aaaaabbbaaa".toList)    // false
enfa1.accepts("ac".toList)             // false

// example from handouts 
val etrans2 : (State, Option[Char]) :=> Set[State] = 
  { case (Q0, Some('a')) => Set(Q0)
    case (Q0, None) => Set(Q1, Q2)
    case (Q1, Some('a')) => Set(Q1)
    case (Q2, Some('b')) => Set(Q2)
    case (Q1, None) => Set(Q0)
  }

val enfa2 = eNFA(Set[State](Q0), etrans2, Set[State](Q2))

enfa2.accepts("a".toList)              // true
enfa2.accepts("".toList)               // true
enfa2.accepts("aaaaa".toList)          // true
enfa2.accepts("aaaaab".toList)         // true
enfa2.accepts("aaaaabbb".toList)       // true
enfa2.accepts("aaaaabbbaaa".toList)    // false
enfa2.accepts("ac".toList)             // false


// states for Thompson construction
case class TState(i: Int) extends State

object TState {
  var counter = 0
  
  def apply() : TState = {
    counter += 1;
    new TState(counter - 1)
  }
}

// some types abbreviations
type NFAt = NFA[TState, Char]
type NFAtrans = (TState, Char) :=> Set[TState]
type eNFAtrans = (TState, Option[Char]) :=> Set[TState]


// for composing an eNFA transition with a NFA transition
implicit class RichPF(val f: eNFAtrans) extends AnyVal {
  def +++(g: NFAtrans) : eNFAtrans = 
  { case (q, None) =>  applyOrElse(f, (q, None)) 
    case (q, Some(c)) => applyOrElse(f, (q, Some(c))) | applyOrElse(g, (q, c))  }
}


// NFA that does not accept any string
def NFA_ZERO(): NFAt = {
  val Q = TState()
  NFA(Set(Q), { case _ => Set() }, Set())
}

// NFA that accepts the empty string
def NFA_ONE() : NFAt = {
  val Q = TState()
  NFA(Set(Q), { case _ => Set() }, Set(Q))
}

// NFA that accepts the string "c"
def NFA_CHAR(c: Char) : NFAt = {
  val Q1 = TState()
  val Q2 = TState()
  NFA(Set(Q1), { case (Q1, d) if (c == d) => Set(Q2) }, Set(Q2))
}

// sequence of two NFAs
def NFA_SEQ(enfa1: NFAt, enfa2: NFAt) : NFAt = {
  val new_delta : eNFAtrans = 
    { case (q, None) if enfa1.fins(q) => enfa2.starts }
  
  eNFA(enfa1.starts, new_delta +++ enfa1.delta +++ enfa2.delta, 
       enfa2.fins)
}

// alternative of two NFAs
def NFA_ALT(enfa1: NFAt, enfa2: NFAt) : NFAt = {
  val new_delta : NFAtrans = { 
    case (q, c) =>  applyOrElse(enfa1.delta, (q, c)) | 
                    applyOrElse(enfa2.delta, (q, c)) }
  val new_fins = (q: TState) => enfa1.fins(q) || enfa2.fins(q)

  NFA(enfa1.starts | enfa2.starts, new_delta, new_fins)
}

// star of a NFA
def NFA_STAR(enfa: NFAt) : NFAt = {
  val Q = TState()
  val new_delta : eNFAtrans = 
    { case (Q, None) => enfa.starts
      case (q, None) if enfa.fins(q) => Set(Q) }

  eNFA(Set(Q), new_delta +++ enfa.delta, Set(Q))
}


// Regular expressions fro derivative automata

abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp 
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 

import scala.language.implicitConversions    
import scala.language.reflectiveCalls 

def charlist2rexp(s: List[Char]): Rexp = s match {
  case Nil => ONE
  case c::Nil => CHAR(c)
  case c::s => SEQ(CHAR(c), charlist2rexp(s))
}
implicit def string2rexp(s: String): Rexp = charlist2rexp(s.toList)

implicit def RexpOps (r: Rexp) = new {
  def | (s: Rexp) = ALT(r, s)
  def % = STAR(r)
  def ~ (s: Rexp) = SEQ(r, s)
}

implicit def stringOps (s: String) = new {
  def | (r: Rexp) = ALT(s, r)
  def | (r: String) = ALT(s, r)
  def % = STAR(s)
  def ~ (r: Rexp) = SEQ(s, r)
  def ~ (r: String) = SEQ(s, r)
}

//optional
def OPT(r: Rexp) = ALT(r, ONE)

//n-times
def NTIMES(r: Rexp, n: Int) : Rexp = n match {
  case 0 => ONE
  case 1 => r
  case n => SEQ(r, NTIMES(r, n - 1))
}

// evil regular exproession
def EVIL(n: Int) = SEQ(NTIMES(OPT("a"), n), NTIMES("a", n))


val EVIL2 = STAR(STAR("a")) ~ "b"

// thompson construction 
def thompson (r: Rexp) : NFAt = r match {
  case ZERO => NFA_ZERO()
  case ONE => NFA_ONE()
  case CHAR(c) => NFA_CHAR(c)  
  case ALT(r1, r2) => NFA_ALT(thompson(r1), thompson(r2))
  case SEQ(r1, r2) => NFA_SEQ(thompson(r1), thompson(r2))
  case STAR(r1) => NFA_STAR(thompson(r1))
}

// regular expression matcher using Thompson's
def tmatcher(r: Rexp, s: String) : Boolean = 
  thompson(r).accepts(s.toList)

def tmatcher2(r: Rexp, s: String) : Boolean = 
  thompson(r).accepts2(s.toList)

// test cases for thompson construction
tmatcher(ZERO, "")   // false
tmatcher(ZERO, "a")  // false

tmatcher(ONE, "")    // true
tmatcher(ONE, "a")   // false

tmatcher(CHAR('a'), "")    // false
tmatcher(CHAR('a'), "a")   // true
tmatcher(CHAR('a'), "b")   // false

tmatcher("a" | "b", "")    // false
tmatcher("a" | "b", "a")   // true
tmatcher("a" | "b", "b")   // true
tmatcher("a" | "b", "c")   // false
tmatcher("a" | "b", "ab")  // false

tmatcher("a" ~ "b", "")    // false
tmatcher("a" ~ "b", "a")   // false
tmatcher("a" ~ "b", "b")   // false
tmatcher("a" ~ "b", "c")   // false
tmatcher("a" ~ "b", "ab")  // true
tmatcher("a" ~ "b", "aba") // false

tmatcher(STAR("a"), "")      // true
tmatcher(STAR("a"), "a")     // true
tmatcher(STAR("a"), "aaaaa") // true
tmatcher(STAR("a"), "b")     // false
tmatcher(STAR("a"), "aaab")  // false

tmatcher(STAR(STAR("a")), "")      // true
tmatcher(STAR(STAR("a")), "a")     // true
tmatcher(STAR(STAR("a")), "aaaaa") // true
tmatcher(STAR(STAR("a")), "b")     // false
tmatcher(STAR(STAR("a")), "aaab")  // false

tmatcher(EVIL2, "aaaaaab")   // true
tmatcher(EVIL2, "aaaaaa")    // false
tmatcher(EVIL2, "a" * 100)   // false

// helper function for recording time
def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}



// test harness for the matcher
for (i <- 0 to 9) {
  println(i + ": " + "%.5f".format(time_needed(1, tmatcher(EVIL(i), "a" * i))))
}

for (i <- 0 to 7) {
  println(i + ": " + "%.5f".format(time_needed(1, tmatcher2(EVIL(i), "a" * i))))
}

for (i <- 0 to 100 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, tmatcher(EVIL2, "a" * i))))
}


for (i <- 0 to 8) {
  println(i + ": " + "%.5f".format(time_needed(1, tmatcher2(EVIL2, "a" * i))))
}
