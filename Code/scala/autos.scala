// DFAs and NFAs based on Scala's partial functions
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


// class for DFAs
case class DFA[A, C](start: A,                // starting state
                     delta: (A, C) :=> A,     // transition
                     fins:  A => Boolean) {   // final states

  // given a state and a "string", what is the next 
  // state, if there is any?
  def deltas(q: A, s: List[C]) : A = s match {
    case Nil => q
    case c::cs => deltas(delta(q, c), cs)
  }

  // is a "string" accepted by an DFA?
  def accepts(s: List[C]) : Boolean = 
    Try(fins(deltas(start, s))) getOrElse false

}

// DFA 1
val dtrans1 : (State, Char) :=> State = 
  { case (Q0, 'a') => Q0 
    case (Q0, 'b') => Q1 
  }

val dfa1 = DFA(Q0, dtrans1, Set[State](Q1))

dfa1.accepts("aaab".toList)     // true
dfa1.accepts("aacb".toList)     // false

// another DFA test
abstract class S
case object S0 extends S
case object S1 extends S
case object S2 extends S
case object Sink extends S

// transition function with a sink state
// S0 --a--> S1 --a--> S2
val sigma : (S, Char) :=> S = 
  { case (S0, 'a') => S1
    case (S1, 'a') => S2
    case _ => Sink
  }

val dfa1a = DFA(S0, sigma, Set[S](S2))

dfa1a.accepts("aa".toList)               //true
dfa1a.accepts("".toList)                 //false
dfa1a.accepts("ab".toList)               //false


// class for NFAs
case class NFA[A, C](starts: Set[A],            // starting states
                     delta: Set[(A, C) :=> A],  // transitions
                     fins:  A => Boolean) {     // final states 

  // given a state and a character, what is the set of next states?
  // if there is none => empty set
  def next(q: A, c: C) : Set[A] = 
    delta.flatMap(d => Try(d(q, c)).toOption)

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
    case c::cs => delta.exists(d => Try(search(d(q, c), cs)) getOrElse false)
  }

  def accepts2(s: List[C]) : Boolean = 
    starts.exists(search(_, s))

}




// NFA test cases

// 1:  NFA for STAR(ALL) ~ "a" ~ NTIMES(ALL, 3) ~ "bc"
val trans1 = Set[(State, Char) :=> State](
  { case (Q0, 'a') => Q1 },
  { case (Q0, _)   => Q0 },
  { case (Q1, _)   => Q2 },
  { case (Q2, _)   => Q3 },
  { case (Q3, _)   => Q4 },
  { case (Q4, 'b') => Q5 },
  { case (Q5, 'c') => Q6 }
)

val nfa1 = NFA(Set[State](Q0), trans1, Set[State](Q6))

nfa1.accepts("axaybzbc".toList)     // true
nfa1.accepts("aaaaxaybzbc".toList)  // true
nfa1.accepts("axaybzbd".toList)     // false

nfa1.accepts2("axaybzbc".toList)     // true
nfa1.accepts2("aaaaxaybzbc".toList)  // true
nfa1.accepts2("axaybzbd".toList)     // false


// 2
val trans2 = Set[(State, Char) :=> State](
  { case (Q0, 'a') => Q0 },
  { case (Q0, 'a') => Q1 },
  { case (Q0, 'b') => Q2 },
  { case (Q1, 'a') => Q1 },
  { case (Q2, 'b') => Q2 }
)

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


// 3
val trans3 = Set[(State, Char) :=> State](
  { case (Q0, _)   => Q0 },
  { case (Q0, 'a') => Q1 },
  { case (Q0, 'b') => Q3 },
  { case (Q1, 'b') => Q2 },
  { case (Q2, 'c') => Q5 },
  { case (Q3, 'c') => Q4 },
  { case (Q4, 'd') => Q5 }
)

val nfa3 = NFA(Set[State](Q0), trans3, Set[State](Q5))

nfa3.accepts("aaaaabc".toList)      // true
nfa3.accepts("aaaabcd".toList)      // true
nfa3.accepts("aaaaab".toList)       // false
nfa3.accepts("aaaabc".toList)       // true
nfa3.accepts("aaaaabbbaaa".toList)  // false



// subset, or powerset, construction
def powerset[A, C](nfa: NFA[A, C]) : DFA[Set[A], C] = {
  DFA(nfa.starts, 
      { case (qs, c) => nfa.nexts(qs, c) },
      _.exists(nfa.fins))
}

val dfa2 = powerset(nfa1)

dfa2.accepts("axaybzbc".toList)     // true
dfa2.accepts("aaaaxaybzbc".toList)  // true
dfa2.accepts("axaybzbd".toList)     // false

val dfa3 = powerset(nfa2)

dfa3.accepts("aa".toList)             // false
dfa3.accepts("aaaaa".toList)          // false
dfa3.accepts("aaaaab".toList)         // true
dfa3.accepts("aaaaabbb".toList)       // true
dfa3.accepts("aaaaabbbaaa".toList)    // false
dfa3.accepts("ac".toList)             // false




// epsilon NFA


// fixpoint construction
import scala.annotation.tailrec
@tailrec
def fixpT[A](f: A => A, x: A): A = {
  val fx = f(x)
  if (fx == x) x else fixpT(f, fx) 
}


case class eNFA[A, C](start: A,                          // starting state
                      delta: Set[(A, Option[C]) :=> A],  // transition edges
                      fins:  A => Boolean) {             // final states 

  // epsilon transitions
  def enext(q: A) : Set[A] = 
    delta.flatMap((d) => Try(d(q, None)).toOption)

  def enexts(qs: Set[A]) : Set[A] = 
    qs | qs.flatMap(enext(_))

  // epsilon closure
  def ecl(qs: Set[A]) : Set[A] = 
    fixpT(enexts, qs)

  // "normal" transition
  def next(q: A, c: C) : Set[A] = 
    delta.flatMap((d) => Try(d(q, Some(c))).toOption)

  def nexts(qs: Set[A], c: C) : Set[A] = 
    ecl(ecl(qs).flatMap(next(_, c)))

  def deltas(qs: Set[A], s: List[C]) : Set[A] = s match {
    case Nil => ecl(qs)
    case c::cs => deltas(nexts(qs, c), cs)
  }

  def accepts(s: List[C]) : Boolean = 
    deltas(Set(start), s.toList).exists(fins)
}

// test cases for eNFAs
val etrans1 = Set[(State, Option[Char]) :=> State](
  { case (Q0, Some('a')) => Q1 },
  { case (Q1, None) => Q0 }
)

val enfa1 = eNFA(Q0, etrans1, Set[State](Q1))

enfa1.accepts("a".toList)              // true
enfa1.accepts("".toList)               // false
enfa1.accepts("aaaaa".toList)          // true
enfa1.accepts("aaaaab".toList)         // false
enfa1.accepts("aaaaabbb".toList)       // false
enfa1.accepts("aaaaabbbaaa".toList)    // false
enfa1.accepts("ac".toList)             // false

// example from handouts 
val etrans2 = Set[(State, Option[Char]) :=> State](
  { case (Q0, Some('a')) => Q0 },
  { case (Q0, None) => Q1 },
  { case (Q0, None) => Q2 },
  { case (Q1, Some('a')) => Q1 },
  { case (Q2, Some('b')) => Q2 },
  { case (Q1, None) => Q0 }
)

val enfa2 = eNFA(Q0, etrans2, Set[State](Q2))

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

// eNFA that does not accept any string
def eNFA_ZERO(): eNFA[TState, Char] = {
  val Q = TState()
  eNFA(Q, Set(), Set())
}

// eNFA that accepts the empty string
def eNFA_ONE() : eNFA[TState, Char] = {
  val Q = TState()
  eNFA(Q, Set(), Set(Q))
}

// eNFA that accepts the string "c"
def eNFA_CHAR(c: Char) : eNFA[TState, Char] = {
  val Q1 = TState()
  val Q2 = TState()
  eNFA(Q1, 
       Set({ case (Q1, Some(d)) if (c == d) => Q2 }),
       Set(Q2))
}

// alternative of two eNFAs
def eNFA_ALT(enfa1: eNFA[TState, Char], enfa2: eNFA[TState, Char]) : eNFA[TState, Char] = {
  val Q = TState()
  eNFA(Q,
       enfa1.delta | enfa2.delta |
       Set({ case (Q, None) => enfa1.start },
           { case (Q, None) => enfa2.start }),
       q => enfa1.fins(q) || enfa2.fins(q))
}

// sequence of two eNFAs
def eNFA_SEQ(enfa1: eNFA[TState, Char], enfa2: eNFA[TState, Char]) : eNFA[TState, Char] = {
  eNFA(enfa1.start,
       enfa1.delta | enfa2.delta | 
       Set({ case (q, None) if enfa1.fins(q) => enfa2.start }),
       enfa2.fins)
}

// star of an eNFA
def eNFA_STAR(enfa: eNFA[TState, Char]) : eNFA[TState, Char] = {
  val Q = TState()
  eNFA(Q,
       enfa.delta |
       Set({ case (q, None) if enfa.fins(q) => Q },
           { case (Q, None) => enfa.start }),
       Set(Q))
}

/*
def tofunset[A, C](d: (A, Option[C]) :=> Set[A])(q: A, c: C) : Set[(A, C) :=> A] = {
  d((q, Some(c))).map ((qs: A) => { case (qi, ci) if (qi == q && ci == c) => qs } : (A, C) :=> A)
}


def eNFA2NFA[A, C](starts: Set[A],                    // starting state
                   delta: Set[(A, Option[C]) :=> A],  // transition edges
                   fins:  A => Boolean) {             // final states 

  // epsilon transitions
  def enext(q: A) : Set[A] = 
    delta.flatMap(d => Try(d(q, None)).toOption)

  def enexts(qs: Set[A]) : Set[A] = 
    qs | qs.flatMap(enext(_))

  // epsilon closure
  def ecl(qs: Set[A]) : Set[A] = 
    fixpT(enexts, qs)

  
  // "normal" transition
  def next(q: A, c: C) : Set[A] = 
    delta.flatMap(d => Try(d(q, Some(c))).toOption)    

  def nexts(qs: Set[A], c: C) : Set[A] = 
    ecl(ecl(qs).flatMap(next(_, c)))
        

  def nfa_delta : Set[(A, C) :=> A] = delta.flatMap(d => tofunset(d))

  def nfa_starts = ecl(starts)

  def nfa_fins = (q: A) => ecl(Set[A](q)) exists fins

  NFA(nfa_starts, nfa_delta, nfa_fins)
}

*/ 

// Regular expressions for derivative automata

abstract class Rexp
case object ZERO extends Rexp
case object ONE extends Rexp
case class CHAR(c: Char) extends Rexp 
case object ALL extends Rexp 
case object ALLPlus extends Rexp
case class ALT(r1: Rexp, r2: Rexp) extends Rexp 
case class SEQ(r1: Rexp, r2: Rexp) extends Rexp 
case class STAR(r: Rexp) extends Rexp 
case class NTIMES(r: Rexp, n: Int) extends Rexp 
case class UPNTIMES(r: Rexp, n: Int) extends Rexp 
case class NOT(r: Rexp) extends Rexp
case class AND(r1: Rexp, r2: Rexp) extends Rexp 

def get_chars(r: Rexp) : Set[Char] = r match {
  case ZERO => Set()
  case ONE => Set()
  case CHAR(c) => Set(c)
  case ALT(r1, r2) => get_chars(r1) | get_chars(r2)
  case SEQ(r1, r2) => get_chars(r1) | get_chars(r2)
  case STAR(r) => get_chars(r)
  case NTIMES(r, _) => get_chars(r)
  case UPNTIMES(r, _) => get_chars(r)
  case ALL => ('a' to 'z').toSet | Set('*','/','\\')
  case NOT(r) => get_chars(r)
  case AND(r1, r2) => get_chars(r1) | get_chars(r2)
}



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

// thompson construction only for basic regular expressions
def thompson (r: Rexp) : eNFA[TState, Char] = r match {
  case ZERO => eNFA_ZERO()
  case ONE => eNFA_ONE()
  case CHAR(c) => eNFA_CHAR(c)  
  case ALT(r1, r2) => eNFA_ALT(thompson(r1), thompson(r2))
  case SEQ(r1, r2) => eNFA_SEQ(thompson(r1), thompson(r2))
  case STAR(r1) => eNFA_STAR(thompson(r1))
}

// regular expression matcher using Thompson's
def tmatcher(r: Rexp, s: String) : Boolean = thompson(r).accepts(s.toList)


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

tmatcher(EVIL2, "aaaaaab")   // true
tmatcher(EVIL2, "aaaaaa")    // false
tmatcher(EVIL2, "a" * 100)   // false


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

// helper function for recording time
def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}



// test harness for the matcher
for (i <- 0 to 35 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, tmatcher(EVIL(i), "a" * i))))
}



// normalisation of regular expressions
// for derivative automata

case class ALTs(rs: Set[Rexp]) extends Rexp
case class ANDs(rs: Set[Rexp]) extends Rexp
case class SEQs(rs: List[Rexp]) extends Rexp 

def normalise(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (normalise(r1), normalise(r2)) match {
    case (ALTs(rs1), ALTs(rs2)) => ALTs(rs1 | rs2)
    case (r1s, ALTs(rs2)) => ALTs(rs2 + r1s)
    case (ALTs(rs1), r2s) => ALTs(rs1 + r2s)
    case (r1s, r2s) => ALTs(Set(r1s, r2s))
  }
  case AND(r1, r2) => (normalise(r1), normalise(r2)) match {
    case (ANDs(rs1), ANDs(rs2)) => ANDs(rs1 | rs2)
    case (r1s, ANDs(rs2)) => ANDs(rs2 + r1s)
    case (ANDs(rs1), r2s) => ANDs(rs1 + r2s)
    case (r1s, r2s) => ANDs(Set(r1s, r2s))
  }
  case SEQ(r1, r2) =>  (normalise(r1), normalise(r2)) match {
    case (SEQs(rs1), SEQs(rs2)) => SEQs(rs1 ++ rs2)
    case (r1s, SEQs(rs2)) => SEQs(r1s :: rs2)
    case (SEQs(rs1), r2s) => SEQs(rs1 ++ List(r2s))
    case (r1s, r2s) => SEQs(List(r1s, r2s))
  }
  case STAR(r) => STAR(normalise(r))
  case NTIMES(r, n) => NTIMES(normalise(r), n)
  case UPNTIMES(r, n) => UPNTIMES(normalise(r), n)
  case NOT(r) => NOT(normalise(r))
  case r => r
}


// simplification of regular expressions

def simp(r: Rexp) : Rexp = r match {
  case ALT(r1, r2) => (simp(r1), simp(r2)) match {
    case (ZERO, r2s) => r2s
    case (r1s, ZERO) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else ALT(r1s, r2s)
  }
  case SEQ(r1, r2) =>  (simp(r1), simp(r2)) match {
    case (ZERO, _) => ZERO
    case (_, ZERO) => ZERO
    case (ONE, r2s) => r2s
    case (r1s, ONE) => r1s
    case (r1s, r2s) => SEQ(r1s, r2s)
  }
  case NTIMES(r, n) => if (n == 0) ONE else NTIMES(simp(r), n)
  case UPNTIMES(r, n) => if (n == 0) ONE else UPNTIMES(simp(r), n)
  case NOT(r) => NOT(simp(r))
  case AND(r1, r2) => (simp(r1), simp(r2)) match {
    case (ALL, r2s) => r2s
    case (r1s, ALL) => r1s
    case (r1s, r2s) => if (r1s == r2s) r1s else AND(r1s, r2s)  
  }
  case r => r
}


// nullable function: tests whether the regular 
// expression can recognise the empty string
def nullable(r: Rexp) : Boolean = r match {
  case ZERO => false
  case ONE => true
  case CHAR(_) => false
  case ALL => true
  case ALLPlus => false
  case ALT(r1, r2) => nullable(r1) || nullable(r2)
  case SEQ(r1, r2) => nullable(r1) && nullable(r2)
  case STAR(_) => true
  case NTIMES(r, i) => if (i == 0) true else nullable(r)
  case UPNTIMES(r: Rexp, n: Int) => true
  case NOT(r) => !nullable(r)
  case AND(r1, r2) => nullable(r1) && nullable(r2)
}

// derivative of a regular expression w.r.t. a character
// they are not finite even for simple regular expressions
def der(c: Char, r: Rexp) : Rexp = r match {
  case ZERO => ZERO
  case ONE => ZERO
  case CHAR(d) => if (c == d) ONE else ZERO
  case ALL => ALL
  case ALLPlus => ALL 
  case ALT(r1, r2) => ALT(der(c, r1), der(c, r2))
  case SEQ(r1, r2) => 
    if (nullable(r1)) ALT(SEQ(der(c, r1), r2), der(c, r2))
    else SEQ(der(c, r1), r2)
  case STAR(r1) => SEQ(der(c, r1), STAR(r1))
  case NTIMES(r1, i) => 
    if (i == 0) ZERO else
    if (nullable(r1)) SEQ(der(c, r1), UPNTIMES(r1, i - 1))
    else SEQ(der(c, r1), NTIMES(r1, i - 1))
  case UPNTIMES(r1, i) => 
    if (i == 0) ZERO
    else SEQ(der(c, r1), UPNTIMES(r1, i - 1)) 
  case NOT(r) => NOT(der(c, r))
  case AND(r1, r2) => AND(der(c, r1), der(c, r2))
}


// derivative based matcher
def matcher(r: Rexp, s: List[Char]): Boolean = s match {
  case Nil => nullable(r)
  case c::cs => matcher(der(c, r), cs)
} 



// partial derivative of a regular expression w.r.t. a character
// does not work for NOT and AND ... see below
def pder(c: Char, r: Rexp) : Set[Rexp] = r match {
  case ZERO => Set()
  case ONE => Set()
  case CHAR(d) => if (c == d) Set(ONE) else Set()
  case ALL => Set(ALL)
  case ALLPlus => Set(ALL)
  case ALT(r1, r2) => pder(c, r1) | pder(c, r2)
  case SEQ(r1, r2) => 
    (for (pr1 <- pder(c, r1)) yield SEQ(pr1, r2)) | 
    (if (nullable(r1)) pder(c, r2) else Set())
  case STAR(r1) => 
    for (pr1 <- pder(c, r1)) yield SEQ(pr1, STAR(r1))
  case NTIMES(r1, i) => 
    if (i == 0) Set() else
    if (nullable(r1)) 
      for (pr1 <- pder(c, r1)) yield SEQ(pr1, UPNTIMES(r1, i - 1))
    else 
      for (pr1 <- pder(c, r1)) yield SEQ(pr1, NTIMES(r1, i - 1))
  case UPNTIMES(r1, i) => 
    if (i == 0) Set()
    else 
      for (pr1 <- pder(c, r1)) yield SEQ(pr1, UPNTIMES(r1, i - 1))
}

// partial derivative matcher (not for NOT and AND)
def pmatcher(rs: Set[Rexp], s: List[Char]): Boolean = s match {
  case Nil => rs.exists(nullable(_))
  case c::cs => pmatcher(rs.flatMap(pder(c, _)), cs)
} 


// quick-and-dirty translation of a pder-automaton 
// does not work for NOT and AND

val r = STAR(ALL) ~ "a" ~ NTIMES(ALL, 3) ~ "bc"
val pder_nfa = NFA[Set[Rexp], Char](Set(Set(r)), 
                                    Set( { case (rs, c) => rs.flatMap(pder(c, _))} ), 
                                    _.exists(nullable))



pder_nfa.accepts("axaybzbc".toList)     // true
pder_nfa.accepts("aaaaxaybzbc".toList)  // true
pder_nfa.accepts("axaybzbd".toList)     // false




// partial derivatives including NOT and AND according to
// PhD-thesis: Manipulation of Extended Regular Expressions 
// with Derivatives; these partial derivatives are also not
// finite...for example NOT((a*)a)

def seq_compose(rs: Set[Rexp], r2: Rexp) : Set[Rexp] =
  for (r <- rs) yield (SEQ(r, r2) : Rexp)

def not_compose(rs: Set[Rexp]) : Set[Rexp] =
  Set(rs.fold(ALL)((r1, r2) => AND(r1, NOT(r2))))

def and_compose(rs1: Set[Rexp], rs2: Set[Rexp]) : Set[Rexp] =
  for (r1 <- rs1; r2 <- rs2) yield AND(r1, r2)

def pder2(c: Char, r: Rexp) : Set[Rexp] = r match {
  case ZERO => Set()
  case ONE => Set()
  case ALL => Set(ALL)
  case ALLPlus => Set(ALL)
  case CHAR(d) => if (c == d) Set(ONE) else Set()
  case ALT(r1, r2) => pder2(c, r1) | pder2(c, r2)
  case SEQ(r1, r2) => {
    val prs1 = seq_compose(pder2(c, r1), r2)
    if (nullable(r1)) (prs1 | pder2(c, r2)) else prs1
  }
  case STAR(r1) => seq_compose(pder2(c, r1), STAR(r1))
  case AND(r1, r2) => and_compose(pder2(c, r1), pder2(c, r2))
  case NOT(r1) => nder2(c, r1)
}

def nder2(c: Char, r: Rexp) : Set[Rexp] = r match {
  case ZERO => Set(ALL)
  case ONE => Set(ALL)
  case ALL => Set()
  case ALLPlus => Set()
  case CHAR(d) => if (c == d) Set(ALLPlus) else Set(ALL)
  case ALT(r1, r2) => and_compose(nder2(c, r1), nder2(c, r2))
  case SEQ(r1, r2) => if (nullable(r1))
                      and_compose(not_compose(seq_compose(pder2(c, r1), r2)), nder2(c, r2))
                      else not_compose(seq_compose(pder2(c, r1), r2))
  case STAR(r1) => not_compose(pder2(c, STAR(r1)))
  case AND(r1, r2) => nder2(c, r1) | nder2(c, r2)
  case NOT(r1) => pder2(c, r1)
}


def pmatcher2(rs: Set[Rexp], s: List[Char]): Boolean = s match {
  case Nil => rs.exists(nullable(_))
  case c::cs => pmatcher2(rs.flatMap(pder2(c, _)), cs)
} 

// pder2/nder2 example

val r_ex = AND("aa" | "a", AND(STAR("a"), NOT(STAR("a") ~ "a"))) 
nder2('a', r_ex).map(simp(_)).mkString("\n")






// Derivative and Partial Derivative Automaton construction


type DState = Rexp                          // state type of the derivative automaton
type DStates = Set[Rexp]                    
type Trans = (DState, Char) :=> DState      // transition functions of the der/pder auto
type MTrans = Map[(DState, Char), DState]   // transition Maps
type STrans = Set[MTrans]                   // set of transition Maps



// Brzozoswki Derivative automaton construction ... simple
// version, might not terminate

def goto(sigma: Set[Char], delta: MTrans, qs: DStates, q: DState, c: Char) : (DStates, MTrans) = {
  val qder = simp(der(c, q)) 
  qs.find(normalise(_) == normalise(qder)) match {
    case Some(qexists) => (qs, delta + ((q, c) -> qexists))
    case None => explore(sigma, delta + ((q, c) -> qder), qs + qder, qder)
  }
}
 
def explore(sigma: Set[Char], delta: MTrans, qs: DStates, q: DState) : (DStates, MTrans) = 
  sigma.foldLeft((qs, delta)) { case ((qs, delta), c) => goto(sigma, delta, qs, q, c) }


def mkDFA(r: Rexp) = {
  val sigma = get_chars(r)
  val (qs, delta) = explore(sigma, Map(), Set[Rexp](r), r)
  val fins = qs.filter(nullable(_))
  val deltaf : (Rexp, Char) :=> Rexp =  { case (q, c) => delta(q, c) }
  println(s"DFA size: ${qs.size}")
  //println(s"""DFA states\n${qs.mkString("\n")}""")
  DFA(r, deltaf, fins)
}

val re = "ab" | "ac"
val d1 = mkDFA(re)

d1.accepts("ab".toList) // true
d1.accepts("ac".toList) // true
d1.accepts("aa".toList) // false

val d2 = mkDFA(r)

d2.accepts("axaybzbc".toList)     // true
d2.accepts("aaaaxaybzbc".toList)  // true
d2.accepts("axaybzbd".toList)     // false


//for (n <- (1 to 10).toList) 
//  mkDFA(STAR(ALL) ~ "a" ~ NTIMES(ALL, n) ~ "bc")


// this is an example where mkDFA without normalisation
// does not terminate
val big_aux = STAR("a" | "b")
val big = SEQ(big_aux, SEQ("a", SEQ("b", big_aux)))

mkDFA(big)   // does not terminate without normalisation



// Antimirov Partial derivative automata construction ... definitely 
// terminates but does not work for extensions of NOT and AND
//
// for this we have to use the extended partial derivatives
// pder2/nder2...but termination is also not guaranteed


// to transform (concrete) Maps into functions
def toFun(m: MTrans) : Trans = 
  { case (q, c) => m(q, c) }

def pgoto(sigma: Set[Char], delta: STrans, qs: DStates, q: DState, c: Char) : (DStates, STrans) = {
  val qders = pder(c, q).map(simp(_))  // set of simplified partial derivatives
  qders.foldLeft((qs, delta)) { case ((qs, delta), qnew) => padd(sigma, delta, qs, q, qnew, c) }
}

def padd(sigma: Set[Char], delta: STrans, qs: DStates, 
         q: DState, qnew: DState, c: Char) : (DStates, STrans) = {
  qs.find(_ == qnew) match {
    case Some(qexists) => (qs, delta + Map((q, c) -> qexists))
    case None => pexplore(sigma, delta + Map((q, c) -> qnew), qs + qnew, qnew)
  }
}
 
def pexplore(sigma: Set[Char], delta: STrans, qs: DStates, q: DState) : (DStates, STrans) = 
  sigma.foldLeft((qs, delta)) { case ((qs, delta), c) => pgoto(sigma, delta, qs, q, c) }

def mkNFA(r: Rexp) : NFA[Rexp, Char]= {
  val sigma = get_chars(r)
  val (qs, delta) = pexplore(sigma, Set(), Set(r), r)
  val fins = qs.filter(nullable(_))
  val deltaf = delta.map(toFun(_))
  //println(s"NFA size: ${qs.size}")
  //println(s"""NFA states\n${qs.mkString("\n")}""")
  //println(s"""NFA transitions\n${delta.mkString("\n")} """)
  NFA(Set(r), deltaf, fins)
}


// simple example from Scott's paper

val n1 = mkNFA(re) // size = 4

n1.accepts("ab".toList) // true
n1.accepts("ac".toList) // true
n1.accepts("aa".toList) // false

// example from: Partial Derivative and Position Bisimilarity 
// Automata, Eva Maia, Nelma Moreira, Rogerio Reis
 
val r_test = STAR(("a" ~ STAR("b")) | "b") ~ "a"
val t1 = pder('a', r_test).map(simp(_))
val t2 = pder('b', r_test).map(simp(_))

mkNFA(r_test) // size = 3


// helper function for recording time
def time_needed[T](i: Int, code: => T) = {
  val start = System.nanoTime()
  for (j <- 1 to i) code
  val end = System.nanoTime()
  (end - start)/(i * 1.0e9)
}

// simple example involving double star (a*)* b
// with depth-first search causes catastrophic backtracing

val n2 = mkNFA(EVIL2)  // size 3

n2.accepts("aaaaaab".toList)   // true
n2.accepts("aaaaaa".toList)    // false
n2.accepts(("a" * 100).toList) // false

n2.accepts2("aaaaaab".toList)   // true
n2.accepts2("aaaaaa".toList)    // false
n2.accepts2(("a" * 100).toList) // false

time_needed(2, n2.accepts("aaaaaab".toList)) 
time_needed(2, n2.accepts("aaaaaa".toList))   
time_needed(2, n2.accepts(("a" * 2000).toList))

time_needed(2, n2.accepts2("aaaaaab".toList)) 
time_needed(2, n2.accepts2("aaaaaa".toList))  
time_needed(2, n2.accepts2(("a" * 2000).toList))


// other evil regular expression

for (i <- 0 to 100 by 5) {
  println(i + ": " + "%.5f".format(time_needed(1, mkNFA(EVIL(i)).accepts(("a" * i).toList))))
}


// example involving not

val rnot = "/*" ~ (NOT ((ALL.%) ~ "*/" ~ (ALL.%))) ~ "*/"


val dfa_not = mkDFA(rnot)  // size 10

dfa_not.accepts("/**/".toList)        // true
dfa_not.accepts("/*aaabaa*/".toList)  // true
dfa_not.accepts("/*/**/".toList)      // true
dfa_not.accepts("/*aaa*/aa*/".toList) // false 
dfa_not.accepts("/aaa*/aa*/".toList)  // false


/* nfa construction according to pder does not work for NOT and AND;
 * nfa construction according to pder2/nder2 does not necesarily terminate
 
val nfa_not = mkNFA(rnot)  // does not termninate

nfa_not.accepts("/**/".toList)        // true
nfa_not.accepts("/*aaabaa*/".toList)  // true
nfa_not.accepts("/*/**/".toList)      // true
nfa_not.accepts("/*aaa*/aa*/".toList) // false  ????
nfa_not.accepts("/aaa*/aa*/".toList) // false
*/

// derivative matcher
matcher(rnot, "/**/".toList)        // true
matcher(rnot, "/*aaabaa*/".toList)  // true
matcher(rnot, "/*/**/".toList)      // true
matcher(rnot, "/*aaa*/aa*/".toList) // false
matcher(rnot, "/aaa*/aa*/".toList)  // false

// pder2/nder2 partial derivative matcher
pmatcher2(Set(rnot), "/**/".toList)        // true
pmatcher2(Set(rnot), "/*aaabaa*/".toList)  // true
pmatcher2(Set(rnot), "/*/**/".toList)      // true
pmatcher2(Set(rnot), "/*aaa*/aa*/".toList) // false
pmatcher2(Set(rnot), "/aaa*/aa*/".toList)  // false

// example from automata paper with counters and backreferences

val r1 = STAR(ALL) ~ "a" ~ NTIMES(ALL, 1) ~ "bc"
mkNFA(r1)     // size = 5
 
val n3 = mkNFA(r) // size = 7

n3.accepts("axaybzbc".toList)     // true
n3.accepts("aaaaxaybzbc".toList)  // true
n3.accepts("axaybzbd".toList)     // false

for (n <- (1 to 100).toList) 
  mkNFA(STAR(ALL) ~ "a" ~ NTIMES(ALL, n) ~ "bc")
