(*<*)
theory Paper
imports 
   "../Lexer"
   "../Simplifying" 
   "../Sulzmann" 
   "~~/src/HOL/Library/LaTeXsugar"
begin

declare [[show_question_marks = false]]

abbreviation 
 "der_syn r c \<equiv> der c r"

abbreviation 
 "ders_syn r s \<equiv> ders s r"

notation (latex output)
  If  ("(\<^raw:\textrm{>if\<^raw:}> (_)/ \<^raw:\textrm{>then\<^raw:}> (_)/ \<^raw:\textrm{>else\<^raw:}> (_))" 10) and
  Cons ("_\<^raw:\mbox{$\,$}>::\<^raw:\mbox{$\,$}>_" [75,73] 73) and  

  ZERO ("\<^bold>0" 78) and 
  ONE ("\<^bold>1" 78) and 
  CHAR ("_" [1000] 80) and
  ALT ("_ + _" [77,77] 78) and
  SEQ ("_ \<cdot> _" [77,77] 78) and
  STAR ("_\<^sup>\<star>" [1000] 78) and
  
  val.Void ("'(')" 1000) and
  val.Char ("Char _" [1000] 78) and
  val.Left ("Left _" [79] 78) and
  val.Right ("Right _" [1000] 78) and
  val.Seq ("Seq _ _" [79,79] 78) and
  val.Stars ("Stars _" [79] 78) and

  L ("L'(_')" [10] 78) and
  der_syn ("_\\_" [79, 1000] 76) and  
  ders_syn ("_\\_" [79, 1000] 76) and
  flat ("|_|" [75] 74) and
  Sequ ("_ @ _" [78,77] 63) and
  injval ("inj _ _ _" [79,77,79] 76) and 
  mkeps ("mkeps _" [79] 76) and 
  length ("len _" [73] 73) and
 
  Prf ("_ : _" [75,75] 75) and  
  Posix ("'(_, _') \<rightarrow> _" [63,75,75] 75) and
 
  lexer ("lexer _ _" [78,78] 77) and 
  F_RIGHT ("F\<^bsub>Right\<^esub> _") and
  F_LEFT ("F\<^bsub>Left\<^esub> _") and  
  F_ALT ("F\<^bsub>Alt\<^esub> _ _") and
  F_SEQ1 ("F\<^bsub>Seq1\<^esub> _ _") and
  F_SEQ2 ("F\<^bsub>Seq2\<^esub> _ _") and
  F_SEQ ("F\<^bsub>Seq\<^esub> _ _") and
  simp_SEQ ("simp\<^bsub>Seq\<^esub> _ _" [1000, 1000] 1) and
  simp_ALT ("simp\<^bsub>Alt\<^esub> _ _" [1000, 1000] 1) and
  slexer ("lexer\<^sup>+" 1000) and

  ValOrd ("_ >\<^bsub>_\<^esub> _" [77,77,77] 77) and
  ValOrdEq ("_ \<ge>\<^bsub>_\<^esub> _" [77,77,77] 77)

definition 
  "match r s \<equiv> nullable (ders s r)"

(*
comments not implemented

p9. The condtion "not exists s3 s4..." appears often enough (in particular in
the proof of Lemma 3) to warrant a definition.

*)

(*>*)

section {* Introduction *}


text {*

Brzozowski \cite{Brzozowski1964} introduced the notion of the {\em
derivative} @{term "der c r"} of a regular expression @{text r} w.r.t.\ a
character~@{text c}, and showed that it gave a simple solution to the
problem of matching a string @{term s} with a regular expression @{term r}:
if the derivative of @{term r} w.r.t.\ (in succession) all the characters of
the string matches the empty string, then @{term r} matches @{term s} (and
{\em vice versa}). The derivative has the property (which may almost be
regarded as its specification) that, for every string @{term s} and regular
expression @{term r} and character @{term c}, one has @{term "cs \<in> L(r)"} if
and only if \mbox{@{term "s \<in> L(der c r)"}}. The beauty of Brzozowski's
derivatives is that they are neatly expressible in any functional language,
and easily definable and reasoned about in theorem provers---the definitions
just consist of inductive datatypes and simple recursive functions. A
mechanised correctness proof of Brzozowski's matcher in for example HOL4
has been mentioned by Owens and Slind~\cite{Owens2008}. Another one in Isabelle/HOL is part
of the work by Krauss and Nipkow \cite{Krauss2011}. And another one in Coq is given
by Coquand and Siles \cite{Coquand2012}.

If a regular expression matches a string, then in general there is more than
one way of how the string is matched. There are two commonly used
disambiguation strategies to generate a unique answer: one is called GREEDY
matching \cite{Frisch2004} and the other is POSIX
matching~\cite{Kuklewicz,Sulzmann2014,Vansummeren2006}. For example consider
the string @{term xy} and the regular expression \mbox{@{term "STAR (ALT
(ALT x y) xy)"}}. Either the string can be matched in two `iterations' by
the single letter-regular expressions @{term x} and @{term y}, or directly
in one iteration by @{term xy}. The first case corresponds to GREEDY
matching, which first matches with the left-most symbol and only matches the
next symbol in case of a mismatch (this is greedy in the sense of preferring
instant gratification to delayed repletion). The second case is POSIX
matching, which prefers the longest match.

In the context of lexing, where an input string needs to be split up into a
sequence of tokens, POSIX is the more natural disambiguation strategy for
what programmers consider basic syntactic building blocks in their programs.
These building blocks are often specified by some regular expressions, say
@{text "r\<^bsub>key\<^esub>"} and @{text "r\<^bsub>id\<^esub>"} for recognising keywords and
identifiers, respectively. There are two underlying (informal) rules behind
tokenising a string in a POSIX fashion according to a collection of regular
expressions:

\begin{itemize} 
\item[$\bullet$] \emph{The Longest Match Rule} (or \emph{``maximal munch rule''}):
The longest initial substring matched by any regular expression is taken as
next token.\smallskip

\item[$\bullet$] \emph{Priority Rule:}
For a particular longest initial substring, the first regular expression
that can match determines the token.
\end{itemize}

\noindent Consider for example a regular expression @{text "r\<^bsub>key\<^esub>"} for recognising keywords
such as @{text "if"}, @{text "then"} and so on; and @{text "r\<^bsub>id\<^esub>"}
recognising identifiers (say, a single character followed by
characters or numbers).  Then we can form the regular expression
@{text "(r\<^bsub>key\<^esub> + r\<^bsub>id\<^esub>)\<^sup>\<star>"} and use POSIX matching to tokenise strings,
say @{text "iffoo"} and @{text "if"}.  For @{text "iffoo"} we obtain
by the Longest Match Rule a single identifier token, not a keyword
followed by an identifier. For @{text "if"} we obtain by the Priority
Rule a keyword token, not an identifier token---even if @{text "r\<^bsub>id\<^esub>"}
matches also.

One limitation of Brzozowski's matcher is that it only generates a
YES/NO answer for whether a string is being matched by a regular
expression.  Sulzmann and Lu~\cite{Sulzmann2014} extended this matcher
to allow generation not just of a YES/NO answer but of an actual
matching, called a [lexical] {\em value}. They give a simple algorithm
to calculate a value that appears to be the value associated with
POSIX matching.  The challenge then is to specify that value, in an
algorithm-independent fashion, and to show that Sulzmann and Lu's
derivative-based algorithm does indeed calculate a value that is
correct according to the specification.

The answer given by Sulzmann and Lu \cite{Sulzmann2014} is to define a
relation (called an ``order relation'') on the set of values of @{term
r}, and to show that (once a string to be matched is chosen) there is
a maximum element and that it is computed by their derivative-based
algorithm. This proof idea is inspired by work of Frisch and Cardelli
\cite{Frisch2004} on a GREEDY regular expression matching
algorithm. However, we were not able to establish transitivity and
totality for the ``order relation'' by Sulzmann and Lu. In Section
\ref{argu} we identify some inherent problems with their approach (of
which some of the proofs are not published in \cite{Sulzmann2014});
perhaps more importantly, we give a simple inductive (and
algorithm-independent) definition of what we call being a {\em POSIX
value} for a regular expression @{term r} and a string @{term s}; we
show that the algorithm computes such a value and that such a value is
unique. Our proofs are both done by hand and checked in Isabelle/HOL.  The
experience of doing our proofs has been that this mechanical checking
was absolutely essential: this subject area has hidden snares. This
was also noted by Kuklewicz \cite{Kuklewicz} who found that nearly all
POSIX matching implementations are ``buggy'' \cite[Page
203]{Sulzmann2014} and by Grathwohl et al \cite[Page 36]{CrashCourse2014}
who wrote:

\begin{quote}
\it{}``The POSIX strategy is more complicated than the greedy because of 
the dependence on information about the length of matched strings in the 
various subexpressions.''
\end{quote}

%\footnote{The relation @{text "\<ge>\<^bsub>r\<^esub>"} defined by Sulzmann and Lu \cite{Sulzmann2014} 
%is a relation on the
%values for the regular expression @{term r}; but it only holds between
%@{term "v\<^sub>1"} and @{term "v\<^sub>2"} in cases where @{term "v\<^sub>1"} and @{term "v\<^sub>2"} have
%the same flattening (underlying string). So a counterexample to totality is
%given by taking two values @{term "v\<^sub>1"} and @{term "v\<^sub>2"} for @{term r} that
%have different flattenings (see Section~\ref{posixsec}). A different
%relation @{text "\<ge>\<^bsub>r,s\<^esub>"} on the set of values for @{term r}
%with flattening @{term s} is definable by the same approach, and is indeed
%total; but that is not what Proposition 1 of \cite{Sulzmann2014} does.}


\noindent {\bf Contributions:} We have implemented in Isabelle/HOL the
derivative-based regular expression matching algorithm of
Sulzmann and Lu \cite{Sulzmann2014}. We have proved the correctness of this
algorithm according to our specification of what a POSIX value is (inspired
by work of Vansummeren \cite{Vansummeren2006}). Sulzmann
and Lu sketch in \cite{Sulzmann2014} an informal correctness proof: but to
us it contains unfillable gaps.\footnote{An extended version of
\cite{Sulzmann2014} is available at the website of its first author; this
extended version already includes remarks in the appendix that their
informal proof contains gaps, and possible fixes are not fully worked out.}
Our specification of a POSIX value consists of a simple inductive definition
that given a string and a regular expression uniquely determines this value.
Derivatives as calculated by Brzozowski's method are usually more complex
regular expressions than the initial one; various optimisations are
possible. We prove the correctness when simplifications of @{term "ALT ZERO
r"}, @{term "ALT r ZERO"}, @{term "SEQ ONE r"} and @{term "SEQ r ONE"} to
@{term r} are applied.

*}

section {* Preliminaries *}

text {* \noindent Strings in Isabelle/HOL are lists of characters with the
empty string being represented by the empty list, written @{term "[]"}, and
list-cons being written as @{term "DUMMY # DUMMY"}. Often we use the usual
bracket notation for lists also for strings; for example a string consisting
of just a single character @{term c} is written @{term "[c]"}. By using the
type @{type char} for characters we have a supply of finitely many
characters roughly corresponding to the ASCII character set. Regular
expressions are defined as usual as the elements of the following inductive
datatype:

  \begin{center}
  @{text "r :="}
  @{const "ZERO"} $\mid$
  @{const "ONE"} $\mid$
  @{term "CHAR c"} $\mid$
  @{term "ALT r\<^sub>1 r\<^sub>2"} $\mid$
  @{term "SEQ r\<^sub>1 r\<^sub>2"} $\mid$
  @{term "STAR r"} 
  \end{center}

  \noindent where @{const ZERO} stands for the regular expression that does
  not match any string, @{const ONE} for the regular expression that matches
  only the empty string and @{term c} for matching a character literal. The
  language of a regular expression is also defined as usual by the
  recursive function @{term L} with the six clauses:

  \begin{center}
  \begin{tabular}{l@ {\hspace{3mm}}rcl}
  (1) & @{thm (lhs) L.simps(1)} & $\dn$ & @{thm (rhs) L.simps(1)}\\
  (2) & @{thm (lhs) L.simps(2)} & $\dn$ & @{thm (rhs) L.simps(2)}\\
  (3) & @{thm (lhs) L.simps(3)} & $\dn$ & @{thm (rhs) L.simps(3)}\\
  \end{tabular}
  \hspace{14mm}
  \begin{tabular}{l@ {\hspace{3mm}}rcl}
  (4) & @{thm (lhs) L.simps(4)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) L.simps(4)[of "r\<^sub>1" "r\<^sub>2"]}\\
  (5) & @{thm (lhs) L.simps(5)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) L.simps(5)[of "r\<^sub>1" "r\<^sub>2"]}\\
  (6) & @{thm (lhs) L.simps(6)} & $\dn$ & @{thm (rhs) L.simps(6)}\\
  \end{tabular}
  \end{center}
  
  \noindent In clause (4) we use the operation @{term "DUMMY ;;
  DUMMY"} for the concatenation of two languages (it is also list-append for
  strings). We use the star-notation for regular expressions and for
  languages (in the last clause above). The star for languages is defined
  inductively by two clauses: @{text "(i)"} the empty string being in
  the star of a language and @{text "(ii)"} if @{term "s\<^sub>1"} is in a
  language and @{term "s\<^sub>2"} in the star of this language, then also @{term
  "s\<^sub>1 @ s\<^sub>2"} is in the star of this language. It will also be convenient
  to use the following notion of a \emph{semantic derivative} (or \emph{left
  quotient}) of a language defined as
  %
  \begin{center}
  @{thm Der_def}\;.
  \end{center}
 
  \noindent
  For semantic derivatives we have the following equations (for example
  mechanically proved in \cite{Krauss2011}):
  %
  \begin{equation}\label{SemDer}
  \begin{array}{lcl}
  @{thm (lhs) Der_null}  & \dn & @{thm (rhs) Der_null}\\
  @{thm (lhs) Der_empty}  & \dn & @{thm (rhs) Der_empty}\\
  @{thm (lhs) Der_char}  & \dn & @{thm (rhs) Der_char}\\
  @{thm (lhs) Der_union}  & \dn & @{thm (rhs) Der_union}\\
  @{thm (lhs) Der_Sequ}  & \dn & @{thm (rhs) Der_Sequ}\\
  @{thm (lhs) Der_star}  & \dn & @{thm (rhs) Der_star}
  \end{array}
  \end{equation}


  \noindent \emph{\Brz's derivatives} of regular expressions
  \cite{Brzozowski1964} can be easily defined by two recursive functions:
  the first is from regular expressions to booleans (implementing a test
  when a regular expression can match the empty string), and the second
  takes a regular expression and a character to a (derivative) regular
  expression:

  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) nullable.simps(1)} & $\dn$ & @{thm (rhs) nullable.simps(1)}\\
  @{thm (lhs) nullable.simps(2)} & $\dn$ & @{thm (rhs) nullable.simps(2)}\\
  @{thm (lhs) nullable.simps(3)} & $\dn$ & @{thm (rhs) nullable.simps(3)}\\
  @{thm (lhs) nullable.simps(4)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) nullable.simps(4)[of "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) nullable.simps(5)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) nullable.simps(5)[of "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) nullable.simps(6)} & $\dn$ & @{thm (rhs) nullable.simps(6)}\medskip\\
  
  %\end{tabular}
  %\end{center}

  %\begin{center}
  %\begin{tabular}{lcl}
  
  @{thm (lhs) der.simps(1)} & $\dn$ & @{thm (rhs) der.simps(1)}\\
  @{thm (lhs) der.simps(2)} & $\dn$ & @{thm (rhs) der.simps(2)}\\
  @{thm (lhs) der.simps(3)} & $\dn$ & @{thm (rhs) der.simps(3)}\\
  @{thm (lhs) der.simps(4)[of c "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) der.simps(4)[of c "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) der.simps(5)[of c "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) der.simps(5)[of c "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) der.simps(6)} & $\dn$ & @{thm (rhs) der.simps(6)}
  \end{tabular}
  \end{center}
 
  \noindent
  We may extend this definition to give derivatives w.r.t.~strings:

  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) ders.simps(1)} & $\dn$ & @{thm (rhs) ders.simps(1)}\\
  @{thm (lhs) ders.simps(2)} & $\dn$ & @{thm (rhs) ders.simps(2)}\\
  \end{tabular}
  \end{center}

  \noindent Given the equations in \eqref{SemDer}, it is a relatively easy
  exercise in mechanical reasoning to establish that

  \begin{proposition}\label{derprop}\mbox{}\\ 
  \begin{tabular}{ll}
  @{text "(1)"} & @{thm (lhs) nullable_correctness} if and only if
  @{thm (rhs) nullable_correctness}, and \\ 
  @{text "(2)"} & @{thm[mode=IfThen] der_correctness}.
  \end{tabular}
  \end{proposition}

  \noindent With this in place it is also very routine to prove that the
  regular expression matcher defined as
  %
  \begin{center}
  @{thm match_def}
  \end{center}

  \noindent gives a positive answer if and only if @{term "s \<in> L r"}.
  Consequently, this regular expression matching algorithm satisfies the
  usual specification for regular expression matching. While the matcher
  above calculates a provably correct YES/NO answer for whether a regular
  expression matches a string or not, the novel idea of Sulzmann and Lu
  \cite{Sulzmann2014} is to append another phase to this algorithm in order
  to calculate a [lexical] value. We will explain the details next.

*}

section {* POSIX Regular Expression Matching\label{posixsec} *}

text {* 

  The clever idea by Sulzmann and Lu \cite{Sulzmann2014} is to define
  values for encoding \emph{how} a regular expression matches a string
  and then define a function on values that mirrors (but inverts) the
  construction of the derivative on regular expressions. \emph{Values}
  are defined as the inductive datatype

  \begin{center}
  @{text "v :="}
  @{const "Void"} $\mid$
  @{term "val.Char c"} $\mid$
  @{term "Left v"} $\mid$
  @{term "Right v"} $\mid$
  @{term "Seq v\<^sub>1 v\<^sub>2"} $\mid$ 
  @{term "Stars vs"} 
  \end{center}  

  \noindent where we use @{term vs} to stand for a list of
  values. (This is similar to the approach taken by Frisch and
  Cardelli for GREEDY matching \cite{Frisch2004}, and Sulzmann and Lu
  for POSIX matching \cite{Sulzmann2014}). The string underlying a
  value can be calculated by the @{const flat} function, written
  @{term "flat DUMMY"} and defined as:

  \begin{center}
  \begin{tabular}[t]{lcl}
  @{thm (lhs) flat.simps(1)} & $\dn$ & @{thm (rhs) flat.simps(1)}\\
  @{thm (lhs) flat.simps(2)} & $\dn$ & @{thm (rhs) flat.simps(2)}\\
  @{thm (lhs) flat.simps(3)} & $\dn$ & @{thm (rhs) flat.simps(3)}\\
  @{thm (lhs) flat.simps(4)} & $\dn$ & @{thm (rhs) flat.simps(4)}
  \end{tabular}\hspace{14mm}
  \begin{tabular}[t]{lcl}
  @{thm (lhs) flat.simps(5)[of "v\<^sub>1" "v\<^sub>2"]} & $\dn$ & @{thm (rhs) flat.simps(5)[of "v\<^sub>1" "v\<^sub>2"]}\\
  @{thm (lhs) flat.simps(6)} & $\dn$ & @{thm (rhs) flat.simps(6)}\\
  @{thm (lhs) flat.simps(7)} & $\dn$ & @{thm (rhs) flat.simps(7)}\\
  \end{tabular}
  \end{center}

  \noindent Sulzmann and Lu also define inductively an inhabitation relation
  that associates values to regular expressions:

  \begin{center}
  \begin{tabular}{c}
  \\[-8mm]
  @{thm[mode=Axiom] Prf.intros(4)} \qquad
  @{thm[mode=Axiom] Prf.intros(5)[of "c"]}\\[4mm]
  @{thm[mode=Rule] Prf.intros(2)[of "v\<^sub>1" "r\<^sub>1" "r\<^sub>2"]} \qquad 
  @{thm[mode=Rule] Prf.intros(3)[of "v\<^sub>2" "r\<^sub>1" "r\<^sub>2"]}\\[4mm]
  @{thm[mode=Rule] Prf.intros(1)[of "v\<^sub>1" "r\<^sub>1" "v\<^sub>2" "r\<^sub>2"]}\\[4mm]
  @{thm[mode=Axiom] Prf.intros(6)[of "r"]} \qquad  
  @{thm[mode=Rule] Prf.intros(7)[of "v" "r" "vs"]}
  \end{tabular}
  \end{center}

  \noindent Note that no values are associated with the regular expression
  @{term ZERO}, and that the only value associated with the regular
  expression @{term ONE} is @{term Void}, pronounced (if one must) as @{text
  "Void"}. It is routine to establish how values ``inhabiting'' a regular
  expression correspond to the language of a regular expression, namely

  \begin{proposition}
  @{thm L_flat_Prf}
  \end{proposition}

  In general there is more than one value associated with a regular
  expression. In case of POSIX matching the problem is to calculate the
  unique value that satisfies the (informal) POSIX rules from the
  Introduction. Graphically the POSIX value calculation algorithm by
  Sulzmann and Lu can be illustrated by the picture in Figure~\ref{Sulz}
  where the path from the left to the right involving @{term derivatives}/@{const
  nullable} is the first phase of the algorithm (calculating successive
  \Brz's derivatives) and @{const mkeps}/@{text inj}, the path from right to
  left, the second phase. This picture shows the steps required when a
  regular expression, say @{text "r\<^sub>1"}, matches the string @{term
  "[a,b,c]"}. We first build the three derivatives (according to @{term a},
  @{term b} and @{term c}). We then use @{const nullable} to find out
  whether the resulting derivative regular expression @{term "r\<^sub>4"}
  can match the empty string. If yes, we call the function @{const mkeps}
  that produces a value @{term "v\<^sub>4"} for how @{term "r\<^sub>4"} can
  match the empty string (taking into account the POSIX constraints in case
  there are several ways). This function is defined by the clauses:

\begin{figure}[t]
\begin{center}
\begin{tikzpicture}[scale=2,node distance=1.3cm,
                    every node/.style={minimum size=6mm}]
\node (r1)  {@{term "r\<^sub>1"}};
\node (r2) [right=of r1]{@{term "r\<^sub>2"}};
\draw[->,line width=1mm](r1)--(r2) node[above,midway] {@{term "der a DUMMY"}};
\node (r3) [right=of r2]{@{term "r\<^sub>3"}};
\draw[->,line width=1mm](r2)--(r3) node[above,midway] {@{term "der b DUMMY"}};
\node (r4) [right=of r3]{@{term "r\<^sub>4"}};
\draw[->,line width=1mm](r3)--(r4) node[above,midway] {@{term "der c DUMMY"}};
\draw (r4) node[anchor=west] {\;\raisebox{3mm}{@{term nullable}}};
\node (v4) [below=of r4]{@{term "v\<^sub>4"}};
\draw[->,line width=1mm](r4) -- (v4);
\node (v3) [left=of v4] {@{term "v\<^sub>3"}};
\draw[->,line width=1mm](v4)--(v3) node[below,midway] {@{text "inj r\<^sub>3 c"}};
\node (v2) [left=of v3]{@{term "v\<^sub>2"}};
\draw[->,line width=1mm](v3)--(v2) node[below,midway] {@{text "inj r\<^sub>2 b"}};
\node (v1) [left=of v2] {@{term "v\<^sub>1"}};
\draw[->,line width=1mm](v2)--(v1) node[below,midway] {@{text "inj r\<^sub>1 a"}};
\draw (r4) node[anchor=north west] {\;\raisebox{-8mm}{@{term "mkeps"}}};
\end{tikzpicture}
\end{center}
\mbox{}\\[-13mm]

\caption{The two phases of the algorithm by Sulzmann \& Lu \cite{Sulzmann2014},
matching the string @{term "[a,b,c]"}. The first phase (the arrows from 
left to right) is \Brz's matcher building successive derivatives. If the 
last regular expression is @{term nullable}, then the functions of the 
second phase are called (the top-down and right-to-left arrows): first 
@{term mkeps} calculates a value @{term "v\<^sub>4"} witnessing
how the empty string has been recognised by @{term "r\<^sub>4"}. After
that the function @{term inj} ``injects back'' the characters of the string into
the values.
\label{Sulz}}
\end{figure} 

  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) mkeps.simps(1)} & $\dn$ & @{thm (rhs) mkeps.simps(1)}\\
  @{thm (lhs) mkeps.simps(2)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) mkeps.simps(2)[of "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) mkeps.simps(3)[of "r\<^sub>1" "r\<^sub>2"]} & $\dn$ & @{thm (rhs) mkeps.simps(3)[of "r\<^sub>1" "r\<^sub>2"]}\\
  @{thm (lhs) mkeps.simps(4)} & $\dn$ & @{thm (rhs) mkeps.simps(4)}\\
  \end{tabular}
  \end{center}

  \noindent Note that this function needs only to be partially defined,
  namely only for regular expressions that are nullable. In case @{const
  nullable} fails, the string @{term "[a,b,c]"} cannot be matched by @{term
  "r\<^sub>1"} and the null value @{term "None"} is returned. Note also how this function
  makes some subtle choices leading to a POSIX value: for example if an
  alternative regular expression, say @{term "ALT r\<^sub>1 r\<^sub>2"}, can
  match the empty string and furthermore @{term "r\<^sub>1"} can match the
  empty string, then we return a @{text Left}-value. The @{text
  Right}-value will only be returned if @{term "r\<^sub>1"} cannot match the empty
  string.

  The most interesting idea from Sulzmann and Lu \cite{Sulzmann2014} is
  the construction of a value for how @{term "r\<^sub>1"} can match the
  string @{term "[a,b,c]"} from the value how the last derivative, @{term
  "r\<^sub>4"} in Fig.~\ref{Sulz}, can match the empty string. Sulzmann and
  Lu achieve this by stepwise ``injecting back'' the characters into the
  values thus inverting the operation of building derivatives, but on the level
  of values. The corresponding function, called @{term inj}, takes three
  arguments, a regular expression, a character and a value. For example in
  the first (or right-most) @{term inj}-step in Fig.~\ref{Sulz} the regular
  expression @{term "r\<^sub>3"}, the character @{term c} from the last
  derivative step and @{term "v\<^sub>4"}, which is the value corresponding
  to the derivative regular expression @{term "r\<^sub>4"}. The result is
  the new value @{term "v\<^sub>3"}. The final result of the algorithm is
  the value @{term "v\<^sub>1"}. The @{term inj} function is defined by recursion on regular
  expressions and by analysing the shape of values (corresponding to 
  the derivative regular expressions).
  %
  \begin{center}
  \begin{tabular}{l@ {\hspace{5mm}}lcl}
  (1) & @{thm (lhs) injval.simps(1)} & $\dn$ & @{thm (rhs) injval.simps(1)}\\
  (2) & @{thm (lhs) injval.simps(2)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1"]} & $\dn$ & 
      @{thm (rhs) injval.simps(2)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1"]}\\
  (3) & @{thm (lhs) injval.simps(3)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>2"]} & $\dn$ & 
      @{thm (rhs) injval.simps(3)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>2"]}\\
  (4) & @{thm (lhs) injval.simps(4)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1" "v\<^sub>2"]} & $\dn$ 
      & @{thm (rhs) injval.simps(4)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1" "v\<^sub>2"]}\\
  (5) & @{thm (lhs) injval.simps(5)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1" "v\<^sub>2"]} & $\dn$ 
      & @{thm (rhs) injval.simps(5)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>1" "v\<^sub>2"]}\\
  (6) & @{thm (lhs) injval.simps(6)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>2"]} & $\dn$ 
      & @{thm (rhs) injval.simps(6)[of "r\<^sub>1" "r\<^sub>2" "c" "v\<^sub>2"]}\\
  (7) & @{thm (lhs) injval.simps(7)[of "r" "c" "v" "vs"]} & $\dn$ 
      & @{thm (rhs) injval.simps(7)[of "r" "c" "v" "vs"]}\\
  \end{tabular}
  \end{center}

  \noindent To better understand what is going on in this definition it
  might be instructive to look first at the three sequence cases (clauses
  (4)--(6)). In each case we need to construct an ``injected value'' for
  @{term "SEQ r\<^sub>1 r\<^sub>2"}. This must be a value of the form @{term
  "Seq DUMMY DUMMY"}\,. Recall the clause of the @{text derivative}-function
  for sequence regular expressions:

  \begin{center}
  @{thm (lhs) der.simps(5)[of c "r\<^sub>1" "r\<^sub>2"]} $\dn$ @{thm (rhs) der.simps(5)[of c "r\<^sub>1" "r\<^sub>2"]}
  \end{center}

  \noindent Consider first the @{text "else"}-branch where the derivative is @{term
  "SEQ (der c r\<^sub>1) r\<^sub>2"}. The corresponding value must therefore
  be of the form @{term "Seq v\<^sub>1 v\<^sub>2"}, which matches the left-hand
  side in clause~(4) of @{term inj}. In the @{text "if"}-branch the derivative is an
  alternative, namely @{term "ALT (SEQ (der c r\<^sub>1) r\<^sub>2) (der c
  r\<^sub>2)"}. This means we either have to consider a @{text Left}- or
  @{text Right}-value. In case of the @{text Left}-value we know further it
  must be a value for a sequence regular expression. Therefore the pattern
  we match in the clause (5) is @{term "Left (Seq v\<^sub>1 v\<^sub>2)"},
  while in (6) it is just @{term "Right v\<^sub>2"}. One more interesting
  point is in the right-hand side of clause (6): since in this case the
  regular expression @{text "r\<^sub>1"} does not ``contribute'' to
  matching the string, that means it only matches the empty string, we need to
  call @{const mkeps} in order to construct a value for how @{term "r\<^sub>1"}
  can match this empty string. A similar argument applies for why we can
  expect in the left-hand side of clause (7) that the value is of the form
  @{term "Seq v (Stars vs)"}---the derivative of a star is @{term "SEQ (der c r)
  (STAR r)"}. Finally, the reason for why we can ignore the second argument
  in clause (1) of @{term inj} is that it will only ever be called in cases
  where @{term "c=d"}, but the usual linearity restrictions in patterns do
  not allow us to build this constraint explicitly into our function
  definition.\footnote{Sulzmann and Lu state this clause as @{thm (lhs)
  injval.simps(1)[of "c" "c"]} $\dn$ @{thm (rhs) injval.simps(1)[of "c"]},
  but our deviation is harmless.}

  The idea of the @{term inj}-function to ``inject'' a character, say
  @{term c}, into a value can be made precise by the first part of the
  following lemma, which shows that the underlying string of an injected
  value has a prepended character @{term c}; the second part shows that the
  underlying string of an @{const mkeps}-value is always the empty string
  (given the regular expression is nullable since otherwise @{text mkeps}
  might not be defined).

  \begin{lemma}\mbox{}\smallskip\\\label{Prf_injval_flat}
  \begin{tabular}{ll}
  (1) & @{thm[mode=IfThen] Prf_injval_flat}\\
  (2) & @{thm[mode=IfThen] mkeps_flat}
  \end{tabular}
  \end{lemma}

  \begin{proof}
  Both properties are by routine inductions: the first one can, for example,
  be proved by induction over the definition of @{term derivatives}; the second by
  an induction on @{term r}. There are no interesting cases.\qed
  \end{proof}

  Having defined the @{const mkeps} and @{text inj} function we can extend
  \Brz's matcher so that a [lexical] value is constructed (assuming the
  regular expression matches the string). The clauses of the Sulzmann and Lu lexer are

  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) lexer.simps(1)} & $\dn$ & @{thm (rhs) lexer.simps(1)}\\
  @{thm (lhs) lexer.simps(2)} & $\dn$ & @{text "case"} @{term "lexer (der c r) s"} @{text of}\\
                     & & \phantom{$|$} @{term "None"}  @{text "\<Rightarrow>"} @{term None}\\
                     & & $|$ @{term "Some v"} @{text "\<Rightarrow>"} @{term "Some (injval r c v)"}                          
  \end{tabular}
  \end{center}

  \noindent If the regular expression does not match the string, @{const None} is
  returned. If the regular expression \emph{does}
  match the string, then @{const Some} value is returned. One important
  virtue of this algorithm is that it can be implemented with ease in any
  functional programming language and also in Isabelle/HOL. In the remaining
  part of this section we prove that this algorithm is correct.

  The well-known idea of POSIX matching is informally defined by the longest
  match and priority rule (see Introduction); as correctly argued in \cite{Sulzmann2014}, this
  needs formal specification. Sulzmann and Lu define an ``ordering
  relation'' between values and argue
  that there is a maximum value, as given by the derivative-based algorithm.
  In contrast, we shall introduce a simple inductive definition that
  specifies directly what a \emph{POSIX value} is, incorporating the
  POSIX-specific choices into the side-conditions of our rules. Our
  definition is inspired by the matching relation given by Vansummeren
  \cite{Vansummeren2006}. The relation we define is ternary and written as
  \mbox{@{term "s \<in> r \<rightarrow> v"}}, relating strings, regular expressions and
  values.
  %
  \begin{center}
  \begin{tabular}{c}
  @{thm[mode=Axiom] Posix.intros(1)}@{text "P"}@{term "ONE"} \qquad
  @{thm[mode=Axiom] Posix.intros(2)}@{text "P"}@{term "c"}\medskip\\
  @{thm[mode=Rule] Posix.intros(3)[of "s" "r\<^sub>1" "v" "r\<^sub>2"]}@{text "P+L"}\qquad
  @{thm[mode=Rule] Posix.intros(4)[of "s" "r\<^sub>2" "v" "r\<^sub>1"]}@{text "P+R"}\medskip\\
  $\mprset{flushleft}
   \inferrule
   {@{thm (prem 1) Posix.intros(5)[of "s\<^sub>1" "r\<^sub>1" "v\<^sub>1" "s\<^sub>2" "r\<^sub>2" "v\<^sub>2"]} \qquad
    @{thm (prem 2) Posix.intros(5)[of "s\<^sub>1" "r\<^sub>1" "v\<^sub>1" "s\<^sub>2" "r\<^sub>2" "v\<^sub>2"]} \\\\
    @{thm (prem 3) Posix.intros(5)[of "s\<^sub>1" "r\<^sub>1" "v\<^sub>1" "s\<^sub>2" "r\<^sub>2" "v\<^sub>2"]}}
   {@{thm (concl) Posix.intros(5)[of "s\<^sub>1" "r\<^sub>1" "v\<^sub>1" "s\<^sub>2" "r\<^sub>2" "v\<^sub>2"]}}$@{text "PS"}\\
  @{thm[mode=Axiom] Posix.intros(7)}@{text "P[]"}\medskip\\
  $\mprset{flushleft}
   \inferrule
   {@{thm (prem 1) Posix.intros(6)[of "s\<^sub>1" "r" "v" "s\<^sub>2" "vs"]} \qquad
    @{thm (prem 2) Posix.intros(6)[of "s\<^sub>1" "r" "v" "s\<^sub>2" "vs"]} \qquad
    @{thm (prem 3) Posix.intros(6)[of "s\<^sub>1" "r" "v" "s\<^sub>2" "vs"]} \\\\
    @{thm (prem 4) Posix.intros(6)[of "s\<^sub>1" "r" "v" "s\<^sub>2" "vs"]}}
   {@{thm (concl) Posix.intros(6)[of "s\<^sub>1" "r" "v" "s\<^sub>2" "vs"]}}$@{text "P\<star>"}
  \end{tabular}
  \end{center}

   \noindent
   We can prove that given a string @{term s} and regular expression @{term
   r}, the POSIX value @{term v} is uniquely determined by @{term "s \<in> r \<rightarrow> v"}.

  \begin{theorem}\mbox{}\smallskip\\\label{posixdeterm}
  \begin{tabular}{ll}
  @{text "(1)"} & If @{thm (prem 1) Posix1(1)} then @{thm (concl)
  Posix1(1)} and @{thm (concl) Posix1(2)}.\\
  @{text "(2)"} & @{thm[mode=IfThen] Posix_determ(1)[of _ _ "v" "v'"]}
  \end{tabular}
  \end{theorem}

  \begin{proof} Both by induction on the definition of @{term "s \<in> r \<rightarrow> v"}. 
  The second parts follows by a case analysis of @{term "s \<in> r \<rightarrow> v'"} and
  the first part.\qed
  \end{proof}

  \noindent
  We claim that our @{term "s \<in> r \<rightarrow> v"} relation captures the idea behind the two
  informal POSIX rules shown in the Introduction: Consider for example the
  rules @{text "P+L"} and @{text "P+R"} where the POSIX value for a string
  and an alternative regular expression, that is @{term "(s, ALT r\<^sub>1 r\<^sub>2)"},
  is specified---it is always a @{text "Left"}-value, \emph{except} when the
  string to be matched is not in the language of @{term "r\<^sub>1"}; only then it
  is a @{text Right}-value (see the side-condition in @{text "P+R"}).
  Interesting is also the rule for sequence regular expressions (@{text
  "PS"}). The first two premises state that @{term "v\<^sub>1"} and @{term "v\<^sub>2"}
  are the POSIX values for @{term "(s\<^sub>1, r\<^sub>1)"} and @{term "(s\<^sub>2, r\<^sub>2)"}
  respectively. Consider now the third premise and note that the POSIX value
  of this rule should match the string \mbox{@{term "s\<^sub>1 @ s\<^sub>2"}}. According to the
  longest match rule, we want that the @{term "s\<^sub>1"} is the longest initial
  split of \mbox{@{term "s\<^sub>1 @ s\<^sub>2"}} such that @{term "s\<^sub>2"} is still recognised
  by @{term "r\<^sub>2"}. Let us assume, contrary to the third premise, that there
  \emph{exist} an @{term "s\<^sub>3"} and @{term "s\<^sub>4"} such that @{term "s\<^sub>2"}
  can be split up into a non-empty string @{term "s\<^sub>3"} and a possibly empty
  string @{term "s\<^sub>4"}. Moreover the longer string @{term "s\<^sub>1 @ s\<^sub>3"} can be
  matched by @{text "r\<^sub>1"} and the shorter @{term "s\<^sub>4"} can still be
  matched by @{term "r\<^sub>2"}. In this case @{term "s\<^sub>1"} would \emph{not} be the
  longest initial split of \mbox{@{term "s\<^sub>1 @ s\<^sub>2"}} and therefore @{term "Seq v\<^sub>1
  v\<^sub>2"} cannot be a POSIX value for @{term "(s\<^sub>1 @ s\<^sub>2, SEQ r\<^sub>1 r\<^sub>2)"}. 
  The main point is that our side-condition ensures the longest 
  match rule is satisfied.

  A similar condition is imposed on the POSIX value in the @{text
  "P\<star>"}-rule. Also there we want that @{term "s\<^sub>1"} is the longest initial
  split of @{term "s\<^sub>1 @ s\<^sub>2"} and furthermore the corresponding value
  @{term v} cannot be flattened to the empty string. In effect, we require
  that in each ``iteration'' of the star, some non-empty substring needs to
  be ``chipped'' away; only in case of the empty string we accept @{term
  "Stars []"} as the POSIX value.

  Next is the lemma that shows the function @{term "mkeps"} calculates
  the POSIX value for the empty string and a nullable regular expression.

  \begin{lemma}\label{lemmkeps}
  @{thm[mode=IfThen] Posix_mkeps}
  \end{lemma}

  \begin{proof}
  By routine induction on @{term r}.\qed 
  \end{proof}

  \noindent
  The central lemma for our POSIX relation is that the @{text inj}-function
  preserves POSIX values.

  \begin{lemma}\label{Posix2}
  @{thm[mode=IfThen] Posix_injval}
  \end{lemma}

  \begin{proof}
  By induction on @{text r}. We explain two cases.

  \begin{itemize}
  \item[$\bullet$] Case @{term "r = ALT r\<^sub>1 r\<^sub>2"}. There are
  two subcases, namely @{text "(a)"} \mbox{@{term "v = Left v'"}} and @{term
  "s \<in> der c r\<^sub>1 \<rightarrow> v'"}; and @{text "(b)"} @{term "v = Right v'"}, @{term
  "s \<notin> L (der c r\<^sub>1)"} and @{term "s \<in> der c r\<^sub>2 \<rightarrow> v'"}. In @{text "(a)"} we
  know @{term "s \<in> der c r\<^sub>1 \<rightarrow> v'"}, from which we can infer @{term "(c # s)
  \<in> r\<^sub>1 \<rightarrow> injval r\<^sub>1 c v'"} by induction hypothesis and hence @{term "(c #
  s) \<in> ALT r\<^sub>1 r\<^sub>2 \<rightarrow> injval (ALT r\<^sub>1 r\<^sub>2) c (Left v')"} as needed. Similarly
  in subcase @{text "(b)"} where, however, in addition we have to use
  Prop.~\ref{derprop}(2) in order to infer @{term "c # s \<notin> L r\<^sub>1"} from @{term
  "s \<notin> L (der c r\<^sub>1)"}.

  \item[$\bullet$] Case @{term "r = SEQ r\<^sub>1 r\<^sub>2"}. There are three subcases:
  
  \begin{quote}
  \begin{description}
  \item[@{text "(a)"}] @{term "v = Left (Seq v\<^sub>1 v\<^sub>2)"} and @{term "nullable r\<^sub>1"} 
  \item[@{text "(b)"}] @{term "v = Right v\<^sub>1"} and @{term "nullable r\<^sub>1"} 
  \item[@{text "(c)"}] @{term "v = Seq v\<^sub>1 v\<^sub>2"} and @{term "\<not> nullable r\<^sub>1"} 
  \end{description}
  \end{quote}

  \noindent For @{text "(a)"} we know @{term "s\<^sub>1 \<in> der c r\<^sub>1 \<rightarrow> v\<^sub>1"} and
  @{term "s\<^sub>2 \<in> r\<^sub>2 \<rightarrow> v\<^sub>2"} as well as
  %
  \[@{term "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s\<^sub>2 \<and> s\<^sub>1 @ s\<^sub>3 \<in> L (der c r\<^sub>1) \<and> s\<^sub>4 \<in> L r\<^sub>2)"}\]

  \noindent From the latter we can infer by Prop.~\ref{derprop}(2):
  %
  \[@{term "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = s\<^sub>2 \<and> (c # s\<^sub>1) @ s\<^sub>3 \<in> L r\<^sub>1 \<and> s\<^sub>4 \<in> L r\<^sub>2)"}\]

  \noindent We can use the induction hypothesis for @{text "r\<^sub>1"} to obtain
  @{term "(c # s\<^sub>1) \<in> r\<^sub>1 \<rightarrow> injval r\<^sub>1 c v\<^sub>1"}. Putting this all together allows us to infer
  @{term "((c # s\<^sub>1) @ s\<^sub>2) \<in> SEQ r\<^sub>1 r\<^sub>2 \<rightarrow> Seq (injval r\<^sub>1 c v\<^sub>1) v\<^sub>2"}. The case @{text "(c)"}
  is similar.

  For @{text "(b)"} we know @{term "s \<in> der c r\<^sub>2 \<rightarrow> v\<^sub>1"} and 
  @{term "s\<^sub>1 @ s\<^sub>2 \<notin> L (SEQ (der c r\<^sub>1) r\<^sub>2)"}. From the former
  we have @{term "(c # s) \<in> r\<^sub>2 \<rightarrow> (injval r\<^sub>2 c v\<^sub>1)"} by induction hypothesis
  for @{term "r\<^sub>2"}. From the latter we can infer
  %
  \[@{term "\<not> (\<exists>s\<^sub>3 s\<^sub>4. s\<^sub>3 \<noteq> [] \<and> s\<^sub>3 @ s\<^sub>4 = c # s \<and> s\<^sub>3 \<in> L r\<^sub>1 \<and> s\<^sub>4 \<in> L r\<^sub>2)"}\]

  \noindent By Lem.~\ref{lemmkeps} we know @{term "[] \<in> r\<^sub>1 \<rightarrow> (mkeps r\<^sub>1)"}
  holds. Putting this all together, we can conclude with @{term "(c #
  s) \<in> SEQ r\<^sub>1 r\<^sub>2 \<rightarrow> Seq (mkeps r\<^sub>1) (injval r\<^sub>2 c v\<^sub>1)"}, as required.

  Finally suppose @{term "r = STAR r\<^sub>1"}. This case is very similar to the
  sequence case, except that we need to also ensure that @{term "flat (injval r\<^sub>1
  c v\<^sub>1) \<noteq> []"}. This follows from @{term "(c # s\<^sub>1)
  \<in> r\<^sub>1 \<rightarrow> injval r\<^sub>1 c v\<^sub>1"}  (which in turn follows from @{term "s\<^sub>1 \<in> der c
  r\<^sub>1 \<rightarrow> v\<^sub>1"} and the induction hypothesis).\qed
  \end{itemize}
  \end{proof}

  \noindent
  With Lem.~\ref{Posix2} in place, it is completely routine to establish
  that the Sulzmann and Lu lexer satisfies our specification (returning
  the null value @{term "None"} iff the string is not in the language of the regular expression,
  and returning a unique POSIX value iff the string \emph{is} in the language):

  \begin{theorem}\mbox{}\smallskip\\\label{lexercorrect}
  \begin{tabular}{ll}
  (1) & @{thm (lhs) lexer_correct_None} if and only if @{thm (rhs) lexer_correct_None}\\
  (2) & @{thm (lhs) lexer_correct_Some} if and only if @{thm (rhs) lexer_correct_Some}\\
  \end{tabular}
  \end{theorem}

  \begin{proof}
  By induction on @{term s} using Lem.~\ref{lemmkeps} and \ref{Posix2}.\qed  
  \end{proof}

  \noindent In (2) we further know by Thm.~\ref{posixdeterm} that the
  value returned by the lexer must be unique.   A simple corollary 
  of our two theorems is:

  \begin{corollary}\mbox{}\smallskip\\\label{lexercorrectcor}
  \begin{tabular}{ll}
  (1) & @{thm (lhs) lexer_correctness(2)} if and only if @{thm (rhs) lexer_correctness(2)}\\ 
  (2) & @{thm (lhs) lexer_correctness(1)} if and only if @{thm (rhs) lexer_correctness(1)}\\
  \end{tabular}
  \end{corollary}

  \noindent
  This concludes our
  correctness proof. Note that we have not changed the algorithm of
  Sulzmann and Lu,\footnote{All deviations we introduced are
  harmless.} but introduced our own specification for what a correct
  result---a POSIX value---should be. A strong point in favour of
  Sulzmann and Lu's algorithm is that it can be extended in various
  ways.

*}

section {* Extensions and Optimisations*}

text {*

  If we are interested in tokenising a string, then we need to not just
  split up the string into tokens, but also ``classify'' the tokens (for
  example whether it is a keyword or an identifier). This can be done with
  only minor modifications to the algorithm by introducing \emph{record
  regular expressions} and \emph{record values} (for example
  \cite{Sulzmann2014b}):

  \begin{center}  
  @{text "r :="}
  @{text "..."} $\mid$
  @{text "(l : r)"} \qquad\qquad
  @{text "v :="}
  @{text "..."} $\mid$
  @{text "(l : v)"}
  \end{center}
  
  \noindent where @{text l} is a label, say a string, @{text r} a regular
  expression and @{text v} a value. All functions can be smoothly extended
  to these regular expressions and values. For example \mbox{@{text "(l :
  r)"}} is nullable iff @{term r} is, and so on. The purpose of the record
  regular expression is to mark certain parts of a regular expression and
  then record in the calculated value which parts of the string were matched
  by this part. The label can then serve as classification for the tokens.
  For this recall the regular expression @{text "(r\<^bsub>key\<^esub> + r\<^bsub>id\<^esub>)\<^sup>\<star>"} for
  keywords and identifiers from the Introduction. With the record regular
  expression we can form \mbox{@{text "((key : r\<^bsub>key\<^esub>) + (id : r\<^bsub>id\<^esub>))\<^sup>\<star>"}}
  and then traverse the calculated value and only collect the underlying
  strings in record values. With this we obtain finite sequences of pairs of
  labels and strings, for example

  \[@{text "(l\<^sub>1 : s\<^sub>1), ..., (l\<^sub>n : s\<^sub>n)"}\]
  
  \noindent from which tokens with classifications (keyword-token,
  identifier-token and so on) can be extracted.

  Derivatives as calculated by \Brz's method are usually more complex
  regular expressions than the initial one; the result is that the
  derivative-based matching and lexing algorithms are often abysmally slow.
  However, various optimisations are possible, such as the simplifications
  of @{term "ALT ZERO r"}, @{term "ALT r ZERO"}, @{term "SEQ ONE r"} and
  @{term "SEQ r ONE"} to @{term r}. These simplifications can speed up the
  algorithms considerably, as noted in \cite{Sulzmann2014}. One of the
  advantages of having a simple specification and correctness proof is that
  the latter can be refined to prove the correctness of such simplification
  steps. While the simplification of regular expressions according to 
  rules like

  \begin{equation}\label{Simpl}
  \begin{array}{lcllcllcllcl}
  @{term "ALT ZERO r"} & @{text "\<Rightarrow>"} & @{term r} \hspace{8mm}%\\
  @{term "ALT r ZERO"} & @{text "\<Rightarrow>"} & @{term r} \hspace{8mm}%\\
  @{term "SEQ ONE r"}  & @{text "\<Rightarrow>"} & @{term r} \hspace{8mm}%\\
  @{term "SEQ r ONE"}  & @{text "\<Rightarrow>"} & @{term r}
  \end{array}
  \end{equation}

  \noindent is well understood, there is an obstacle with the POSIX value
  calculation algorithm by Sulzmann and Lu: if we build a derivative regular
  expression and then simplify it, we will calculate a POSIX value for this
  simplified derivative regular expression, \emph{not} for the original (unsimplified)
  derivative regular expression. Sulzmann and Lu \cite{Sulzmann2014} overcome this obstacle by
  not just calculating a simplified regular expression, but also calculating
  a \emph{rectification function} that ``repairs'' the incorrect value.
  
  The rectification functions can be (slightly clumsily) implemented  in
  Isabelle/HOL as follows using some auxiliary functions:

  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) F_RIGHT.simps(1)} & $\dn$ & @{text "Right (f v)"}\\
  @{thm (lhs) F_LEFT.simps(1)} & $\dn$ & @{text "Left (f v)"}\\
  
  @{thm (lhs) F_ALT.simps(1)} & $\dn$ & @{text "Right (f\<^sub>2 v)"}\\
  @{thm (lhs) F_ALT.simps(2)} & $\dn$ & @{text "Left (f\<^sub>1 v)"}\\
  
  @{thm (lhs) F_SEQ1.simps(1)} & $\dn$ & @{text "Seq (f\<^sub>1 ()) (f\<^sub>2 v)"}\\
  @{thm (lhs) F_SEQ2.simps(1)} & $\dn$ & @{text "Seq (f\<^sub>1 v) (f\<^sub>2 ())"}\\
  @{thm (lhs) F_SEQ.simps(1)} & $\dn$ & @{text "Seq (f\<^sub>1 v\<^sub>1) (f\<^sub>2 v\<^sub>2)"}\medskip\\
  %\end{tabular}
  %
  %\begin{tabular}{lcl}
  @{term "simp_ALT (ZERO, DUMMY) (r\<^sub>2, f\<^sub>2)"} & $\dn$ & @{term "(r\<^sub>2, F_RIGHT f\<^sub>2)"}\\
  @{term "simp_ALT (r\<^sub>1, f\<^sub>1) (ZERO, DUMMY)"} & $\dn$ & @{term "(r\<^sub>1, F_LEFT f\<^sub>1)"}\\
  @{term "simp_ALT (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2)"} & $\dn$ & @{term "(ALT r\<^sub>1 r\<^sub>2, F_ALT f\<^sub>1 f\<^sub>2)"}\\
  @{term "simp_SEQ (ONE, f\<^sub>1) (r\<^sub>2, f\<^sub>2)"} & $\dn$ & @{term "(r\<^sub>2, F_SEQ1 f\<^sub>1 f\<^sub>2)"}\\
  @{term "simp_SEQ (r\<^sub>1, f\<^sub>1) (ONE, f\<^sub>2)"} & $\dn$ & @{term "(r\<^sub>1, F_SEQ2 f\<^sub>1 f\<^sub>2)"}\\
  @{term "simp_SEQ (r\<^sub>1, f\<^sub>1) (r\<^sub>2, f\<^sub>2)"} & $\dn$ & @{term "(SEQ r\<^sub>1 r\<^sub>2, F_SEQ f\<^sub>1 f\<^sub>2)"}\\
  \end{tabular}
  \end{center}

  \noindent
  The functions @{text "simp\<^bsub>Alt\<^esub>"} and @{text "simp\<^bsub>Seq\<^esub>"} encode the simplification rules
  in \eqref{Simpl} and compose the rectification functions (simplifications can occur
  deep inside the regular expression). The main simplification function is then 

  \begin{center}
  \begin{tabular}{lcl}
  @{term "simp (ALT r\<^sub>1 r\<^sub>2)"} & $\dn$ & @{term "simp_ALT (simp r\<^sub>1) (simp r\<^sub>2)"}\\
  @{term "simp (SEQ r\<^sub>1 r\<^sub>2)"} & $\dn$ & @{term "simp_SEQ (simp r\<^sub>1) (simp r\<^sub>2)"}\\
  @{term "simp r"} & $\dn$ & @{term "(r, id)"}\\
  \end{tabular}
  \end{center} 

  \noindent where @{term "id"} stands for the identity function. The
  function @{const simp} returns a simplified regular expression and a corresponding
  rectification function. Note that we do not simplify under stars: this
  seems to slow down the algorithm, rather than speed it up. The optimised
  lexer is then given by the clauses:
  
  \begin{center}
  \begin{tabular}{lcl}
  @{thm (lhs) slexer.simps(1)} & $\dn$ & @{thm (rhs) slexer.simps(1)}\\
  @{thm (lhs) slexer.simps(2)} & $\dn$ & 
                         @{text "let (r\<^sub>s, f\<^sub>r) = simp (r "}$\backslash$@{text " c) in"}\\
                     & & @{text "case"} @{term "slexer r\<^sub>s s"} @{text of}\\
                     & & \phantom{$|$} @{term "None"}  @{text "\<Rightarrow>"} @{term None}\\
                     & & $|$ @{term "Some v"} @{text "\<Rightarrow>"} @{text "Some (inj r c (f\<^sub>r v))"}                          
  \end{tabular}
  \end{center}

  \noindent
  In the second clause we first calculate the derivative @{term "der c r"}
  and then simplify the result. This gives us a simplified derivative
  @{text "r\<^sub>s"} and a rectification function @{text "f\<^sub>r"}. The lexer
  is then recursively called with the simplified derivative, but before
  we inject the character @{term c} into the value @{term v}, we need to rectify
  @{term v} (that is construct @{term "f\<^sub>r v"}). Before we can establish the correctness
  of @{term "slexer"}, we need to show that simplification preserves the language
  and simplification preserves our POSIX relation once the value is rectified
  (recall @{const "simp"} generates a (regular expression, rectification function) pair):

  \begin{lemma}\mbox{}\smallskip\\\label{slexeraux}
  \begin{tabular}{ll}
  (1) & @{thm L_fst_simp[symmetric]}\\
  (2) & @{thm[mode=IfThen] Posix_simp}
  \end{tabular}
  \end{lemma}

  \begin{proof} Both are by induction on @{text r}. There is no
  interesting case for the first statement. For the second statement,
  of interest are the @{term "r = ALT r\<^sub>1 r\<^sub>2"} and @{term "r = SEQ r\<^sub>1
  r\<^sub>2"} cases. In each case we have to analyse four subcases whether
  @{term "fst (simp r\<^sub>1)"} and @{term "fst (simp r\<^sub>2)"} equals @{const
  ZERO} (respectively @{const ONE}). For example for @{term "r = ALT
  r\<^sub>1 r\<^sub>2"}, consider the subcase @{term "fst (simp r\<^sub>1) = ZERO"} and
  @{term "fst (simp r\<^sub>2) \<noteq> ZERO"}. By assumption we know @{term "s \<in>
  fst (simp (ALT r\<^sub>1 r\<^sub>2)) \<rightarrow> v"}. From this we can infer @{term "s \<in> fst (simp r\<^sub>2) \<rightarrow> v"}
  and by IH also (*) @{term "s \<in> r\<^sub>2 \<rightarrow> (snd (simp r\<^sub>2) v)"}. Given @{term "fst (simp r\<^sub>1) = ZERO"}
  we know @{term "L (fst (simp r\<^sub>1)) = {}"}. By the first statement
  @{term "L r\<^sub>1"} is the empty set, meaning (**) @{term "s \<notin> L r\<^sub>1"}.
  Taking (*) and (**) together gives by the \mbox{@{text "P+R"}}-rule 
  @{term "s \<in> ALT r\<^sub>1 r\<^sub>2 \<rightarrow> Right (snd (simp r\<^sub>2) v)"}. In turn this
  gives @{term "s \<in> ALT r\<^sub>1 r\<^sub>2 \<rightarrow> snd (simp (ALT r\<^sub>1 r\<^sub>2)) v"} as we need to show.
  The other cases are similar.\qed
  \end{proof}

  \noindent We can now prove relatively straightforwardly that the
  optimised lexer produces the expected result:

  \begin{theorem}
  @{thm slexer_correctness}
  \end{theorem}

  \begin{proof} By induction on @{term s} generalising over @{term
  r}. The case @{term "[]"} is trivial. For the cons-case suppose the
  string is of the form @{term "c # s"}. By induction hypothesis we
  know @{term "slexer r s = lexer r s"} holds for all @{term r} (in
  particular for @{term "r"} being the derivative @{term "der c
  r"}). Let @{term "r\<^sub>s"} be the simplified derivative regular expression, that is @{term
  "fst (simp (der c r))"}, and @{term "f\<^sub>r"} be the rectification
  function, that is @{term "snd (simp (der c r))"}.  We distinguish the cases
  whether (*) @{term "s \<in> L (der c r)"} or not. In the first case we
  have by Thm.~\ref{lexercorrect}(2) a value @{term "v"} so that @{term
  "lexer (der c r) s = Some v"} and @{term "s \<in> der c r \<rightarrow> v"} hold.
  By Lem.~\ref{slexeraux}(1) we can also infer from~(*) that @{term "s
  \<in> L r\<^sub>s"} holds.  Hence we know by Thm.~\ref{lexercorrect}(2) that
  there exists a @{term "v'"} with @{term "lexer r\<^sub>s s = Some v'"} and
  @{term "s \<in> r\<^sub>s \<rightarrow> v'"}. From the latter we know by
  Lem.~\ref{slexeraux}(2) that @{term "s \<in> der c r \<rightarrow> (f\<^sub>r v')"} holds.
  By the uniqueness of the POSIX relation (Thm.~\ref{posixdeterm}) we
  can infer that @{term v} is equal to @{term "f\<^sub>r v'"}---that is the 
  rectification function applied to @{term "v'"}
  produces the original @{term "v"}.  Now the case follows by the
  definitions of @{const lexer} and @{const slexer}.

  In the second case where @{term "s \<notin> L (der c r)"} we have that
  @{term "lexer (der c r) s = None"} by Thm.~\ref{lexercorrect}(1).  We
  also know by Lem.~\ref{slexeraux}(1) that @{term "s \<notin> L r\<^sub>s"}. Hence
  @{term "lexer r\<^sub>s s = None"} by Thm.~\ref{lexercorrect}(1) and
  by IH then also @{term "slexer r\<^sub>s s = None"}. With this we can
  conclude in this case too.\qed   

  \end{proof} 
*}

section {* The Correctness Argument by Sulzmann and Lu\label{argu} *}

text {*
%  \newcommand{\greedy}{\succcurlyeq_{gr}}
 \newcommand{\posix}{>}

  An extended version of \cite{Sulzmann2014} is available at the website of
  its first author; this includes some ``proofs'', claimed in
  \cite{Sulzmann2014} to be ``rigorous''. Since these are evidently not in
  final form, we make no comment thereon, preferring to give general reasons
  for our belief that the approach of \cite{Sulzmann2014} is problematic.
  Their central definition is an ``ordering relation'' defined by the
  rules (slightly adapted to fit our notation):

\begin{center}  
\begin{tabular}{@ {}c@ {\hspace{4mm}}c@ {}}	
@{thm[mode=Rule] C2[of "v\<^sub>1" "r\<^sub>1" "v\<^sub>1\<iota>" "v\<^sub>2" "r\<^sub>2" "v\<^sub>2\<iota>"]}\,(C2) &
@{thm[mode=Rule] C1[of "v\<^sub>2" "r\<^sub>2" "v\<^sub>2\<iota>" "v\<^sub>1" "r\<^sub>1"]}\,(C1)\smallskip\\

@{thm[mode=Rule] A1[of "v\<^sub>1" "v\<^sub>2" "r\<^sub>1" "r\<^sub>2"]}\,(A1) &
@{thm[mode=Rule] A2[of "v\<^sub>2" "v\<^sub>1" "r\<^sub>1" "r\<^sub>2"]}\,(A2)\smallskip\\

@{thm[mode=Rule] A3[of "v\<^sub>1" "r\<^sub>2" "v\<^sub>2" "r\<^sub>1"]}\,(A3) &
@{thm[mode=Rule] A4[of "v\<^sub>1" "r\<^sub>1" "v\<^sub>2" "r\<^sub>2"]}\,(A4)\smallskip\\

@{thm[mode=Rule] K1[of "v" "vs" "r"]}\,(K1) &
@{thm[mode=Rule] K2[of "v" "vs" "r"]}\,(K2)\smallskip\\

@{thm[mode=Rule] K3[of "v\<^sub>1" "r" "v\<^sub>2" "vs\<^sub>1" "vs\<^sub>2"]}\,(K3) &
@{thm[mode=Rule] K4[of "vs\<^sub>1" "r" "vs\<^sub>2" "v"]}\,(K4)
\end{tabular}
\end{center}

  \noindent The idea behind the rules (A1) and (A2), for example, is that a
  @{text Left}-value is bigger than a @{text Right}-value, if the underlying
  string of the @{text Left}-value is longer or of equal length to the
  underlying string of the @{text Right}-value. The order is reversed,
  however, if the @{text Right}-value can match a longer string than a
  @{text Left}-value. In this way the POSIX value is supposed to be the
  biggest value for a given string and regular expression.

  Sulzmann and Lu explicitly refer to the paper \cite{Frisch2004} by Frisch
  and Cardelli from where they have taken the idea for their correctness
  proof. Frisch and Cardelli introduced a similar ordering for GREEDY
  matching and they showed that their GREEDY matching algorithm always
  produces a maximal element according to this ordering (from all possible
  solutions). The only difference between their GREEDY ordering and the
  ``ordering'' by Sulzmann and Lu is that GREEDY always prefers a @{text
  Left}-value over a @{text Right}-value, no matter what the underlying
  string is. This seems to be only a very minor difference, but it has
  drastic consequences in terms of what properties both orderings enjoy.
  What is interesting for our purposes is that the properties reflexivity,
  totality and transitivity for this GREEDY ordering can be proved
  relatively easily by induction.

  These properties of GREEDY, however, do not transfer to the POSIX
  ``ordering'' by Sulzmann and Lu, which they define as @{text "v\<^sub>1 \<ge>\<^sub>r v\<^sub>2"}. 
  To start with, @{text "v\<^sub>1 \<ge>\<^sub>r v\<^sub>2"} is
  not defined inductively, but as $($@{term "v\<^sub>1 = v\<^sub>2"}$)$ $\vee$ $($@{term "(v\<^sub>1 >r
  v\<^sub>2) \<and> (flat v\<^sub>1 = flat (v\<^sub>2::val))"}$)$. This means that @{term "v\<^sub>1
  >(r::rexp) (v\<^sub>2::val)"} does not necessarily imply @{term "v\<^sub>1 \<ge>(r::rexp)
  (v\<^sub>2::val)"}. Moreover, transitivity does not hold in the ``usual''
  formulation, for example:

  \begin{falsehood}
  Suppose @{term "\<turnstile> v\<^sub>1 : r"}, @{term "\<turnstile> v\<^sub>2 : r"} and @{term "\<turnstile> v\<^sub>3 : r"}.
  If @{term "v\<^sub>1 >(r::rexp) (v\<^sub>2::val)"} and @{term "v\<^sub>2 >(r::rexp) (v\<^sub>3::val)"}
  then @{term "v\<^sub>1 >(r::rexp) (v\<^sub>3::val)"}.
  \end{falsehood}

  \noindent If formulated in this way, then there are various counter
  examples: For example let @{term r} be @{text "a + ((a + a)\<cdot>(a + \<zero>))"}
  then the @{term "v\<^sub>1"}, @{term "v\<^sub>2"} and @{term "v\<^sub>3"} below are values
  of @{term r}:

  \begin{center}
  \begin{tabular}{lcl}
  @{term "v\<^sub>1"} & $=$ & @{term "Left(Char a)"}\\
  @{term "v\<^sub>2"} & $=$ & @{term "Right(Seq (Left(Char a)) (Right Void))"}\\
  @{term "v\<^sub>3"} & $=$ & @{term "Right(Seq (Right(Char a)) (Left(Char a)))"}
  \end{tabular}
  \end{center}

  \noindent Moreover @{term "v\<^sub>1 >(r::rexp) v\<^sub>2"} and @{term "v\<^sub>2 >(r::rexp)
  v\<^sub>3"}, but \emph{not} @{term "v\<^sub>1 >(r::rexp) v\<^sub>3"}! The reason is that
  although @{term "v\<^sub>3"} is a @{text "Right"}-value, it can match a longer
  string, namely @{term "flat v\<^sub>3 = [a,a]"}, while @{term "flat v\<^sub>1"} (and
  @{term "flat v\<^sub>2"}) matches only @{term "[a]"}. So transitivity in this
  formulation does not hold---in this example actually @{term "v\<^sub>3
  >(r::rexp) v\<^sub>1"}!

  Sulzmann and Lu ``fix'' this problem by weakening the transitivity
  property. They require in addition that the underlying strings are of the
  same length. This excludes the counter example above and any
  counter-example we were able to find (by hand and by machine). Thus the
  transitivity lemma should be formulated as:

  \begin{conject}
  Suppose @{term "\<turnstile> v\<^sub>1 : r"}, @{term "\<turnstile> v\<^sub>2 : r"} and @{term "\<turnstile> v\<^sub>3 : r"},
  and also @{text "|v\<^sub>1| = |v\<^sub>2| = |v\<^sub>3|"}.\\
  If @{term "v\<^sub>1 >(r::rexp) (v\<^sub>2::val)"} and @{term "v\<^sub>2 >(r::rexp) (v\<^sub>3::val)"}
  then @{term "v\<^sub>1 >(r::rexp) (v\<^sub>3::val)"}.
  \end{conject}

  \noindent While we agree with Sulzmann and Lu that this property
  probably(!) holds, proving it seems not so straightforward: although one
  begins with the assumption that the values have the same flattening, this
  cannot be maintained as one descends into the induction. This is a problem
  that occurs in a number of places in the proofs by Sulzmann and Lu.

  Although they do not give an explicit proof of the transitivity property,
  they give a closely related property about the existence of maximal
  elements. They state that this can be verified by an induction on @{term r}. We
  disagree with this as we shall show next in case of transitivity. The case
  where the reasoning breaks down is the sequence case, say @{term "SEQ r\<^sub>1 r\<^sub>2"}.
  The induction hypotheses in this case are

\begin{center}
\begin{tabular}{@ {}c@ {\hspace{10mm}}c@ {}}
\begin{tabular}{@ {}l@ {\hspace{-7mm}}l@ {}}
IH @{term "r\<^sub>1"}:\\
@{text "\<forall> v\<^sub>1, v\<^sub>2, v\<^sub>3."} \\
  & @{term "\<turnstile> v\<^sub>1 : r\<^sub>1"}\;@{text "\<and>"}
    @{term "\<turnstile> v\<^sub>2 : r\<^sub>1"}\;@{text "\<and>"}
    @{term "\<turnstile> v\<^sub>3 : r\<^sub>1"}\\
  & @{text "\<and>"} @{text "|v\<^sub>1| = |v\<^sub>2| = |v\<^sub>3|"}\\
  & @{text "\<and>"} @{term "v\<^sub>1 >(r\<^sub>1::rexp) v\<^sub>2 \<and> v\<^sub>2 >(r\<^sub>1::rexp) v\<^sub>3"}\medskip\\
  & $\Rightarrow$ @{term "v\<^sub>1 >(r\<^sub>1::rexp) v\<^sub>3"}
\end{tabular} &
\begin{tabular}{@ {}l@ {\hspace{-7mm}}l@ {}}
IH @{term "r\<^sub>2"}:\\
@{text "\<forall> v\<^sub>1, v\<^sub>2, v\<^sub>3."}\\ 
  & @{term "\<turnstile> v\<^sub>1 : r\<^sub>2"}\;@{text "\<and>"}
    @{term "\<turnstile> v\<^sub>2 : r\<^sub>2"}\;@{text "\<and>"}
    @{term "\<turnstile> v\<^sub>3 : r\<^sub>2"}\\
  & @{text "\<and>"} @{text "|v\<^sub>1| = |v\<^sub>2| = |v\<^sub>3|"}\\
  & @{text "\<and>"} @{term "v\<^sub>1 >(r\<^sub>2::rexp) v\<^sub>2 \<and> v\<^sub>2 >(r\<^sub>2::rexp) v\<^sub>3"}\medskip\\
  & $\Rightarrow$ @{term "v\<^sub>1 >(r\<^sub>2::rexp) v\<^sub>3"}
\end{tabular}
\end{tabular}
\end{center} 

  \noindent We can assume that
  %
  \begin{equation}
  @{term "(Seq (v\<^sub>1\<^sub>l) (v\<^sub>1\<^sub>r)) >(SEQ r\<^sub>1 r\<^sub>2) (Seq (v\<^sub>2\<^sub>l) (v\<^sub>2\<^sub>r))"}
  \qquad\textrm{and}\qquad
  @{term "(Seq (v\<^sub>2\<^sub>l) (v\<^sub>2\<^sub>r)) >(SEQ r\<^sub>1 r\<^sub>2) (Seq (v\<^sub>3\<^sub>l) (v\<^sub>3\<^sub>r))"}
  \label{assms}
  \end{equation}

  \noindent hold, and furthermore that the values have equal length, namely:
  %
  \begin{equation}
  @{term "flat (Seq (v\<^sub>1\<^sub>l) (v\<^sub>1\<^sub>r)) = flat (Seq (v\<^sub>2\<^sub>l) (v\<^sub>2\<^sub>r))"}
  \qquad\textrm{and}\qquad
  @{term "flat (Seq (v\<^sub>2\<^sub>l) (v\<^sub>2\<^sub>r)) = flat (Seq (v\<^sub>3\<^sub>l) (v\<^sub>3\<^sub>r))"}
  \label{lens}
  \end{equation} 

  \noindent We need to show that @{term "(Seq (v\<^sub>1\<^sub>l) (v\<^sub>1\<^sub>r)) >(SEQ r\<^sub>1 r\<^sub>2)
  (Seq (v\<^sub>3\<^sub>l) (v\<^sub>3\<^sub>r))"} holds. We can proceed by analysing how the
  assumptions in \eqref{assms} have arisen. There are four cases. Let us
  assume we are in the case where we know

  \[
  @{term "v\<^sub>1\<^sub>l >(r\<^sub>1::rexp) v\<^sub>2\<^sub>l"}
  \qquad\textrm{and}\qquad
  @{term "v\<^sub>2\<^sub>l >(r\<^sub>1::rexp) v\<^sub>3\<^sub>l"}
  \]

  \noindent and also know the corresponding inhabitation judgements. This is
  exactly a case where we would like to apply the induction hypothesis
  IH~$r_1$. But we cannot! We still need to show that @{term "flat (v\<^sub>1\<^sub>l) =
  flat(v\<^sub>2\<^sub>l)"} and @{term "flat(v\<^sub>2\<^sub>l) = flat(v\<^sub>3\<^sub>l)"}. We know from
  \eqref{lens} that the lengths of the sequence values are equal, but from
  this we cannot infer anything about the lengths of the component values.
  Indeed in general they will be unequal, that is

  \[
  @{term "flat(v\<^sub>1\<^sub>l) \<noteq> flat(v\<^sub>2\<^sub>l)"}  
  \qquad\textrm{and}\qquad
  @{term "flat(v\<^sub>1\<^sub>r) \<noteq> flat(v\<^sub>2\<^sub>r)"}
  \]

  \noindent but still \eqref{lens} will hold. Now we are stuck, since the IH
  does not apply. As said, this problem where the induction hypothesis does
  not apply arises in several places in the proof of Sulzmann and Lu, not
  just for proving transitivity.

*}

section {* Conclusion *}

text {*

  We have implemented the POSIX value calculation algorithm introduced by
  Sulzmann and Lu
  \cite{Sulzmann2014}. Our implementation is nearly identical to the
  original and all modifications we introduced are harmless (like our char-clause for
  @{text inj}). We have proved this algorithm to be correct, but correct
  according to our own specification of what POSIX values are. Our
  specification (inspired from work by Vansummeren \cite{Vansummeren2006}) appears to be
  much simpler than in \cite{Sulzmann2014} and our proofs are nearly always
  straightforward. We have attempted to formalise the original proof
  by Sulzmann and Lu \cite{Sulzmann2014}, but we believe it contains
  unfillable gaps. In the online version of \cite{Sulzmann2014}, the authors
  already acknowledge some small problems, but our experience suggests
  that there are more serious problems. 
  
  Having proved the correctness of the POSIX lexing algorithm in
  \cite{Sulzmann2014}, which lessons have we learned? Well, this is a
  perfect example for the importance of the \emph{right} definitions. We
  have (on and off) explored mechanisations as soon as first versions
  of \cite{Sulzmann2014} appeared, but have made little progress with
  turning the relatively detailed proof sketch in \cite{Sulzmann2014} into a
  formalisable proof. Having seen \cite{Vansummeren2006} and adapted the
  POSIX definition given there for the algorithm by Sulzmann and Lu made all
  the difference: the proofs, as said, are nearly straightforward. The
  question remains whether the original proof idea of \cite{Sulzmann2014},
  potentially using our result as a stepping stone, can be made to work?
  Alas, we really do not know despite considerable effort.


  Closely related to our work is an automata-based lexer formalised by
  Nipkow \cite{Nipkow98}. This lexer also splits up strings into longest
  initial substrings, but Nipkow's algorithm is not completely
  computational. The algorithm by Sulzmann and Lu, in contrast, can be
  implemented with ease in any functional language. A bespoke lexer for the
  Imp-language is formalised in Coq as part of the Software Foundations book
  by Pierce et al \cite{Pierce2015}. The disadvantage of such bespoke lexers is that they
  do not generalise easily to more advanced features.
  Our formalisation is available from the Archive of Formal Proofs \cite{aduAFP16}
  under \url{http://www.isa-afp.org/entries/Posix-Lexing.shtml}.\medskip

  \noindent
  {\bf Acknowledgements:}
  We are very grateful to Martin Sulzmann for his comments on our work and 
  moreover for patiently explaining to us the details in \cite{Sulzmann2014}. We
  also received very helpful comments from James Cheney and anonymous referees.
  %  \small
  \bibliographystyle{plain}
  \bibliography{root}

*}


(*<*)
end
(*>*)