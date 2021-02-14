
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Introduction.Bootstrap where

open import TypeTheory.Lambda.Base.Import
  hiding (Bool ; ⊤ ; ⊥ ; _+_ ; _∧_ ; ℕ)

open import Agda.Builtin.String

\end{code}


\section*{Types}
Agda is a dependently typed programming language. The basic constructions
are terms and types. We say a term $t$ is of type $\AD{A}$ by writing $t : \AD{A}$.

\section*{Universes}
Types themselves may be considered as terms. A type of types is called a universe.
Since such a universe needs to have a type itself, there is hierarchy of universes 𝒰₀, 𝒰₁, 𝒰₂, ... .
Every type lives in a specific universe, and every universe lives in the next higher one.
For example, if $A$ lives in $𝒰₃$, then $t : \AD{A} : 𝒰₃ : 𝒰₄ : 𝒰₅ : ...$.



\section*{Simple types}

Like most programming languages, Agda provides builtin types such as \AD{Int} or
\AD{String} in order to faciliate "real world" programming.

Furthermore it offers a mechanism for defining new data types. This is done
by specifying in which universe this type lives, and how it's terms
can be constructed.

\begin{definition}
The type \AD{Bool} is defined by:
\begin{code}
data Bool : 𝒰₀ where
  true   : Bool
  false  : Bool
\end{code}
\end{definition}

\begin{definition}{(\AD{⊤} and \AD{⊥})}
\leavevmode
\begin{enumerate}[i)]
\item The type \AD{⊤} (top) has a single inhabitant:
  \begin{code}
data ⊤ : 𝒰₀ where
  tt : ⊤
  \end{code}
\item The type \AD{⊥} (bottom) has no inhabitants:
  \begin{code}
data ⊥ : 𝒰₀ where
  \end{code}
\end{enumerate}
\end{definition}

\section*{Functions}
Functions are defined by specifying their type, and how they act on elements of the input type.
The type is written using the usual mathematical arrow notation, e.g. $\AD{Bool} \to \AD{Bool}$.
The value of the function may be defined by specifying it separately for every constructor
of the argument. Such a language feature is called "pattern matching".
Of course, the definition is only accepted if the provided patterns cover all possible input values.

\begin{example}
(Boolean negation)
\begin{code}
negate : Bool -> Bool
negate true   = false
negate false  = true
\end{code}
\end{example}

Functions with multiple arguments, like the logical connective ∧, whose type in set theory
would be written like $∧ : Bool × Bool \to Bool$ are usually defined as a function with a
single argument which returns a function; i.e. $\AF{\_∧\_} : \AD{Bool} \to (\AD{Bool} \to \AD{Bool})$.
This can be seen to be equivalent to the first version. %TODO: cite
Since the function arrow is defined to be right associative, we can even skip the parentheses.

\begin{example}
(Boolean ∧)
\begin{code}
_∧_ : Bool -> Bool -> Bool
_∧_ true   true   = true
_∧_ true   false  = false
_∧_ false  true   = false
_∧_ false  false  = false
\end{code}
\end{example}

%TODO: Remark about usage of _



\section*{Compound data types}
Constructors of data types may have parameters. In order to construct an element we need to apply the
constructor to the necessary arguments. Later, these values can be inspected by pattern matching.
Since calling a constructor is effectively the same as calling a function, the same syntax is used.
\begin{example}
The type $\AD{Result}$ represents the result of $\AF{f₀}$, a partial function, which either returns a boolean value,
or fails with an error message.
\begin{code}
data Result : 𝒰₀ where
  failure  : String -> Result
  success  : Bool -> Result

f₀ : Bool -> Result
f₀ false  = failure "An error occured."
f₀ true   = success true
\end{code}
\end{example}
Data types may be generic, which means, that they can take type parameters, which decide, what type
their constructors act on.

In the case of $\AD{Result}$, by abstracting over the content of $\AIC{failure}$ and of $\AIC{success}$,
we obtain the sum type.
\begin{definition}
(The sum type \AD{+})
\begin{code}
data _+_ (A : 𝒰₀) (B : 𝒰₀) : 𝒰₀ where
  left   : A -> A + B
  right  : B -> A + B
\end{code}
\end{definition}
Thus we could write $\AD{Result}$ as $\AD{String}\,\AD{+}\,\AD{Bool}$.

\section*{Record types}
If we want to define a type which has a single constructor and lots of arguments,
the record type notation is useful. A record is specified by it's type parameters,
the universe it lives in, named fields that it should contain and an optional
constructor name.

\begin{definition}
(The product type \AR{×})
\begin{code}
record _×_ (A : 𝒰₀) (B : 𝒰₀) : 𝒰₀ where
  constructor _,_
  field
    fst  : A
    snd  : B
\end{code}
\end{definition}
The fields \AF{fst} and \AF{snd} are actually projection functions of type $\AFd{fst} : \AD{A}\,\AR{×}\,\AD{B} \to \AD{A}$
and $\AFd{snd} : \AD{A}\,\AR{×}\,\AD{B} \to \AD{B}$.


\section*{The natural numbers}
In order to define the natural numbers, we observe that for every number there are
only two possibilities: Either it is zero, or it is the successor of another
natural number. Therefore we define them by the follwing recursive data type:
\begin{definition}
(The natural numbers ℕ)
\begin{code}
data ℕ : 𝒰₀ where
  zero  : ℕ
  suc   : ℕ -> ℕ

\end{code}
\end{definition}
The sequence of natural numbers then is:
\begin{equation}
\AIC{zero},\;\AIC{suc}\:\AIC{zero},\;\AIC{suc}\:(\AIC{suc}\:\AIC{zero}),...
\end{equation}
