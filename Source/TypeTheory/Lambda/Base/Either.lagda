\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Either where


open import TypeTheory.Lambda.Base.Import
  hiding (_>>=_ ; _>>_)
open import TypeTheory.Lambda.Base.TypeProperties

-- open TypeNotation

\end{code}


\section{Error handling}\label{Base:Error}
In functional programming languages, the sum type is useful for handling errors
and exceptions. This functionality is implemented as part of a monad
interface \citep{Monads}, but for the sake of brevity we specialize the
following definitions to our use case.

\medskip

For a type $Err$ containing error information, the function type $A \to Err + B$
models a function which, given an element of $A$, either fails with an
error of type $Err$, or succeeds with an element of $B$.

Given such a result, we can feed it into another possibly failing function by
inspecting whether it is a success or a failure:
\begin{code}[hide]
private
\end{code}
\begin{code}
  _>>=_ : ∀{ℓ}  -> {A B Err : 𝒰 ℓ}
                -> (Err + A) -> (A -> Err + B) -> Err + B
  _>>=_ (left e)   f = left e
  _>>=_ (right a)  f = f a
\end{code}

\noindent
We can also ignore the value of a successful result and only propagate errors:
\begin{code}
  _>>_ : ∀{ℓ}  -> {A B Err : 𝒰 ℓ}
              -> (Err + A) -> (Err + B) -> (Err + B)
  _>>_ (left e)   b = left e
  _>>_ (right _)  b = b
\end{code}

\noindent
Furthermore, given two such functions, they can be chained together:
\begin{code}
  _>=>_ :  ∀{ℓ}  -> {A B C Err : 𝒰 ℓ}
                -> (A -> Err + B) -> (B -> Err + C) -> (A -> Err + C)
  _>=>_ f g a = f a >>= g
\end{code}








\begin{code}[hide]

module _ {A B : 𝒰₀} where

  π-right : (l : B) -> (a : A + B) ->  B
  π-right l (left _)   = l
  π-right _ (right r)  = r

  π-left : (l : A) -> (a : A + B) -> A
  π-left l (right _) = l
  π-left _ (left l) = l

  right-inj : {x y : B} -> (right x == right y) -> x == y
  right-inj {x} p = cong (π-right x) p

  left-inj : {x y : A} -> (left x == left y) -> x == y
  left-inj {x} p = cong (π-left x) p


  case-right : A + B -> 𝒰₀
  case-right (left _) = ⊥
  case-right (right _) = ⊤

  leftNotRight : {a : A} {b : B} -> left {B = B} a == right b -> ⊥
  leftNotRight p = subst {P = case-right} (sym p) tt

  Either-isDisc : (DA : isDiscrete A) -> (DB : isDiscrete B) -> isDiscrete (A + B)
  Either-isDisc DA DB (left x) (left y) = mapDiscrete left (λ p x -> p (left-inj x)) (DA x y)
  Either-isDisc DA DB (left x) (right y) = no (leftNotRight)
  Either-isDisc DA DB (right x) (left y) = no (leftNotRight ∘ sym)
  Either-isDisc DA DB (right x) (right y) = mapDiscrete right (λ p x -> p (right-inj x)) (DB x y)

\end{code}
