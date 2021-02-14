
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Fin where


open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Path
open import TypeTheory.Lambda.Base.TypeProperties
open import TypeTheory.Lambda.Base.Nat

----------------------------------------------------------------------
-- Fin


--------------------------------------
-- Definition
\end{code}

In this chapter we define some objects which will serve as basic building blocks
later on.

\section{Finite type}
We often need a finite set of indices. For a given size $n$, such a type can be
modelled by the sum of natural numbers $i$ smaller than $n$, that is:
\[
  \sum_{i : ℕ} i < n
\]
In Agda, in order to improve type inference and error messages, we explicitly
define this type as a record, instead of reusing $Σ$.

\begin{definition}
Given a natural number $n$, we define a type $\AR{Fin}\,n$, which has exactly $n$
elements, as the type containing natural numbers smaller than $n$. Sometimes we
refer to the elements as indices.
\begin{code}
record Fin (n : ℕ) : 𝒰₀ where
  constructor _⌈_
  field
    ⍛ : ℕ
    ⍛less : ⍛ < n
\end{code}
\end{definition}
\noindent
Elements of $\AR{Fin}\:n$ can be constructed by giving a natural number
and a proof that it is smaller than $n$. For construction and
pattern matching, the infix constructor $\AIC{\_⌈\_}$ is used.

\begin{code}[hide]

open Fin public

fnat = ⍛
fnatless = ⍛less
infixl 80 _⌈_
pattern fin a b = a ⌈ b



--------------------------------------
-- Properties
finEqual : ∀{n} -> (l : ℕ) -> {p q : l < n} -> fin l p == fin l q
finEqual l {p} {q} i = fin l (ℕOrd-isProp p q i)




finEqual2 : ∀{n} -> (i : Fin n) -> (j : Fin n) -> {p : fnat i == fnat j} -> i == j
finEqual2 {n} (fin i i<n) (fin j j<n) {i=j} k = fin (i=j k) (compi (λ x -> x < n) i=j i<n j<n (ℕOrd-isProp _ _) k)

Fin-isDisc : ∀{n} -> (i j : Fin n) -> (isDec (i == j))
Fin-isDisc {n} (i ⌈ ip) (j ⌈ jp) with ℕ-isDisc i j
Fin-isDisc {n} (i ⌈ ip) (j ⌈ jp) | yes x = yes (finEqual2 (i ⌈ ip) (j ⌈ jp) {x})
Fin-isDisc {n} (i ⌈ ip) (j ⌈ jp) | no x = no (x ∘ cong ⍛)

Fin-isSet : ∀{n} -> isSet (Fin n)
Fin-isSet = hedberg Fin-isDisc


fpred : ∀{n} -> (i : Fin (suc n)) -> (0 < fnat i) -> Fin (n)
fpred (fin zero _) (p) = ⊥-elim (less-antirefl p)
fpred (fin (suc n) p) _ = fin (n) (pred-monotone p)

\end{code}


\begin{example}
  Common indices are:
\begin{enumerate}[(i)]
\item
  In every finite type with at least one element, there is an element $\AF{fzero}$.
\begin{code}
fzero : ∀{n} -> Fin (suc n)
fzero = zero ⌈ 0<suc
\end{code}
\item
  Given an index, we can construct its successor. It lives
  in the next greater finite type.
\begin{code}
fsuc : ∀{n} -> Fin n -> Fin (suc n)
fsuc (k ⌈ k<n) = (suc k) ⌈ (suc-monotone k<n)
\end{code}
\item
  Combining these functions, the element $\AF{fone}$ of finite types with at
  least two elements is defined as follows.
\begin{code}
fone : ∀{n} -> Fin (suc (suc n))
fone = fsuc fzero
\end{code}
\end{enumerate}
\end{example}


\begin{code}[hide]

flast : ∀{n} -> Fin (suc n)
flast {n} = fin n (diff zero refl)

fsmaller : ∀{n} -> (i j : Fin (suc n)) -> (fnat i < fnat j) -> Fin n
fsmaller (fin ni nip) (fin nj njp) i<j = fin ni (killLeSuc i<j njp)

finNatFin : ∀ {n} -> (i : Fin n) -> (lep : ((fnat i) < n)) -> (fin (fnat i) (lep)) == i
finNatFin (fin ni nip) lep = finEqual ni

natFinNat : ∀{n} -> (i : ℕ) -> (lep : i < n) -> fnat (fin i (lep)) == i
natFinNat i lep = refl

injFin : ∀{n} -> (i : Fin n) -> Fin (suc n)
injFin (fin ni (diff k kp)) = fin ni (diff (suc k) (cong suc kp))


fcompare-eq : ∀{n} -> (i j : Fin n) -> EqComp i j
fcompare-eq (i) (j) with compare-eq (fnat i) (fnat j)
fcompare-eq {n} (i) (j) | equal x =
  let
      p : i == j
      p = finEqual2 i j {p = x}
  in equal p
fcompare-eq (fin i ip) (fin j jp) | noteq x = noteq $ x ∘ (cong fnat)


--------------------------------------
-- Comparisons


infixl 80 _↥_
_↥_ : (a b : ℕ) -> ℕ
_↥_ i j with compare i j
...         | less a<b = i
...         | equal a<b = (suc i)
...         | greater a<b = (suc i)

infixl 60 _↧_
_↧_ : (i j : ℕ) -> ℕ
_↧_ i j with compare i j
_↧_ i j | less x = i
_↧_ i j | equal x = i
_↧_ zero j    | greater x = ⊥-elim $ lessZero-⊥ x
_↧_ (suc i) j | greater x = i

↥fp : ∀{n} -> (j i : ℕ) -> (j < n) -> (i < suc n) -> ((j ↥ i) < suc n)
↥fp {n} j i j<n i<sn with compare j i
↥fp {n} j i j<n i<sn | less p = lt-to-leq j<n
↥fp {n} j i j<n i<sn | equal p = suc-monotone j<n
↥fp {n} j i j<n i<sn | greater p = suc-monotone j<n


_↥f_ : ∀{n} -> (j : Fin n) -> (i : Fin (suc n)) -> Fin (suc n)
_↥f_ {n} (j ⌈ jp) (i ⌈ ip) = (j ↥ i) ⌈ ↥fp j i jp ip



↧fp : ∀{n} -> (j i : ℕ) -> (j < suc n) -> (i < suc n) -> (j == i -> ⊥) -> j ↧ i < n
↧fp j i j<ssn i<sn p with compare j i
↧fp j i j<ssn i<sn p | less x = (killLeSuc x i<sn)
↧fp j i j<ssn i<sn p | equal x = ⊥-elim (p x)
↧fp zero i j<ssn i<sn p | greater x = ⊥-elim (lessZero-⊥ x)
↧fp (suc j) i j<ssn i<sn p | greater x = pred-monotone j<ssn

↧f : ∀{n} -> (j : Fin (suc n)) -> (i : Fin (suc n)) -> (⍛ j == ⍛ i -> ⊥) -> Fin (n)
↧f (j ⌈ jp) (i ⌈ ip) p = (j ↧ i) ⌈ ↧fp j i jp ip p

\end{code}
