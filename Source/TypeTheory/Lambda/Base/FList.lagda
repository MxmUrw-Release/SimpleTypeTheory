
\section{Finite lists}

\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.FList where


open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Basics
open import TypeTheory.Lambda.Base.Nat
open import TypeTheory.Lambda.Base.Fin

variable
  {ℓ} : ULevel
  {A} : 𝒰 ℓ
  {m n} : ℕ

infixr 80 _,,_


\end{code}

\begin{definition}
Given a type $A$, a \textbf{finite list over $A$ of length $n$} is a
function $\AR{Fin}\:n \to A$, mapping indices to elements.
\begin{code}
FList : 𝒰 ℓ -> ℕ -> 𝒰 ℓ
FList A n = Fin n -> A
\end{code}
\end{definition}

\begin{remark}
  To construct a list $Γ$ means to construct a function which, given an index $i$,
  returns the $i$-th element of this list. We access it by writing $Γ\:i$.
\end{remark}


\begin{example}
  We look at some examples for constructing lists.
  \begin{enumerate}[(i)]
  \item
    Empty list over $A$. We are given an index of type $\AR{Fin}\:0$ and
    have to return the element at this position. But being given such an
    index means we are given a natural number $k : ℕ$ and a proof that $k < 0$.
    This is a contradiction, so we can conclude by applying $\AF{⊥-elim}$.
\begin{code}
[] : FList A 0
[] (k ⌈ k<0) = ⊥-elim (lessZero-⊥ k<0)
\end{code}
  \item
    Prepending $x$ to $Γ$. The resulting list has $x$ at index $0$
    (first case)
    and $Γ\:i$ at index $i + 1$ (second case).
    In order to have an index of type $\AR{Fin}\:n$ which is accepted by $Γ$,
    we turn the proof of $\AF{suc}\:i < \AF{suc}\:n$ into a proof of $i<n$ by applying
    $\AF{pred-monotone}$.
\begin{code}
_,,_ : A -> FList A n -> FList A (suc n)
(x ,, Γ) (zero   ⌈ _)      = x
(x ,, Γ) (suc i  ⌈ si<sn)  = Γ (i ⌈ pred-monotone si<sn)
\end{code}

  \item
    Inserting $x$ at index $j$. In order to compute the element at position $i$,
    we compare the natural number part of both indices. If $i$ is smaller than
    $j$, which means that we are trying to access an element before the
    insertion point, we simply return the $i$-th element of the original list.
    If we are exactly at the point of insertion, we return the
    new element $x$. Else, if we are already past the point of insertion, we
    first decrement our given index by 1 ($\AF{fpred}$), in order to access the correct
    element in the original list.
    \newpage
\begin{code}
insertL : (Γ : FList A n) -> Fin (suc n) -> A -> FList A (suc n)
insertL Γ j x i with compare (⍛ i) (⍛ j)
...                    | less i<j     = Γ (fsmaller i j i<j)
...                    | equal i=j    = x
...                    | greater i>j  = Γ (fpred i (mkNotZero i>j))
\end{code}

\end{enumerate}
\end{example}

\begin{notation}
We denote the insertion of an element $x$ at position $j$ into a list $Γ$ by:
\begin{code}
_↓_ : Fin (suc n) -> A -> FList A n -> FList A (suc n)
(j ↓ x) Γ = insertL Γ j x
\end{code}
\end{notation}







\begin{remark}
Lists may be defined in different ways. In addition to the definition
shown above, we could also define a list inductively with two constructors:
\begin{itemize}
\setlength\itemsep{0em}
\item $[]$ (the empty list)
\item $x ,, Γ$ (an element $x : A$ prepended to some list $Γ : List\,A$)
\end{itemize}
Depending on which definition is chosen, different list operations become easier
to implement. With the former definition, accessing the $i$-th element of a List
$Γ$ for some index $i : \AR{Fin}\,n$ is simply $Γ\,i$.
The latter definition makes prepending elements and writing functions which
recurse on the head $x$ and tail $Γ$ easier.
\end{remark}

Since we often need to access and insert elements in the middle of the list, we
choose the former definition. But this comes with a cost; prepending an element to a
list and then taking the tail is not definitionally equal to the original list:
\[
  Γ \not\equiv \AF{tail}\:(x\:,,\:Γ)
\]

\begin{code}[hide]
tail : FList A (suc n) -> FList A n
tail l i = l (fsuc i)
\end{code}

\noindent
Instead, we often have to explicitly use the following equality:
\begin{code}
tail= : (x : A) -> (Γ : FList A n) -> Γ == tail (x ,, Γ)
\end{code}
\begin{code}[hide]
tail= {n} τ Γ i j = Γ (finEqual (fnat j) {p = fnatless j} {q = pred-monotone (fnatless (fsuc j))} i)
\end{code}




\begin{code}[hide]


module _ {ℓ} {A : 𝒰 ℓ} where
  last : ∀{n} -> FList A (suc n) -> FList A n × A
  last {n} xs = (λ i -> xs (injFin i)) , xs flast

  tailComma : ∀{n} -> (a : A) -> (L : FList A n) -> (i : Fin n) -> tail (a ,, L) i == L i
  tailComma {n} a L i with fsuc i
  ... | ii = cong L (finEqual (⍛ i))


  size : ∀{n} -> FList A n -> Fin (suc n)
  size {n} _ = fin n (diff zero refl)

  flfold : {B : 𝒰₀} {n : ℕ} -> (B -> A -> B) -> B -> FList A n -> B
  flfold {B} {zero} f b l = b
  flfold {B} {suc n} f b l = flfold f (f b (l fzero)) (tail l)






  -- insertLSmaller : ∀{n} -> (Γ : FList A n) -> (j : Fin (suc n)) -> (B : A) -> (i : Fin (suc n)) -> (pi<j : fnat i < fnat j) -> ⦅ j ↓ B ⦆ Γ i == Γ (fsmaller i j pi<j)
  -- insertLSmaller Γ j B i pi<j = {!!} -- with compare (fnat i) (fnat j)
  -- -- ...                            | less i<j     = λ 𝒊 -> Γ (fsmaller i j (ℕOrd-isProp i<j pi<j 𝒊))
  -- -- ...                            | equal i=j    = ⊥-elim (lessEqual-⊥ pi<j i=j)
  -- -- ...                            | greater i>j  = ⊥-elim (lessGreater-⊥ pi<j i>j)

  insertLGreater : ∀{n} -> (Γ : FList A n) -> (j : Fin (suc n)) -> (B : A) -> (i : Fin (suc n)) -> (pj<i : fnat j < fnat i) -> ( j ↓ B ) Γ i == Γ (fpred i (mkNotZero pj<i))
  insertLGreater Γ j B i pj<i with compare (fnat i) (fnat j)
  ...                            | less i<j     = ⊥-elim (lessGreater-⊥ pj<i i<j)
  ...                            | equal i=j    = ⊥-elim (lessEqual-⊥ pj<i (sym i=j))
  ...                            | greater i>j  = cong (Γ ∘ fpred i) (ℕOrd-isProp _ _)


  insertLComma : ∀{n} -> (Γ : FList A n) -> (j : Fin (suc n)) -> (B : A) -> {X : A} -> (i : Fin (suc (suc n))) -> (X ,, ( j ↓ B ) Γ) i == ( (fsuc j) ↓ B ) (X ,, Γ) i
  insertLComma Γ j B {X} (fin zero ip) = refl
  insertLComma Γ j B {X} (fin (suc i) ip) with compare (i) (fnat j)
  ...                                        | less i<j = cong Γ (finEqual2 _ _ {refl})
  ...                                        | equal i=j = refl
  ...                                        | greater (diff k pk) with i
  ...                                                                 | zero = ⊥-elim (zNotS pk)
  ...                                                                 | suc ii = refl


  insertLZero : ∀{n} -> (Γ : FList A n) -> (B : A) -> (i : Fin (suc n)) -> ( fzero ↓ B ) Γ i == (B ,, Γ) i
  insertLZero {n} Γ B (fin zero _) = refl
  insertLZero {n} Γ B (fin (suc i) _) = refl

  insertLEq : ∀{n} -> (Γ : FList A n) -> (B : A) -> (i : Fin (suc n)) -> (i ↓ B) Γ i == B
  insertLEq Γ B i with compare (fnat i) (fnat i)
  insertLEq Γ B i | less x = ⊥-elim $ lessEqual-⊥ x refl
  insertLEq Γ B i | equal x = refl
  insertLEq Γ B i | greater x = ⊥-elim $ lessEqual-⊥ x refl


  insertLEq2 : ∀{n} -> (Γ : FList A n) -> (B : A)
                    -> (i : Fin (suc n)) -> (j : Fin ((suc n))) -> ⍛ i == ⍛ j
                    -> (i ↓ B) Γ j == B
  insertLEq2 Γ B i j i=j with compare (fnat j) (fnat i)
  insertLEq2 Γ B i j i=j | less x = ⊥-elim $ lessEqual-⊥ x (sym i=j)
  insertLEq2 Γ B i j i=j | equal x = refl
  insertLEq2 Γ B i j i=j | greater x = ⊥-elim $ lessEqual-⊥ x (i=j)





  insertLShift : ∀{n} -> (Γ : FList A n) -> (i : Fin (suc n)) -> {x : A} -> (j : Fin n) -> (Γ j == x) -> (y : A) -> (i ↓ y) Γ (j ↥f i) == x
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y with compare (j) (i)
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | less q with compare j i
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | less q | less r    = cong Γ (finEqual j) ∙ p
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | less q | equal r   = ⊥-elim (lessEqual-⊥ q r)
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | less q | greater r = ⊥-elim (lessGreater-⊥ q r)
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | equal q with compare (suc j) i
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | equal q | less r    = ⊥-elim (lessEqual-⊥ (pred-monotone (lt-to-leq r)) q)
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | equal q | equal r   = ⊥-elim (less-antirefl (eq-to-leq (r ∙ sym q)))
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | equal q | greater r = cong Γ (finEqual j) ∙ p
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | greater q with compare (suc j) i
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | greater q | less r    = ⊥-elim (lessGreater-⊥ q (pred-monotone (lt-to-leq r)))
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | greater q | equal r   = ⊥-elim (lessGreater-⊥ q (pred-monotone (eq-to-leq r)))
  insertLShift {n} Γ (i ⌈ ip) {x} (j ⌈ jp) p y | greater q | greater r = cong Γ (finEqual j) ∙ p



  insertLShiftL₂ : ∀{n} -> (Γ : FList A n) -> (i : Fin (suc n)) -> (y : A) -> (j : Fin n) -> (i ↓ y) Γ (j ↥f i) == (Γ j)
  insertLShiftL₂ Γ i y j = insertLShift Γ i j refl y


  insertLShiftL : ∀{n} -> (Γ : FList A n) -> (i : Fin (suc n)) -> (y : A) -> (λ (j : Fin n) -> (i ↓ y) Γ (j ↥f i)) == Γ
  insertLShiftL Γ i y = funExt (insertLShiftL₂ Γ i y)


  liftZero : ∀{n} -> (i : Fin (suc n)) -> (fzero ↥f (fsuc i)) == fzero
  liftZero {n} (i ⌈ ip) with compare zero i
  ... | p = refl

  insertLCommaZero : ∀{n} -> (i : Fin (suc n)) -> (y : A) -> (σ : A) -> (Γ : FList A n) -> (fsuc i ↓ y) (σ ,, Γ) fzero == σ
  insertLCommaZero {n} i y σ Γ = cong ((fsuc i ↓ y) (σ ,, Γ)) (liftZero i) ∙ insertLShiftL₂ (σ ,, Γ) (fsuc i) y fzero




  insertLShiftDown : ∀{n} -> (Γ : FList A n) -> (i : Fin (suc n)) -> {x : A} -> (j : Fin (suc n)) -> (p : ⍛ j == ⍛ i -> ⊥) -> (y : A) -> (i ↓ y) Γ j == x -> Γ (↧f j i p) == x
  insertLShiftDown {n} Γ (i ⌈ ip) {x} (j ⌈ jp) j!=i y p with compare j i
  insertLShiftDown {n} Γ (i ⌈ ip) {x} (j ⌈ jp) j!=i y p | less q = cong Γ (finEqual j) ∙ p
  insertLShiftDown {n} Γ (i ⌈ ip) {x} (j ⌈ jp) j!=i y p | equal q = ⊥-elim (j!=i q)
  insertLShiftDown {n} Γ (i ⌈ ip) {x} (zero ⌈ jp) i!=j y p | greater q = ⊥-elim (lessZero-⊥ q)
  insertLShiftDown {n} Γ (i ⌈ ip) {x} (suc j ⌈ jp) i!=j y p | greater q = p




compComma : ∀{n ℓ ℓ'} -> {A : 𝒰 ℓ} -> {B : 𝒰 ℓ'} -> (F : A -> B) -> (a : A) -> (L : FList A n) -> (i : Fin (suc n))
            -> F ((a ,, L) i) == (F a ,, (F ∘ L)) i
compComma F a L (zero ⌈ ip) = refl
compComma F a L (suc i ⌈ ip) = refl


\end{code}
