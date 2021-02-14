
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core.Type {i j} {param : LambdaParam i j} where
open LambdaParam param

\end{code}


The types of $\lamto$ can be either constructed by taking ground types or by forming a function type between two other types.
\begin{definition}
  A type of $\lamto$ is either an element of
  $\AFd{Gnd}$ ($\AIC{ι}$), or a pair of types ($\AFd{\_⇒\_}$).
\begin{code}
data Ty : 𝒰₀ where
  ι    : Gnd -> Ty
  _⇒_  : Ty -> Ty -> Ty
\end{code}
\end{definition}

\noindent
The typing of terms depends on what context they appear in. In order to describe
a context, it is sufficient to state what variables are in scope and what their
types are. Here we give the definition of a context. Its meaning will be explained in
the next section.
\begin{definition}
  A \textbf{context} is given by a finite list of types:
\begin{code}
Ctx : ℕ -> 𝒰₀
Ctx n = Fin n -> Ty
\end{code}
\end{definition}




\begin{code}[hide]
infixr 200 _⇒_


case-ι : Ty -> 𝒰₀
case-ι (ι _) = ⊤
case-ι (_ ⇒ _) = ⊥

ιinj : isInj ι
ιinj {A} {B} p q = p (cong f q)
  where
    f : Ty -> Gnd
    f (ι X) = X
    f (_ ⇒ _) = A


⇒1 : Ty -> Ty
⇒1 (ι a) = ι a
⇒1 (a ⇒ x) = a

⇒2 : Ty -> Ty
⇒2 (ι a) = (ι a)
⇒2 (x ⇒ b) = b


⇒inj : {a x b y : Ty} -> ((a == b) -> ⊥) + ((x == y) -> ⊥) -> (a ⇒ x == b ⇒ y) -> ⊥
⇒inj (right ¬x=y) p = ¬x=y (cong ⇒2 p)
⇒inj (left ¬a=b) p = ¬a=b (cong ⇒1 p)



mapDisc2 : {A B : 𝒰₀} -> (f : A -> A -> B) -> {a b c d : A}
        -> (inj : {x0 x1 x2 x3 : A} -> (¬ (x0 == x2)) + (¬ (x1 == x3)) -> ¬ (f x0 x1 == f x2 x3))
        -> isDec (a == c) -> isDec (b == d) -> isDec (f a b == f c d)
mapDisc2 f inj (yes x) (yes y) = yes (λ i -> f (x i) (y i))
mapDisc2 f inj (yes x) (no y) = no (inj (right y))
mapDisc2 f inj (no x) _ = no (inj (left x))


Ty-isDisc : (a b : Ty) -> isDec (a == b)
Ty-isDisc (ι A) (ι B) = mapDiscrete ι ιinj (Gnd-isDisc A B)
Ty-isDisc (ι A) (a ⇒ b) = no (λ r -> subst {P = case-ι} r tt)
Ty-isDisc (a ⇒ b) (ι A) = no (λ r -> subst {P = case-ι} (sym r) tt)
Ty-isDisc (a ⇒ b) (c ⇒ d) = mapDisc2 _⇒_ ⇒inj (Ty-isDisc a c) (Ty-isDisc b d)

_=stype=_ = Ty-isDisc

Ty-isSet = hedberg Ty-isDisc

\end{code}

