
\begin{code}[hide]

module TypeTheory.Lambda.Base.Basics where


open import TypeTheory.Lambda.Base.Import

infixr 80 _×_
_×_ : ∀ {i j} (A : 𝒯 i) (B : 𝒯 j) → 𝒯 (lmax i j)
A × B = Σ (λ (_ : A) -> B)

infixl 10 _&_
_&_ : ∀{A B : 𝒰₀} -> A -> (A -> B) -> B
a & f = f a
