
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Typing.Error {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}

\end{code}


For this, we need to define a type which is going to contain the error
information, i.e., why a term was incorrectly typed.
\begin{definition}
  The following type errors may occur:
\begin{code}
data TypeError : 𝒰₀ where
  ErrTypeMismatch    : Ty -> Ty -> TypeError
  ErrNoSuchVariable  : ℕ -> TypeError
  ErrIsNoFunction    : TypeError
\end{code}
\end{definition}
\begin{code}[hide]


case-ErrType : TypeError -> 𝒰₀
case-ErrType (ErrTypeMismatch x x₁) = ⊤
case-ErrType (ErrNoSuchVariable x) = ⊥
case-ErrType ErrIsNoFunction = ⊥

case-ErrVar : TypeError -> 𝒰₀
case-ErrVar (ErrTypeMismatch x x₁) = ⊥
case-ErrVar (ErrNoSuchVariable x) = ⊤
case-ErrVar ErrIsNoFunction = ⊥

case-ErrFunc : TypeError -> 𝒰₀
case-ErrFunc (ErrTypeMismatch x x₁) = ⊥
case-ErrFunc (ErrNoSuchVariable x) = ⊥
case-ErrFunc ErrIsNoFunction = ⊤

π-ErrType₁ : Ty -> TypeError -> Ty
π-ErrType₁ def (ErrTypeMismatch x y) = x
π-ErrType₁ def (ErrNoSuchVariable x) = def
π-ErrType₁ def ErrIsNoFunction = def

π-ErrType₂ : Ty -> TypeError -> Ty
π-ErrType₂ def (ErrTypeMismatch x y) = y
π-ErrType₂ def (ErrNoSuchVariable x) = def
π-ErrType₂ def ErrIsNoFunction = def

ErrType-inj : {a b c d : Ty} -> (a == b -> ⊥) + (c == d -> ⊥) -> ErrTypeMismatch a c == ErrTypeMismatch b d -> ⊥
ErrType-inj {a} (left x) p = x (cong (π-ErrType₁ a) p)
ErrType-inj {a} (right x) p = x (cong (π-ErrType₂ a) p)


π-ErrVar : (i : ℕ) -> TypeError -> ℕ
π-ErrVar i (ErrTypeMismatch x x₁) = i
π-ErrVar i (ErrNoSuchVariable x) = x
π-ErrVar i ErrIsNoFunction = i

ErrVar-inj : {a b : ℕ} -> (a == b -> ⊥) -> ErrNoSuchVariable a == ErrNoSuchVariable b -> ⊥
ErrVar-inj bot p = bot (cong (π-ErrVar 0) p)


TypeError-isDec : (e f : TypeError) -> isDec (e == f)
TypeError-isDec (ErrTypeMismatch a b) (ErrTypeMismatch c d) = mapDisc2 ErrTypeMismatch ErrType-inj (Ty-isDisc a c) (Ty-isDisc b d)
TypeError-isDec (ErrTypeMismatch x x₁) (ErrNoSuchVariable x₂) = no (λ p -> subst {P = case-ErrType} p tt)
TypeError-isDec (ErrTypeMismatch x x₁) ErrIsNoFunction = no (λ p -> subst {P = case-ErrType} p tt)
TypeError-isDec (ErrNoSuchVariable x) (ErrTypeMismatch x₁ x₂) = no (λ p -> subst {P = case-ErrVar} p tt)
TypeError-isDec (ErrNoSuchVariable x) (ErrNoSuchVariable x₁) = mapDiscrete ErrNoSuchVariable ErrVar-inj (ℕPath-isDec x x₁)
TypeError-isDec (ErrNoSuchVariable x) ErrIsNoFunction = no (λ p -> subst {P = case-ErrVar} p tt)
TypeError-isDec ErrIsNoFunction (ErrTypeMismatch x x₁) = no (λ p -> subst {P = case-ErrFunc} p tt)
TypeError-isDec ErrIsNoFunction (ErrNoSuchVariable x) = no (λ p -> subst {P = case-ErrFunc} p tt)
TypeError-isDec ErrIsNoFunction ErrIsNoFunction = yes refl

\end{code}
