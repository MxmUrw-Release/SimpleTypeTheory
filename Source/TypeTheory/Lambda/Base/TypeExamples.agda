
{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.TypeExamples where

open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Path
open import TypeTheory.Lambda.Base.TypeProperties

case-true : Bool -> 𝒰₀
case-true false = ⊥
case-true true = ⊤

Bool-isDisc : isDiscrete Bool
Bool-isDisc false false = yes refl
Bool-isDisc false true = no (λ ξ -> subst {P = case-true} (sym ξ) tt)
Bool-isDisc true false = no (λ ξ -> subst {P = case-true} ξ tt)
Bool-isDisc true true = yes refl
