{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Import.CubicalPrimitives where

module Postulates where
  open import Agda.Primitive.Cubical public
  open import Agda.Builtin.Cubical.Path public
  open import Agda.Builtin.Cubical.Id public
  open import Agda.Builtin.Cubical.Sub public

  infix 4 _[_≡_]
  _[_≡_] : ∀ {ℓ} (A : I → Set ℓ) → A i0 → A i1 → Set ℓ
  _[_≡_] = PathP

  Path = _≡_


open Postulates public renaming
  ( primPFrom1 to p[_]
  ; primIMin       to _∧_   ; primIMax       to _∨_  ; primINeg   to ~_
  ; isOneEmpty     to empty ; primIdJ        to J    ; primSubOut to ouc )


module Unsafe' (dummy : Set₁) = Postulates
unsafeComp = Unsafe'.primComp Set
unsafePOr  = Unsafe'.primPOr  Set


_[_↦_] = Sub

-- {-# BUILTIN SUB Sub #-}

-- postulate
--   inc : ∀ {ℓ} {A : Set ℓ} {φ} (x : A) → Sub A φ (λ _ → x)

-- {-# BUILTIN SUBIN inc #-}

-- primitive
--   primSubOut : ∀ {ℓ} {A : Set ℓ} {φ : I} {u : Partial A φ} → Sub _ φ u → A
