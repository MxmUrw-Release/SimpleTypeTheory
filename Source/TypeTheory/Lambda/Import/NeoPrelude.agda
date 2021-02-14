{-# OPTIONS --cubical #-}


module TypeTheory.Lambda.Import.NeoPrelude where

-- open import TypeTheory.Lambda.Import.StdPrelude public


data ⊥ : Set where

⊥-elim : ∀ {a} {A : Set a} → ⊥ → A
⊥-elim ()
{-# INLINE ⊥-elim #-}



{-
Renaming Agda primitives (copied from the HoTT library)
-}
open import Agda.Primitive public using (lzero)
  renaming (Level to ULevel; lsuc to lsucc; _⊔_ to lmax)


𝒯 : (i : ULevel) -> Set (lsucc i)
𝒯 i = Set i

𝒰 = 𝒯

ℓ₀ = lzero
ℓ₁ = lsucc lzero
-- 𝒯 = Type
𝒰₀ = 𝒯 ℓ₀
𝒰₁ = 𝒯 ℓ₁



{-
Pi Type without reference to base
-}
Π : ∀ {i j} -> {A : 𝒯 i} -> (P : A -> 𝒯 j) -> 𝒯 (lmax i j)
Π {A = A} P = (x : A) -> P x


-- module TypeNotation where

--   -- Cartesian product
--   infixl 30 _×_
--   _×_ : ∀ {i j} (A : 𝒯 i) (B : 𝒯 j) → 𝒯 (lmax i j)
--   _×_ = _×'_

{- Lifting to a higher universe level

The operation of lifting enjoys both β and η definitionally.
It’s a bit annoying to use, but it’s not used much (for now).
-}

record Lift {i j} (A : 𝒯 i) : 𝒯 (lmax i j) where
  instance constructor lift
  field
    lower : A
open Lift public

lift' : ∀ {i} -> (j : ULevel) -> {A : 𝒯 i} -> A -> Lift {i} {j} A
lift' j a = lift a
