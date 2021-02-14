{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Import where

-- open import NeoPrelude public
--   hiding
--   (
--     refl ; sym ; cong ; trans ;
--     eqReasoningStep ;
--     _<_ ; _>_ ; LessNat ; suc-monotone ; less-antirefl ; less-antisym ;
--     eq-to-leq ; lt-to-leq ;
--     Comparison ; compare ;
--     smashed ; Dec ;
--     Const ; const ;
--     _∎ ; Sub ;
--     Σ ; Σ' ; _,_ ; fst ; snd ;
--     right-inj ; left-inj ;
--     _^_ ; curry ;
--     join ;
--     _/_
--   )
--   renaming
--   (
--     [] to []'
--   )

open import TypeTheory.Lambda.Import.StdPrelude public
  renaming (id to idf)
  hiding (_∘_ ; flip)

open import TypeTheory.Lambda.Import.NeoPrelude public
   hiding (⊥ ; ⊥-elim )

open import TypeTheory.Lambda.Import.Cubical public
  renaming (Σ to Σ' ; _≡_ to _==_)
  hiding (comp ; curry)

-- open import Cubical.PathPrelude public
--   renaming
--   (
--   _≡_ to _==_
--   )

-- open import Agda.Builtin.Sigma public
--   renaming
--   (
--   Σ to Σ'
--   )

-- open import Cubical.Lemmas public

Σ : ∀{𝒊 𝒋} {A : 𝒰 𝒊} -> (A -> 𝒰 𝒋) -> 𝒰 (lmax 𝒊 𝒋)
Σ {A = A} B = Σ' A B


----------------------------------------------------------------------
-- Shortcuts

infixl 100 _∙_
_∙_ = trans
