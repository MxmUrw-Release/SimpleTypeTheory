
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.TypeProperties {ℓ} where

open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Path
-- open TypeNotation

----------------------------------------------------------------------
-- Functions
isInj : {A B : 𝒰 ℓ} -> (f : A -> B) -> 𝒰 ℓ
isInj {A} {B} f = {a b : A} -> (a == b -> ⊥) -> (f a == f b -> ⊥)

----------------------------------------------------------------------
-- Bottom (⊥)

dNeg : {A : 𝒰 ℓ} → A → ¬ (¬ A)
dNeg a = λ h → h a

⊥-isProp : isProp ⊥
⊥-isProp x y = ⊥-elim x

neg-isProp : (A : 𝒰 ℓ) → isProp (¬ A)
neg-isProp A f g = λ i → λ a → ⊥-isProp (f a) (g a) i


----------------------------------------------------------------------
-- Decidable

data isDec (A : 𝒰 ℓ) : 𝒰 ℓ where
  yes : A → isDec A
  no  : (A → ⊥) → isDec A

mapDec : {A B : 𝒰 ℓ}
       → (f : A → B) → (g : B → A)
         → isDec A → isDec B
mapDec f g (yes a)  = yes (f a)
mapDec f g (no a)   = no  (a ∘ g)

isDiscrete : (A : 𝒰 ℓ) -> 𝒰 ℓ
isDiscrete A = (x y : A) -> isDec (x == y)

mapDiscrete : {A B : 𝒰 ℓ} {a b : A} -> (f : A -> B) -> (fInj : isInj f) -> (p : isDec (a == b)) -> isDec (f a == f b)
mapDiscrete f inj (yes x) = yes (cong f x)
mapDiscrete f inj (no x) = no (inj x)




----------------------------------------------------------------------
-- Stability & Const

isStable : (𝒰 ℓ) → 𝒰 ℓ
isStable A = ¬ (¬ A) → A

decStable : {A : 𝒰 ℓ} → isDec A → isStable A
decStable (yes a) = λ _ →  a
decStable (no b)  = λ h → ⊥-elim (h b)


isConst : (A : 𝒰 ℓ) → (f : A → A) → 𝒰 ℓ
isConst A f = (x y : A) → f x == f y

stableConst : {A : 𝒰 ℓ} → (SA : isStable A) → Σ (isConst A)
stableConst {A} SA = (λ x → SA (dNeg x)) , (λ x y → λ i → SA (neg-isProp (¬ A) (dNeg x) (dNeg y) i) )



----------------------------------------------------------------------
-- Hedbergs Lemma
--
-- CITE: mort-ctt
--
--

hedbergLemma : {A : 𝒰 ℓ}  →  (a b : A)
               →  (f : (x : A) → (a == x) → (a == x))
               →  (p : (a == b))
               →  Square refl p (f a refl) (f b p)
hedbergLemma {A} a b f p = primComp (λ i → Square (λ _ → a)
                                                (λ j → p (i ∧ j))
                                                (f a (λ _ → a))
                                                (f (p i) (λ j →  p (i ∧ j))))
                                  _
                                  (λ _ → empty)
                                  (λ i → f a refl)

hedbergStable : (A : 𝒰 ℓ)  → (a b : A)
                → (h : (x : A) → isStable (a == x))
                → (p q : a == b)
                → p == q
hedbergStable A a b h p q = λ j i → primComp (λ _ → A)
                                             _
                                             (λ { k (j = i0) → rem2 i k
                                                ; k (j = i1) → rem3 i k
                                                ; k (i = i0) → r k
                                                ; k (i = i1) → rem4 j k
                                                })
                                             a
  where
    ra : a == a
    ra = λ _ → a

    rem1 : (x : A) → Σ (isConst (a == x))
    rem1 x = stableConst (h x)

    f : (x : A) → a == x → a == x
    f x = fst (rem1 x)

    f-isConst : (x : A) → isConst (a == x) (f x)
    f-isConst x = snd (rem1 x)

    rem4 : Square ra refl (f b p) (f b q)
    rem4 = f-isConst b p q

    r : a == a
    r = f a ra

    rem2 : Square ra p r (f b p)
    rem2 = hedbergLemma a b f p

    rem3 : Square ra q r (f b q)
    rem3 = hedbergLemma a b f q

hedberg : {A : 𝒰 ℓ} → (h : isDiscrete A) → isSet A
hedberg {A} h = λ a b → hedbergStable A a b (λ b → decStable (h a b))


\end{code}

