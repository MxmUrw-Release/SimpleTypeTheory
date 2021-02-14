{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Import.Cubical where

open import TypeTheory.Lambda.Import.CubicalPrimitives public

--------------------------------------------------------------------
-- from stdlib

open import Agda.Primitive public
  using    ( Level )
  renaming ( lzero to ℓ-zero ; lsuc  to ℓ-suc ; _⊔_  to ℓ-max )


-- open import Agda.Builtin.List public

-- open import Agda.Builtin.Nat public
--   using (zero; suc; _+_; _*_)
--   renaming (Nat to ℕ)

data ⊥ : Set where

⊥-elim : ∀ {l} {A : Set l} → ⊥ → A
⊥-elim ()

¬_ : ∀ {l} → Set l → Set l
¬ A = A → ⊥

open import Agda.Builtin.Bool public

open import Agda.Builtin.Sigma public

infix 2 Σ-syntax

Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (ℓ-max a b)
Σ-syntax = Σ

syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

-- infixr 2 _×_

curry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
        ((p : Σ A B) → C p) →
        ((x : A) → (y : B x) → C (x , y))
curry f x y = f (x , y)

uncurry : ∀ {a b c} {A : Set a} {B : A → Set b} {C : Σ A B → Set c} →
          ((x : A) → (y : B x) → C (x , y)) →
          ((p : Σ A B) → C p)
uncurry f (x , y) = f x y

-- _×_ : ∀ {a b} (A : Set a) (B : Set b) → Set (ℓ-max a b)
-- A × B = Σ[ x ∈ A ] B

flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} →
       ((x : A) (y : B) → C x y) → ((y : B) (x : A) → C x y)
flip f = λ y x → f x y

_∘_ : ∀ {a b c}
        {A : Set a} {B : A → Set b} {C : {x : A} → B x → Set c} →
        (∀ {x} (y : B x) → C y) → (g : (x : A) → B x) →
        ((x : A) → C (g x))
f ∘ g = λ x → f (g x)
infixr 9 _∘_

idFun : ∀ {ℓ} → (A : Set ℓ) → A → A
idFun A x = x


--------------------------------------------------------------------
-- Path prelude


module _ {ℓ : Level} where
  module _ (A : Set ℓ) where
    isContr : Set ℓ
    isContr = Σ[ x ∈ A ] (∀ y → x ≡ y)

    isProp  : Set ℓ
    isProp  = (x y : A) → x ≡ y

    isSet   : Set ℓ
    isSet   = (x y : A) → (p q : x ≡ y) → p ≡ q

    isGrpd  : Set ℓ
    isGrpd  = (x y : A) → (p q : x ≡ y) → (a b : p ≡ q) → a ≡ b


module _ {ℓ} {A : Set ℓ} where
  refl : {x : A} → x ≡ x
  refl {x = x} = λ _ → x

  sym : {x y : A} → x ≡ y → y ≡ x
  sym p = λ i → p (~ i)

  trans' : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans' {y = y} p q i = primComp (λ _ → A) _
                          (λ { j (i = i0) → p (~ j)
                             ; j (i = i1) → q j })
                          y

  trans : {x y z : A} → x ≡ y → y ≡ z → x ≡ z
  trans {x = x} p q i = primComp (λ _ → A) _ (λ { j (i = i0) → x
                                                 ; j (i = i1) → q j }) (p i)



  -- Dependent version of the above.
  cong-d : ∀ {ℓ'} {B : A → Set ℓ'} {x y : A}
            → (f : (a : A) → B a) → (p : PathP (λ _ → A) x y)
            → PathP (λ i → B (p i)) (f x) (f y)
  cong-d f p = λ i → f (p i)

  cong : ∀ {ℓ'} {B : Set ℓ'} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
  cong = cong-d

  infix  3 _≡-qed _∎
  infixr 2 _≡⟨⟩_ _≡⟨_⟩_
  infix  1 ≡-proof_ begin_

  ≡-proof_ begin_ : {x y : A} → x ≡ y → x ≡ y
  ≡-proof x≡y = x≡y
  begin_ = ≡-proof_

  _≡⟨⟩_ : (x {y} : A) → x ≡ y → x ≡ y
  _ ≡⟨⟩ x≡y = x≡y

  _≡⟨_⟩_ : (x {y z} : A) → x ≡ y → y ≡ z → x ≡ z
  _ ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _≡-qed _∎ : (x : A) → x ≡ x
  _ ≡-qed  = refl
  _∎ = _≡-qed


transp : {ℓ : I → Level} → (A : (i : I) → Set (ℓ i)) → A i0 → A i1
transp A x = primComp A i0 (λ _ → empty) x


module _ {ℓ} {A : Set ℓ} where
  singl : (a : A) → Set ℓ
  singl a = Σ[ x ∈ A ] (a ≡ x)

  contrSingl : {a b : A} (p : a ≡ b) → _≡_ {A = singl a} (a , refl) (b , p)
  contrSingl p = λ i → ((p i) , λ j → p (i ∧ j))

module _ {ℓ ℓ'} {A : Set ℓ} {x : A}
         (P : ∀ y → x ≡ y → Set ℓ') (d : P x ((λ i → x))) where
  pathJ : (y : A) → (p : x ≡ y) → P y p
  pathJ _ p = transp (λ i → uncurry P (contrSingl p i)) d

  pathJprop : pathJ _ refl ≡ d
  pathJprop i = primComp (λ _ → P x refl) i (λ {j (i = i1) → d}) d

module _ {ℓ ℓ'} {A : Set ℓ} {P : A → Set ℓ'} where
  subst : {a b : A} (p : Path a b) → P a → P b
  subst {a} {b} p p0 = pathJ {ℓ} {ℓ'} (λ (y : A) → λ _ → P y) p0 b p

  substInv : {a x : A} (p : Path a x) → P x → P a
  substInv p  =  subst (λ i → p (~ i))

  subst-prop : ∀ {a} (b : A) (p : Path a b) → (x : P a) → PathP (\ i → P (p (~ i))) (subst p x) x
  subst-prop = pathJ _ \ x → pathJprop (\ y eq → P y) x


module _ {ℓa ℓb} {A : Set ℓa} {B : A → Set ℓb} where
  funUnImp : ({x : A} → B x) → (x : A) → B x
  funUnImp f x = f {x}

  funExt : {f g : (x : A) → B x} → ((x : A) → f x ≡ g x) → f ≡ g
  funExt p = λ i x → p x i

  funExtImp : {f g : {x : A} → B x} → ((x : A) → f {x} ≡ g {x}) →
              {x : A} → f {x} ≡ g {x}
  funExtImp p {x} = λ i → p x i


--------------------------------------------------------------------
-- Comp

comp : ∀ {ℓ} → (A : (i : I) → Set ℓ) → {φ : I} →
        (u : (i : I) → Partial (A i) φ) → A i0 [ φ ↦ u i0 ]
        → A i1
comp A {φ} u a0 = primComp A φ u (ouc a0)

fill : ∀ {ℓ} → (A : (i : I) → Set ℓ) → (φ : I) →
        (u : (i : I) → Partial (A i) φ) → (a0 : A i0 [ φ ↦ u i0 ])
        → PathP A (ouc a0)
                  (comp A (λ { i (φ = i1) → u i _ }) a0)

fill A φ u a0 i = comp (\ j → A (i ∧ j))
                    (\ { j (φ = i1) → u (i ∧ j) itIsOne; j (i = i0) → ouc a0 })
                    (inc {φ = φ ∨ (~ i)} (ouc {φ = φ} a0))


--------------------------------------------------------------------
-- Lemmas




trans-id : ∀ {ℓ}{A : Set ℓ} {x y : A} → (p : x ≡ y) → trans p (\ i → y) ≡ p
trans-id {A = A} {x} {y} p i j =              fill (λ _ → A) _
                                             (λ { i (j = i0) → x
                                                ; i (j = i1) → y })
                                             (inc (p j))
                                             (~ i)

trans-id-l : ∀ {ℓ}{A : Set ℓ} {x y : A} → (p : x ≡ y) → trans (\ i → x) p ≡ p
trans-id-l {A = A} {x} {y} p i j = comp (λ _ → A)
                                             (λ { k (j = i0) → x
                                                ; k (j = i1) → p k
                                                ; k (i = i1) → p (k ∧ j) })
                                             (inc x)


trans-cong : ∀ {l l'} {A : Set l} {B : Set l'}{x y} (f : A → B)(eq : x ≡ y) z (eq' : y ≡ z)
               → trans (\ i → f (eq i)) (\ i → f (eq' i)) ≡ (\ i → f (trans eq eq' i))
trans-cong f eq = pathJ _ (trans (trans-id (λ z → f (eq z))) \ j i →  f (trans-id eq (~ j) i) )
