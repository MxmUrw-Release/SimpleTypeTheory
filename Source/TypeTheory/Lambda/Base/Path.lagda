
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Path where

open import TypeTheory.Lambda.Base.Import 

-- open import Cubical.Comp
-- open import Cubical.Lemmas

----------------------------------------------------------------------
-- Square

Square : ∀{ℓ} {A : Set ℓ} {a0 a1 b0 b1 : A}
         (u : a0 == a1) (v : b0 == b1) (r0 : a0 == b0) (r1 : a1 == b1)
         → Set ℓ
Square {A = A} u v r0 r1 = PathP (λ i → (u i == v i)) r0 r1

PathC : ∀{ℓ} (A : 𝒰 ℓ) -> (a b : A) -> 𝒰 ℓ
PathC A a b = PathP (λ _ -> A) a b

-- infix 20 _[_==_]
-- _[_==_] = _[_≡_]
-- PathC = _[_≡_]

----------------------------------------------------------------------
-- Proof

-- withr : {A : 𝒰 ℓ} -> {a b : A} -> (p : a == b) 

compi : ∀{ℓ} {A : 𝒰 ℓ} -> (P : A -> 𝒰 ℓ) -> {a b : A} -> (a=b : a == b) -> (pa : P a) -> (pb : P b) -> (subst= : subst {P = P} a=b pa == pb) -> PathP (λ i -> P (a=b i)) pa pb
compi {A = A} P {a} {b} a=b pa pb subst= i = primComp (λ j -> P (a=b (i ∨ (~ j))))
                                                _
                                                (λ { j (i = i0) -> subst-prop {P = P} b a=b pa (j)
                                                   ; j (i = i1) -> subst= (j)
                                                   })
                                                (subst {P = P} a=b pa)



depSet : ∀{ℓ} {A : 𝒰 ℓ} -> (P : A -> 𝒰 ℓ) -> {a b : A} -> (a=b : a == b) -> {pa : P a} -> {pb : P b} -> (isProp (P b)) -> PathP (λ i -> P (a=b i)) pa pb
depSet {A = A} P {a} {b} a=b {pa} {pb} prop =
  let
      pa=pb' : subst {P = P} a=b pa == pb
      pa=pb' = prop (subst {P = P} a=b pa) pb

  in compi P a=b pa pb pa=pb'


trans-sym : ∀{ℓ} {A : 𝒰 ℓ} -> {a b : A} -> (p : a == b) -> p ∙ sym p == refl
trans-sym {ℓ} {A} {a} {b} p i j = primComp (λ _ -> A) _
                                           (λ { k (i = i1) -> a
                                              ; k (j = i0) -> a
                                              ; k (j = i1) -> p (~ k ∧ ~ i)})
                                           (p (~ i ∧ j))



-- we create a custom notation for dependent paths.

-- bbb : I -> ℕ
-- bbb i0 = 0
-- bbb i1 = 1



_=⟮_⟯=_ : ∀{ℓ} {A B : 𝒰 ℓ} -> (a : A) -> (A=B : A == B) -> (b : B) -> 𝒰 ℓ
_=⟮_⟯=_ a A=B b = PathP (λ i -> A=B i) a b

infixl 30 _⊙_
_⊙_ : ∀{ℓ} {A B C : 𝒰 ℓ} {a b c} -> {A=B : A == B} -> {B=C : B == C} -> (a =⟮ A=B ⟯= b) -> (b =⟮ B=C ⟯= c) -> a =⟮ A=B ∙ B=C ⟯= c
_⊙_ {ℓ} {A} {B} {C} {a} {b} {c} {A=B} {B=C} a=b b=c =
  let
      S : Square (A=B) (A=B ∙ B=C) (λ j -> A) (B=C)
      S i j = primComp (λ _ -> 𝒰 ℓ) _
                       (λ { k (i = i0) -> A
                          ; k (i = i1) -> B=C (k ∧ j)
                          ; k (j = i0) -> A=B i})
                       (A=B i)

      p : PathP (λ i -> (A=B ∙ B=C) i) a c
      p i = primComp (λ j -> S i j) _
                     (λ { j (i = i0) -> a
                        ; j (i = i1) -> b=c j})
                     (a=b i)
  in p


substP : ∀{ℓ} {A B : 𝒰 ℓ} {a b} -> {P : A == B} -> {Q : A == B} -> (P == Q) -> a =⟮ P ⟯= b -> a =⟮ Q ⟯= b
substP {ℓ} {A} {B} {a} {b} {P} {Q} P=Q a=b = subst {P = λ ξ -> a =⟮ ξ ⟯= b} P=Q a=b


infixl 30 _∙⊙_
_∙⊙_ : ∀{ℓ} {B C : 𝒰 ℓ} {a b c} -> {B=C : B == C} -> (a == b) -> (b =⟮ B=C ⟯= c) -> a =⟮ B=C ⟯= c
_∙⊙_ {ℓ} {B} {C} {a} {b} {c} {B=C} a=b b=c =
  let
      p1 : a =⟮ refl ∙ B=C ⟯= c
      p1 = a=b ⊙ b=c

      p2 : a =⟮ B=C ⟯= c
      p2 = subst {P = λ ξ -> a =⟮ ξ ⟯= c} (trans-id-l B=C) p1

  in p2


infixl 30 _⊙∙_
_⊙∙_ : ∀{ℓ} {A B : 𝒰 ℓ} {a b c} -> {A=B : A == B} -> (a =⟮ A=B ⟯= b) -> (b == c) -> a =⟮ A=B ⟯= c
_⊙∙_ {ℓ} {B} {C} {a} {b} {c} {A=B} a=b b=c =
  let
      p1 : a =⟮ A=B ∙ refl ⟯= c
      p1 = a=b ⊙ b=c

      p2 : a =⟮ A=B ⟯= c
      p2 = substP (trans-id A=B) p1

  in p2

-- ⊙prop : ∀{A B} {a b} -> {A=B : A == B} -> (a =⦃ A=B ∙ sym A=B ⦄= b == (a == b))
-- ⊙prop = refl



-- P : Ty -> 𝒰₀
-- P ξ = τ ⇒ ξ == ψ

-- τσ=ψ' : τ ⇒ σ == ψ
-- τσ=ψ' = subst {P = P} ρ=σ τρ=ψ

-- P5 : PathP (λ i -> τ ⇒ ρ=σ i == ψ) τρ=ψ τσ=ψ
-- P5 = compi P ρ=σ τρ=ψ τσ=ψ (Ty-isSet (τ ⇒ σ) (ψ) τσ=ψ' τσ=ψ)


-- compi2 : ∀{ℓ'} {A : 𝒰 ℓ} {B : 𝒰 ℓ'} -> (P : A -> B) -> {a b : A} -> (a=b : a == b) -> (pa : P a) -> (pb : P b) -> (subst= : subst {P = P} a=b pa == pb) -> PathP (λ i -> P (a=b i)) pa pb
-- compi2 {A = A} P {a} {b} a=b pa pb subst= i = primComp (λ j -> P (a=b (i ∨ (~ j))))
--                                                 _
--                                                 (λ { j (i = i0) -> subst-prop {P = P} b a=b pa (j)
--                                                    ; j (i = i1) -> subst= (j)
--                                                    })
--                                                 (subst {P = P} a=b pa)


----------------------------------------------------------------------
-- Notation

cong2 : ∀ {ℓ ℓ'} {A : Set ℓ} {B : Set ℓ'} {x y : A} → (f : A → B) → x == y → f x == f y
cong2 = cong

syntax cong2 f p = p |ctx| f


\end{code}
