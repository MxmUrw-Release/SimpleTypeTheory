
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base
  renaming (_×_ to _|×|_ )
open import TypeTheory.Lambda.Param
open import TypeTheory.Lambda.IParam

module TypeTheory.Lambda.Base.CCCid {ℓ ℓ'} {iparam : IParam ℓ ℓ'} where
open IParam iparam

open Category 𝒞
open isCCC CCC
open hasTerminal Terminal
open hasProducts Products
open hasExponentials Exponentials




dom=⟦_⟧ : ∀{X Y : Obj} -> (X == Y) -> X ⇁ Y
dom=⟦_⟧ {X} {Y} X=Y = subst {P = (λ ξ -> ξ ⇁ Y)} (sym X=Y) id



dom=⟦_⟧-prop : ∀{X Y : Obj} -> (X=Y : X == Y) -> dom=⟦ X=Y ⟧ =⟮ (λ i -> X=Y i ⇁ Y) ⟯= id
dom=⟦_⟧-prop {X} {Y} X=Y = subst-prop {P = λ ξ -> ξ ⇁ Y} X (sym X=Y) id

cod=⟦_⟧ : ∀{X Y : Obj} -> (X == Y) -> X ⇁ Y
cod=⟦_⟧ {X} {Y} X=Y = subst {P = λ ξ -> X ⇁ ξ} X=Y id

cod=⟦_⟧-prop : ∀{X Y : Obj} -> (X=Y : X == Y) -> cod=⟦ X=Y ⟧ =⟮ (λ i -> X ⇁ X=Y (~ i)) ⟯= id
cod=⟦_⟧-prop {X} {Y} X=Y = subst-prop {P = λ ξ -> X ⇁ ξ} Y X=Y id

dom=cod⟦_⟧ : ∀{X Y : Obj} -> (p : X == Y) -> dom=⟦ p ⟧ == cod=⟦ p ⟧
dom=cod⟦_⟧ {X} {Y} p =
  let
       _∣_ = _⇁_

       P : X ∣ Y == Y ∣ Y
       P = λ i -> p i ∣ Y

       Q = λ i -> p (~ i) ∣ p (~ i)
       R = λ i -> X ∣ p i

       S = λ i -> X ∣ p (~ i)

       p1 : id {Y} =⟮ Q ⟯= id {X}
       p1 = λ 𝒊 -> id {p (~ 𝒊)}

       p2 : id {X} =⟮ R ⟯= cod=⟦ p ⟧
       p2 = λ 𝒊 -> cod=⟦ p ⟧-prop (~ 𝒊)

       p3 : dom=⟦ p ⟧ =⟮ P ∙ Q ∙ R ⟯= cod=⟦ p ⟧
       p3 = dom=⟦ p ⟧-prop ⊙ p1 ⊙ p2

       PQ=S : P ∙ Q == S
       PQ=S i j = primComp (λ _ -> 𝒰 (ℓ')) _
                           (λ { k (i = i1) -> X ∣ p (~ j ∨ ~ k)
                              ; k (j = i0) -> X ∣ Y
                              ; k (j = i1) -> p (~ i ∧ ~ k) ∣ p (~ k)})
                           (p (~ i ∧ j) ∣ Y)

       SR=refl : S ∙ R == refl
       SR=refl i j = primComp (λ _ -> 𝒰 ℓ') _
                              (λ { k (i = i1) -> X ∣ Y
                                 ; k (j = i0) -> X ∣ Y
                                 ; k (j = i1) -> X ∣ p (i ∨ k)})
                              (X ∣ p (i ∨ ~ j))

       PQR=refl : (P ∙ Q ∙ R) == refl
       PQR=refl = cong (_∙ R) PQ=S ∙ SR=refl

       p4 : dom=⟦ p ⟧ =⟮ refl ⟯= cod=⟦ p ⟧
       p4 = subst {P = λ ξ -> dom=⟦ p ⟧ =⟮ ξ ⟯= cod=⟦ p ⟧} PQR=refl p3

  in p4


O=⟦_⟧ : ∀{X Y : Obj} -> (X == Y) -> X ⇁ Y
O=⟦_⟧ = dom=⟦_⟧


p-unit-r : ∀{A B C} -> (p : B == C) -> (f : A ⇁ B) -> (g : A ⇁ C) -> (PathP (λ i -> A ⇁ p i) f g) -> f ◇ O=⟦ p ⟧ == g
p-unit-r {A} {B} {C} p f g f=g =
  let

      P1 : f ◇ O=⟦ p ⟧ == g ◇ id
      P1 𝒊 = f=g 𝒊 ◇ dom=⟦ p ⟧-prop 𝒊

  in P1 ∙ unit-r g

p-unit-l : ∀{A B C} -> (p : A == B) -> (f : B ⇁ C) -> (g : A ⇁ C) -> f =⟮ (λ i -> p (~ i) ⇁ C) ⟯= g -> O=⟦ p ⟧ ◇ f == g
p-unit-l {A} {B} {C} p f g f=g =
  let
      P1 : cod=⟦ p ⟧ ◇ f == id ◇ g
      P1 𝒊 = cod=⟦ p ⟧-prop 𝒊 ◇ f=g 𝒊

  in cong (_◇ f) (dom=cod⟦ p ⟧) ∙ P1 ∙ unit-l g

p-inv : ∀{A B} -> (p : A == B) -> O=⟦ p ⟧ ◇ O=⟦ sym p ⟧ == id
p-inv {A} {B} p =
  let
      P = λ i -> A ⇁ p (~ i)

      p1 : O=⟦ p ⟧ =⟮ P ⟯= id
      p1 = dom=cod⟦ p ⟧ ∙⊙ cod=⟦ p ⟧-prop

      p2 = p-unit-r (sym p) O=⟦ p ⟧ id p1

  in p2


O=comp : ∀{A B C : Obj} -> (p : A == B) -> (q : B == C) -> O=⟦ p ⟧ ◇ O=⟦ q ⟧ == O=⟦ p ∙ q ⟧
O=comp {A} {B} {C} p q =
  let
      P1 : refl =⟮ (λ i -> B == q i) ⟯= q
      P1 i j = q (i ∧ j)

      P2 : O=⟦ p ∙ refl ⟧ =⟮ (λ i -> A ⇁ q i) ⟯= O=⟦ p ∙ q ⟧
      P2 𝒊 = O=⟦ p ∙ P1 𝒊 ⟧

      P3 : O=⟦ p ⟧ =⟮ (λ i -> A ⇁ q i) ⟯= O=⟦ p ∙ q ⟧
      P3 = cong O=⟦_⟧ (sym (trans-id p)) ∙⊙ P2

      P = p-unit-r q (O=⟦ p ⟧) (O=⟦ p ∙ q ⟧) P3
  in P

\end{code}
