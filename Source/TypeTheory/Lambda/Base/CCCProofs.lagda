
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base.Basics
  renaming (_×_ to _|×|_ )
open import TypeTheory.Lambda.Param
open import TypeTheory.Lambda.IParam

module TypeTheory.Lambda.Base.CCCProofs {ℓ ℓ'} {iparam : IParam ℓ ℓ'} where
open IParam iparam

open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Nat
open import TypeTheory.Lambda.Base.Fin
open import TypeTheory.Lambda.Base.FList
open import TypeTheory.Lambda.Base.Path
open import TypeTheory.Lambda.Base.Category
open import TypeTheory.Lambda.Base.CCC
open import TypeTheory.Lambda.Base.CCCid {iparam = iparam}

open Category 𝒞
open isCCC CCC
open hasTerminal Terminal
open hasProducts Products
open hasExponentials Exponentials



\end{code}

\section{Finite products}

Using our previously introduced concepts, we define a similar, very helpful
object, the finite product. As the name implies, it may be constructed by repeatedly 
taking the (binary) product. But in order for this to be well-defined, the case
of taking the product of zero objects also needs to be considered.

\begin{definition}
  In a CCC, the \textbf{finite product of objects} is defined as a function
  which given a finite list of objects $A$, calculates their product $⨅ A$ by recursion
  on the size of the list. The product of an empty list is the terminal object $𝟏$.
\begin{code}
⨅ : ∀{n} -> (Fin n -> Obj) -> Obj
⨅ {zero}   A = 𝟏
⨅ {suc n}  A = ⨅ (λ i -> A (fsuc i)) × A fzero
\end{code}
\end{definition}
Similarly, by recursion on the size of the list, and by invoking the
corresponding functions for binary products, we define finite projections and
finite products of morphisms.
\begin{definition}
  For a finite list of objects $A$, the \textbf{projection function of
  finite products} $πᵢ$, which projects the $i$-th element of the finite product
$⨅ A$, is defined as:
\begin{code}
πᵢ : ∀{n} -> {A : Fin n -> Obj} -> (i : Fin n) -> ⨅ A ⇁ A i
πᵢ {zero}   {A} (fin i (diff k p))  = ⊥-elim (zNotS p)
πᵢ {suc n}  {A} (fin zero p)        = π₂  ◇ O=⟦ cong A (finEqual zero) ⟧
πᵢ {suc n}  {A} (fin (suc i) p)     = π₁  ◇ πᵢ (fin i (pred-monotone p))
                                          ◇ O=⟦ cong A (finEqual (suc i)) ⟧
\end{code}
\end{definition}

\begin{remark}
Here, $\AF{zNotS}$ is a function which constructs a contradiction from a proof
of $\AIC{zero} = \AIC{suc}\:n$. The operator $\OOeq{\_}$ takes an equality of
objects $A = B$ as argument and returns
an arrow $A ⇁ B$. The function $\AF{finEqual}$ takes a natural number as input
and returns a proof of equality for finite indices represented by this number.
\end{remark}

\begin{definition}
  For an object $A$, a finite list of objects $B$, and a finite list of
  morphisms $Fᵢ : A ⇁ Bᵢ$, the \textbf{finite product of morphisms} $⟪ F ⟫$ of
  type $A ⇁ ⨅ B$ is defined by:
\begin{code}
⟪_⟫ : ∀{n}  -> {A : Obj} -> {B : Fin n -> Obj}
            -> (F : (i : Fin n) -> A ⇁ B i)
            -> A ⇁ ⨅ B
⟪_⟫ {zero}   F = !
⟪_⟫ {suc n}  F = ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩
\end{code}
\end{definition}

\newpage
\begin{definition}
  For a finite list of functions $Fᵢ : A_i ⇁ B_i$, the \textbf{morphism between finite products}
  $⨉ F$ of type $⨅ A ⇁ ⨅ B$ is defined by:
\begin{code}
⨉ : ∀{n}  -> {A B : Fin n -> Obj} -> (F : ∀ i -> A i ⇁ B i)
          -> ⨅ A ⇁ ⨅ B
⨉ F = ⟪ (λ i -> πᵢ i ◇ F i) ⟫
\end{code}
\end{definition}

\begin{code}[hide]

comp-⟪,⟫ : ∀{n} -> {A B : Obj} -> {C : Fin n -> Obj} -> (F : A ⇁ B) -> (G : ∀(i) -> B ⇁ C i) -> F ◇ ⟪ G ⟫ == ⟪ (λ i -> F ◇ G i) ⟫
comp-⟪,⟫ {zero} {A} {B} {C} F G = sym !-uprop
comp-⟪,⟫ {suc n} {A} {B} {C} F G =
  let
      P = F ◇ ⟨ ⟪ (λ i -> G (fsuc i)) ⟫ , G fzero ⟩       ≡⟨ comp-⟨,⟩ F ⟪ (λ i -> G (fsuc i)) ⟫ (G fzero) ⟩
          ⟨ F ◇ ⟪ (λ i -> G (fsuc i)) ⟫ , F ◇ G fzero ⟩   ≡⟨ comp-⟪,⟫ F (λ i -> G (fsuc i)) |ctx| ⟨_, F ◇ G fzero ⟩ ⟩
          ⟨ ⟪ (λ i -> F ◇ G (fsuc i)) ⟫ , F ◇ G fzero ⟩   ∎

  in P

⟪⟫-id : ∀{n} -> {A : Fin n -> Obj} -> ⟪ πᵢ {A = A} ⟫ == id
πfzero : ∀{n} -> {A : Fin (suc n) -> Obj} -> πᵢ {A = A} fzero == π₂
πfsuc : ∀{n} -> {A : Fin (suc n) -> Obj} -> ⟪ (λ i -> πᵢ {A = A} (fsuc i)) ⟫ == π₁


⟪⟫-id {zero} {A} = !-uprop
⟪⟫-id {suc n} {A} =
  let
      P1 = λ 𝒊 -> ⟨ πfsuc {A = A} 𝒊 , πfzero {A = A} 𝒊 ⟩
  in P1 ∙ ⟨,⟩-id





πfzero {n} {A} =
  let

      P4 : π₂ {A = ⨅ (tail A)} {B = A fzero} ◇ O=⟦ cong A (finEqual zero {fnatless fzero} {fnatless fzero}) ⟧ == π₂
      P4 = cong (λ ξ -> π₂ ◇ O=⟦ cong A ξ ⟧) (Fin-isSet fzero fzero (finEqual zero) refl) ∙ p-unit-r (cong A (refl)) π₂ π₂ refl

      P3 :  πᵢ {A = A} fzero == π₂ {A = ⨅ (tail A)} {B = A fzero}
      P3 = P4

  in P4

πfsuc {n} {A} =
  let

      ii : Fin n -> Fin n
      ii = λ i -> ⍛ i ⌈ pred-monotone (fnatless (fsuc i))


      ipp : (i : Fin n) -> (fsuc (ii i)) == fsuc i
      ipp i = finEqual (suc (⍛ i)) {fnatless (fsuc (ii i))} {fnatless (fsuc i)}

      ip : (i : Fin n) -> A (fsuc (ii i)) == A (fsuc i)
      ip i 𝒊 = A (ipp i 𝒊)


      p3 : ∀(i : Fin n) -> ii i == i
      p3 i = finEqual (⍛ i)

      defp : (i : Fin n) -> A (fsuc (ii i)) == A (fsuc i)
      defp i = cong (A ∘ fsuc) (p3 i)

      p4 : ∀(i : Fin n) -> πᵢ (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ defp i 𝒊) ⟯= πᵢ i
      p4 i 𝒊 = πᵢ (p3 i 𝒊)

      p5 : ∀(i : Fin n) -> ipp i == cong fsuc (p3 i)
      p5 i = Fin-isSet (fsuc (ii i)) (fsuc i) (ipp i) (cong fsuc (p3 i))

      p6 : ∀(i : Fin n) -> ip i == defp i
      p6 i = cong (cong A) (p5 i)


      -- Here we need to substitute the path over which our equality goes. For it must go over the custom (fsuc (ii i) == fsuc i) path above,
      -- but by refl we can go only over (cong fsuc (πᵢ p3)), since the πᵢ {A = tail A} automatically adds an (fsuc).
      p0 : ∀(i : Fin n) -> πᵢ {n} {A = (tail A)} (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ ip i 𝒊) ⟯= πᵢ {n} {A = (tail A)} i
      p0 (i) = subst {P = λ ξ -> πᵢ (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ ξ 𝒊) ⟯= πᵢ i } (sym (p6 i)) (p4 i)


      P0 : ∀(i) -> π₁ ◇ πᵢ (ii i) ◇ O=⟦ ip i ⟧ == π₁ ◇ (πᵢ (ii i) ◇ O=⟦ ip i ⟧)
      P0 i = asc π₁ (πᵢ (ii i)) O=⟦ ip i ⟧


      P2 = ⟪ (λ i -> π₁ {B = A fzero} ◇ πᵢ (ii i) ◇ O=⟦ ip i ⟧) ⟫        ≡⟨ (λ 𝒊 -> ⟪ (λ i -> P0 i 𝒊) ⟫) ⟩
            ⟪ (λ i -> π₁ ◇ (πᵢ (ii i) ◇ O=⟦ ip i ⟧ )) ⟫                  ≡⟨ sym (comp-⟪,⟫ π₁ (λ i -> (πᵢ (ii i) ◇ O=⟦ ip i ⟧))) ⟩
            π₁ ◇ ⟪ (λ i -> πᵢ (ii i) ◇ O=⟦ ip i ⟧) ⟫                     ≡⟨ (λ 𝒊 -> π₁ ◇ ⟪ (λ i -> p-unit-r (ip i) (πᵢ (ii i)) (πᵢ i) (p0 i) 𝒊 ) ⟫ ) ⟩
            π₁ ◇ ⟪ πᵢ {A = tail A} ⟫                                     ≡⟨ ⟪⟫-id {A = tail A} |ctx| (π₁ ◇_) ⟩
            π₁ ◇ id                                                       ≡⟨ unit-r π₁ ⟩
            π₁                                                           ∎

  in P2


⨉-tail : ∀{n} -> {A B : Fin (suc n) -> Obj} -> (F : ∀(i) -> A i ⇁ B i) -> ⟨ ⟪ (λ (i : Fin n) -> πᵢ {A = A} (fsuc i) ◇ F (fsuc i)) ⟫ , πᵢ {A = A} fzero ◇ F fzero ⟩ == ⟨ π₁ ◇ ⨉ (λ i -> F (fsuc i)) , π₂ ◇ F fzero ⟩

⟪⟫-comp : ∀{n} -> {A : Obj} -> {B C : Fin n -> Obj} -> (F : ∀(i) -> A ⇁ B i) -> (G : ∀(i) -> B i ⇁ C i) -> ⟪ (λ i -> F i ◇ G i) ⟫ == ⟪ F ⟫ ◇ ⨉ G
⟪⟫-comp {zero} {A} {B} {C} F G = !-uprop
⟪⟫-comp {suc n} {A} {B} {C} F G =
  let
      P1 = ⟨ ⟪ (λ i -> F (fsuc i) ◇ G (fsuc i)) ⟫ , F fzero ◇ G fzero ⟩      ≡⟨ ⟪⟫-comp (λ i -> F (fsuc i)) (λ i -> G (fsuc i)) |ctx| ⟨_, F fzero ◇ G fzero ⟩ ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ ◇ ⨉ (λ i -> G (fsuc i)) , F fzero ◇ G fzero ⟩                ≡⟨ sym (⟨,⟩-comp ⟪ (λ i -> F (fsuc i)) ⟫ (F fzero) (⨉ (λ i -> G (fsuc i))) (G fzero)) ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ ⟨ π₁ ◇ ⨉ (λ i -> G (fsuc i)) , π₂ ◇ G fzero ⟩  ≡⟨ sym (⨉-tail G) |ctx| (⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇_) ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ ⨉ G                                 ∎

  in P1


⨉-tail {n} {A} {B} F =
  let
      P1 = ⟨ ⟪ (λ (i : Fin n) -> πᵢ {A = A} (fsuc i) ◇ F (fsuc i)) ⟫ , πᵢ {A = A} fzero ◇ F fzero ⟩

              ≡⟨ (⟪⟫-comp (λ i -> πᵢ {A = A} (fsuc i)) (λ i -> F (fsuc i))) |ctx| (λ ξ -> ⟨ ξ , πᵢ {A = A} fzero ◇ F fzero ⟩) ⟩

           ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i)) ⟫ ◇ ⨉ (λ i -> F (fsuc i)) , πᵢ {A = A} fzero ◇ F fzero ⟩

              ≡⟨ (λ 𝒊 -> ⟨ πfsuc {A = A} (𝒊) ◇ ⨉ (λ i -> F (fsuc i)) , πfzero {A = A} (𝒊) ◇ F fzero ⟩) ⟩

           ⟨ π₁ ◇ ⨉ (λ i -> F (fsuc i)) , π₂ ◇ F fzero ⟩

              ∎

  in P1




⨉-comp : ∀{n} -> {A B C : Fin n -> Obj} -> (F : ∀(i) -> A i ⇁ B i) -> (G : ∀(i) -> B i ⇁ C i) -> ⨉ F ◇ ⨉ G == ⨉ (λ i -> F i ◇ G i)
⨉-comp {zero} {A} {B} {C} F G =
  let
      P : !! {T1} ◇ !! {T1} == !!
      P = sym !-uprop
  in P
⨉-comp {suc n} {A} {B} {C} F G =
  let
      X = G
      P = ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i) ◇ F (fsuc i)) ⟫ , πᵢ {A = A} fzero ◇ F fzero ⟩ ◇ ⟨ ⟪ (λ i -> πᵢ {A = B} (fsuc i) ◇ G (fsuc i)) ⟫ , πᵢ {A = B} fzero ◇ G fzero ⟩

                ≡⟨ ⨉-tail F |ctx| (_◇ ⟨ ⟪ (λ i -> πᵢ {A = B} (fsuc i) ◇ G (fsuc i)) ⟫ , πᵢ {A = B} fzero ◇ G fzero ⟩) ⟩

          (⨉ (λ i -> F (fsuc i)) ×× F fzero) ◇ ⟨ ⟪ (λ i -> πᵢ {A = B} (fsuc i) ◇ G (fsuc i)) ⟫ , πᵢ {A = B} fzero ◇ G fzero ⟩

                ≡⟨ ⨉-tail G |ctx| ((⨉ (λ i -> F (fsuc i)) ×× F fzero) ◇_) ⟩

          (⨉ (λ i -> F (fsuc i)) ×× F fzero) ◇ (⨉ (λ i -> G (fsuc i)) ×× G fzero)

                ≡⟨ ××-comp (⨉ (λ i -> F (fsuc i))) (F fzero) (⨉ (λ i -> G (fsuc i))) (G fzero) ⟩

          (⨉ (λ i -> F (fsuc i)) ◇ ⨉ (λ i -> G (fsuc i))) ×× (F fzero ◇ G fzero)

                ≡⟨ ⨉-comp (λ i -> F (fsuc i)) (λ i -> G (fsuc i)) |ctx| (_×× (F fzero ◇ G fzero)) ⟩

          ⟨ π₁ ◇ (⨉ (λ i -> F (fsuc i) ◇ G (fsuc i))) , π₂ ◇ (F fzero ◇ G fzero) ⟩

                ≡⟨ sym (⨉-tail (λ i -> F i ◇ G i)) ⟩

          ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i) ◇ (F (fsuc i) ◇ G (fsuc i))) ⟫ , πᵢ {A = A} fzero ◇ (F fzero ◇ G fzero) ⟩

                ∎
  in P

⨉-id : ∀{n} -> (A : Fin n -> Obj) -> ⨉ (λ i -> id {A i}) == id {⨅ A}
⨉-id {zero} A = !-uprop
⨉-id {suc n} A =
  let
      P =
          ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i) ◇ id {A (fsuc i)}) ⟫ , πᵢ {A = A} fzero ◇ id {A fzero} ⟩    ≡⟨ ⨉-tail (λ i -> id {A i}) ⟩
          ⟨ π₁ ◇ ⨉ (λ i -> id {A (fsuc i)}) , π₂ ◇ id {A fzero} ⟩                    ≡⟨ ⨉-id (tail A) |ctx| (λ ξ -> ⟨ π₁ ◇ ξ , π₂ ◇ id {A fzero} ⟩) ⟩
          ⟨ π₁ ◇ id {⨅ (tail A)} , π₂ ◇ id {A fzero} ⟩                                ≡⟨ ××-id ⟩
          id                                                                            ∎

  in P


--------------------------------------
-- Equalities




⟪,⟫-prop : ∀{n A} -> {B : Fin n -> Obj} -> (F : (i : Fin n) -> A ⇁ B i) -> (i : Fin n) -> ⟪ F ⟫ ◇ πᵢ i == F i
⟪,⟫-prop {zero} {A} {B} F (fin i (diff k p)) = ⊥-elim (zNotS p)
⟪,⟫-prop {suc n} {A} {B} F (zero ⌈ p) =
  let
      P1 = ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ (π₂ ◇ O=⟦ cong B (finEqual zero) ⟧)
                                                                                         ≡⟨ sym (asc ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ π₂ O=⟦ cong B (finEqual zero) ⟧) ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ π₂ ◇ O=⟦ cong B (finEqual zero) ⟧
                                                                                         ≡⟨ snd (⟨,⟩-prop _ _) |ctx| (_◇ O=⟦ cong B (finEqual zero) ⟧) ⟩
           F fzero ◇ O=⟦ cong B (finEqual zero) ⟧
                                                                                         ≡⟨ (p-unit-r (cong B (finEqual zero)) (F fzero) (F (zero ⌈ p)) (λ 𝒊 -> F (finEqual zero {0<suc} {p} 𝒊))) ⟩
           F (zero ⌈ p)
                                                                                         ∎
  in P1
⟪,⟫-prop {suc n} {A} {B} F (suc i ⌈ p) =
  let
      ipred = (i ⌈ pred-monotone p)
      Bp = cong B (finEqual (suc i))

      P1 = ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ (π₁ ◇ πᵢ ipred ◇ O=⟦ Bp ⟧)
                                                                                ≡⟨ (asc π₁ (πᵢ ipred) O=⟦ Bp ⟧) |ctx| (⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇_) ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ (π₁ ◇ (πᵢ ipred ◇ O=⟦ Bp ⟧))
                                                                                ≡⟨ sym (asc ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ π₁ (πᵢ ipred ◇ O=⟦ Bp ⟧)) ⟩
           ⟨ ⟪ (λ i -> F (fsuc i)) ⟫ , F fzero ⟩ ◇ π₁ ◇ (πᵢ ipred ◇ O=⟦ Bp ⟧)
                                                                                ≡⟨ fst (⟨,⟩-prop _ _) |ctx| (_◇ (πᵢ ipred ◇ O=⟦ Bp ⟧)) ⟩
           ⟪ (λ i -> F (fsuc i)) ⟫ ◇ (πᵢ ipred ◇ O=⟦ Bp ⟧)
                                                                                ≡⟨ sym (asc ⟪ (λ i -> F (fsuc i)) ⟫ (πᵢ ipred) O=⟦ Bp ⟧) ⟩
           ⟪ (λ i -> F (fsuc i)) ⟫ ◇ πᵢ ipred ◇ O=⟦ Bp ⟧
                                                                                ≡⟨ ⟪,⟫-prop (λ i -> F (fsuc i)) ipred |ctx| (_◇ O=⟦ Bp ⟧) ⟩
           F (fsuc ipred) ◇ O=⟦ Bp ⟧
                                                                                ≡⟨ p-unit-r Bp (F (fsuc ipred)) (F (suc i ⌈ p)) (λ 𝒊 -> F (finEqual (suc i) {fnatless (fsuc ipred)} {p} 𝒊)) ⟩
           F (suc i ⌈ p)
                                                                                ∎
  in P1


⨉-π : ∀{n} -> {A B : Fin n -> Obj} -> (F : ∀(i) -> A i ⇁ B i) -> (i : Fin n) -> ⨉ F ◇ πᵢ {A = B} i == πᵢ {A = A} i ◇ F i
⨉-π {n} {A} {B} F i = ⟪,⟫-prop (λ j -> πᵢ j ◇ F j) i

⨉-π₁ : ∀{n} -> {A B : Fin (suc n) -> Obj} -> (F : ∀(i) -> A i ⇁ B i) -> ⨉ F ◇ π₁ == π₁ ◇ ⨉ (λ i -> F (fsuc i))
⨉-π₁ F =
  let
      P = ⨉ F ◇ π₁                                                  ≡⟨ ⨉-tail F |ctx| (_◇ π₁) ⟩
          ⟨ π₁ ◇ ⨉ (λ i -> (F (fsuc i))) , π₂ ◇ F fzero ⟩ ◇ π₁      ≡⟨ fst (⟨,⟩-prop (π₁ ◇ ⨉ (λ i -> F (fsuc i))) (π₂ ◇ F fzero)) ⟩
          π₁ ◇ ⨉ (λ i -> (F (fsuc i)))                              ∎


  in P



××-O= : ∀{A B C D : Obj} -> (p : A == B) -> (q : C == D) -> O=⟦ p ⟧ ×× O=⟦ q ⟧ == O=⟦ (λ 𝒊 -> p 𝒊 × q 𝒊) ⟧
××-O= {A} {B} {C} {D} p q =
  let
      Arr1 = λ 𝒊 -> p 𝒊 × q 𝒊 ⇁ B × D
      O1 = λ 𝒊 -> p 𝒊 × q 𝒊

      P1 : O=⟦ p ⟧ ×× O=⟦ q ⟧ =⟮ Arr1 ⟯= id ×× id
      P1 𝒊 = dom=⟦ p ⟧-prop 𝒊 ×× dom=⟦ q ⟧-prop 𝒊

      P2 : id =⟮ sym Arr1 ⟯= O=⟦ O1 ⟧
      P2 𝒊 = dom=⟦ O1 ⟧-prop (~ 𝒊)

      P3 : O=⟦ p ⟧ ×× O=⟦ q ⟧ =⟮ Arr1 ∙ sym Arr1 ⟯= O=⟦ O1 ⟧
      P3 = P1 ⊙∙ ××-id ⊙ P2

  in substP (trans-sym Arr1) P3

⨉-O= : ∀{n} -> {A B : Fin n -> Obj} -> (p : ∀(i) -> A i == B i) -> ⨉ (λ i -> O=⟦ p i ⟧) == O=⟦ (λ 𝒊 -> ⨅ (λ i -> p i 𝒊)) ⟧
⨉-O= {zero} {A} {B} p = !-uprop
⨉-O= {suc n} {A} {B} p =
  let
      P1 = ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i) ◇ O=⟦ p (fsuc i) ⟧) ⟫ , πᵢ {A = A} fzero ◇ O=⟦ p fzero ⟧ ⟩          ≡⟨ ⨉-tail (λ i -> O=⟦ p i ⟧) ⟩
           ⟨ π₁ ◇ ⨉ (λ i -> O=⟦ p (fsuc i) ⟧) , π₂ ◇ O=⟦ p fzero ⟧ ⟩             ≡⟨ ⨉-O= (λ i -> p (fsuc i)) |ctx| (λ ξ -> ⟨ π₁ ◇ ξ , π₂ ◇ O=⟦ p fzero ⟧ ⟩) ⟩
           ⟨ π₁ ◇ O=⟦ (λ 𝒊 -> ⨅ (λ i -> p (fsuc i) 𝒊)) ⟧ , π₂ ◇ O=⟦ p fzero ⟧ ⟩  ≡⟨ ××-O= (λ 𝒊 -> ⨅ (λ i -> p (fsuc i) 𝒊)) (p fzero) ⟩
           O=⟦ (λ 𝒊 -> ⨅ (λ i -> p i 𝒊)) ⟧                                       ∎

  in P1



suc↥ : (i j : ℕ) -> suc (i ↥ j) == suc i ↥ suc j
suc↥ i j with compare i j | compare (suc i) (suc j)
suc↥ i j | less x | less x₁ = refl
suc↥ i j | less x | equal x₁ = ⊥-elim (lessEqual-⊥ x (cong pred x₁))
suc↥ i j | less x | greater x₁ = ⊥-elim (lessGreater-⊥ x (pred-monotone x₁))
suc↥ i j | equal x | less x₁ = ⊥-elim (lessEqual-⊥ x₁ (cong suc x))
suc↥ i j | equal x | equal x₁ = refl
suc↥ i j | equal x | greater x₁ = ⊥-elim (lessEqual-⊥ x₁ (cong suc (sym x)))
suc↥ i j | greater x | less x₁ = ⊥-elim (lessGreater-⊥ (suc-monotone x) x₁)
suc↥ i j | greater x | equal x₁ = ⊥-elim (lessEqual-⊥ (suc-monotone x) (sym x₁))
suc↥ i j | greater x | greater x₁ = refl

fsuc↥ : ∀{n} -> (i : Fin n) ->  (j : Fin (suc n)) -> fsuc (i ↥f j) == (fsuc i ↥f fsuc j)
fsuc↥ i j = finEqual2 _ _ {suc↥ (⍛ i) (⍛ j)}



-- TODO: Merge with the above at πfsuc
πfsuc-i : ∀{n} -> (A : Fin (suc n) -> Obj) -> (i : Fin n) -> πᵢ {A = A} (fsuc i) == π₁ ◇ πᵢ {A = tail A} i
πfsuc-i {n} A i =
  let

      ii : Fin n -> Fin n
      ii k = ⍛ k ⌈ pred-monotone (fnatless (fsuc k))


      ipp : (fsuc (ii i)) == fsuc i
      ipp = finEqual (suc (⍛ i)) {fnatless (fsuc (ii i))} {fnatless (fsuc i)}

      ip : A (fsuc (ii i)) == A (fsuc i)
      ip 𝒊 = A (ipp 𝒊)


      p3 : ii i == i
      p3 = finEqual (⍛ i)

      defp : A (fsuc (ii i)) == A (fsuc i)
      defp = cong (A ∘ fsuc) (p3)

      p4 : πᵢ (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ defp 𝒊) ⟯= πᵢ i
      p4 𝒊 = πᵢ (p3 𝒊)

      p5 : ipp == cong fsuc (p3)
      p5 = Fin-isSet (fsuc (ii i)) (fsuc i) (ipp) (cong fsuc (p3))

      p6 : ip == defp
      p6 = cong (cong A) (p5)


      -- Here we need to substitute the path over which our equality goes. For it must go over the custom (fsuc (ii i) == fsuc i) path above,
      -- but by refl we can go only over (cong fsuc (πᵢ p3)), since the πᵢ {A = tail A} automatically adds an (fsuc).
      p0 : πᵢ {n} {A = (tail A)} (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ ip 𝒊) ⟯= πᵢ {n} {A = (tail A)} i
      p0 = subst {P = λ ξ -> πᵢ (ii i) =⟮ (λ 𝒊 -> ⨅ (tail A) ⇁ ξ 𝒊) ⟯= πᵢ i } (sym (p6)) (p4)


      P0 = π₁ ◇ πᵢ (ii i) ◇ O=⟦ ip ⟧        ≡⟨ asc π₁ (πᵢ (ii i)) O=⟦ ip ⟧ ⟩
            π₁ ◇ (πᵢ (ii i) ◇ O=⟦ ip ⟧)     ≡⟨ p-unit-r (ip) (πᵢ (ii i)) (πᵢ i) (p0) |ctx| (λ ξ -> π₁ ◇ ξ) ⟩
            π₁ ◇ πᵢ {A = tail A} i          ∎


  in P0


⟪⟫-fsuc↥ : ∀{n} -> (A : Fin (suc (suc n)) -> Obj) -> (j : Fin (suc n)) ->
           ⟪ (λ i -> πᵢ {A = A} (i ↥f fsuc j)) ⟫
           == ( ⟪ (λ i -> πᵢ {A = tail A} (i ↥f j)) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧)) ×× id
⟪⟫-fsuc↥ {n} A j =
  let

      P2 : ∀ i -> πᵢ {A = A} (fsuc (i ↥f j)) =⟮ (λ 𝒊 -> ⨅ A ⇁ A (fsuc↥ i j 𝒊)) ⟯= πᵢ {A = A} (fsuc i ↥f fsuc j)
      P2 i 𝒊 = πᵢ {A = A} (fsuc↥ i j 𝒊)

      P1 : ∀ i -> πᵢ {A = A} (fsuc i ↥f fsuc j) == πᵢ {A = A} (fsuc (i ↥f j)) ◇ O=⟦ cong A (fsuc↥ i j) ⟧
      P1 i = sym (p-unit-r (cong A (fsuc↥ i j)) (πᵢ {A = A} (fsuc (i ↥f j))) (πᵢ {A = A} (fsuc i ↥f fsuc j))  (P2 i))

      P = ⟪ (λ i -> πᵢ {A = A} (i ↥f fsuc j)) ⟫            ≡⟨ refl ⟩
          ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc i ↥f fsuc j)) ⟫ , πᵢ {A = A} fzero ⟩                ≡⟨ (λ 𝒊 -> ⟨ ⟪ (λ i -> P1 i 𝒊) ⟫ , πfzero {A = A} 𝒊 ⟩) ⟩
          ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc (i ↥f j)) ◇ O=⟦ cong A (fsuc↥ i j) ⟧ ) ⟫ , π₂ {A = ⨅ (tail A)} ⟩

            ≡⟨ (λ 𝒊 -> ⟨ ⟪⟫-comp (λ i -> πᵢ {A = A} (fsuc (i ↥f j))) (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) (𝒊) , unit-r π₂ (~ 𝒊) ⟩ ) ⟩

          ⟨ ⟪ (λ i -> πᵢ {A = A} (fsuc (i ↥f j))) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) , π₂ ◇ id ⟩

            ≡⟨ (λ 𝒊 -> ⟨ ⟪ (λ i -> πfsuc-i A (i ↥f j) 𝒊) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) , π₂ ◇ id ⟩ ) ⟩

          ⟨ ⟪ (λ i -> π₁ ◇ πᵢ {A = tail A} (i ↥f j)) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) , π₂ ◇ id ⟩

            ≡⟨ sym (comp-⟪,⟫ π₁ (λ i -> πᵢ {A = tail A} (i ↥f j))) |ctx| (λ ξ -> ⟨ ξ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) , π₂ ◇ id ⟩ ) ⟩

          ⟨ π₁ ◇ ⟪ (λ i -> πᵢ {A = tail A} (i ↥f j)) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧) , π₂ ◇ id ⟩

            ≡⟨ asc π₁ ⟪ (λ i -> πᵢ {A = tail A} (i ↥f j)) ⟫ (⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧)) |ctx| (λ ξ -> ⟨ ξ , π₂ ◇ id ⟩ ) ⟩

          ⟨ π₁ ◇ (⟪ (λ i -> πᵢ {A = tail A} (i ↥f j)) ⟫ ◇ ⨉ (λ i -> O=⟦ cong A (fsuc↥ i j) ⟧)) , π₂ ◇ id ⟩

            ∎

  in P

\end{code}
