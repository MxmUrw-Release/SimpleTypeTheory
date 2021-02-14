
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base
  renaming (_×_ to _|×|_ )
open import TypeTheory.Lambda.Param
open import TypeTheory.Lambda.IParam

module TypeTheory.Lambda.Interpretation.InterpretationProofsWeak {ℓ ℓ'} {iparam : IParam ℓ ℓ'} where
open IParam iparam

open import TypeTheory.Lambda.Base.CCCProofs {iparam = iparam}
open import TypeTheory.Lambda.Base.CCCid {iparam = iparam}
open import TypeTheory.Lambda.Interpretation.Interpretation {iparam = iparam}

open Category 𝒞
open isCCC CCC
open hasTerminal Terminal
open hasProducts Products
open hasExponentials Exponentials

open LambdaParam param
open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction {param = param}

\end{code}



%----------------------------------------------------------------------
\section{Properties}
%----------------------------------------------------------------------

Having defined the interpretation functions, we can now state how they
interact with concepts like weakening and substitution.


%---------------------------------------------
%-- Simultaneous Substitution
\begin{code}[hide]
IΛ⇓ : ∀{m t σ τ} -> {Γ : Ctx m} -> (T : σ ,, Γ ⊢ t :: τ) -> J⟦ Λ⇓ T ⟧ == C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ T ⟧
\end{code}
\begin{code}[hide]
IΛ⇓ {m} {t} {σ} {τ} {Γ} T =
  let
      T2 , _ = addVarLambda (Λ⇓ T)

      P0 : T2 == T
      P0 = Jmapt= T2 T refl

      P1 : C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ T2 ⟧ == C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ T ⟧
      P1 = P0 |ctx| (λ ξ -> C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ ξ ⟧)

  in P1

\end{code}
\begin{code}[hide]
Iapp⇓ : ∀{m t s τ σ} -> {Γ : Ctx m} -> (T : Γ ⊢ t :: σ ⇒ τ) -> (S : Γ ⊢ s :: σ) -> J⟦ app⇓ T S ⟧ == ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev
\end{code}
\begin{code}[hide]
Iapp⇓ {m} {t} {s} {τ} {σ} {Γ} T S =
  let
      ξ , T2 , S2 = app⇑ (app⇓ T S)

      ξ=σ = uniqueT S2 S

      P0 : T2 =⟮ (λ 𝒊 -> Γ ⊢ t :: ξ=σ 𝒊 ⇒ τ) ⟯= T
      P0 = JmapT= T2 T (cong (_⇒ τ) ξ=σ)

      P1 : S2 =⟮ (λ 𝒊 -> Γ ⊢ s :: ξ=σ 𝒊) ⟯= S
      P1 = JmapT= S2 S ξ=σ

      P2 : ⟨ J⟦ T2 ⟧ , J⟦ S2 ⟧ ⟩ ◇ ev == ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev
      P2 𝒊 = ⟨ J⟦ P0 𝒊 ⟧ , J⟦ P1 𝒊 ⟧ ⟩ ◇ ev

  in P2


\end{code}
\begin{code}[hide]
IVarType⇓ : ∀{m} {Γ : Ctx m} -> (i : Fin m) -> J⟦ iVarType {Γ = Γ} i ⟧ == πᵢ i
\end{code}
\begin{code}[hide]
IVarType⇓ {m} {Γ} i =
  let
      i₂ , Γi₂=Γi , ⍛i₂=⍛i = V⇑ (iVarType {Γ = Γ} i)

      i₂=i : i₂ == i
      i₂=i = finEqual2 i₂ i {⍛i₂=⍛i}

      p : Γ i₂ == Γ i
      p 𝒊 = Γ (i₂=i 𝒊)

      p2 : Γ i₂ == Γ i
      p2 = Γi₂=Γi


      A = λ k -> T⟦ Γ k ⟧

      q : C⟦ Γ ⟧ ⇁ T⟦ Γ i₂ ⟧ == C⟦ Γ ⟧ ⇁ T⟦ Γ i ⟧
      q = λ 𝒊 -> C⟦ Γ ⟧ ⇁ T⟦ p 𝒊 ⟧

      q2 : C⟦ Γ ⟧ ⇁ T⟦ Γ i₂ ⟧ == C⟦ Γ ⟧ ⇁ T⟦ Γ i ⟧
      q2 = λ 𝒊 -> C⟦ Γ ⟧ ⇁ T⟦ p2 𝒊 ⟧

      P1 : πᵢ {A = A} i₂ =⟮ q ⟯= πᵢ {A = A} i
      P1 𝒊 = πᵢ (i₂=i 𝒊)

      P2 : p == p2
      P2 = (Ty-isSet _ _ p p2)

      P3 : q == q2
      P3 = cong (cong (λ ξ -> C⟦ Γ ⟧ ⇁ T⟦ ξ ⟧)) P2

      P4 = πᵢ i₂ ◇ T=⟦ Γi₂=Γi ⟧   ≡⟨ p-unit-r (cong T⟦_⟧ p2) (πᵢ i₂) (πᵢ i) (substP P3 P1) ⟩
           πᵢ i                   ∎

  in P4
\end{code}





%--------------------------------------
%-- Sub₀ as fan


\begin{lemma}\label{lem:ISub0}
  The context morphism of substituting the first variable with a term ${T : Γ ⊢ t :: τ}$ is like
  the product of $\AF{id}$ and $\JJ{T}$, except that a type correction arrow is used instead of
  $\AF{id}$.
  Using diagrams, we say that the arrow
  \[
    \begin{tikzcd}[column sep=9em]
      \CC{Γ} \ar[r, "\MM{\AF{Sub₀}\:T}"] & \CC{τ,,Γ}
    \end{tikzcd}
  \]
  is equal to the following:
  \[
    \begin{tikzcd}[column sep=9em]
      \CC{Γ} \ar[r, "{⟨ \CCeq{\AF{tail=}\:τ\:Γ}\,,\,\JJ{T} ⟩}"] & \CC{\AF{tail}\:(τ,,Γ)} × \TT{τ}
    \end{tikzcd}
  \]
  In Agda this is formalized using the following statement:
\newpage
\begin{code}
ISub₀ : ∀{t τ}  -> {Γ : Ctx m}
                -> (T : Γ ⊢ t :: τ)
                -> M⟦ Sub₀ T ⟧ == ⟨ C=⟦ (tail= τ Γ) ⟧ , J⟦ T ⟧ ⟩
\end{code}
\end{lemma}
\begin{code}[hide]
ISub₀ {m} {t} {τ} {Γ} T =
  let
      0/t , T0 = Sub₀ T

      p : 0/t 0 == t
      p = /same 0 t

      P1 : J⟦ T0 fzero ⟧ == J⟦ T ⟧
      P1 i = J⟦ Jmapt= (T0 fzero) T p i ⟧

      Γi=τΓsi : ∀(i) -> Γ i == (τ ,, Γ) (fsuc i)
      Γi=τΓsi i = cong (_$ i) (tail= τ Γ)

      Vᵢ : ∀(i : Fin m) -> Γ ⊢ V (⍛ i) :: (τ ,, Γ) (fsuc i)
      Vᵢ i = V⇓ (Γi=τΓsi i)

      Q1 : ∀(i : Fin m) -> J⟦ T0 (fsuc i) ⟧ == πᵢ i ◇ T=⟦ Γi=τΓsi i ⟧
      Q1 i =
        let
            R1 : J⟦ T0 (fsuc i) ⟧ == J⟦ Vᵢ i ⟧
            R1 𝒊 = J⟦ Jmapt= (T0 (fsuc i)) (Vᵢ i) refl 𝒊 ⟧

            j , Γj=τΓsi , ⍛j=⍛i = V⇑ (Vᵢ i)

            j=i : j == i
            j=i = finEqual2 j i {p = ⍛j=⍛i}

            depP : Fin m -> 𝒰₀
            depP k = Γ k == (τ ,, Γ) (fsuc i)

            p2 : PathP (λ 𝒊 -> depP (j=i 𝒊)) Γj=τΓsi (Γi=τΓsi i)
            p2 = depSet depP j=i (Ty-isSet (Γ i) ((τ ,, Γ) (fsuc i)))

            R2 : πᵢ j ◇ T=⟦ Γj=τΓsi ⟧ == πᵢ i ◇ T=⟦ Γi=τΓsi i ⟧
            R2 𝒊 = πᵢ (j=i 𝒊) ◇ T=⟦ p2 𝒊 ⟧

        in R1 ∙ R2

      Q2 : ⟪ (λ i -> J⟦ T0 (fsuc i) ⟧) ⟫ == ⨉ (λ i -> T=⟦ Γi=τΓsi i ⟧)
      Q2 𝒊 = ⟪ (λ i -> Q1 i 𝒊) ⟫

      P3 : ⟪ J⟦_⟧ ∘ T0 ⟫ == ⟨ C=⟦ tail= τ Γ ⟧ , J⟦ T ⟧ ⟩
      P3 𝒊 = ⟨ Q2 𝒊 , P1 𝒊 ⟩

  in P3

IJmapC : ∀{m t τ} -> {Γ Δ : Ctx m} -> (p : Γ == Δ) -> (T : Γ ⊢ t :: τ) -> J⟦ JmapC p T ⟧ == C=⟦ sym p ⟧ ◇ J⟦ T ⟧
IJmapC {m} {t} {τ} {Γ} {Δ} p T =
  let
      P = (λ 𝒊 -> ⨅ (λ i -> T⟦ p (~ 𝒊) i ⟧))

      P1 : C=⟦ sym p ⟧ == O=⟦ P ⟧
      P1 = ⨉-O= (λ i 𝒊 -> T⟦ p (~ 𝒊) i ⟧)

      P3 : J⟦ T ⟧ =⟮ (λ 𝒊 -> P (~ 𝒊) ⇁ T⟦ τ ⟧) ⟯= J⟦ JmapC p T ⟧
      P3 𝒊 = J⟦ JmapC= T (JmapC p T) p 𝒊 ⟧

      P2 : O=⟦ P ⟧ ◇ J⟦ T ⟧ == J⟦ JmapC p T ⟧
      P2 = p-unit-l P J⟦ T ⟧ J⟦ JmapC p T ⟧ P3

  in sym P2 ∙ cong (_◇ J⟦ T ⟧) (sym P1)


T=comp : ∀{A B C : Ty} -> (p : A == B) -> (q : B == C) -> T=⟦ p ⟧ ◇ T=⟦ q ⟧ == T=⟦ p ∙ q ⟧
T=comp {A} {B} {C} p q = O=comp (cong T⟦_⟧ p) (cong T⟦_⟧ q) ∙ cong O=⟦_⟧ (trans-cong T⟦_⟧ p C q)


Imapt= : ∀{n t u τ} -> {Γ : Ctx n} -> (p : t == u) -> (T : Γ ⊢ t :: τ) -> J⟦ Jmapt p T ⟧ == J⟦ T ⟧
Imapt= {n} {t} {u} {τ} {Γ} p T = λ 𝒊 -> J⟦ (Jmapt= (Jmapt p T) T (sym p)) 𝒊 ⟧

\end{code}

\begin{theorem}[Semantics of weakening]\label{th:IWeak}
  The interpretation of a weakened term $\AF{weak}\:T\:σ\:j$ is equal to the
  morphism of type $\CC{(j ↓ σ)\:Γ} \to \CC{Γ}$ which projects all types
  except the $j$-th, followed by $\JJ{T}$.
  \[
    \begin{tikzcd}[column sep=6em, row sep=large]
      \CC{(j ↓ σ)\:Γ} \ar[r, "{⟪ (λ i \to πᵢ (i\:\AF{↥f}\:j)) ⟫}"] \ar[rdd, swap, "\JJ{\AF{weak}\:T\:σ\:j}"] & \CC{λ i \to (j ↓ σ) Γ (i\:\AF{↥f}\:j)} \ar[d, "\CCeq{\AF{insertLShiftL}\:Γ\:j\:σ}"] \\
      & \CC{Γ} \ar[d, "\JJ{T}"] \\
      & \TT{τ}
    \end{tikzcd}
  \]
\begin{code}
IWeak : ∀{m t τ}  -> {Γ : Ctx m} -> (σ : Ty)
                  -> (T : Γ ⊢ t :: τ) -> (j : Fin (suc m))
                  -> J⟦ weak T σ j ⟧
                     ==
                     ⟪ (λ i -> πᵢ {A = λ k -> T⟦ ((j ↓ σ) Γ) k ⟧} (i ↥f j)) ⟫
                     ◇ C=⟦ insertLShiftL Γ j σ ⟧
                     ◇ J⟦ T ⟧
\end{code}
\end{theorem}
\begin{code}[hide]
IWeak {m} {cconst x} {τ} {Γ} σ T j =
  let
      xp1 = cconst⇑ T
      xp2 = cconst⇑ (weak T σ j)


      A = λ k -> T⟦ (j ↓ σ) Γ k ⟧

      F : (i : Fin m) -> C⟦ (j ↓ σ) Γ ⟧ ⇁ T⟦ (j ↓ σ) Γ (i ↥f j) ⟧
      F i = πᵢ {A = A} (i ↥f j)

      P0 : xp2 == xp1
      P0 = Ty-isSet _ _ xp2 xp1

      P1 = !! ◇ Mc x ◇ T=⟦ xp2 ⟧                                           ≡⟨ P0       |ctx| (λ ξ -> !! ◇ Mc x ◇ T=⟦ ξ ⟧) ⟩
           !! ◇ Mc x ◇ T=⟦ xp1 ⟧                                           ≡⟨ asc !! (Mc x) T=⟦ xp1 ⟧ ⟩
           !! ◇ (Mc x ◇ T=⟦ xp1 ⟧)                                         ≡⟨ !-uprop |ctx| (λ ξ -> ξ ◇ (Mc x ◇ T=⟦ xp1 ⟧)) ⟩
           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ !! ◇ (Mc x ◇ T=⟦ xp1 ⟧)    ≡⟨ asc (⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧) !! (Mc x ◇ T=⟦ xp1 ⟧) ⟩
           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (!! ◇ (Mc x ◇ T=⟦ xp1 ⟧))  ≡⟨ sym (asc !! (Mc x) (T=⟦ xp1 ⟧)) |ctx| (λ ξ -> ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ ξ) ⟩
           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (!! ◇ Mc x ◇ T=⟦ xp1 ⟧)    ∎

  in P1
IWeak {m} {V i} {τ} {Γ} σ T j =
  let
      i₃ , Γi₃=τ , i₃=i↥j = V⇑ (weak T σ j)
      i₂ , Γi₂=τ , i₂=i = V⇑ (T)

      A = λ k -> T⟦ (j ↓ σ) Γ k ⟧

      F : (i : Fin m) -> C⟦ (j ↓ σ) Γ ⟧ ⇁ T⟦ (j ↓ σ) Γ (i ↥f j) ⟧
      F i = πᵢ {A = A} (i ↥f j)

      P1 : ⍛ i₃ == ⍛ (i₂ ↥f j)
      P1 =
           ⍛ i₃       ≡⟨ i₃=i↥j ⟩
           i ↥ ⍛ j    ≡⟨ (sym i₂=i) |ctx| (_↥ ⍛ j) ⟩
           ⍛ i₂ ↥ ⍛ j ∎

      P2 : i₃ == (i₂ ↥f j)
      P2 = finEqual2 _ _ {P1}

      P4 : πᵢ i₃ =⟮ (λ 𝒊 -> ⨅ A ⇁ A (P2 𝒊) ) ⟯= πᵢ {A = A} (i₂ ↥f j)
      P4 𝒊 = πᵢ {A = A} (P2 𝒊)

      P3 : πᵢ {A = A} (i₂ ↥f j) == πᵢ {A = A} i₃ ◇ T=⟦ cong ((j ↓ σ) Γ) P2 ⟧
      P3 = sym (p-unit-r (cong A P2) (πᵢ {A = A} i₃) (πᵢ {A = A} (i₂ ↥f j)) P4)

      Q1 =
            ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (πᵢ i₂ ◇ T=⟦ Γi₂=τ ⟧)           ≡⟨ asc ⟪ F ⟫ C=⟦ insertLShiftL Γ j σ ⟧ (πᵢ i₂ ◇ T=⟦ Γi₂=τ ⟧) ⟩
            ⟪ F ⟫ ◇ (C=⟦ insertLShiftL Γ j σ ⟧ ◇ (πᵢ i₂ ◇ T=⟦ Γi₂=τ ⟧))         ≡⟨ sym (asc C=⟦ insertLShiftL Γ j σ ⟧ (πᵢ i₂) T=⟦ Γi₂=τ ⟧) |ctx| (⟪ F ⟫ ◇_) ⟩
            ⟪ F ⟫ ◇ (C=⟦ insertLShiftL Γ j σ ⟧ ◇ πᵢ i₂ ◇ T=⟦ Γi₂=τ ⟧)           ≡⟨ ⨉-π (λ i -> T=⟦ insertLShiftL₂ Γ j σ i ⟧) i₂ |ctx| (λ ξ -> ⟪ F ⟫ ◇ (ξ ◇ T=⟦ Γi₂=τ ⟧)) ⟩
            ⟪ F ⟫ ◇ (πᵢ i₂ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ ◇ T=⟦ Γi₂=τ ⟧)       ≡⟨ sym (asc ⟪ F ⟫ (πᵢ i₂ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧) T=⟦ Γi₂=τ ⟧) ⟩
            ⟪ F ⟫ ◇ (πᵢ i₂ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧) ◇ T=⟦ Γi₂=τ ⟧       ≡⟨ sym (asc ⟪ F ⟫ (πᵢ i₂) T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ |ctx| (_◇ T=⟦ Γi₂=τ ⟧)) ⟩
            ⟪ F ⟫ ◇ πᵢ i₂ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ ◇ T=⟦ Γi₂=τ ⟧         ≡⟨ ⟪,⟫-prop F i₂ |ctx| (λ ξ -> ξ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ ◇ T=⟦ Γi₂=τ ⟧) ⟩
            πᵢ {A = A} (i₂ ↥f j) ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ ◇ T=⟦ Γi₂=τ ⟧   ≡⟨ asc (πᵢ {A = A} (i₂ ↥f j)) T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ T=⟦ Γi₂=τ ⟧ ⟩
            πᵢ {A = A} (i₂ ↥f j) ◇ (T=⟦ insertLShiftL₂ Γ j σ i₂ ⟧ ◇ T=⟦ Γi₂=τ ⟧) ≡⟨ T=comp ((insertLShiftL₂ Γ j σ i₂)) ((Γi₂=τ)) |ctx| (πᵢ {A = A} (i₂ ↥f j) ◇_) ⟩
            πᵢ {A = A} (i₂ ↥f j) ◇ (T=⟦ insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ ⟧)       ≡⟨ P3 |ctx| (_◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ ⟧) ⟩
            πᵢ {A = A} i₃ ◇ T=⟦ cong ((j ↓ σ) Γ) P2 ⟧ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ ⟧    ≡⟨ asc (πᵢ {A = A} i₃) T=⟦ cong ((j ↓ σ) Γ) P2 ⟧ (T=⟦ insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ ⟧) ⟩
            πᵢ {A = A} i₃ ◇ (T=⟦ cong ((j ↓ σ) Γ) P2 ⟧ ◇ T=⟦ insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ ⟧)  ≡⟨ T=comp (cong ((j ↓ σ) Γ) P2) (insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ) |ctx| (πᵢ {A = A} i₃ ◇_) ⟩
            πᵢ {A = A} i₃ ◇ T=⟦ cong ((j ↓ σ) Γ) P2 ∙ (insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ) ⟧        ≡⟨ Ty-isSet _ _ (cong ((j ↓ σ) Γ) P2 ∙ (insertLShiftL₂ Γ j σ i₂ ∙ Γi₂=τ)) Γi₃=τ |ctx| (λ ξ -> πᵢ {A = A} i₃ ◇ T=⟦ ξ ⟧) ⟩
            πᵢ {A = A} i₃ ◇ T=⟦ Γi₃=τ ⟧                                                           ∎


  in sym Q1
IWeak {m} {Λ x t} {ι x₁} {Γ} σ T j = ⊥-elim (lambdaNoFunc T)
IWeak {m} {Λ τ r} {ψ ⇒ ξ} {Γ} σ ΛR j =
  let
      R , ψ=τ = addVarLambda ΛR
      pΓ = sym (funExt (insertLComma Γ j σ))

      A = λ k -> T⟦ (j ↓ σ) Γ k ⟧
      A₂ = λ k -> T⟦ (fsuc j ↓ σ) (ψ ,, Γ) k ⟧

      F : (i : Fin m) -> C⟦ (j ↓ σ) Γ ⟧ ⇁ T⟦ (j ↓ σ) Γ (i ↥f j) ⟧
      F i = πᵢ {A = A} (i ↥f j)


\end{code}
      % --------------------------------------
      % -- pulling out the ids
      % --
      % -- 1 : C=⟦ sym pΓ ⟧ => G1
\begin{code}[hide]
      q1-1 : (ψ ,, (j ↓ σ) Γ) fzero == ψ
      q1-1 = refl

      q1-2 : (fsuc j ↓ σ) (ψ ,, Γ) fzero == ψ
      q1-2 = insertLCommaZero j σ ψ Γ

      G1-P : ∀(i : Fin (suc (suc m))) -> (ψ ,, (j ↓ σ) Γ) i == (fsuc j ↓ σ) (ψ ,, Γ) i
      G1-P = λ i 𝒊 -> pΓ (~ 𝒊) i

      G1A = λ (i : Fin (suc m)) -> T=⟦ (λ 𝒊 -> pΓ (~ 𝒊) (fsuc i)) ⟧
      G1B = T=⟦ (λ 𝒊 -> pΓ (~ 𝒊) fzero) ⟧

      q1-3 : C=⟦ sym pΓ ⟧ == ⨉ (G1A) ×× G1B
      q1-3 = ⨉-tail (λ i -> T=⟦ (λ 𝒊 -> pΓ (~ 𝒊) i) ⟧)

\end{code}
      %-- 2 : ⟪ ... ⟫ => G2
\begin{code}[hide]

      G2-P : ∀(i : Fin (m)) -> (fsuc j ↓ σ) (ψ ,, Γ) (fsuc (i ↥f j)) == (fsuc j ↓ σ) (ψ ,, Γ) (fsuc i ↥f fsuc j)
      G2-P i = λ 𝒊 -> (fsuc j ↓ σ) (ψ ,, Γ) (fsuc↥ i j 𝒊)

      G2A = (λ i -> πᵢ {A = tail A₂} (i ↥f j))
      G2B = λ i -> T=⟦ G2-P i ⟧

      q2-1 : ⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ == (⟪ G2A ⟫ ◇ ⨉ (G2B)) ×× id
      q2-1 = ⟪⟫-fsuc↥ A₂ j

\end{code}
      %-- 3 : C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧ => G3
\begin{code}[hide]

      G3-P : ∀(i : Fin (suc (m))) -> (fsuc j ↓ σ) (ψ ,, Γ) (i ↥f fsuc j) == (ψ ,, Γ) i
      G3-P = λ i 𝒊 -> insertLShiftL (ψ ,, Γ) (fsuc j) σ 𝒊 i

      G3-F = λ i -> T=⟦ G3-P i ⟧

      G3A = (λ i -> G3-F (fsuc i))
      G3B = G3-F fzero

      q3-1 : C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧ == ⨉ G3A ×× G3B
      q3-1 = ⨉-tail G3-F

\end{code}
      % -- preparing the replacement
\begin{code}[hide]

      r1 : C=⟦ sym pΓ ⟧ ◇ ⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ ◇ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧ == (⨉ G1A ×× G1B) ◇ ((⟪ G2A ⟫ ◇ ⨉ G2B) ×× id) ◇ (⨉ G3A ×× G3B)
      r1 𝒊 = q1-3 𝒊 ◇ q2-1 𝒊 ◇ q3-1 𝒊

      r2 = G1B ◇ id ◇ G3B           ≡⟨ unit-r G1B |ctx| (_◇ G3B) ⟩
           G1B ◇ G3B                 ≡⟨ (λ 𝒊 -> G1B ◇ T=⟦ Ty-isSet _ _ (G3-P fzero) (sym (G1-P fzero)) 𝒊 ⟧ ) ⟩
           T=⟦ G1-P fzero ⟧ ◇ T=⟦ sym (G1-P fzero) ⟧ ≡⟨ p-inv (cong T⟦_⟧ (G1-P fzero)) ⟩
           id                       ∎

      r3 = (⨉ G1A ×× G1B) ◇ ((⟪ G2A ⟫ ◇ ⨉ G2B) ×× id) ◇ (⨉ G3A ×× G3B)       ≡⟨ ××-comp (⨉ G1A) G1B (⟪ G2A ⟫ ◇ ⨉ G2B) id |ctx| (_◇ (⨉ G3A ×× G3B)) ⟩
           ((⨉ G1A ◇ (⟪ G2A ⟫ ◇ ⨉ G2B)) ×× (G1B ◇ id)) ◇ (⨉ G3A ×× G3B)      ≡⟨ ××-comp (⨉ G1A ◇ (⟪ G2A ⟫ ◇ ⨉ G2B)) (G1B ◇ id) (⨉ G3A) G3B ⟩
           (⨉ G1A ◇ (⟪ G2A ⟫ ◇ ⨉ G2B) ◇ ⨉ G3A) ×× (G1B ◇ id ◇ G3B)           ≡⟨ r2 |ctx| ((⨉ G1A ◇ (⟪ G2A ⟫ ◇ ⨉ G2B) ◇ ⨉ G3A) ××_) ⟩
           (⨉ G1A ◇ (⟪ G2A ⟫ ◇ ⨉ G2B) ◇ ⨉ G3A) ×× id                         ≡⟨ sym (asc (⨉ G1A) ⟪ G2A ⟫ (⨉ G2B)) |ctx| (λ ξ -> (ξ ◇ ⨉ G3A) ×× id) ⟩
           (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) ×× id                           ∎


\end{code}
      % -- finding common shape of LHS and RHS

      % -- step 1: shifting the fan of LHS to the beginning
\begin{code}[hide]

      G0-P : ∀(i : Fin (suc m)) -> (j ↓ σ) Γ i == tail (τ ,, (j ↓ σ) Γ) i
      G0-P = λ i 𝒊 -> tail= τ ((j ↓ σ) Γ) 𝒊 i

      G0 = λ i -> T=⟦ G0-P i ⟧


      lhs-1 = ⨉ G0 ◇ ⨉ G1A ◇ ⟪ G2A ⟫                                              ≡⟨ ⨉-comp G0 G1A |ctx| (_◇ ⟪ G2A ⟫) ⟩
              ⨉ (λ i -> G0 i ◇ G1A i) ◇ ⟪ G2A ⟫                                    ≡⟨ comp-⟪,⟫ (⨉ (λ i -> G0 i ◇ G1A i)) G2A ⟩
              ⟪ (λ i -> ⨉ (λ i -> G0 i ◇ G1A i) ◇ πᵢ {A = tail A₂} (i ↥f j)) ⟫     ≡⟨ (λ 𝒊 -> ⟪ (λ i -> (⨉-π (λ i -> G0 i ◇ G1A i) (i ↥f j) 𝒊)) ⟫) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j))) ⟫       ∎

\end{code}
      % -- step 2: including all other products
\begin{code}[hide]
      lhs-2 = ⨉ G0 ◇ ⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A                                             ≡⟨ lhs-1 |ctx| (λ ξ -> ξ ◇ ⨉ G2B ◇ ⨉ G3A) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j))) ⟫ ◇ ⨉ G2B ◇ ⨉ G3A      ≡⟨ sym (⟪⟫-comp (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j))) G2B) |ctx| (_◇ ⨉ G3A) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j)) ◇ G2B i) ⟫ ◇ ⨉ G3A       ≡⟨ sym (⟪⟫-comp (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j)) ◇ G2B i) G3A) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j)) ◇ G2B i ◇ G3A i) ⟫        ∎

\end{code}
      % -- step 3: combining all the T=⟦⟧'s into a single one
\begin{code}[hide]
      lhs-3 = λ (i : Fin (m)) ->
              πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j)) ◇ G2B i ◇ G3A i                      ≡⟨ T=comp (G0-P (i ↥f j)) (G1-P (fsuc (i ↥f j))) |ctx| (λ ξ -> πᵢ {A = A} (i ↥f j) ◇ ξ ◇ G2B i ◇ G3A i) ⟩
              πᵢ {A = A} (i ↥f j) ◇ T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ ◇ G2B i ◇ G3A i      ≡⟨ asc (πᵢ {A = A} (i ↥f j) ◇ T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧) (G2B i) (G3A i) ⟩
              πᵢ {A = A} (i ↥f j) ◇ T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ ◇ (G2B i ◇ G3A i)    ≡⟨ asc (πᵢ {A = A} (i ↥f j)) T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ (G2B i ◇ G3A i) ⟩
              πᵢ {A = A} (i ↥f j) ◇ (T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ ◇ (G2B i ◇ G3A i))

                ≡⟨ T=comp (G2-P i) (G3-P (fsuc i)) |ctx| (λ ξ -> πᵢ {A = A} (i ↥f j) ◇ (T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ ◇ ξ)) ⟩

              πᵢ {A = A} (i ↥f j) ◇ (T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ⟧ ◇ (T=⟦ G2-P i ∙ G3-P (fsuc i) ⟧))

                ≡⟨ T=comp (G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j))) (G2-P i ∙ G3-P (fsuc i)) |ctx| (πᵢ {A = A} (i ↥f j) ◇_) ⟩

              πᵢ {A = A} (i ↥f j) ◇ (T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ∙ (G2-P i ∙ G3-P (fsuc i)) ⟧)

                ∎

\end{code}
      % -- step 4: now the same for the RHS
\begin{code}[hide]
      H0-P : ∀(i : Fin m) -> (j ↓ σ) Γ (i ↥f j) == Γ i
      H0-P i = λ 𝒊 -> insertLShiftL Γ j σ 𝒊 i

      H1-P : ∀(i : Fin m) -> Γ i == (ψ ,, Γ) (fsuc i)
      H1-P i = λ 𝒊 -> tail= ψ Γ 𝒊 i

      rhs-1 = ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ C=⟦ tail= ψ Γ ⟧                         ≡⟨ refl ⟩
              ⟪ F ⟫ ◇ ⨉ (λ i -> T=⟦ H0-P i ⟧) ◇ ⨉ (λ i -> T=⟦ H1-P i ⟧)                  ≡⟨ sym (⟪⟫-comp F (λ i -> T=⟦ H0-P i ⟧) |ctx| (_◇ ⨉ (λ i -> T=⟦ H1-P i ⟧))) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ⟧) ⟫ ◇ ⨉ (λ i -> T=⟦ H1-P i ⟧)   ≡⟨ sym (⟪⟫-comp (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ⟧) (λ i -> T=⟦ H1-P i ⟧)) ⟩
              ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ⟧ ◇ T=⟦ H1-P i ⟧) ⟫               ∎

      rhs-2 = λ (i : Fin m) ->
              πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ⟧ ◇ T=⟦ H1-P i ⟧                            ≡⟨ asc (πᵢ {A = A} (i ↥f j)) T=⟦ H0-P i ⟧ T=⟦ H1-P i ⟧ ⟩
              πᵢ {A = A} (i ↥f j) ◇ (T=⟦ H0-P i ⟧ ◇ T=⟦ H1-P i ⟧)                          ≡⟨ T=comp (H0-P i) (H1-P i) |ctx| (πᵢ {A = A} (i ↥f j) ◇_) ⟩
              πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ∙ H1-P i ⟧                                  ∎

\end{code}
      % -- step 5: show that the paths inside the T=⟦⟧ must be equal, by Ty-isSet
\begin{code}[hide]
      lhs-rhs : ∀(i : Fin m) -> T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ∙ (G2-P i ∙ G3-P (fsuc i)) ⟧ == T=⟦ H0-P i ∙ H1-P i ⟧
      lhs-rhs i = cong T=⟦_⟧ (Ty-isSet _ _ (G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ∙ (G2-P i ∙ G3-P (fsuc i))) (H0-P i ∙ H1-P i) )



      P3 : ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ J⟦ ΛR ⟧ == ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (C=⟦ tail= ψ Γ ⟧ ◇ curry J⟦ R ⟧)
      P3 = refl


\end{code}
      % -- step 6: bringing it all together
\begin{code}[hide]

      P1 : J⟦ Jmapt (ΛT= ψ=τ) (Λ⇓ (JmapC pΓ (weak R σ (fsuc j)))) ⟧ == ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ J⟦ ΛR ⟧

      P1 = J⟦ Jmapt (ΛT= ψ=τ) (Λ⇓ (JmapC pΓ (weak R σ (fsuc j)))) ⟧               ≡⟨ Imapt= (ΛT= ψ=τ) (Λ⇓ (JmapC pΓ (weak R σ (fsuc j)))) ⟩
           J⟦ Λ⇓ (JmapC pΓ (weak R σ (fsuc j))) ⟧                                  ≡⟨ IΛ⇓ (JmapC pΓ (weak R σ (fsuc j))) ⟩
           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry J⟦ JmapC pΓ (weak R σ (fsuc j)) ⟧     ≡⟨ IJmapC pΓ (weak R σ (fsuc j)) |ctx| (λ ξ -> C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry ξ) ⟩
           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (C=⟦ sym pΓ ⟧ ◇ J⟦ (weak R σ (fsuc j)) ⟧)

             ≡⟨ IWeak σ R (fsuc j) |ctx| (λ ξ -> C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (C=⟦ sym pΓ ⟧ ◇ ξ)) ⟩

           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (C=⟦ sym pΓ ⟧ ◇ (⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ ◇ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧ ◇ J⟦ R ⟧))

             ≡⟨ sym (asc C=⟦ sym pΓ ⟧ (⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ ◇ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧) J⟦ R ⟧) |ctx| (λ ξ -> C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry ξ) ⟩

           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (C=⟦ sym pΓ ⟧ ◇ (⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ ◇ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧) ◇ J⟦ R ⟧)

            ≡⟨ sym (asc C=⟦ sym pΓ ⟧ ⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧) |ctx| (λ ξ -> C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (ξ ◇ J⟦ R ⟧)) ⟩

           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (C=⟦ sym pΓ ⟧ ◇ ⟪ (λ i -> πᵢ {A = A₂} (i ↥f fsuc j)) ⟫ ◇ C=⟦ insertLShiftL (ψ ,, Γ) (fsuc j) σ ⟧ ◇ J⟦ R ⟧)

             ≡⟨ r1 ∙ r3 |ctx| (λ ξ -> C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (ξ ◇ J⟦ R ⟧)) ⟩

           C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇ curry (((⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) ×× id) ◇ J⟦ R ⟧)

             ≡⟨ curry-comp (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) J⟦ R ⟧ |ctx| (C=⟦ tail= τ ((j ↓ σ) Γ) ⟧ ◇_) ⟩

           ⨉ G0 ◇ ((⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) ◇ curry J⟦ R ⟧)

             ≡⟨ sym (asc (⨉ G0) (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) (curry J⟦ R ⟧)) ⟩

           ⨉ G0 ◇ (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A) ◇ curry J⟦ R ⟧

             ≡⟨ sym (asc (⨉ G0) (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B) (⨉ G3A)) |ctx| (_◇ curry J⟦ R ⟧) ⟩

           ⨉ G0 ◇ (⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B) ◇ ⨉ G3A ◇ curry J⟦ R ⟧

             ≡⟨ sym (asc (⨉ G0) (⨉ G1A ◇ ⟪ G2A ⟫) (⨉ G2B)) |ctx| (λ ξ -> ξ ◇ (⨉ G3A) ◇ curry J⟦ R ⟧) ⟩

           ⨉ G0 ◇ (⨉ G1A ◇ ⟪ G2A ⟫) ◇ ⨉ G2B ◇ ⨉ G3A ◇ curry J⟦ R ⟧

             ≡⟨ sym (asc (⨉ G0) (⨉ G1A) ⟪ G2A ⟫ ) |ctx| (λ ξ -> ξ ◇ (⨉ G2B) ◇ (⨉ G3A) ◇ curry J⟦ R ⟧) ⟩

           ⨉ G0 ◇ ⨉ G1A ◇ ⟪ G2A ⟫ ◇ ⨉ G2B ◇ ⨉ G3A ◇ curry J⟦ R ⟧

             ≡⟨ lhs-2 |ctx| (_◇ curry J⟦ R ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (G0 (i ↥f j) ◇ G1A (i ↥f j)) ◇ G2B i ◇ G3A i) ⟫ ◇ curry J⟦ R ⟧

             ≡⟨ funExt lhs-3 |ctx| (λ ξ -> ⟪ ξ ⟫ ◇ curry J⟦ R ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ G0-P (i ↥f j) ∙ G1-P (fsuc (i ↥f j)) ∙ (G2-P i ∙ G3-P (fsuc i)) ⟧) ⟫ ◇ curry J⟦ R ⟧

             ≡⟨ (λ 𝒊 -> ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ (lhs-rhs i 𝒊)) ⟫ ◇ curry J⟦ R ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ∙ H1-P i ⟧) ⟫ ◇ curry J⟦ R ⟧

             ≡⟨ sym (funExt rhs-2) |ctx| (λ ξ -> ⟪ ξ ⟫ ◇ curry J⟦ R ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (i ↥f j) ◇ T=⟦ H0-P i ⟧ ◇ T=⟦ H1-P i ⟧) ⟫ ◇ curry J⟦ R ⟧

             ≡⟨ sym rhs-1 |ctx| (_◇ curry J⟦ R ⟧) ⟩

           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ C=⟦ tail= ψ Γ ⟧ ◇ curry J⟦ R ⟧

             ≡⟨ asc (⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧) C=⟦ tail= ψ Γ ⟧ (curry J⟦ R ⟧) ⟩

           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (C=⟦ tail= ψ Γ ⟧ ◇ curry J⟦ R ⟧)

             ≡⟨ refl ⟩

           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ J⟦ ΛR ⟧

             ∎


  in P1
IWeak {m} {app t s} {τ} {Γ} σ TS j =
  let
      ξ , T , S = app⇑ TS

      A = λ k -> T⟦ (j ↓ σ) Γ k ⟧

      F : (i : Fin m) -> C⟦ (j ↓ σ) Γ ⟧ ⇁ T⟦ (j ↓ σ) Γ (i ↥f j) ⟧
      F i = πᵢ {A = A} (i ↥f j)

      P1 : J⟦ weak TS σ j ⟧ == ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev)

      P1 = J⟦ weak TS σ j ⟧                                                                                      ≡⟨ refl ⟩
           J⟦ app⇓ (weak T σ j) (weak S σ j) ⟧                                                                   ≡⟨ Iapp⇓ (weak T σ j) (weak S σ j) ⟩
           ⟨ J⟦ weak T σ j ⟧ , J⟦ weak S σ j ⟧ ⟩ ◇ ev                                                             ≡⟨ (λ 𝒊 -> ⟨ IWeak σ T j 𝒊 , IWeak σ S j 𝒊 ⟩ ◇ ev) ⟩
           ⟨ ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ J⟦ T ⟧ , ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ J⟦ S ⟧ ⟩ ◇ ev      ≡⟨ sym (comp-⟨,⟩ (⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧) J⟦ T ⟧ J⟦ S ⟧) |ctx| (_◇ ev) ⟩
           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev                                           ≡⟨ asc (⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧) ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ev ⟩
           ⟪ F ⟫ ◇ C=⟦ insertLShiftL Γ j σ ⟧ ◇ (⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev)                                         ∎

  in P1


↥fzero : ∀{n} -> (i : Fin n) -> (i ↥f fzero) == fsuc i
↥fzero {n} i with compare (⍛ i) zero
↥fzero {n} i | less x = ⊥-elim (lessZero-⊥ x)
↥fzero {n} i | equal x = finEqual (suc (⍛ i))
↥fzero {n} i | greater x = finEqual (suc (⍛ i))

\end{code}

\begin{remark}
The function $\AF{\_↥f\_}$ is like $\AF{\_↥\_}$, but defined for finite indices
instead of natural numbers. The term $\AF{insertLShiftL}\:Γ\:σ\:j$ is a proof of
\[
(λ i \to (j ↓ σ)\:Γ\:(i\:\AF{↥f}\:j)) = Γ
\]
meaning that inserting an element into
a list $Γ$, and then building a list which skips this element is equal to the
original list.
\end{remark}

\begin{corollary}\label{cor:IWeak0}
  The interpretation of weakening can be specialized to the case where an element
  is inserted at the front. Instead of the complex projection function which skips
  the $j$-th object from before, we can simply use $π₁$, projecting the tail of
  $(0 ↓ σ)\:Γ$.
  \[
    \begin{tikzcd}
      \CC{(0 ↓ σ)\:Γ} \ar[r, "π₁"] \ar[ddr, swap, "\JJ{\AF{weak}\:T\:σ\:0}"] & \CC{\AF{tail}((0 ↓ σ)\:Γ)} \ar[d, "\CCeq{\AF{sym}(\AF{tail=}\:σ\:Γ)}"] \\
      & \CC{Γ} \ar[d, "\JJ{T}"] \\
      & \TT{τ}
    \end{tikzcd}
  \]
\newpage
\begin{code}
IWeak₀ : ∀{t τ}  -> {Γ : Ctx m} -> (σ : Ty) -> (T : Γ ⊢ t :: τ)
                 ->  J⟦ weak T σ fzero ⟧
                     ==
                     π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ J⟦ T ⟧
\end{code}
\end{corollary}
\begin{proof}
This statement is a special case of Theorem \ref{th:Iext}.
\end{proof}
\begin{code}[hide]
IWeak₀ {m} {t} {τ} {Γ} σ T =
  let
      A = λ k -> T⟦ ((fzero ↓ σ) Γ) k ⟧


      p1 : ∀(i : Fin (m)) -> (fzero ↓ σ) Γ (fsuc i) == (fzero ↓ σ) Γ (i ↥f fzero)
      p1 i = cong ((fzero ↓ σ) Γ) (sym (↥fzero i))

      P3 : ∀(i : Fin m) -> πᵢ {A = A} (fsuc i) =⟮ (λ 𝒊 -> C⟦ (fzero ↓ σ) Γ ⟧ ⇁ T⟦ p1 i 𝒊 ⟧) ⟯= πᵢ {A = A} (i ↥f fzero)
      P3 i = λ 𝒊 -> πᵢ {A = A} (↥fzero i (~ 𝒊))

      P2 : ∀(i : Fin (m)) -> πᵢ {A = A} (i ↥f fzero) == πᵢ {A = A} (fsuc i) ◇ T=⟦ p1 i ⟧
      P2 i = sym (p-unit-r (cong T⟦_⟧ (p1 i)) (πᵢ {A = A} (fsuc i)) (πᵢ {A = A} (i ↥f fzero)) (P3 i))

      P1 = J⟦ weak T σ fzero ⟧                                                                      ≡⟨ IWeak σ T fzero ⟩
           ⟪ (λ i -> πᵢ {A = A} (i ↥f fzero)) ⟫ ◇ C=⟦ insertLShiftL Γ fzero σ ⟧ ◇ J⟦ T ⟧           ≡⟨ (λ 𝒊 -> ⟪ (λ i -> P2 i 𝒊) ⟫ ◇ C=⟦ insertLShiftL Γ fzero σ ⟧ ◇ J⟦ T ⟧) ⟩
           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ◇ T=⟦ p1 i ⟧ ) ⟫ ◇ C=⟦ insertLShiftL Γ fzero σ ⟧ ◇ J⟦ T ⟧

              ≡⟨ ⟪⟫-comp (λ i -> πᵢ {A = A} (fsuc i)) (λ i -> T=⟦ p1 i ⟧) |ctx| (λ ξ -> ξ ◇ C=⟦ insertLShiftL Γ fzero σ ⟧ ◇ J⟦ T ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ ⨉ (λ i -> T=⟦ p1 i ⟧) ◇ ⨉ (λ i -> T=⟦ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧) ◇ J⟦ T ⟧

              ≡⟨ asc ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ (⨉ (λ i -> T=⟦ p1 i ⟧)) (⨉ (λ i -> T=⟦ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧)) |ctx| (_◇ J⟦ T ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=⟦ p1 i ⟧) ◇ ⨉ (λ i -> T=⟦ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧)) ◇ J⟦ T ⟧

              ≡⟨ ⨉-comp (λ i -> T=⟦ p1 i ⟧) (λ i -> T=⟦ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧) |ctx| (λ ξ -> ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ ξ ◇ J⟦ T ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=⟦ p1 i ⟧ ◇ T=⟦ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧)) ◇ J⟦ T ⟧

              ≡⟨ (λ 𝒊 -> ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=comp (p1 i) (cong (_$ i) (insertLShiftL Γ fzero σ)) 𝒊)) ◇ J⟦ T ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=⟦ p1 i ∙ cong (_$ i) (insertLShiftL Γ fzero σ) ⟧)) ◇ J⟦ T ⟧

              ≡⟨ (λ 𝒊 -> ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=⟦ Ty-isSet _ _ (p1 i ∙ cong (_$ i) (insertLShiftL Γ fzero σ)) (cong (_$ i) (sym (tail= σ Γ))) 𝒊 ⟧)) ◇ J⟦ T ⟧) ⟩

           ⟪ (λ i -> πᵢ {A = A} (fsuc i) ) ⟫ ◇ (⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧)) ◇ J⟦ T ⟧

              ≡⟨ πfsuc {A = A} |ctx| (λ ξ -> ξ ◇ (⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧)) ◇ J⟦ T ⟧) ⟩

           π₁ ◇ (⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧)) ◇ J⟦ T ⟧

              ∎

  in P1



\end{code}

\begin{remark}
Here, $\AF{tail=}$ can be used since the definitional equality
$\AF{tail}\:((\AF{fzero} ↓ σ)\:Γ) \equiv \AF{tail}\:(σ ,, Γ)$ holds.
\end{remark}


\begin{lemma}[Semantics of extending a context morphism]\label{th:Iext}
  The arrow
  \[
    \begin{tikzcd}[column sep=6em]
      \CC{σ,,Γ} \ar[r, "\MM{\AF{extM}\:σ\:F}"] & \CC{σ,,Δ}
    \end{tikzcd}
  \]
  can be split into the arrows
  \[
    \begin{tikzcd}[column sep=16em]
      \CC{\AF{tail}\:(σ,,Γ)} \ar[r, "\CCeq{\AF{sym}\:(\AF{tail=}\:σ\:Γ)}\,◇\,\MM{F}\,◇\,\CCeq{\AF{tail=}\:σ\:Δ}"] & \CC{\AF{tail}\:(σ,,Δ)}
    \end{tikzcd}
  \]
  and
  \[
    \begin{tikzcd}[column sep=16em]
      \TT{σ} \ar[r, "\AF{id}"] & \TT{σ}
    \end{tikzcd}
  \]

\begin{code}
Iext :  {Γ : Ctx m} -> {Δ : Ctx n} -> (F : Γ ⇉ Δ) -> (σ : Ty)
        ->  M⟦ extM σ F ⟧
            ==
            (C=⟦ sym (tail= σ Γ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Δ ⟧) ×× id
\end{code}
\end{lemma}
\begin{proof}
This proof uses Corollary \ref{cor:IWeak0} in order to decompose arrows of type
$\CC{σ,,Γ} \to \TT{Δ\:i}$ into $π₁$ and an arrow of type ${\CC{Γ} \to \TT{Δ\:i}}$.
\end{proof}
\begin{code}[hide]
Iext {m} {n} {Γ} {Δ} F σ =
  let


      P3 : ∀(i) -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧ ◇ T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧ == T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧
      P3 i = T=comp (sym (insertLZero Γ σ (fsuc i))) (cong (_$ i) (sym (tail= σ Γ)))
             ∙ cong T=⟦_⟧ (Ty-isSet _ _ ((sym (insertLZero Γ σ (fsuc i))) ∙ cong (_$ i) (sym (tail= σ Γ))) (cong (_$ i) (sym (tail= σ Γ))))

      p0a : ∀(i) -> i == ii i
      p0a i = finEqual (⍛ i)

      p1a : ∀(i) -> Δ i == (σ ,, Δ) (fsuc i)
      p1a i = λ 𝒊 -> Δ (p0a i 𝒊)

      p1b : ∀(i) -> Δ i == (σ ,, Δ) (fsuc i)
      p1b i = cong (_$ i) (tail= σ Δ)

      X = λ ψ -> C⟦ Γ ⟧ ⇁ T⟦ ψ ⟧

      p3 : ∀ i -> cong X (p1a i) == cong X (p1b i)
      p3 i = cong (cong X) (Ty-isSet _ _ (p1a i) (p1b i))

      p2a : ∀ i -> J⟦ snd F i ⟧ =⟮ cong X (p1a i) ⟯= J⟦ snd F (ii i) ⟧
      p2a i = λ 𝒊 -> J⟦ snd F (p0a i 𝒊) ⟧

      p2b : ∀ i -> J⟦ snd F i ⟧ =⟮ cong X (p1b i) ⟯= J⟦ snd F (ii i) ⟧
      p2b i = substP (p3 i) (p2a i)

      P4 : ∀(i) -> J⟦ snd F (ii i) ⟧ == J⟦ snd F i ⟧ ◇ T=⟦ cong (_$ i) (tail= σ Δ) ⟧
      P4 i = sym (p-unit-r (cong T⟦_⟧ (p1b i)) J⟦ snd F i ⟧ J⟦ snd F (ii i) ⟧ (p2b i))

      P2 = λ(i : Fin n) ->
           J⟦ snd (extM σ F) (fsuc i) ⟧                                                 ≡⟨ refl ⟩
           J⟦ JmapC (funExt (insertLZero Γ σ)) (weak (snd F (ii i)) σ fzero) ⟧           ≡⟨ IJmapC (funExt (insertLZero Γ σ)) (weak (snd F (ii i)) σ fzero) ⟩
           C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ ◇ J⟦ (weak (snd F (ii i)) σ fzero) ⟧   ≡⟨ IWeak₀ σ (snd F (ii i)) |ctx| (C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ ◇_) ⟩
           C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ ◇ (π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ J⟦ snd F (ii i) ⟧)

            ≡⟨ sym (asc C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ (π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧) J⟦ snd F (ii i) ⟧) ⟩

            C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ ◇ (π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧) ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ sym (asc C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ π₁ C=⟦ sym (tail= σ Γ) ⟧) |ctx| (_◇ J⟦ snd F (ii i) ⟧) ⟩

            C=⟦ (sym (funExt (insertLZero Γ σ))) ⟧ ◇ π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ ⨉-π₁ (λ i -> T=⟦ (sym (insertLZero Γ σ i)) ⟧) |ctx| (λ ξ -> ξ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ J⟦ snd F (ii i) ⟧) ⟩

            π₁ ◇ ⨉ (λ i -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧) ◇ ⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧) ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ asc π₁ (⨉ (λ i -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧)) (⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧)) |ctx| (_◇ J⟦ snd F (ii i) ⟧) ⟩

            π₁ ◇ (⨉ (λ i -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧) ◇ ⨉ (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧)) ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ ⨉-comp (λ i -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧) (λ i -> T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧) |ctx| (λ ξ -> π₁ ◇ ξ ◇ J⟦ snd F (ii i) ⟧) ⟩

            π₁ ◇ ⨉ (λ i -> T=⟦ (sym (insertLZero Γ σ (fsuc i))) ⟧ ◇ T=⟦ cong (_$ i) (sym (tail= σ Γ)) ⟧) ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ (λ 𝒊 -> π₁ ◇ ⨉ (λ k -> P3 k 𝒊) ◇ J⟦ snd F (ii i) ⟧ ) ⟩

            π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ J⟦ snd F (ii i) ⟧

            ≡⟨ P4 i |ctx| (π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇_) ⟩

            π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ (J⟦ snd F i ⟧ ◇ T=⟦ cong (_$ i) (tail= σ Δ) ⟧)

            ∎



      P1 = M⟦ extM σ F ⟧                                                                             ≡⟨ refl ⟩
            ⟨ ⟪ (λ i -> J⟦ snd (extM σ F) (fsuc i) ⟧) ⟫ , J⟦ iVarType {Γ = (σ ,, Γ)} fzero ⟧ ⟩

              ≡⟨ IVarType⇓ {Γ = (σ ,, Γ)} fzero ∙ πfzero {A = λ i -> T⟦ (σ ,, Γ) i ⟧} |ctx| ⟨ ⟪ (λ i -> J⟦ snd (extM σ F) (fsuc i) ⟧) ⟫ ,_⟩ ⟩

            ⟨ ⟪ (λ i -> J⟦ snd (extM σ F) (fsuc i) ⟧) ⟫ , π₂ ⟩

              ≡⟨ (λ 𝒊 -> ⟨ ⟪ (λ i -> P2 i 𝒊) ⟫ , unit-r π₂ (~ 𝒊) ⟩ ) ⟩

            ⟨ ⟪ (λ i -> π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ (J⟦ snd F i ⟧ ◇ T=⟦ cong (_$ i) (tail= σ Δ) ⟧)) ⟫ , π₂ ◇ id ⟩

              ≡⟨ sym (comp-⟪,⟫ (π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧) (λ i -> J⟦ snd F i ⟧ ◇ T=⟦ cong (_$ i) (tail= σ Δ) ⟧)) |ctx| ⟨_, π₂ ◇ id ⟩ ⟩

            ⟨ π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ ⟪ (λ i -> J⟦ snd F i ⟧ ◇ T=⟦ cong (_$ i) (tail= σ Δ) ⟧) ⟫ , π₂ ◇ id ⟩

              ≡⟨ ⟪⟫-comp (λ i -> J⟦ snd F i ⟧) (λ i -> T=⟦ cong (_$ i) (tail= σ Δ) ⟧) |ctx| (λ ξ -> ⟨ π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ ξ , π₂ ◇ id ⟩) ⟩

            ⟨ π₁ ◇ C=⟦ sym (tail= σ Γ) ⟧ ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Δ ⟧) , π₂ ◇ id ⟩

              ≡⟨ asc π₁ C=⟦ sym (tail= σ Γ) ⟧ (M⟦ F ⟧ ◇ C=⟦ tail= σ Δ ⟧) |ctx| ⟨_, π₂ ◇ id ⟩ ⟩

            ⟨ π₁ ◇ (C=⟦ sym (tail= σ Γ) ⟧ ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Δ ⟧)) , π₂ ◇ id ⟩

              ≡⟨ sym (asc C=⟦ sym (tail= σ Γ) ⟧ M⟦ F ⟧ C=⟦ tail= σ Δ ⟧) |ctx| (λ ξ -> ⟨ π₁ ◇ ξ , π₂ ◇ id ⟩) ⟩

            ⟨ π₁ ◇ (C=⟦ sym (tail= σ Γ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Δ ⟧) , π₂ ◇ id ⟩

              ∎

  in P1

    where
      ii : Fin n -> Fin n
      ii (i ⌈ ip) = i ⌈ (pred-monotone (suc-monotone ip))

\end{code}
