\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base
  renaming (_×_ to _|×|_ )
open import TypeTheory.Lambda.Param
open import TypeTheory.Lambda.IParam

module TypeTheory.Lambda.Interpretation.InterpretationProofsBeta {ℓ ℓ'} {iparam : IParam ℓ ℓ'} where
open IParam iparam

open import TypeTheory.Lambda.Base.CCCProofs {iparam = iparam}
open import TypeTheory.Lambda.Base.CCCid {iparam = iparam}
open import TypeTheory.Lambda.Interpretation.Interpretation {iparam = iparam}
open import TypeTheory.Lambda.Interpretation.InterpretationProofsWeak {iparam = iparam}

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
\begin{theorem}[Semantics of substitution]\label{th:ISub}
  The interpretation of a substitution $T\:[\:F\:]⇓$ is a composition
  of the interpretations of the context morphism $F$ and the judgement $T$.
  \[
  \begin{tikzcd}[column sep=huge, row sep=huge]
    \CC{Δ} \ar[r, "\MM{F}"] \ar[rd, swap, "\JJ{T\,[\,F\,]⇓}"] & \CC{Γ} \ar[d, "\JJ{T}"] \\
    & \TT{τ}
  \end{tikzcd}
  \]
\begin{code}
ISub : ∀{t τ}  -> {Γ : Ctx m} -> {Δ : Ctx n}
               -> (T : Γ ⊢ t :: τ)
               -> (F : Δ ⇉ Γ)
               -> J⟦ T [ F ]⇓ ⟧ == M⟦ F ⟧ ◇ J⟦ T ⟧
\end{code}
\end{theorem}
\begin{proof}
  Similar to the proof of Theorem \ref{th:subst}, this proof uses Lemma \ref{th:Iext} for the case of $t$ being a lambda term.
\end{proof}
\begin{code}[hide]
ISub {m} {n} {cconst c} {τ} {Γ} {Δ} T F =
  let
      p = cconst⇑ T
      p2 = cconst⇑ {Γ = Δ} (T [ F ]⇓)

      P1 : ! == M⟦ F ⟧ ◇ !
      P1 = !-uprop

      P2 : T=⟦ p2 ⟧ == T=⟦ p ⟧
      P2 = cong T=⟦_⟧ (Ty-isSet (ι (ctype c)) τ p2 p)

      P3 : ! ◇ Mc c ◇ T=⟦ p2 ⟧ == M⟦ F ⟧ ◇ !! ◇ Mc c ◇ T=⟦ p ⟧
      P3 𝒊 = P1 𝒊 ◇ Mc c ◇ P2 𝒊

      P4 = (M⟦ F ⟧ ◇ ! ◇ Mc c ◇ T=⟦ p ⟧)           ≡⟨ asc (M⟦ F ⟧ ◇ !) (Mc c) T=⟦ p ⟧ ⟩
           (M⟦ F ⟧ ◇ !) ◇ (Mc c ◇ T=⟦ p ⟧)         ≡⟨ asc M⟦ F ⟧ ! (Mc c ◇ T=⟦ p ⟧) ⟩
           M⟦ F ⟧ ◇ (! ◇ (Mc c ◇ T=⟦ p ⟧))         ≡⟨ sym (asc ! (Mc c) (T=⟦ p ⟧)) |ctx| (M⟦ F ⟧ ◇_) ⟩
           M⟦ F ⟧ ◇ ((! ◇ Mc c) ◇ T=⟦ p ⟧)         ∎

  in P3 ∙ P4

ISub {m} {n} {V j} {τ} {Γ} {Δ} T (f , F) =
  let
      i , Δi=τ , i=j = V⇑ T

      P : J⟦ Jmapt (cong f i=j) (JmapT Δi=τ (F i)) ⟧ == M⟦ (f , F) ⟧ ◇ (πᵢ i ◇ T=⟦ Δi=τ ⟧)

      P = J⟦ Jmapt (cong f i=j) (JmapT Δi=τ (F i)) ⟧        ≡⟨ Imapt= (cong f i=j) (JmapT Δi=τ (F i)) ⟩
          J⟦ JmapT Δi=τ (F i) ⟧                             ≡⟨ sym (p-unit-r (cong T⟦_⟧ Δi=τ) J⟦ F i ⟧ J⟦ JmapT Δi=τ (F i) ⟧ (λ 𝒊 -> J⟦ JmapT= (F i) (JmapT Δi=τ (F i)) Δi=τ 𝒊 ⟧ )) ⟩
          J⟦ F i ⟧ ◇ T=⟦ Δi=τ ⟧                             ≡⟨ sym (⟪,⟫-prop (λ j -> J⟦ F j ⟧) i) |ctx| (_◇ T=⟦ Δi=τ ⟧) ⟩
          ⟪ (λ j -> J⟦ F j ⟧) ⟫ ◇ πᵢ i ◇ T=⟦ Δi=τ ⟧        ≡⟨ asc ⟪ (λ j -> J⟦ F j ⟧) ⟫ (πᵢ i) (T=⟦ Δi=τ ⟧) ⟩
          ⟪ (λ j -> J⟦ F j ⟧) ⟫ ◇ (πᵢ i ◇ T=⟦ Δi=τ ⟧)      ∎

  in P

ISub {m} {n} {Λ σ t} {ι x} {Γ} {Δ} T F = ⊥-elim (lambdaNoFunc T)
ISub {m} {n} {Λ σ₂ t} {σ ⇒ ψ} {Γ} {Δ} ΛT F =
  let
      T , σ=σ₂ = addVarLambda ΛT

      P = J⟦ Jmapt (cong (λ ξ -> Λ ξ (t [ extT (fst F) ])) σ=σ₂) (Λ⇓ (T [ extM σ F ]⇓)) ⟧

                  ≡⟨ Imapt= ((cong (λ ξ -> Λ ξ (t [ extT (fst F) ])) σ=σ₂)) (Λ⇓ (T [ extM σ F ]⇓)) ⟩

          J⟦ (Λ⇓ (T [ extM σ F ]⇓)) ⟧                               ≡⟨ IΛ⇓ (T [ extM σ F ]⇓) ⟩
          C=⟦ tail= σ Δ ⟧ ◇ curry J⟦ (T [ extM σ F ]⇓) ⟧           ≡⟨ ISub T (extM σ F) |ctx| (λ ξ -> C=⟦ tail= σ Δ ⟧ ◇ curry ξ) ⟩
          C=⟦ tail= σ Δ ⟧ ◇ curry (M⟦ extM σ F ⟧ ◇ J⟦ T ⟧)           ≡⟨ Iext F σ |ctx| (λ ξ -> C=⟦ tail= σ Δ ⟧ ◇ curry (ξ ◇ J⟦ T ⟧)) ⟩

          C=⟦ tail= σ Δ ⟧ ◇ curry (((C=⟦ sym (tail= σ Δ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ×× id) ◇ J⟦ T ⟧)

                  ≡⟨ curry-comp (C=⟦ sym (tail= σ Δ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) J⟦ T ⟧ |ctx| (C=⟦ tail= σ Δ ⟧ ◇_) ⟩

          C=⟦ tail= σ Δ ⟧ ◇ ((C=⟦ sym (tail= σ Δ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧)

                  ≡⟨ sym (asc C=⟦ tail= σ Δ ⟧ (C=⟦ sym (tail= σ Δ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) (curry J⟦ T ⟧)) ⟩

          C=⟦ tail= σ Δ ⟧ ◇ (C=⟦ sym (tail= σ Δ) ⟧ ◇ M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧

                  ≡⟨ asc C=⟦ sym (tail= σ Δ) ⟧ M⟦ F ⟧ C=⟦ tail= σ Γ ⟧ |ctx| (λ ξ -> C=⟦ tail= σ Δ ⟧ ◇ ξ ◇ curry J⟦ T ⟧) ⟩

          C=⟦ tail= σ Δ ⟧ ◇ (C=⟦ sym (tail= σ Δ) ⟧ ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧)) ◇ curry J⟦ T ⟧

                  ≡⟨ sym (asc C=⟦ tail= σ Δ ⟧ C=⟦ sym (tail= σ Δ) ⟧ (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧)) |ctx| (_◇ curry J⟦ T ⟧) ⟩

          C=⟦ tail= σ Δ ⟧ ◇ C=⟦ sym (tail= σ Δ) ⟧ ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧

                  ≡⟨ C=⟦⟧-inv (tail= σ Δ) |ctx| (λ ξ -> ξ ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧) ⟩

          id ◇ (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧

                  ≡⟨ unit-l (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) |ctx| (_◇ curry J⟦ T ⟧) ⟩

          (M⟦ F ⟧ ◇ C=⟦ tail= σ Γ ⟧) ◇ curry J⟦ T ⟧

                  ≡⟨ asc M⟦ F ⟧ C=⟦ tail= σ Γ ⟧ (curry J⟦ T ⟧) ⟩

          M⟦ F ⟧ ◇ (C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ T ⟧)

                  ∎
  in P
ISub {m} {n} {app t s} {τ} {Γ} {Δ} TS F =
  let
      σ , T , S = app⇑ TS

      T[F] = T [ F ]⇓
      S[F] = S [ F ]⇓

      P = J⟦ app⇓ T[F] S[F] ⟧                        ≡⟨ Iapp⇓ T[F] S[F] ⟩
          ⟨ J⟦ T[F] ⟧ , J⟦ S[F] ⟧ ⟩ ◇ ev              ≡⟨ ISub T F |ctx| (λ ξ -> ⟨ ξ , J⟦ S[F] ⟧ ⟩ ◇ ev) ⟩
          ⟨ M⟦ F ⟧ ◇ J⟦ T ⟧ , J⟦ S[F] ⟧ ⟩ ◇ ev        ≡⟨ ISub S F |ctx| (λ ξ -> ⟨ M⟦ F ⟧ ◇ J⟦ T ⟧ , ξ ⟩ ◇ ev) ⟩
          ⟨ M⟦ F ⟧ ◇ J⟦ T ⟧ , M⟦ F ⟧ ◇ J⟦ S ⟧ ⟩ ◇ ev  ≡⟨ sym (comp-⟨,⟩ M⟦ F ⟧ J⟦ T ⟧ J⟦ S ⟧) |ctx| (_◇ ev) ⟩
          M⟦ F ⟧ ◇ ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev           ≡⟨ asc M⟦ F ⟧ ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ev ⟩
          M⟦ F ⟧ ◇ (⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev)         ∎

  in P

\end{code}


%----------------------------------------------------------------------
\section{Soundness}
%----------------------------------------------------------------------
The interpretation of $\lamto$ terms into categories should be compatible
with the internal notion of $β$-equality: Terms which are considered
equal should have the same interpretation. Such a property is called
soundness.

$β$-equality is based on reduction, therefore the main challenge is to prove
that a single reduction step does not change the interpretation of a term.


\begin{code}[hide]

mapCtxArr=d : ∀{n t τ υ} -> {Γ : Ctx n} -> {T : Γ ⊢ t :: τ} -> {U : Γ ⊢ t :: υ} -> (p : τ == υ)
              -> PathP (λ i -> Γ ⊢ t :: p i) T U -> PathP (λ i -> C⟦ Γ ⟧ ⇁ T⟦ p i ⟧) J⟦ T ⟧ J⟦ U ⟧
mapCtxArr=d p P i = J⟦ P i ⟧

trans-d : ∀{ℓ ℓ'} {A : 𝒰 ℓ} {B : A -> 𝒰 ℓ'} {x y : A} -> {u v : B x} -> {w : B y} -> (L : PathP (λ _ -> B x) u v) -> (p : x == y) -> PathP (λ i -> B (p i)) v w -> PathP (λ i -> B (p i)) u w
trans-d {B = B} {v = v} L p R i = primComp (λ j -> B (p (i ∧ j))) _
                        (λ { j (i = i0) -> L (~ j)
                           ; j (i = i1) -> R j})
                        (v)

Jntl : ∀{n τ} -> {Γ : Ctx n} -> (T : Γ ⊩ τ) -> J⟦ T ⟧tl == J⟦ snd T ⟧
Jntl _ = refl


B : ∀{n} -> (Γ : Ctx n) -> Ty -> 𝒰 ℓ'
B {n} (Γ) x = C⟦ Γ ⟧ ⇁ T⟦ x ⟧

JApp= : ∀{n w r s τ ψ ξ} -> {Γ : Ctx n} -> (ψ=ξ : ψ == ξ)
        -> (W₁ : Γ ⊢ w :: ψ ⇒ τ) -> (W₂ : Γ ⊢ w :: ξ ⇒ τ)
        -> (R : Γ ⊢ r :: ψ) -> (S₂ : Γ ⊢ s :: ξ)
        -> (P1 : PathP (λ i -> B Γ (ψ=ξ i ⇒ τ)) J⟦ W₁ ⟧ J⟦ W₂ ⟧)
        -> (P2 : PathP (λ i -> B Γ (ψ=ξ i)) J⟦ R ⟧ J⟦ S₂ ⟧)
        -> ⟨ J⟦ W₁ ⟧ , J⟦ R ⟧ ⟩ ◇ ev == ⟨ J⟦ W₂ ⟧ , J⟦ S₂ ⟧ ⟩ ◇ ev
JApp= _ _ _ _ _ P1 P2 i = ⟨ P1 i , P2 i ⟩ ◇ ev



SingleStepTl : ∀{n u τ} -> {Γ : Ctx n} ->  (T : Γ ⊩ τ) -> (w : fst T ↦ u) -> J⟦ T ⟧tl == J⟦ JStep-tl T w ⟧tl

\end{code}

\begin{theorem}
  The interpretation of a well typed term does not change after a single
  reduction step.
\begin{code}
SingleStep : ∀{t u τ}  -> {Γ : Ctx n}
                       -> (w : t ↦ u)
                       -> (T : Γ ⊢ t :: τ)
                       -> J⟦ T ⟧ == J⟦ JStep w T ⟧
\end{code}
\end{theorem}
\begin{proof}
The proof works by induction on the definition of a single reduction step.
The most interesting case is that of $\AIC{rbeta}$, it involves substition
of the first variable. In order to prove it, we have to use the properties
described in Lemma \ref{lem:ISub0} and Theorem \ref{th:ISub}.
\end{proof}

\begin{code}[hide]
SingleStep {n} {t} {u} (w) T = SingleStepTl (t , T) w



-- We have this abstract, for else the checker gets confused by the normalized term
abstract
  fstTy= : ∀{a b c d} -> a ⇒ b == c ⇒ d -> a == c
  fstTy= p = cong ⇒1 p

AppT : ∀{n} -> (Γ : Ctx n) -> (r s : Term) -> (τ : Ty) -> 𝒰₀
AppT Γ r s τ = Σ (λ σ -> (Γ ⊢ r :: σ ⇒ τ) |×| (Γ ⊢ s :: σ))


abstract
  breakApp : ∀{n t r s τ} -> {Γ : Ctx n} -> (T : Γ ⊢ t :: τ) -> (t == app r s) -> Σ (λ (σRS : AppT Γ r s τ) -> J⟦ T ⟧ == ⟨ J⟦ fst (snd σRS) ⟧ , (J⟦ snd (snd σRS) ⟧) ⟩ ◇ ev)
  breakApp {n} {t} {r} {s} {τ} {Γ} T t=rs =
    let
        RS = Jmapt t=rs T
        σ , R , S = app⇑ (RS)

        P1 : J⟦ T ⟧ == ⟨ J⟦ R ⟧ , (J⟦ S ⟧) ⟩ ◇ ev
        P1 𝒊 = J⟦ Jmapt= T RS t=rs 𝒊 ⟧

    in (σ , R , S) , P1




SingleStepTl {n} {τ = ψ} {Γ} T (rbeta {σ₂} {r} {s} {t} {u} t=Λrs u=r[0/s]) =
  let
      -- -- left side judgements
      (σ , ΛR , S) , PZ0 = breakApp (snd T) t=Λrs
      R , _ = addVarLambda ΛR


      -- right side judgements
      U = JStep-tl T (rbeta t=Λrs u=r[0/s])
      R[0/S] = Jmapt-tl U u=r[0/s]


      R[Sub₀S] : Γ ⊩ ψ
      R[Sub₀S] = r [ 0 / s ] , R [ Sub₀ S ]⇓

      -- Proof chain
      P1 : J⟦ R [ Sub₀ S ]⇓ ⟧ == M⟦ Sub₀ S ⟧ ◇ J⟦ R ⟧
      P1 = ISub R (Sub₀ S)

      P2 : M⟦ Sub₀ S ⟧ ◇ J⟦ R ⟧ == ⟨ C=⟦ tail= σ Γ ⟧ , J⟦ S ⟧ ⟩ ◇ ((curry J⟦ R ⟧ ×× id) ◇ ev)
      P2 𝒊 = ISub₀ S 𝒊 ◇ sym (curry-prop J⟦ R ⟧) 𝒊

      P3 =
          ⟨ C=⟦ tail= σ Γ ⟧ , J⟦ S ⟧ ⟩ ◇ ((curry J⟦ R ⟧ ×× id) ◇ ev)
                                                                          ≡⟨ sym (asc ⟨ C=⟦ tail= σ Γ ⟧ , J⟦ S ⟧ ⟩ (curry J⟦ R ⟧ ×× id) ev) ⟩
          ⟨ C=⟦ tail= σ Γ ⟧ , J⟦ S ⟧ ⟩ ◇ (curry J⟦ R ⟧ ×× id) ◇ ev
                                                                          ≡⟨ ⟨,⟩-comp C=⟦ tail= σ Γ ⟧ J⟦ S ⟧ (curry J⟦ R ⟧) id |ctx| (_◇ ev) ⟩
          ⟨ C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ R ⟧ , J⟦ S ⟧ ◇ id ⟩ ◇ ev
                                                                          ≡⟨ unit-r J⟦ S ⟧ |ctx| (λ ξ -> ⟨ C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ R ⟧ , ξ ⟩ ◇ ev) ⟩
          ⟨ C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ R ⟧ , J⟦ S ⟧ ⟩ ◇ ev
                                                                          ∎

      P4 : J⟦ U ⟧tl == J⟦ R[Sub₀S] ⟧tl
      P4 = cong J⟦_⟧tl (Jmapt=tl (U) R[Sub₀S] u=r[0/s])

      P7 : J⟦ T ⟧tl == ⟨ C=⟦ tail= σ Γ ⟧ ◇ curry J⟦ R ⟧ , J⟦ S ⟧ ⟩ ◇ ev
      P7 = PZ0


      Q1 : J⟦ T ⟧tl == J⟦ JStep-tl T (rbeta t=Λrs u=r[0/s]) ⟧tl
      Q1 = P7 ∙ (sym P3) ∙ (sym P2) ∙ (sym P1) ∙ sym (Jntl R[Sub₀S]) ∙ (sym P4)

  in Q1
SingleStepTl {n} {.(Λ _ _)} {ι X} {Γ} (_ , ΛR) (rlam {τ} {r} {s} r↦s) = ⊥-elim (lambdaNoFunc ΛR)
SingleStepTl {n} {.(Λ _ _)} {ψ ⇒ ξ} {Γ} (_ , ΛR) (rlam {τ} {r} {s} r↦s) =
  let

      R , ψ=τ = addVarLambda ΛR

      S₁ = JStep r↦s R

      ΛS = JStep (rlam r↦s) ΛR

      S₂ , ψ=τ₂ = addVarLambda ΛS


      P1 : J⟦ R ⟧ == J⟦ S₁ ⟧
      P1 = SingleStep r↦s R

      P2 : J⟦ S₁ ⟧ == J⟦ S₂ ⟧
      P2 i = J⟦ JmapT= S₁ S₂ refl i ⟧

      P4 :(curry J⟦ R ⟧) == (curry J⟦ S₂ ⟧)
      P4 i = curry ((P1 ∙ P2) i)


      P7 : J⟦ ΛR ⟧ == J⟦ ΛS ⟧
      P7 i = C=⟦ tail= τ Γ ⟧ ◇ P4 i

  in P7


SingleStepTl {n} {u} {τ} {Γ} T (rapp1 {r} {s} {t} {u} {v = w} r↦s t=rw u=sw) =
  let

      RW : Γ ⊩ τ
      RW = Jmapt-tl T t=rw
      ψ , R , W₁ = app⇑ (snd RW)

      S = JStep r↦s R

      U  = JStep-tl T (rapp1 r↦s t=rw u=sw)
      SW = Jmapt-tl U u=sw
      ξ , S₂ , W₂ = app⇑ (snd SW)

      ψ=ξ : ψ == ξ
      ψ=ξ = uniqueT W₁ W₂


      ψτ=ξτ : ψ ⇒ τ == ξ ⇒ τ
      ψτ=ξτ = cong (_⇒ τ) ψ=ξ

      P1 : J⟦ T ⟧tl == J⟦ RW ⟧tl
      P1 = cong J⟦_⟧tl (Jmapt=tl T RW t=rw)


      P4 : J⟦ R ⟧ == J⟦ S ⟧
      P4 = SingleStep r↦s R

      P5 : PathP (λ i -> Γ ⊢ s :: ψτ=ξτ i) S S₂
      P5 = JmapT= S S₂ (ψτ=ξτ)

      P6 : PathP (λ i -> C⟦ Γ ⟧ ⇁ T⟦ ψτ=ξτ i ⟧) J⟦ S ⟧ J⟦ S₂ ⟧
      P6 i = J⟦ P5 i ⟧

      B : Ty -> 𝒰 ℓ'
      B x = C⟦ Γ ⟧ ⇁ T⟦ x ⟧

      P7 : PathP (λ i -> B (ψτ=ξτ i)) J⟦ R ⟧ J⟦ S₂ ⟧
      P7 = trans-d {B = B} P4 ψτ=ξτ P6

      P8 : PathP (λ i -> B (ψ=ξ i)) J⟦ W₁ ⟧ J⟦ W₂ ⟧
      P8 i = J⟦ JmapT= W₁ W₂ ψ=ξ i ⟧

      Q1 : J⟦ U ⟧tl == J⟦ SW ⟧tl
      Q1 = cong J⟦_⟧tl (Jmapt=tl U SW u=sw)

      Q2 : J⟦ snd RW ⟧ == J⟦ snd SW ⟧
      Q2 i = ⟨ P7 i , P8 i ⟩ ◇ ev


      Q3 = P1 ∙ Jntl RW ∙ Q2 ∙ sym (Jntl SW) ∙ sym Q1

  in Q3

SingleStepTl {n} {u} {τ} {Γ} T (rapp2 {r} {s} {t} {u} {w} r↦s t=wr u=ws) =
  let
      WR : Γ ⊩ τ
      WR = Jmapt-tl T t=wr
      ψ , W₁ , R = app⇑ (snd WR)

      S = JStep r↦s R

      U  = JStep-tl T (rapp2 r↦s t=wr u=ws)
      WS = Jmapt-tl U u=ws
      ξ , W₂ , S₂ = app⇑ (snd WS)

      p00 : ψ ⇒ τ == ξ ⇒ τ
      p00 = uniqueT W₁ W₂

      ψ=ξ : ψ == ξ
      ψ=ξ = cong (⇒1) p00

      ψτ=ξτ : ψ ⇒ τ == ξ ⇒ τ
      ψτ=ξτ = cong (_⇒ τ) ψ=ξ

      P1 : J⟦ T ⟧tl == J⟦ WR ⟧tl
      P1 = cong J⟦_⟧tl (Jmapt=tl T WR t=wr)


      P4 : J⟦ R ⟧ == J⟦ S ⟧
      P4 = SingleStep r↦s R


      P6 : PathP (λ i -> C⟦ Γ ⟧ ⇁ T⟦ ψ=ξ i ⟧) J⟦ S ⟧ J⟦ S₂ ⟧
      P6 i = J⟦ JmapT= S S₂ ψ=ξ i ⟧


      P7 : PathP (λ i -> B Γ (ψ=ξ i)) J⟦ R ⟧ J⟦ S₂ ⟧
      P7 = trans-d {B = B Γ} P4 ψ=ξ P6

      P8 : PathP (λ i -> B Γ (ψτ=ξτ i)) J⟦ W₁ ⟧ J⟦ W₂ ⟧
      P8 i = J⟦ JmapT= W₁ W₂ ψτ=ξτ i ⟧

      Q1 : J⟦ U ⟧tl == J⟦ WS ⟧tl
      Q1 = cong J⟦_⟧tl (Jmapt=tl U WS u=ws)


      Q2 : J⟦ snd WR ⟧ == J⟦ snd WS ⟧
      Q2 i = ⟨ P8 i , P7 i ⟩ ◇ ev

      Q3 = P1 ∙ Jntl WR ∙ Q2 ∙ sym (Jntl WS) ∙ sym Q1

  in Q3



\end{code}

By combining multiple steps, and then applying the resulting proof to the case of
normalization, the following two corollaries are obtained.

\begin{corollary}
  The interpretation of a well typed term does not change after multiple
  reduction steps.
\begin{code}
MultiStep : ∀{t u τ}  -> {Γ : Ctx n}
                      -> (w : t ↦* u)
                      -> (T : Γ ⊢ t :: τ) -> (U : Γ ⊢ u :: τ)
                      -> J⟦ T ⟧ == J⟦ U ⟧
\end{code}
\end{corollary}
\begin{code}[hide]
MultiStep {n} {t} {.t} rid T U = cong J⟦_⟧ (Jmapt= T U refl)
MultiStep {n} {t} {u} (x ∙∘ w) T U = SingleStep x T ∙ MultiStep w (JStep x T) U
\end{code}


\begin{corollary}\label{cor:norsound}
  The interpretation of a term and of its normal form are the same.
\begin{code}
norsound : ∀{t τ}  -> {Γ : Ctx n}
                   -> (T : Γ ⊢ t :: τ)
                   -> J⟦ T ⟧ == J⟦ nor⇓ T ⟧
\end{code}
\end{corollary}
\begin{code}[hide]
norsound {n} {t} {A} {Γ} T =
  let
      u , W , U = nf T

  in MultiStep W T (nfj↑ U)
\end{code}
\noindent
Finally, this can be used to show soundness.

\begin{corollary}[Soundness]
  The interpretation is sound with respect to $β$-equality.
\begin{code}
sound : ∀{t u τ}  -> {Γ : Ctx n}
                  -> (T : Γ ⊢ t :: τ) -> (U : Γ ⊢ u :: τ)
                  -> (T =β= U)
                  -> J⟦ T ⟧ == J⟦ U ⟧
\end{code}
\end{corollary}
\begin{proof}
Since the normal forms $\AF{nor⇓}\:T$ and $\AF{nor⇓}\:U$ are equal,
so are their interpretations:
\[
\JJ{\AF{nor⇓}\:T} = \JJ{\AF{nor⇓}\:U}
\]
By applying Corollary \ref{cor:norsound} to both sides, this means that
the interpretations of the original terms have to be equal as well:
\[
\JJ{T} = \JJ{U}\qedhere
\]
\end{proof}

\begin{code}[hide]
sound T U p =
  let
    p01 : J⟦ nor⇓ T ⟧ == J⟦ nor⇓ U ⟧
    p01 = λ 𝒊 -> J⟦ nor= T U p 𝒊 ⟧

  in norsound T ∙ p01 ∙ (sym (norsound U))
\end{code}
