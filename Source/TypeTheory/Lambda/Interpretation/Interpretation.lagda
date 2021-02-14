
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base
  renaming (_×_ to _|×|_ )
open import TypeTheory.Lambda.Param
open import TypeTheory.Lambda.IParam

module TypeTheory.Lambda.Interpretation.Interpretation {ℓ ℓ'} {iparam : IParam ℓ ℓ'} where
open IParam iparam

open import TypeTheory.Lambda.Base.CCCProofs {iparam = iparam}
open import TypeTheory.Lambda.Base.CCCid {iparam = iparam}

open Category 𝒞
open isCCC CCC
open hasTerminal Terminal
open hasProducts Products
open hasExponentials Exponentials

open LambdaParam param
open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction {param = param}

----------------------------------------------------------------------
-- Notation






⨅Comma= : ∀{n} -> (F : Fin n -> Obj) -> (X : Obj) -> ⨅ (X ,, F) == ⨅ F × X
⨅Comma= {zero} F X = refl
⨅Comma= {suc n} F X 𝒊 = ⨅ (funExt (tailComma X F) 𝒊) × X



----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
\end{code}



\section{Definition}

The interpretation is divided into four seperate functions: the interpretation of
types ($\AF{T⟦\_⟧}$), of contexts ($\AF{C⟦\_⟧}$), of typing judgements
($\AF{J⟦\_⟧}$) and of context morphisms ($\AF{M⟦\_⟧}$).

\begin{definition}
  A type of $\lamto$ is interpreted as an object of $𝒞$. For ground types,
  $\AF{M}$ is used. Function types are mapped to exponential objects.
\begin{code}
T⟦_⟧ : Ty -> Obj
T⟦_⟧ (ι x)    = M x
T⟦_⟧ (A ⇒ B)  = T⟦ B ⟧ ^ T⟦ A ⟧
\end{code}
\end{definition}

\begin{code}[hide]
T=⟦_⟧ : ∀{X Y} -> X == Y -> (T⟦ X ⟧ ⇁ T⟦ Y ⟧)
T=⟦_⟧ {X = X} p = O=⟦ cong T⟦_⟧ p ⟧

----------------------------------------------------------------------
-- Contexts
----------------------------------------------------------------------
\end{code}


\begin{definition}
  A context of $\lamto$ is interpreted as the finite product of its types (themselves interpreted first).
\begin{code}
C⟦_⟧ : ∀{n} -> Ctx n -> Obj
C⟦_⟧ Γ = ⨅ (T⟦_⟧ ∘ Γ)
\end{code}
\end{definition}

\begin{remark}
Similarly to $\OOeq{\_}$, which turns equalities of objects into arrows, we define $\TTeq{\_}$ and
$\CCeq{\_}$ for equalities of types and of contexts.
\end{remark}

\begin{code}[hide]


ctxComma= : ∀{n} -> (τ : Ty) -> (Γ : Ctx n) -> C⟦ τ ,, Γ ⟧ == C⟦ Γ ⟧ × T⟦ τ ⟧
ctxComma= τ Γ = cong ⨅ (sym (funExt (compComma T⟦_⟧ τ Γ))) ∙ ⨅Comma= (T⟦_⟧ ∘ Γ) T⟦ τ ⟧



C=⟦_⟧ : ∀{n} {Γ Δ : Ctx n} -> (Γ == Δ) -> C⟦ Γ ⟧ ⇁ C⟦ Δ ⟧
C=⟦_⟧ {Γ = Γ} p = ⨉ (λ i -> T=⟦ cong (λ Γ -> Γ i) p ⟧)


C=⟦⟧-inv : ∀{n} {Γ Δ : Ctx n} -> (p : Γ == Δ) -> C=⟦ p ⟧ ◇ C=⟦ sym p ⟧ == id
C=⟦⟧-inv {n} {Γ} {Δ} p =
  let
      P = ⨉ (λ i -> T=⟦ cong (_$ i) p ⟧) ◇ ⨉ (λ i -> T=⟦ cong (_$ i) (sym p) ⟧)      ≡⟨ ⨉-comp (λ i -> T=⟦ cong (_$ i) p ⟧) (λ i -> T=⟦ cong (_$ i) (sym p) ⟧) ⟩
          ⨉ (λ i -> T=⟦ cong (_$ i) p ⟧ ◇ T=⟦ cong (_$ i) (sym p) ⟧)                  ≡⟨ (λ 𝒊 -> ⨉ (λ i -> p-inv (λ 𝒋 -> T⟦ p 𝒋 i ⟧) 𝒊 )) ⟩
          ⨉ (λ i -> id {T⟦ Γ i ⟧})                                                   ≡⟨ ⨉-id (λ i -> T⟦ Γ i ⟧) ⟩
          id {C⟦ Γ ⟧}                                                                 ∎

  in P



----------------------------------------------------------------------
-- Judgements
----------------------------------------------------------------------




-- abstract
mapΛCtx : ∀{n r σ σ₂ ρ ψ} -> {Γ : Ctx n} -> (σ₂ ⇒ ρ == σ ⇒ ψ) -> (σ₂ ,, Γ ⊢ r :: ρ) -> (σ ,, Γ ⊢ r :: ψ)
mapΛCtx {Γ = Γ} p R =
  let p1 = cong ⇒1 p
      p2 = cong ⇒2 p
      R1 = JmapT p2 R
      R2 = JmapC (cong (_,, Γ) p1) R1
  in R2

\end{code}


\begin{definition}
  A typing judgement $Γ ⊢ t :: τ$ is interpreted as a morphism from the context
  $\CC{Γ}$ to the type $\TT{τ}$:
\begin{code}
J⟦_⟧ : ∀{t τ} -> {Γ : Ctx n} -> (Γ ⊢ t :: τ) -> C⟦ Γ ⟧ ⇁ T⟦ τ ⟧
\end{code}
\begin{enumerate}[(i)]
  \item
  A constant term $\AIC{cconst}\:c$ is interpreted using the terminal arrow $!$ and the global
  section $\AF{Mc}\:c$. Finally, since the target type of the resulting arrow must
  be $\TT{τ}$, a type correction has to be added using $\TTeq{\_}$.
  \[
  \begin{tikzcd}
    \CC{Γ} \ar[r, "!"] & 𝟏 \ar[r, "\AF{Mc}\:c"] & \AF{M}\:(\AF{ctype}\:c) \ar[r, "\TTeq{p}"] & \TT{τ}
  \end{tikzcd}
  \]
\NoIndent{
\begin{code}
J⟦_⟧ {t = cconst c} T =  let  p = cconst⇑ T
                         in   ! ◇ (Mc c) ◇ T=⟦ p ⟧
\end{code}
}

  \item
  A variable with index $i$ is interpreted by the $i$-th projection arrow $πᵢ\:i$, followed
  by a type correction.
  \[
    \begin{tikzcd}[column sep=large]
      \CC{Γ} \ar[r, "πᵢ\:i"] & \TT{Γ\:i} \ar[r, "T=⟦ Γi=τ ⟧"] & \TT{τ}
    \end{tikzcd}
  \]
\NoIndent{
\begin{code}
J⟦_⟧ {t = V x} {τ} T =  let  i , Γi=τ , _ = V⇑ T
                        in   πᵢ i ◇ T=⟦ Γi=τ ⟧
\end{code}
}

  \item
  A lambda abstraction $\AIC{Λ\:σ\:r}$ is interpreted recursively: Since its
  type has to be a function type ($ψ ⇒ ρ$), we can use $Λ⇑⇒$ to get a judgement
  $(ψ ,, Γ) ⊢ r :: ρ$. Interpreting this, we get a morphism $\CC{Γ} × \TT{ψ} ⇁
  \TT{ρ}$, which we can curry to get a morphism $\CC{Γ} ⇁ \TT{ρ} \ehat \TT{ψ}$. A
  type correction has to be added.
  \[
    \begin{tikzcd}[column sep=huge]
      \CC{Γ} \ar[r, "\CCeq{\AF{tail=}\:ψ\:Γ}"] & \CC{\AF{tail}\:(ψ ,, Γ)} \ar[r, "\AF{curry}\:\JJ{R}"] & \TT{ρ} \ehat \TT{ψ} = \TT{τ}
    \end{tikzcd}
  \]
\NoIndent{
\begin{code}
J⟦_⟧ {t = Λ σ r} {ι _}        ΛR  = ⊥-elim (Λ⇑ι ΛR)
J⟦_⟧ {t = Λ σ r} {ψ ⇒ ρ} {Γ}  ΛR  =  let  R , _ = Λ⇑⇒ ΛR
                                     in   C=⟦ tail= ψ Γ ⟧ ◇ curry J⟦ R ⟧
\end{code}
}

  \item
    An application $\AIC{app}\:t\:s$ is also interpreted recursively: The typing
    judgements for $t$ and $s$ are interpreted individually, resulting in the
    morphisms $\CC{Γ} ⇁ \TT{τ} \ehat \TT{σ}$ and $\CC{Γ} ⇁ \TT{σ}$. These are combined
    using the product of morphisms and then joined with $\AF{ev}$.
    \[
      \begin{tikzcd}[column sep=huge]
        \CC{Γ} \ar[r, "{⟨ \JJ{T}\,,\,\JJ{S} ⟩}"] & \TT{τ} \ehat {\TT{σ}} × \TT{σ} \ar[r, "\AF{ev}"] & \TT{τ}
      \end{tikzcd}
    \]
\NoIndent{
\begin{code}
J⟦_⟧ {t = app t s} {τ} TS =  let  σ , T , S = app⇑ TS
                             in   ⟨ J⟦ T ⟧ , J⟦ S ⟧ ⟩ ◇ ev
\end{code}
}
\end{enumerate}
\end{definition}

\begin{code}[hide]


J⟦_⟧tl : ∀{n A} -> {Γ : Ctx n} -> (t : Γ ⊩ A) -> C⟦ Γ ⟧ ⇁ T⟦ A ⟧
J⟦_⟧tl (t , tp) = J⟦_⟧ tp

\end{code}

\begin{definition}
  A context morphism is interpreted as a finite product over the interpretations
  of the judgements it contains.
\begin{code}
M⟦_⟧ : {Γ : Ctx m} -> {Δ : Ctx n} -> (f : Γ ⇉ Δ) -> C⟦ Γ ⟧ ⇁ C⟦ Δ ⟧
M⟦_⟧ (f , F) = ⟪ (λ i -> J⟦ F i ⟧) ⟫
\end{code}
\end{definition}

