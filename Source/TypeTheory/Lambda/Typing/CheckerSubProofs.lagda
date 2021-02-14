
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Typing.CheckerSubProofs {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing.Error {param = param}
open import TypeTheory.Lambda.Typing.Checker {param = param}
open import TypeTheory.Lambda.Typing.CheckerProofs {param = param}

\end{code}


%----------------------------------------------------------------------
%-- Context morphisms
%----------------------------------------------------------------------


\medskip

Typing information can be added to substitutions. For this, we consider a
well-typed term $Δ ⊢ t :: τ$, to which a substitution $δ$ is going to be
applied. Since the variables of $t$ all have to be in $Δ$, these are the only
entries of $δ$ which we have to consider. It is now natural to add the following
requirement for $δ$: All replacements terms must have the same type as the
variable which they replace. Additionally, since the replacement terms may
contain variables themselves, they all have to be valid in the same context $Γ$.

Such a typed substitution is called a context morphism:

\begin{definition}
A \textbf{context morphism between $Γ$ and $Δ$} is a substitution $δ$, together
with a proof that for every variable in $Δ$, its replacement term has the same
type, as checked in the context $Γ$.
\begin{code}
_⇉_ : Ctx m -> Ctx n -> 𝒰₀
_⇉_ Γ Δ = Σ (λ (δ : TSub) -> Π (λ i -> Γ ⊢ δ (⍛ i) :: Δ i))
\end{code}
\end{definition}

\begin{code}[hide]

----------------------------------------------------------------------
-- Substitution
----------------------------------------------------------------------


suc↧0 : (i : ℕ) -> (suc i ↧ 0) == i
suc↧0 i with compare (suc i) 0
suc↧0 i | less x = ⊥-elim (lessGreater-⊥ x (0<suc))
suc↧0 i | equal x = ⊥-elim (zNotS (sym x))
suc↧0 i | greater x = refl

\end{code}


For the next step, we add typing information to the extension of substitutions,
giving us an extension of context morphisms.
\begin{definition}\label{def:extM}
  The \textbf{extension of context morphisms} is defined using the extension of
  substitions, as well as context weakening (Theorem \ref{th:weak}). It has the
  following type:
\begin{code}
extM :  {Γ : Ctx m} -> {Δ : Ctx n} -> (σ : Ty)
        -> (Γ ⇉ Δ)
        -> (σ ,, Γ) ⇉ (σ ,, Δ)
\end{code}
\begin{code}[hide]
extM {m} {n} {Γ} {Δ} A (δ , ps) = (extT δ) , p
  where
    p : (i : Fin (suc n)) -> (A ,, Γ) ⊢ (extT δ) (fnat i) :: (A ,, Δ) i
    p (fin zero d) = iVarType fzero
    p (fin (suc ii) d) =
          let i : Fin n
              i = (fin ii (pred-monotone d))

              p01 : Γ ⊢ δ ii :: Δ i
              p01 = ps (i)

              p02 : (A ,, Γ) ⊢ δ ii ⇈ zero :: Δ i
              p02 = JmapC (funExt (insertLZero Γ A)) (weak p01 A fzero)

          in p02
\end{code}
\end{definition}

\noindent
Now the following theorem about substition can be stated and proven:

\begin{theorem}[Substitution]\label{th:subst}
  Substituting a well typed term $Δ ⊢ t :: τ$ with a context morphism $δ : Γ ⇉
  Δ$ preserves well-typedness.
\begin{code}
_[_]⇓ : ∀{t σ}  -> {Γ : Ctx m} -> {Δ : Ctx n}
                -> Δ ⊢ t :: σ
                -> (δ : Γ ⇉ Δ)
                -> Γ ⊢ t [ fst δ ] :: σ
\end{code}
\end{theorem}
\begin{proof}
  This proof works by induction on the term $t$. For the case of a lambda term,
  it recursively calls itself with an extended $δ$ (as in Definition \ref{def:extM}),
  in order to accomodate for the newly introduced variable.
\end{proof}
\begin{code}[hide]
_[_]⇓ {m} {n} {cconst x} {A} {Γ} {Δ} p δ = cconst⇓ (cconst⇑ p)
_[_]⇓ {m} {n} {V j}      {τ} {Γ} {Δ} T (f , F) =
  let
      p01 : Σ $ λ i -> (Δ i == τ) × (fnat i == j)
      p01 = (V⇑ T)

      i , Δi=τ , i=j = p01

      Fi : Γ ⊢ f (fnat i) :: Δ i
      Fi = F i

      p05 : Γ ⊢ f (fnat i) :: τ
      p05 = JmapT Δi=τ Fi

      p06 : Γ ⊢ f j :: τ
      p06 = Jmapt (cong f i=j) p05

  in p06
_[_]⇓ {m} {n} {Λ τ r} {ι x} {Γ} {Δ} T (f , F) = ⊥-elim (lambdaNoFunc T)
_[_]⇓ {m} {n} {Λ σ₂ t} {σ ⇒ ψ} {Γ} {Δ} ΛT (f , F) =
  let
      T , σ=σ₂ = addVarLambda ΛT
      T[F] = T [ extM σ (f , F) ]⇓
      ΛT[F] = Λ⇓ T[F]
      ΛT[F]₂ = Jmapt (cong (λ ξ -> Λ ξ (t [ extT f ])) σ=σ₂) ΛT[F]

  in ΛT[F]₂

_[_]⇓ {m} {n} {app t s} {τ} {Γ} {Δ} TS (F) =
  let
      p01 : Σ $ λ σ -> (Δ ⊢ t :: σ ⇒ τ) × (Δ ⊢ s :: σ)
      p01 = app⇑ TS

      σ , T , S = p01

      T[F] : Γ ⊢ t [ fst F ] :: σ ⇒ τ
      T[F] = T [ F ]⇓

      S[F] : Γ ⊢ s [ fst F ] :: σ
      S[F] = S [ F ]⇓

  in app⇓ T[F] S[F]


_[_]⇓tl : ∀{m n A} -> {Γ : Ctx m} -> {Δ : Ctx n}
      -> Δ ⊩ A -> (δ : Γ ⇉ Δ) -> Γ ⊩ A
_[_]⇓tl (t , T) F = t [ fst F ] , T [ F ]⇓

\end{code}




