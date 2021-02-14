
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Typing.CheckerSingSubProofs {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing.Error {param = param}
open import TypeTheory.Lambda.Typing.Checker {param = param}
open import TypeTheory.Lambda.Typing.CheckerProofs {param = param}
open import TypeTheory.Lambda.Typing.CheckerSubProofs {param = param}

\end{code}



\noindent
For the case of substituting the first variable, we define a corresponding
context morphism.

\begin{definition}
  For a well-typed term $T : Γ ⊢ t :: τ$, the following context morphism
  can be defined.
\begin{code}
Sub₀ : ∀{t τ} -> {Γ : Ctx m} -> (T : Γ ⊢ t :: τ) -> Γ ⇉ (τ ,, Γ)
Sub₀ {m} {t} {τ} {Γ} T = (0 / t) , proof
  where
    proof : (i : Fin (suc m)) -> Γ ⊢ (0 / t) (⍛ i) :: (τ ,, Γ) i
\end{code}
  Here, the implementation of $\AF{proof}$ uses $T$ for the case of $i = 0$,
  and the fact that $Γ ⊢ \AF{V}\:i :: Γ\:i$ for $i > 0$.
\begin{code}[hide]
    proof (zero ⌈ fnatless₁) = Jmapt (sym (/same 0 t)) T
    proof (suc ii ⌈ iip) =
      let
          i = (ii ⌈ pred-monotone iip)

          Vi : Γ ⊢ V (ii) :: Γ i
          Vi = iVarType (i)

          Vi2 = Jmapt (cong V (sym (suc↧0 ii))) Vi

          Vi3 = Jmapt (sym (/diff 0 (suc ii) (zNotS ∘ sym) t)) Vi2

      in Vi3
\end{code}
\end{definition}

