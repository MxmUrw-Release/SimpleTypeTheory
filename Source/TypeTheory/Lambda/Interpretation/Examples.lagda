
\begin{code}[hide]
{-# OPTIONS --cubical  #-}

open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Interpretation.Examples where
\end{code}


\begin{code}[hide]
Const : 𝒰₀
Const = ⊤ + ℕ

ctype : Const -> Bool
ctype = either (const false) (const true)


param : LambdaParam (lsuc lzero) lzero
param = lambdaParam Bool Bool-isDisc Const ctype

M : Bool -> 𝒰₀
M false = ⊤
M true = ℕ

Mc : (a : ⊤ + ℕ) -> Lift {j = lzero} ⊤ -> M (ctype a)
Mc (left x) t = tt
Mc (right x) t = x

model : Model (lsuc lzero) lzero
model = lambdaModel param (𝐓𝐲𝐩𝐞 lzero) Type-isCCC M (Mc)
\end{code}

\begin{code}[hide]
open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction {param = param}
open import TypeTheory.Lambda.Interpretation.Interpretation {model = model}
\end{code}

\begin{code}

NF : Ty
NF = ι true ⇒ ι true

compT : [] ⊢ Λ NF (Λ NF (Λ (ι true) (V 2 $$ (V 1 $$ V 0)))) :: NF ⇒ NF ⇒ NF
compT = tt ,fir, refl

compN : (ℕ -> ℕ) -> (ℕ -> ℕ) -> ℕ -> ℕ
compN f g x = f (g x)

idT : [] ⊢ Λ (ι true) (V 0) :: NF
idT = tt ,fir, refl

idN : ℕ -> ℕ
idN x = x

-- th1 : J⟦ idT ⟧ == const idN
-- th1 = refl

-- th2 : J⟦ compT ⟧ == const compN
-- th2 = refl

\end{code}
