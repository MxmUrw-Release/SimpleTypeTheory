
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Introduction.Nat where

open import TypeTheory.Lambda.Base.Import
  hiding (ℕ)

\end{code}

\begin{definition}[Natural numbers]
The natural numbers $\AD{ℕ}$ are defined by induction. An element of $\AD{ℕ}$ is either $0$, or the successor of another natural number.
\begin{code}
data ℕ : 𝒰₀ where
  zero  : ℕ
  suc   : ℕ -> ℕ
\end{code}
\end{definition}

