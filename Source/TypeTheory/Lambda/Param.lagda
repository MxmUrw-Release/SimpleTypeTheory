
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base

module TypeTheory.Lambda.Param where


\end{code}


In Agda, we could define custom data types and their terms inside the type
theory. This is not possible in $\lamto$, where the basic types and terms
have to be chosen beforehand. Since this choice is arbitrary and does not affect
the underlying theory, we parametrize $\lamto$ over every possible choice.

\begin{definition}
  The simply typed $λ$-calculus is parametrized by:
  \begin{itemize}
  \setlength{\itemsep}{0pt}
  \item A type $\AFd{Gnd}$, whose elements will be the ground types. Since types
    have to be comparable, $\AFd{Gnd}$ has to be discrete.
  \item A type $\AFd{Const}$, whose elements will be the constant terms.
  \item A function $\AFd{ctype}$ mapping a constant to its type.
  \end{itemize}
  This parametrization is formalized by the following record:
\begin{code}
record LambdaParam (ℓ ℓ' : ULevel) : 𝒰 (lsuc (lmax ℓ ℓ')) where
  constructor lambdaParam
  field
    Gnd         : 𝒰₀
    Gnd-isDisc  : isDiscrete Gnd
    Const       : 𝒰₀
    ctype       : Const -> Gnd
\end{code}
\end{definition}

\noindent
The following sections all assume that such a parametrization has been given.



