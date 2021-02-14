
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core.TermSingSub {i j} {param : LambdaParam i j} where

open import TypeTheory.Lambda.Core.Type {param = param}
open import TypeTheory.Lambda.Core.Term {param = param}
open import TypeTheory.Lambda.Core.TermSub {param = param}


open LambdaParam param

\end{code}



%-----------------------------
%-- single substitution

Having defined simultaneous substitution, we can, as a special case of it,
define single substitution. Here, only a single variable gets replaced.

\begin{definition}
The \textbf{single substitution} of the $j$-th variable with the term $t$ is
denoted by $j\:/\:t$.

It is defined as a simultaneous substitution, where the
$j$-th variable is replaced with $t$, variables with index $i < j$ are kept
the same, and variables with index $i > j$ are down-translated, filling
in the hole left at index $j$. This is done using $\AF{↧}$, which is defined analogously
to $\AF{↥}$.
\begin{code}[hide]
infixl 60 _/_
\end{code}
\begin{code}
_/_ : ℕ -> Term -> TSub
_/_ j t i with  compare-eq i j
_/_ j t i       | equal _  = t
_/_ j t i       | noteq _  = V (i ↧ j)
\end{code}
\end{definition}
