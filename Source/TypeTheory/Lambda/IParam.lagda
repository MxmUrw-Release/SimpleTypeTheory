
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.IParam where

\end{code}


\section{Parametrization}
In order to formulate an interpretation, we need to choose a parametrization for
$\lamto$, as well as a corresponding CCC into which it can be interpreted. Such
a choice is again encoded in a parametrization.

\begin{definition}
  A parametrization of the interpretation is given by the following record:
\begin{AgdaAlign}
\begin{code}
record IParam (i j : ULevel) : 𝒰 (lsuc (lmax i j)) where
  constructor iParam
\end{code}
  It contains a parametrization of $\lamto$,
\begin{code}
  field
    param : LambdaParam i j
\end{code}
  a cartesian closed category $𝒞$,
\begin{code}
  field
    𝒞     : Category i j
    CCC   : isCCC 𝒞
\end{code}
  a function $\AF{M}$, relating ground types of $\lamto$ to objects in $𝒞$, and a function
  $\AF{Mc}$, relating constants to global sections of their respective type.
\begin{code}[hide]
  open LambdaParam param
  open Category 𝒞
  open isCCC CCC
  open hasTerminal Terminal
\end{code}
\begin{code}
  field
    M   : Gnd -> Obj
    Mc  : (c : Const) -> 𝟏 ⇁ (M (ctype (c)))
\end{code}
\end{AgdaAlign}
\end{definition}

\begin{remark}
  A global section of an object $A$ is simply a morphism $1 ⇁ A$.
\end{remark}
