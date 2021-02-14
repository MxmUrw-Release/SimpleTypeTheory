
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core.TermSub {i j} {param : LambdaParam i j} where

open import TypeTheory.Lambda.Core.Type {param = param}
open import TypeTheory.Lambda.Core.Term {param = param}


open LambdaParam param

\end{code}

%----------------------------------------------------------------------
%-- Shifting of DB indices
%-- CITE: name and notation based on http://math.andrej.com/2012/11/29/how-to-implement-dependent-type-theory-iii/

%-----------------------------
%-- Weakening



\begin{code}[hide]
infixl 80 _⇈_
_⇈_ : Term -> ℕ -> Term
_⇈_ (cconst x) j  = cconst x
_⇈_ (V i) j       = V (i ↥ j)
_⇈_ (Λ X t) j    = Λ X (t ⇈ suc j)
_⇈_ (app f x) j   = app (f ⇈ j) (x ⇈ j)
\end{code}



%-----------------------------
%-- multiple substitution

Substitution is the operation of replacing variables in a term
with their respective values. First, the operation of simultaneously substituting
all variables is encoded in a type. Then, its effect on a term can be stated.

\begin{definition}
  A \textbf{simultaneous substitution of terms} is encoded as an infinite list
  of terms, mapping every possible index to a new term.
\begin{code}
TSub : 𝒰₀
TSub = ℕ -> Term
\end{code}
\end{definition}

Before continuing, we have to consider how substitution is going to work inside
of lambda abstractions. A lambda abstraction inserts a new variable at the front
of the context, which means that inside, all previous variables are accessed
using indices that are incremented by one. It follows that, in order to apply a
substitution inside of a lambda, we need to modify it to correctly handle the new
variable names.

\begin{definition}
  We call such a modification an \textbf{extended substitution}. It maps the
  newly introduced lambda variable to itself. All other variables are mapped to
  terms in the original substitution (at a decremented index), which need to be
  up-translated in order to account for the new indexing.
\begin{code}
extT : TSub -> TSub
extT δ zero     = V 0
extT δ (suc n)  = (δ n) ⇈ 0
\end{code}
\end{definition}

Now the action of a simultaneous substitution on a term can be stated.

\begin{definition}
  The \textbf{action of a simultaneous substitution $δ$ on a term $t$} is defined by
  induction on $t$. A constant remains unchanged. A variable is replaced by the
  corresponding term in $δ$. For lambda abstractions, the term inside is
  substituted using $\AF{extT}\:δ$. For applications, the substitution 
  acts on both, the function and its argument.
\begin{code}[hide]
infixl 80 _[_]
\end{code}
\begin{code}
_[_] : Term -> TSub -> Term
_[_] (cconst x)  δ = cconst x
_[_] (V i)       δ = δ i
_[_] (Λ X t)     δ = Λ X (t [ extT δ ])
_[_] (app f x)   δ = app (f [ δ ]) (x [ δ ])
\end{code}
\end{definition}


