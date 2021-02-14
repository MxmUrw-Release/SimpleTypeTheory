
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core.Term {i j} {param : LambdaParam i j} where

open import TypeTheory.Lambda.Core.Type {param = param}

open LambdaParam param


\end{code}
Just like types, terms are defined as an inductive data type.
Consequently, $\lamto$ programs can be constructed directly in Agda by
constructing an element of this type.

\begin{definition}
  The terms of $\lamto$ are defined as follows:
\begin{code}
data Term : 𝒰₀ where
  cconst  : Const -> Term
  V       : ℕ -> Term
  Λ       : Ty -> Term -> Term
  app     : Term -> Term -> Term
\end{code}
\end{definition}

\begin{notation}
  The relation of a term $t$ being well-typed and having the type $τ$ in the context $Γ$ is written as:
  \[
    Γ ⊢ t :: τ
  \]
  In order to distinguish this typing relation from Agda's own types, we use a
  double colon instead of a single one.
\end{notation}

We now discuss the different constructors of terms together with their typing rules.
\subsection*{Constants}
The constant terms and their types depend on the parametrization of $\lamto$.
A constant term can be constructed with an element of $\AFd{Const}$, its
type is determined by $\AF{ctype}$. As such, the type does not depend at all
on the context in which the term appears. We write, for a context $Γ : \AF{Ctx}\:n$:
\begin{prooftree*}
  \infer0{Γ ⊢ \AF{cconst}\:c :: \AF{ι}\:(\AF{ctype}\:c)}
\end{prooftree*}
\begin{remark}
  This presents a derivation rule, describing how the typing relation $\_⊢\_::\_$
  should behave. From the hypothesis (above the line), the conclusion (below the line)
  can be derived. For simplicity, we do not include the conditition
  of elements having a certain type when it can be inferred from their usage. For
  example, here, $c$ should be of type $\AD{Const}$.
\end{remark}

\subsection*{Variables}
Variables are not represented by names, but by natural numbers, so called
de Brujin indices. These are not arbitrary, but depend on the location where the
variable was introduced. This way, we skip the notion of $α$-equivalence of
terms, which else would be needed in order to group terms that use different
variable names but are otherwise equal into equivalence classes. Using
de Brujin indices, such an equivalence class collapses to a unique representation.

A context is a list of variables currently in scope, represented by their
type. A variable term can be constructed with $\AIC{V} : ℕ \to \AD{Term}$,
by specifying the index in the context which we want to access.

A variable term can contain any natural number, but it is only well-typed if
there actually is such a variable in the context. We write, for a context $Γ : \AF{Ctx}\:n$:

\begin{prooftree*}
  \hypo{i < n}
  \infer1{Γ ⊢ \AIC{V}\:i :: Γ_i}
\end{prooftree*}

\subsection*{Abstraction}
Lambda abstraction introduces a new variable into the context, which then can be used
by the term inside. Outside of the lambda, this corresponds to a function
taking such an argument.

Our version of $\lamto$ is ``Church-style''. This means that, when creating a
lambda abstraction, the type of the newly introduced variable has to be
explicitly stated, as opposed to ``Curry-style'', where it can be inferred by the
typechecker instead. But this would mean additional complexity in the typechecker, which we choose to avoid,
accepting the cost of slightly more verbose programs.

So, in order to construct such a lambda-abstraction-term, the constructor $\AIC{Λ} :
\AD{Ty} \to \AD{Term} \to \AD{Term}$ has to be given the type of the new variable and the
term for the function body. Here we use an uppercase $Λ$, because the lowercase version
is already taken by Agda's own lambda abstraction.

For a context $Γ : \AF{Ctx}\:n$, the typing rule is given by:
\begin{prooftree*}
  \hypo{(σ ,, Γ) ⊢ t :: τ}
  \infer1{Γ ⊢ Λ_σ\:t :: (σ ⇒ τ)}
\end{prooftree*}

\begin{remark}
  The new variable is inserted at the beginning of the context. This means that
  the indices of all previously existing variables get incremented. As a result,
  the index by which a variable has to be accessed depends on the location where
  it is accessed from.
\end{remark}

\subsection*{Application}
The constructor for function application is $\AIC{app} : \AD{Term} \to \AD{Term}
\to \AD{Term}$. It has to be given the term of the function and the term of the
argument. Such an application is well-typed if the type of the argument matches
the domain type of the function.

For a context $Γ : \AF{Ctx}\:n$, the typing rule is given by:
\begin{prooftree*}
  \hypo{Γ ⊢ t :: (σ ⇒ τ)}
  \hypo{Γ ⊢ s :: σ}
  \infer2{Γ ⊢ \AIC{app}\:t\:s :: τ}
\end{prooftree*}



\begin{code}[hide]
infixl 60 _$$_
_$$_ = app
\end{code}




