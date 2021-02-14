\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Typing.Checker {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing.Error {param = param}




----------------------------------------------------------------------
-- type checking helpers
----------------------------------------------------------------------

infixr 20 _⇀_
_⇀_ : 𝒰₀ -> 𝒰₀ -> 𝒰₀
A ⇀ B = A -> TypeError + B

\end{code}



\noindent
During typechecking, different conditions need to be asserted. This is done in
auxilliary functions.
\begin{definition}
  The auxilliary functions for typechecking are defined as follows:
\begin{enumerate}[(i)]
\item  The function $\AF{testTypeEq}$ checks whether two given types are equal.
Here, $\AF{=stype=}$ is used to compare types with each other. It is a proof
of $\AF{isDiscrete}\:\AD{Ty}$, which itself is derived from the requirement of ground
types to be discrete.
\begin{code}
testTypeEq : Ty -> Ty -> TypeError + ⊤
testTypeEq σ τ with σ =stype= τ
...                  | yes _  = right tt
...                  | no  _  = left (ErrTypeMismatch σ τ)
\end{code}
\item The function $\AF{testFin}$ checks whether a given natural number refers
  to a valid variable. If it is valid, the corresponding index for accessing the
  context is returned, or else, an error.
\begin{code}
testFin : (n : ℕ) -> (i : ℕ) -> TypeError + Fin n
testFin n i with compare i n
...                | less (i<n)  = right (fin i i<n)
...                | equal _     = left (ErrNoSuchVariable i)
...                | greater _   = left (ErrNoSuchVariable i)
\end{code}
\item The function $\AF{testFunctionType}$ checks whether a given type is a
  function type, and if it is, returns the domain and target types, or
  else, an error.
\begin{code}
testFunctionType : Ty -> TypeError + (Ty × Ty)
testFunctionType (ι _)    = left (ErrIsNoFunction)
testFunctionType (σ ⇒ τ)  = right (σ , τ)
\end{code}
\end{enumerate}
\end{definition}



% --------------------------------------
% -- New Church type checker






\begin{definition}
  The typechecker of $\lamto$ is defined by two mutually recursive functions.
  $\AF{syn'}$ synthesizes the type of a term in a context.
  $\AF{check'}$ checks whether a term has a given type in a context. The idea for
  such an architecture is taken from \citet{Dunfield:Bidi}.
\begin{code}
syn'    : Ctx n -> Term -> TypeError + Ty
check'  : Ctx n -> Term -> Ty -> TypeError + ⊤
\end{code}
  Since our $λ$-abstractions are ``Church-style'', types can actually be fully
  synthesized. This leads to a simple checking function. It only has to check
  whether the inferred type of a term is equal to the stated type.
\begin{code}
check' Γ t τ = syn' Γ t >>= testTypeEq τ
\end{code}
  The synthesizing is done as follows:
\begin{code}
syn' {n} Γ (Λ σ t)     = syn' (σ ,, Γ) t >>= (λ τ -> right (σ ⇒ τ))
syn' {n} Γ (app t s)   =  syn' Γ t
                         >>= testFunctionType
                         >>= λ {(σ , τ) -> check' Γ s σ >> right τ}
syn' {n} Γ (V i)       = testFin n i >>= (right ∘ Γ)
syn' {n} Γ (cconst c)  = right (ι (ctype c))
\end{code}
\end{definition}

\noindent
We want to be able to use the $\AR{FIR}$ type for expressing the fact that
type checking or synthesizing succeeds. In order to do this, we define
alternative functions, taking a single tuple as argument.
\begin{code}
syn : Ctx n × Term -> TypeError + Ty
syn (Γ , t) = syn' Γ t

check : Ctx n × Term × Ty -> TypeError + ⊤
check (Γ , t , A)      = check' Γ t A
\end{code}

\begin{notation}
  We denote successful typechecking of the term $t$ with the type $τ$ in the context $Γ$
  by $Γ ⊢ t :: τ$.
\begin{code}
_⊢_::_ : (Γ : Ctx n) -> Term -> Ty -> 𝒰₀
Γ ⊢ t :: τ = FIR (Γ , t , τ) check
\end{code}
\end{notation}

\begin{code}[hide]
_⊩_ : ∀ {n} -> Ctx n -> Ty -> 𝒰₀
_⊩_ Γ τ = Σ (λ (t : Term) -> Γ ⊢ t :: τ)
\end{code}

\begin{code}[hide]
infix 60 _⊢_::_
\end{code}





