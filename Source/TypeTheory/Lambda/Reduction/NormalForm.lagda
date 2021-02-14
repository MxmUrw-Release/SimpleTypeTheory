
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param



module TypeTheory.Lambda.Reduction.NormalForm {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction.Beta {param = param}


----------------------------------------------------------------------
-- Normal form
----------------------------------------------------------------------
-- CITE: Normalization for the Simply-Typed Lambda-Calculus in Twelf (Andreas Abel)




\end{code}


% Note: In our formalization of weak head reduction we must be careful to use
% code which computes to a canonical (definition?) form. For example, in CTT,
% $subst \{\}$ does not compute. This is because we want to able to compute the normal
% form later. This would not work if we used "subst" to transform a term of
% type $Γ ⊢ t :: A$ into something else.
% Because of this constraint, the following definitions do not rely on "result type matching"
% but contain extra paths, which are then used to define special equality mapping functions. (WNEmap, ...)
% (=> less beautiful, but more computational)

A term is called normal if it cannot be reduced any further
\citep{nlab:normal_form}. Consequently, an important goal for a type theory is
to be normalizing, i.e., for every term in it to have a normal form.

More practically, we want to have a reduction algorithm for $\lamto$ which can
be used to evaluate terms. Proving that such an algorithm terminates would imply
normalization.

But since in Agda all functions have to be terminating, and a termination proof
for an algorithm like stated in \citet{Sestoft:Reduction} seems to be
to be too complex to be automatically derived by the Agda typechecker, we cannot
even define this algorithm without resorting to macros which disable the
termination checker.

Because of this, we approach this problem by first proving normalization
for terms of $\lamto$. Such a proof, being necessarily constructive, gives us a
reduction algorithm for free.

The proof we use is an adaptation of Abel's proof of \textit{Normalization for
  the Simply-Typed Lambda-Calculus in Twelf} \citep{Abel:Norm}. It is not
repeated here - only the necessary definitions and conclusions are stated.

\medskip


\begin{code}[hide]
data Ir : 𝒰₀ where
  DB : ℕ -> Ir
  CC : Const -> Ir

data _⊢_⇑_ {n : ℕ} (Γ : Ctx n) : Term -> Ty -> 𝒰₀


data _⊢_⇓[_]_ {n : ℕ} (Γ : Ctx n) : Term -> Ir -> Ty -> 𝒰₀ where
  wne-var   : {t : Term} -> (i : Fin n) -> (pt : t == V (⍛ i)) -> {A : Ty} -> (Γ i == A) -> Γ ⊢ t ⇓[ DB (⍛ i) ] (A)
  wne-const : {t : Term} -> {c : Const} -> (pt : t == cconst c) -> {A : Ty} -> (ι (ctype c) == A) -> Γ ⊢ t ⇓[ CC c ] (A)
  wne-app   : ∀{r s t i X A} -> (pt : t == app r s) -> (R1 : Γ ⊢ r ⇓[ i ] (X ⇒ A)) -> (R2 : Γ ⊢ s ⇑ X) -> Γ ⊢ t ⇓[ i ] A

data _⊢_⇑_ {n} Γ where
  wn-ne : ∀{i t X} -> (R : Γ ⊢ t ⇓[ i ] X) -> Γ ⊢ t ⇑ X
  wn-lam : ∀{s A B X t} -> (pt : t == Λ A s) -> (P : X == A ⇒ B) -> (R : (A ,, Γ) ⊢ s ⇑ B) -> Γ ⊢ t ⇑ X
  wn-exp : ∀{s t X} -> (W : t ↦w s) -> (R : Γ ⊢ s ⇑ X) -> Γ ⊢ t ⇑ X
\end{code}

\begin{code}[hide]

WNEmapt : ∀{n t u i A} -> {Γ : Ctx n} -> (t == u) -> Γ ⊢ t ⇓[ i ] A -> Γ ⊢ u ⇓[ i ] A
WNEmapt p (wne-var i pt x) = wne-var i (sym p ∙ pt) x
WNEmapt p (wne-const pt x) = wne-const (sym p ∙ pt) x
WNEmapt p (wne-app pt R R2) = wne-app (sym p ∙ pt) R R2


WNmapt : ∀{n t u A} -> {Γ : Ctx n} -> (t == u) -> Γ ⊢ t ⇑ A -> Γ ⊢ u ⇑ A
WNmapt p (wn-ne R) = wn-ne (WNEmapt p R)
WNmapt p (wn-lam pt P R) = wn-lam (sym p ∙ pt) P R
WNmapt p (wn-exp W R) = wn-exp (↦wmap p W) (WNmapt refl R)


WNEmapT : ∀{n t i A B} -> {Γ : Ctx n} -> (A == B) -> Γ ⊢ t ⇓[ i ] A -> Γ ⊢ t ⇓[ i ] B
WNEmapT p (wne-var i pt x) = wne-var i pt (x ∙ p)
WNEmapT p (wne-const pt x) = wne-const pt (x ∙ p)
WNEmapT {A = A} {B} p (wne-app {X = X} pt R R2) =
  let
      p2 : X ⇒ A == X ⇒ B
      p2 = cong (X ⇒_) p

  in wne-app pt (WNEmapT p2 R) R2

WNmapT : ∀{n t A B} -> {Γ : Ctx n} -> (A == B) -> Γ ⊢ t ⇑ A -> Γ ⊢ t ⇑ B
WNmapT p (wn-ne R) = wn-ne (WNEmapT p R)
WNmapT {A = X} {B = Y} p (wn-lam pt P R) = wn-lam pt (sym p ∙ P) R
WNmapT p (wn-exp W R) = wn-exp W (WNmapT p R)


----------------------------------------------------------------------
-- Typed normal forms
\end{code}

The proof works by taking the well-typedness of the term which is being reduced
into account. As a result, the definition of a term in normal form also contains
typing information.

\begin{definition}
  A term in \textbf{typed normal form} is defined by two mutually inductive datatypes.
\begin{code}
data _⊢_↓_ {n : ℕ} (Γ : Ctx n) : Term -> Ty -> 𝒰₀
data _⊢_↑_ {n : ℕ} (Γ : Ctx n) : Term -> Ty -> 𝒰₀
\end{code}
  We write $Γ ⊢ t ↓ τ$ if $t$ is normal and neutral, i.e., if it is either a
  variable ($\AIC{ne-var}$) or a constant ($\AIC{ne-const}$), or if it is an
  application ($\AIC{ne-app}$) where the function term is neutral (and as such does not
  contain lambda expressions) and therefore cannot be reduced.
\begin{code}
data _⊢_↓_ {n} Γ where
  ne-var    : (i : Fin n) -> {σ : Ty} -> (Γ i == σ) -> Γ ⊢ V (⍛ i) ↓ σ
  ne-const  : (c : Const) -> {σ : Ty} -> (ι (ctype c) == σ) -> Γ ⊢ cconst c ↓ σ
  ne-app    : ∀{r s ρ σ}  -> (Γ ⊢ r ↓ (σ ⇒ ρ)) -> (Γ ⊢ s ↑ σ)
                          -> Γ ⊢ (app r s) ↓ ρ
\end{code}
  We write $Γ ⊢ t ↑ τ$ if $t$ is normal, i.e., if it is either neutral
  ($\AIC{nf-ne}$) or a lambda abstraction of a normal term ($\AIC{nf-lam}$).
\begin{code}
data _⊢_↑_ {n} Γ where
  nf-ne   : ∀{t τ} -> (Γ ⊢ t ↓ τ) -> Γ ⊢ t ↑ τ
  nf-lam  : ∀{s σ τ ψ} -> (ψ == σ ⇒ τ) -> ((σ ,, Γ) ⊢ s ↑ τ) -> Γ ⊢ Λ σ s ↑ ψ
\end{code}
\end{definition}

This definition guarantees that a normal term cannot have subterms of the form
$\AIC{app}\:(Λ\:σ\:t)\:s$. This is because lambda abstractions can only be
formed at the outermost level of a term or in the argument position of an
application. Without such subterms, no $β$-reduction can be done, making terms
in normal form irreducible.


