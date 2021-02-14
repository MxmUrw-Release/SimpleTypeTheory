
\begin{code}[hide]

{-# OPTIONS --cubical --allow-unsolved-metas #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Reduction.Beta {i j} {param : LambdaParam i j} where
open LambdaParam param


open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}



----------------------------------------------------------------------
-- Beta reduction
----------------------------------------------------------------------

-- CITE: Normalization for the Simply-Typed Lambda-Calculus in Twelf (Andreas Abel)




--------------------------------------
-- Weak head reduction
\end{code}

A $\lamto$ term can be executed. This means that applying a function to an
argument is evaluated by substituting the function variable with the argument.
Such a process is called $β$-reduction.

In this section we introduce $β$-reduction as a relation between terms. The
definitions are based on Twelf code found in \citet{Schuermann:Beta}.


\begin{code}[hide]
infixl 20 _↦w_
data _↦w_ : Term -> Term -> 𝒰₀ where
  rbeta : ∀{X } -> {r s t u : Term} -> (pt1 : t == (Λ X r) $$ s) -> (pt2 : u == r [ 0 / s ]) -> t ↦w u
  rapp1 : ∀{r s t u v} -> (r ↦w s) -> (t == app r v) -> (u == app s v) -> t ↦w u
\end{code}

\begin{code}[hide]

↦wmap : ∀{r s t} -> (r == s) -> (r ↦w t) -> (s ↦w t)
↦wmap p (rbeta pt1 pt2) = rbeta (sym p ∙ pt1) pt2
↦wmap p (rapp1 W pt1 pt2) = rapp1 W (sym p ∙ pt1) pt2




lem21 : ∀{t₀ t₁ u i} -> (t₀ ↦w t₁) -> t₀ [ i / u ] ↦w t₁ [ i / u ]
lem21 {t₀ = t0} {t₁ = t1} {u = u} {i} (rbeta {X} {r} {s} pt1 pt2) =
  let

    pt1' : t0 [ i / u ] == app (Λ X (r [ suc i / u ⇈ 0 ])) (s [ i / u ])
    pt1' =
           t0 [ i / u ]                                   ≡⟨ pt1 |ctx| _[ i / u ] ⟩
           app (Λ X (r [ extT (i / u )])) (s [ i / u ])  ≡⟨ sym (funExt (/suc i u)) |ctx| (λ ξ -> app (Λ X (r [ ξ ])) (s [ i / u ])) ⟩
           app (Λ X (r [ suc i / u ⇈ 0 ])) (s [ i / u ]) ∎

    pt2' : t1 [ i / u ] == (r [ suc i / u ⇈ 0 ]) [ 0 / s [ i / u ] ]
    pt2' =
           t1 [ i / u ]                                  ≡⟨ pt2 |ctx| _[ i / u ] ⟩
           r [ 0 / s ] [ i / u ]                         ≡⟨ subrot0 r s u i ⟩
           r [ suc i / u ⇈ 0 ] [ 0 / s [ i / u ] ]      ∎

  in rbeta pt1' pt2'

lem21 {u = u} {i} (rapp1 R pt1 pt2 ) = rapp1 (lem21 R) (cong _[ i / u ] pt1) (cong _[ i / u ] pt2)


β⇈ : ∀{t u} -> (i : ℕ) -> (t ↦w u) -> (t ⇈ i) ↦w (u ⇈ i)
β⇈ {t} {u} i (rbeta {X} {r} {s} pt1 pt2) =
  let
      pt1' : t ⇈ i == app (Λ X (r ⇈ suc i)) (s ⇈ i)
      pt1' = cong (_⇈ i) pt1

      pt2' : u ⇈ i == ((r ⇈ suc i) [ 0 / (s ⇈ i) ])
      pt2' = cong (_⇈ i) pt2 ∙ []⇈ r s i

  in rbeta pt1' pt2'
β⇈ i (rapp1 w pt1 pt2) = rapp1 (β⇈ i w) (cong (_⇈ i) pt1) (cong (_⇈ i) pt2)


\end{code}
\begin{definition}
  The \textbf{single step $β$ reduction} of a term $t$ to a term $u$ is denoted by $t
  ↦ u$ and defined as the following inductive data type.
\begin{code}
data _↦_ : Term -> Term -> 𝒰₀ where
  rbeta  : ∀{σ r s t u} -> (t == app (Λ σ r) s) -> (u == r [ 0 / s ]) -> t ↦ u
  rlam   : ∀{σ r s}      -> r ↦ s -> Λ σ r ↦ Λ σ s
  rapp1  : ∀{r s t u v}  -> (r ↦ s) -> (t == app r v) -> (u == app s v) -> t ↦ u
  rapp2  : ∀{r s t u v}  -> (r ↦ s) -> (t == app v r) -> (u == app v s) -> t ↦ u
\end{code}
\end{definition}
The actual reduction is performed in $\AIC{rbeta}$, where the application of
a lambda abstraction $Λ\:σ\:r$ to a term $s$ is reduced to $r\:[\:0/s\:]$.
The other constructors allow for beta reduction to be performed inside lambda
terms ($\AIC{rlam}$) and on both sides of a function application
($\AIC{rapp1}$ and $\AIC{rapp2}$).

The constructor $\AIC{rlam}$ differs from the other three in that its output
type directly expresses the form of the resulting reduction, while everywhere
else the auxilliary terms $t$ and $u$ are used, together with proofs about
what form they should have. This is necessitated by the implementation of the
normalization proof mentioned in the next section, which needs to be able to
explictly transform these equalities. But since this is not necessary for
$\AIC{rlam}$, it can be stated here in this more concise form.

\begin{remark}
  When considering the connection of type theory and logic, $β$-reduction
  corresponds to cut-elimination \citep{IntroTT}.
\end{remark}
\begin{code}[hide]

ιwhr : ∀{t s} -> t ↦w s -> t ↦ s
ιwhr (rbeta pt1 pt2) = rbeta pt1 pt2
ιwhr (rapp1 W pt1 pt2) = rapp1 (ιwhr W) pt1 pt2




----------------------------------------------------------------------
-- beta closure
-- CITE: https://www.cs.cmu.edu/~rwh/theses/schuermann.pdf

\end{code}
\newpage
\begin{definition}
  The \textbf{multi step $β$ reduction} of a term $t$ to a term $u$ is denoted by
  $t\:\AF{↦*}\:u$ and defined as a sequence of single step reductions.
\begin{code}
data _↦*_ : Term -> Term -> 𝒰₀ where
  rid   : ∀{t} -> t ↦* t
  _∙∘_  : ∀{r s t} -> r ↦ s -> s ↦* t -> r ↦* t
\end{code}
  % We extend the constructor $\_∙∘\_$ by a concatenation operation taking multi
  % step reductions as arguments 
\end{definition}
\begin{code}[hide]

infixl 40 _∙∘_ _∘∙_ _∘∘_
_∘∙_ : ∀{r s t} -> r ↦* s -> s ↦ t -> r ↦* t
rid ∘∙ w = w ∙∘ rid
(x ∙∘ v) ∘∙ w = x ∙∘ (v ∘∙ w)

\end{code}

% We define an extended composition of reduction steps.
\begin{code}[hide]
_∘∘_ : ∀{r s t} -> r ↦* s -> s ↦* t -> r ↦* t
_∘∘_ v rid = v
_∘∘_ v (x ∙∘ w) = (v ∘∙ x) ∘∘ w
\end{code}
\begin{code}[hide]



rapp1* : ∀{r s t} -> r ↦* s -> r $$ t ↦* s $$ t
rapp1* rid = rid
rapp1* (x ∙∘ w) = rapp1 x refl refl ∙∘ rapp1* w


rapp2* : ∀{r s t} -> r ↦* s -> t $$ r ↦* t $$ s
rapp2* rid = rid
rapp2* (x ∙∘ w) = rapp2 x refl refl ∙∘ rapp2* w

rlam* : ∀{A r s} -> r ↦* s -> Λ A r ↦* Λ A s
rlam* rid = rid
rlam* {A = A} {r} (x ∙∘ w) = rlam (x) ∙∘ rlam* w


prid : {a b : Term} -> (a == b) -> a ↦* b
prid {a} {b} p = subst {P = λ ξ -> a ↦* ξ} p rid

\end{code}

\noindent
Evaluating a term should not change its type. This is formulated as a theorem.

\begin{theorem}
  For every well-typed term $t$, the term $u$ obtained by a single reduction
  step is also well-typed.
\begin{code}
JStep : ∀{t u τ} -> {Γ : Ctx n} -> (t ↦ u) -> Γ ⊢ t :: τ -> Γ ⊢ u :: τ
\end{code}
\end{theorem}
\begin{proof}
  This proof works by induction on the constructors of reduction. For the case of
  $\AIC{rbeta}$, Theorem \ref{th:subst} is be used.
\end{proof}
\begin{code}[hide]
JStep (rbeta {σ = ψ} {r} {s} {t} {u} t=Λψrs u=r[0/s]) T =
  let
      RS = Jmapt t=Λψrs T
      σ , ΛR , S = app⇑ RS
      R , _ = addVarLambda ΛR
      R[S] = R [ Sub₀ S ]⇓
      U = Jmapt (sym u=r[0/s]) R[S]
  in U

JStep (rlam {σ = X} {r} {s} W) J =
  let
      B , Jr , XB=A = Λ⇑ J
      Js = JStep W Jr
      Js' = Λ⇓ Js
  in JmapT XB=A Js'
JStep (rapp1 {r} {s} {t} {u} {v} r↦s tp up) Jt =
  let
      Jrv = Jmapt tp Jt
      X , Jr , Jv = app⇑ Jrv
      Js = JStep r↦s Jr
      Jsv = app⇓ Js Jv
      Ju = Jmapt (sym up) Jsv
  in Ju
JStep (rapp2 {r} {s} {t} {u} {v} r↦s tp up) Jt =
  let
      Jvr = Jmapt tp Jt
      X , Jv , Jr = app⇑ Jvr
      Js = JStep r↦s Jr
      Jvs = app⇓ Jv Js
      Ju = Jmapt (sym up) Jvs
  in Ju


JStep-tl : ∀{n u τ} -> {Γ : Ctx n} -> (T : Γ ⊩ τ) -> (fst T ↦ u) -> Γ ⊩ τ
JStep-tl {u = u} (t , T) w = u , JStep w T


\end{code}
