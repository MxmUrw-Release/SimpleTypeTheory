
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Reduction.NormalFormProofs {i j} {param : LambdaParam i j} where
open LambdaParam param


open import TypeTheory.Lambda.Core {param = param}
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction.Beta {param = param}
open import TypeTheory.Lambda.Reduction.NormalForm {param = param}





shiftDown2 : ∀{n A T i j} -> {Γ : Ctx n} -> (p : (⍛ j) == (⍛ i) -> ⊥) -> (i ↓ A) Γ j == T -> Γ ⊢ V (⍛ j ↧ ⍛ i) ⇓[ DB (⍛ j ↧ ⍛ i) ] T
shiftDown2 {A = A} {T} {i} {j} {Γ} p (P) = wne-var (↧f j i p) refl (insertLShiftDown Γ i j p A P)





weak-wn-db⇓ : ∀{n t A B i j} -> {Γ : Ctx n} -> Γ ⊢ t ⇓[ DB j ] B -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> Δ ⊢ (t ⇈ ⍛ i) ⇓[ DB (j ↥ (⍛ i)) ] B
weak-wn-cc⇓ : ∀{n t A B i c} -> {Γ : Ctx n} -> Γ ⊢ t ⇓[ CC c ] B -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> Δ ⊢ (t ⇈ ⍛ i) ⇓[ CC c ] B

\end{code}

  % We may weaken a weak head normal form.
\begin{code}[hide]
weak-wn⇑ : ∀{n t A B i}   -> {Γ : Ctx n} -> Γ ⊢ t ⇑ B         -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> Δ ⊢ (t ⇈ ⍛ i) ⇑ B
\end{code}

\begin{code}[hide]

weak-wn-cc⇓ {t = t} {A} {B} {i} {d} {Γ} (wne-const pt p) Δ ctxp = wne-const (cong (_⇈ ⍛ i) pt) p
weak-wn-cc⇓ {t = t} {A} {B} {i} {c} {Γ} (wne-app pt R1 R2) Δ ctxp =
  let
      P1 = weak-wn-cc⇓ R1 Δ ctxp
      P2 = weak-wn⇑    R2 Δ ctxp
  in wne-app (cong (_⇈ ⍛ i) pt) P1 P2


weak-wn-db⇓ {n} {t = t} {A} {B} {i} {.(⍛ j)} {Γ} (wne-var j pt x) Δ ctxp =
  let
      k = (⍛ j) ↥ (⍛ i)

      kk : Fin (suc n)
      kk = j ↥f i

      R1 : (i ↓ A) Γ kk == B
      R1 = insertLShift Γ i j x A

      R1' : Δ kk == B
      R1' = (cong (_$ kk) ctxp) ∙ R1

      R2 : Δ ⊢ V (⍛ kk) ⇓[ DB (⍛ kk)] B
      R2 = wne-var kk refl R1'

      R3 : Δ ⊢ V k ⇓[ DB k ] B
      R3 = R2

  in WNEmapt (cong (_⇈ ⍛ i) (sym pt)) R3
weak-wn-db⇓ {t = t} {A} {B} {i} {j} {Γ} (wne-app pt R1 R2) Δ ctxp =
  let
      P1 = weak-wn-db⇓ R1 Δ ctxp
      P2 = weak-wn⇑    R2 Δ ctxp

  in wne-app (cong (_⇈ ⍛ i) pt) P1 P2

weak-wn⇑ {t = t} {A} {B} {i} {Γ} (wn-ne {DB x} R) Δ ctxp = wn-ne (weak-wn-db⇓ R Δ ctxp)
weak-wn⇑ {t = t} {A} {B} {i} {Γ} (wn-ne {CC x} R) Δ ctxp = wn-ne (weak-wn-cc⇓ R Δ ctxp)
weak-wn⇑ {t = t} {A} {Y} {i} {Γ} (wn-lam {A = X} pt P R) Δ ctxp =
  let

      p0 : X ,, (i ↓ A) Γ == (fsuc i ↓ A) (X ,, Γ)
      p0 = funExt (insertLComma Γ i A)

      p1 : X ,, Δ == ((fsuc i) ↓ A) (X ,, Γ)
      p1 = cong (X ,,_) ctxp ∙ p0

      R1 = (weak-wn⇑ R (X ,, Δ) p1)
  in wn-lam (cong (_⇈ ⍛ i ) pt) P R1
weak-wn⇑ {t = t} {A} {B} {i} {Γ} (wn-exp (rbeta {r = r} {s} pt1 pt2) R) Δ ctxp =
  let
    ii = ⍛ i

    R1 = weak-wn⇑ R Δ ctxp

    R2 : Δ ⊢ r [ 0 / s ] ⇈ ii ⇑ B
    R2 = WNmapt (cong (_⇈ ii) pt2) R1

    R3 : Δ ⊢ (r ⇈ suc ii) [ 0 / (s ⇈ ii)] ⇑ B
    R3 = WNmapt ([]⇈ r s ii) R2

  in wn-exp (rbeta (cong (_⇈ ii) pt1) refl) R3
weak-wn⇑ {t = t} {A} {B} {i} {Γ} (wn-exp (rapp1 {r} {s} {t} {u} {v} W pt1 pt2) R) Δ ctxp =
  let
      ii = ⍛ i

      w : (r ⇈ ii) ↦w (s ⇈ ii)
      w = β⇈ ii W

  in wn-exp (rapp1 w (cong (_⇈ ii) pt1) (cong (_⇈ ii) pt2)) (weak-wn⇑ R Δ ctxp)



weak-wn0⇑ : ∀{n t A B} -> {Γ : Ctx n} -> Γ ⊢ t ⇑ B -> (A ,, Γ) ⊢ (t ⇈ 0) ⇑ B
weak-wn0⇑ {t = t} {A} {B} {Γ} R =
  let
      P1 : (A ,, Γ) ⊢ (t ⇈ 0) ⇑ B
      P1 = weak-wn⇑ R (A ,, Γ) (sym (funExt (insertLZero Γ A)))

  in P1






\end{code}

% ---------------------------------------------------------------------
% \subsection*{Substitution and Application 4-Lemma}




% A type may be part of another type.
\begin{code}[hide]
data _partOf_ : Ty -> Ty -> 𝒰₀ where
  eqpart : ∀{A B} -> (A == B) -> A partOf B
  rpart  : {A B X : Ty} -> A partOf B -> A partOf X ⇒ B
\end{code}




% NOTE
% We explicitly give a Δ instead of (i ↓ A) Γ, because of termination checking. We need to be able to recursively call
% our functions on the arguments (R1, R2, ...) without modifying them. For else the termination checker cannot know
% that the arguments get smaller in every iteration.
% The way it is handled now, allows us simply forward the arguments, while also providing a proof (which is not always
% trivially refl) that shows that they indeed have the right form.

\begin{code}[hide]
app-wn   : ∀{n r s A C} -> {Γ : Ctx n} -> (R1 : Γ ⊢ r ⇑ A ⇒ C)               -> (R2 : Γ ⊢ s ⇑ A) -> Γ ⊢ (app r s) ⇑ C
subst-wn : ∀{n s t A C i}   -> {Γ : Ctx n} -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> (R1 : Δ ⊢ t ⇑ C)                                    -> (R2 : Γ ⊢ s ⇑ A) -> Γ ⊢ t [ ⍛ i / s ] ⇑ C
subst-0  : ∀{n s t A i j C} -> {Γ : Ctx n} -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> (R1 : Δ ⊢ t ⇓[ DB j ] C) -> (j == (⍛ i))          -> (R2 : Γ ⊢ s ⇑ A) -> (Γ ⊢ t [ ⍛ i / s ] ⇑ C) × (C partOf A)
subst-si : ∀{n s t A i j C} -> {Γ : Ctx n} -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> (R1 : Δ ⊢ t ⇓[ DB j ] C) -> (p : j == (⍛ i) -> ⊥) -> (R2 : Γ ⊢ s ⇑ A) -> Γ ⊢ t [ ⍛ i / s ] ⇓[ DB (j ↧ ⍛ i) ] C
subst-cc : ∀{n s t A i c C} -> {Γ : Ctx n} -> (Δ : Ctx (suc n)) -> (Δ == (i ↓ A) Γ) -> (R1 : Δ ⊢ t ⇓[ CC c ] C) ->                          (R2 : Γ ⊢ s ⇑ A) -> (Γ ⊢ t [ ⍛ i / s ] ⇓[ CC c ] C)
\end{code}

\begin{code}[hide]

subst-cc {s = s} {t} {A} {i} {d} {C} Δ ctxp (wne-const c x) R2 = wne-const (cong (_[ ⍛ i / s ]) c) x
subst-cc {s = s} {t} {A} {i} {c} {C} Δ ctxp (wne-app {r = t₁} {s = t₂} {X = X} pt R1 R3) R2 =
  let
      P1 = subst-cc Δ ctxp R1 R2
      P2 = subst-wn Δ ctxp R3 R2

  in wne-app (cong _[ ⍛ i / s ] pt) P1 P2

subst-wn0 : ∀{n s t A C} -> {Γ : Ctx n} -> (R1 : (A ,, Γ) ⊢ t ⇑ C)             -> (R2 : Γ ⊢ s ⇑ A) -> Γ ⊢ t [ 0 / s ] ⇑ C
subst-wn0 {n} {s} {t} {A} {C} {Γ} R1 R2 =
  let

      p01 : (A ,, Γ) == (fzero ↓ A) Γ
      p01 = sym $ funExt $ insertLZero Γ A

  in subst-wn (A ,, Γ) p01 R1 R2

app-wn (wn-ne R) R2 = wn-ne (wne-app refl R R2)
app-wn {s = s} {A = A1} {C = C} {Γ} (wn-lam {A = A2} {B = B} pt P R) R2 =
  let
      p0 : A2 == A1
      p0 = cong ⇒1 (sym P)

      p : (A2 ,, Γ) == (fzero ↓ A1) Γ
      p = cong (_,, Γ) p0 ∙ sym (funExt (insertLZero Γ A1))


      P1 = subst-wn (A2 ,, Γ) p R R2

      P2 = wn-exp (rbeta refl refl) P1
  in WNmapT (sym (cong ⇒2 P)) (WNmapt (sym (cong (λ ξ -> app ξ s) pt)) P2)

app-wn (wn-exp W R1) R2 =
  let
      P1 = wn-exp (rapp1 W refl refl) (app-wn R1 R2)
  in P1

subst-wn {s = s} {t} {A} {C} {i} Δ ctxp (wn-ne {i = CC c} R1) R2 = wn-ne (subst-cc Δ ctxp R1 R2)
subst-wn {s = s} {t} {A} {C} {i} Δ ctxp (wn-ne {i = DB j} R1) R2 with compare-eq (j) (⍛ i)
subst-wn {s = s} {t} {A} {C} {i} {Γ} Δ ctxp (wn-ne {j} R1) R2 | equal x = fst $ subst-0 Δ ctxp R1 x R2
subst-wn {s = s} {t} {A} {C} {i} Δ ctxp (wn-ne {j} R1) R2 | noteq x = wn-ne $ subst-si Δ ctxp R1 (x) R2
subst-wn {s = s} {A = A} {C = B} {i = i} {Γ = Γ} Δ ctxp (wn-lam {s = t'} {A = A'} {B = B'} pt P R1) R2 =
  let
      p01 : (A' ,, Δ) == (fsuc i ↓ A) (A' ,, Γ)
      p01 = cong (A' ,,_) ctxp ∙ (funExt (insertLComma Γ i A))

      ss : (A' ,, Γ) ⊢ s ⇈ 0 ⇑ A
      ss = weak-wn0⇑ R2

      P4 : (A' ,, Γ) ⊢ t' [ fnat (fsuc i) / (s ⇈ 0) ] ⇑ B'
      P4 = subst-wn (A' ,, Δ) p01 R1 ss

      P2 : (A' ,, Γ) ⊢ t' [ extT ((fnat i) / s) ] ⇑ B'
      P2 = WNmapt (cong (t' [_]) (funExt (/suc (fnat i) s))) P4

      P5 = wn-lam (cong _[ ⍛ i / s ] pt) P P2

  in P5
subst-wn {s = s} {t} {A} {C} {i} {Γ} Δ ctxp (wn-exp {s = s'} W R1) R2 =
  let
      P1 : t [ ⍛ i / s ] ↦w s' [ ⍛ i / s ]
      P1 = lem21 W

      P2 : Γ ⊢ s' [ ⍛ i / s ] ⇑ C
      P2 = subst-wn Δ ctxp R1 R2

  in wn-exp P1 P2

subst-0 {s = s} {t} {A} {i} {j} {C} {Γ} Δ ctxp (wne-var (fin .j ip) pt p) i=j R2 =
  let
      ii = fin (j) ip

      A=C : A == C
      A=C = sym (insertLEq Γ A i) ∙ cong (λ ξ -> (i ↓ A) Γ ξ) (finEqual2 i ii {sym i=j}) ∙ cong (_$ ii) (sym ctxp) ∙ p

      P2 : Γ ⊢ s ⇑ C
      P2 = WNmapT A=C R2

      P1 : Γ ⊢ (V (fnat i)) [ fnat i / s ] ⇑ C
      P1 = WNmapt (sym $ /same (fnat i) s) P2

      P3 : Γ ⊢ (V j) [ fnat i / s ] ⇑ C
      P3 = WNmapt (cong (λ ξ -> V ξ [ ⍛ i / s ]) (sym i=j)) P1
  in WNmapt (cong _[ ⍛ i / s ] (sym pt)) P3 , eqpart (sym A=C)
subst-0 {s = s} {t} {A} {i} {j} {C} {Γ} Δ ctxp (wne-app {r = t1} {s = t2} {X = X} pt R1 R3) i=j R2 =
  let
      pp = subst-0 Δ ctxp R1 i=j R2

      XC⊂A'B = snd pp

      P1 : Γ ⊢ t1 [ (⍛ i) / s ] ⇑ (X ⇒ C)
      P1 = fst pp

      P2 : Γ ⊢ t2 [ (fnat i) / s ] ⇑ X
      P2 = subst-wn Δ ctxp R3 R2

      P3 , PP = callApp (A) XC⊂A'B P1 P2

  in WNmapt (cong _[ ⍛ i / s ] (sym pt)) P3 , PP
    where
      callApp : (Y : Ty) -> (X ⇒ C) partOf Y -> Γ ⊢ t1 [ (fnat i) / s ] ⇑ (X ⇒ C) -> Γ ⊢ t2 [ (fnat i) / s ] ⇑ X ->  (Γ ⊢ app t1 t2 [ fnat i / s ] ⇑ C) × (C partOf Y)
      callApp (A' ⇒ B) (eqpart eq) P1 P2 =
        let
            lem : X == A'
            lem = cong ⇒1 eq

            P1' : Γ ⊢ t1 [ (fnat i) / s ] ⇑ (A' ⇒ C)
            P1' = WNmapT (cong (_⇒ C) lem) P1

            P2' : Γ ⊢ t2 [ (fnat i) / s ] ⇑ (A')
            P2' = WNmapT lem P2

            P3 : Γ ⊢ app t1 t2 [ fnat i / s ] ⇑ C
            P3 = app-wn {A = A'} P1' P2'

        in P3 , rpart (eqpart (cong ⇒2 eq))
      callApp (A' ⇒ B) (rpart part) P1 P2 =
        let
            P , Part = callApp B part P1 P2

        in P , rpart Part


      callApp (ι _) (eqpart eq) _ _ = ⊥-elim $ subst {P = case-ι} (sym eq) tt

subst-si {s = s} {t} {A} {i} {j} {C} {Γ} Δ ctxp (wne-var jj pt x) i!=j R2 =
  let
      k =  (⍛ jj) ↧ (⍛ i)

      p : ((i ↓ A) Γ) jj == C
      p = (sym (cong (_$ jj) ctxp)) ∙ x

      p2 : V j [ (fnat i) / s ] == V k
      p2 = /diff (fnat i) j i!=j s

      P1 = shiftDown2 i!=j p


      P2 : Γ ⊢ V j [ (fnat i) / s ] ⇓[ DB k ] C
      P2 = WNEmapt (sym p2) P1

  in WNEmapt (cong _[ ⍛ i / s ] (sym pt)) P2
subst-si {s = s} {t} {A} {i} {j} {C} {Γ} Δ ctxp (wne-app {r = t₁} {s = t₂} {X = X} pt R1 R3) i!=j R2 =
  let
      P1 : Γ ⊢ t₁ [ ⍛ i / s ] ⇓[ DB (j ↧ ⍛ i) ] (X ⇒ C)
      P1 = subst-si Δ ctxp R1 i!=j R2

      P2 : Γ ⊢ t₂ [ ⍛ i / s ] ⇑ X
      P2 = subst-wn Δ ctxp R3 R2

      P3 : Γ ⊢ app (t₁ [ ⍛ i / s ]) (t₂ [ ⍛ i / s ]) ⇓[ DB (j ↧ ⍛ i) ] C
      P3 = wne-app refl P1 P2

  in WNEmapt (cong _[ ⍛ i / s ] (sym pt)) P3


\end{code}

% If a term is well typed, then it is in the relation.
\begin{code}[hide]
jrel : ∀{n t A} -> {Γ : Ctx n} -> (Γ ⊢ t :: A) -> (Γ ⊢ t ⇑ A)
jrel {t = cconst c} {A} {Γ} J =
  let
      p = cconst⇑ J

  in wn-ne (wne-const refl p)
jrel {t = V x} {A} {Γ} J =
  let
      i , Γi=A , _ = V⇑ J
  in wn-ne (wne-var i refl Γi=A)
jrel {t = Λ A t} {X} {Γ} J =
  let
      B , J2 , p = Λ⇑ J

      R1 : Γ ⊢ Λ A t ⇑ A ⇒ B
      R1 = wn-lam refl refl (jrel J2)

      R2 : Γ ⊢ Λ A t ⇑ X
      R2 = WNmapT p R1

  in R2
jrel {t = app f x} {B} {Γ} J =
  let
      A , Jf , Jx = app⇑ J

      R1 = app-wn (jrel Jf) (jrel Jx)

  in R1

\end{code}





\begin{lemma}
  A term in typed normal form is well-typed. 
\begin{code}
nfj↑ : ∀{n t A} -> {Γ : Ctx n} -> Γ ⊢ t ↑ A -> Γ ⊢ t :: A
\end{code}
\end{lemma}
\begin{proof}
  Since the definition of a typed normal form already captures the concept of
  well-typedness, this proof is trivial.
\end{proof}

\begin{code}[hide]


nfj↓ : ∀{n t A} -> {Γ : Ctx n} -> Γ ⊢ t ↓ A -> Γ ⊢ t :: A
nfj↓ {n} {.(V (⍛ i))} {A} {Γ} (ne-var i x) = V⇓ x
nfj↓ {n} {.(cconst c)} {A} {Γ} (ne-const c x) = cconst⇓ x
nfj↓ {n} {.(app _ _)} {A} {Γ} (ne-app R1 R2) = app⇓ (nfj↓ R1) (nfj↑ R2)

nfj↑ {n} {t} {A} {Γ} (nf-ne R) = nfj↓ R
nfj↑ {n} {.(Λ _ _)} {A} {Γ} (nf-lam P R) = JmapT (sym P) (Λ⇓ (nfj↑ R))





----------------------------------------------------------------------
-- "Soundness"


\end{code}
% If a term is in the relation, then there exists a sequence of reduction steps
% which reduce to a normal form.
\begin{code}[hide]
sound⇓ : ∀{n t A i} -> {Γ : Ctx n} -> Γ ⊢ t ⇓[ i ] A -> Σ $ λ u -> (t ↦* u) × (Γ ⊢ u ↓ A)
sound⇑ : ∀{n t A} -> {Γ : Ctx n} -> Γ ⊢ t ⇑ A -> Σ $ λ u -> (t ↦* u) × (Γ ⊢ u ↑ A)
\end{code}
\begin{code}[hide]

sound⇓ {t = t} {A} {.(DB (⍛ i))} {Γ} (wne-var i pt x) = V (⍛ i) , prid pt , ne-var i x
sound⇓ {t = t} {A} {(CC c)} {Γ} (wne-const pt x) = cconst c , prid pt , ne-const c x
sound⇓ {t = t} {A} {i} {Γ} (wne-app {r} {s} pt R1 R2) =
  let
      r' , rw , S1 = sound⇓ R1
      s' , sw , S2 = sound⇑ R2

      w01 : (app r s) ↦* r' $$ s'
      w01 = (rapp1* rw) ∘∘ (rapp2* sw)

  in app r' s' , prid pt ∘∘ w01 , ne-app S1 S2

sound⇑ {t = t} {A} {Γ} (wn-ne R) =
  let
      s , sw , S1 = (sound⇓ R)

  in s , sw , nf-ne S1
sound⇑ {t = t} {Y} {Γ} (wn-lam {s} {A} {B} pt P R) =
  let
      s' , sw , S1 = sound⇑ R

      ww : Λ A s ↦* Λ A s'
      ww = rlam* sw

  in Λ A s' , prid pt ∘∘ ww , nf-lam P (S1)
sound⇑ {t = t} {A} {Γ} (wn-exp W R) =
  let
      s , sw , S1 = sound⇑ R
  in s , ιwhr W ∙∘ sw , S1



----------------------------------------------------------------------
-- back into term


\end{code}

\begin{theorem}[Weak normalization]
  For every well-typed term $Γ ⊢ t :: τ$ there exists a sequence of reduction
  steps $t ↦* u$ to a term in normal form $Γ ⊢ u ↑ τ$.
\begin{code}
nf : ∀{t τ} -> {Γ : Ctx n} -> Γ ⊢ t :: τ -> Σ (λ u -> (t ↦* u) × (Γ ⊢ u ↑ τ))
\end{code}
\end{theorem}
\begin{proof}
  Omitted.
\begin{code}[hide]
nf J = sound⇑ (jrel J)
\end{code}
\end{proof}

\begin{remark}
  This is a proof of weak normalization. Strong normalization
  would imply that \textit{every} sequence of reduction steps terminates.
\end{remark}

The normalization algorithm for $\lamto$ is defined as follows:
\begin{definition}
   The \textbf{normal form} of a well-typed term $t$ is the term $u$ whose existence was proven above.
\begin{code}
nor : ∀{t τ} -> {Γ : Ctx n} -> Γ ⊢ t :: τ -> Term
nor T = fst (nf T)
\end{code}
\end{definition}

\begin{code}[hide]
nor⇓ : ∀{n t A} -> {Γ : Ctx n} -> (J : Γ ⊢ t :: A) -> Γ ⊢ nor J :: A
nor⇓ Jt =
  let _ , _ , Ju = sound⇑ (jrel Jt)
  in nfj↑ Ju


----------------------------------------------------------------------
-- Beta equality

\end{code}

\noindent
Using this, a notion of equality between terms can be introduced:

\begin{definition}
  Two terms are said to be \textbf{$β$-equal} if their normal forms are equal.
\begin{code}
_=β=_ : ∀{t u τ} -> {Γ : Ctx n} -> (Γ ⊢ t :: τ) -> (Γ ⊢ u :: τ) -> 𝒰₀
_=β=_ T U = nor T == nor U
\end{code}
\end{definition}

\begin{remark}
  This is the concept behind the definitional equality ($\equiv$) which was mentioned in  chapter 2.
\end{remark}


\begin{code}[hide]
nor= : ∀{n t u A} -> {Γ : Ctx n} -> (Jt : Γ ⊢ t :: A) -> (Ju : Γ ⊢ u :: A) -> (p : Jt =β= Ju) -> PathP (λ i -> Γ ⊢ p i :: A) (nor⇓ Jt) (nor⇓ Ju)
nor= {A = A} {Γ} Jt Ju p = Jmapt= _ _ p
\end{code}
