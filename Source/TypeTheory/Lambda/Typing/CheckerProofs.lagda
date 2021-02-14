\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
  hiding (_↥_)
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Typing.CheckerProofs {i j} {param : LambdaParam i j} where
open LambdaParam param

open import TypeTheory.Lambda.Core {param = param}
  hiding (_⇈_)
open import TypeTheory.Lambda.Typing.Error {param = param}
open import TypeTheory.Lambda.Typing.Checker {param = param}





----------------------------------------------------------------------
-- Helper functions

--------------------------------------
-- type
varrefl : {a : Ty} -> testTypeEq a a == right tt
varrefl {a} with a =stype= a
...           | yes _ = refl
...           | no  p = ⊥-elim (p refl)

varreflfir : {a : Ty} -> FIR (a) (testTypeEq a)
varreflfir = tt ,fir, varrefl


testVarTypeBack : {A B : Ty} -> testTypeEq A B == right tt -> A == B
testVarTypeBack {A} {B} p with A =stype= B
...                  | yes p2 = p2
...                  | no  p2 = ⊥-elim $ subst {P = case-right} (sym p) tt


testVarTypeBack' : {A B : Ty} -> FIR (B) (testTypeEq A) -> B == A
testVarTypeBack' p = sym $ testVarTypeBack (firProof p)

testVarPath : {A B : Ty} -> A == B -> testTypeEq A B == right tt
testVarPath {A} {B} p with A =stype= B
...                  | yes _ = refl
...                  | no  p2 = ⊥-elim $ p2 p


--------------------------------------
-- fin
testfinfin : {n : ℕ} -> (i : Fin n) -> (testFin n) (fnat i) == right i
testfinfin {n} i with compare (fnat i) n
...                     | less (i<n)   = cong right (finNatFin i i<n)
...                     | equal i=n    = ⊥-elim $ lessEqual-⊥ (fnatless i) i=n
...                     | greater i>n  = ⊥-elim $ lessGreater-⊥ (fnatless i) i>n

testfinfir : {n : ℕ} -> (i : Fin n) -> FIR (fnat i) (testFin n)
testfinfir {n} i = i ,fir, testfinfin i


--------------------------------------
-- function
testFunctionTypeFir : {A B : Ty} -> FIR (A ⇒ B) testFunctionType
testFunctionTypeFir {A} {B} = (A , B) ,fir, refl

testFTback : {X : Ty} -> FIR X testFunctionType -> Σ' (Ty × Ty) (λ {(A , B) -> X == A ⇒ B})
testFTback {A ⇒ B} p = (A , B) , refl
testFTback {ι C} (X ,fir, p) = ⊥-elim (leftNotRight p)


----------------------------------------------------------------------
-- Mapping

JmapT : ∀{n t A B} -> {Γ : Ctx n} -> (A == B) -> Γ ⊢ t :: A -> Γ ⊢ t :: B
JmapT {n} {t} {A} {B} {Γ} tp (tt ,fir, Jp) = tt ,fir, tp2 ∙ Jp
  where
    tp2 : check (Γ , t , B) == check (Γ , t , A)
    tp2 = cong (λ ξ -> check (Γ , t , ξ)) (sym tp)


Jmapt : ∀{n t u A} -> {Γ : Ctx n} -> (t == u) -> Γ ⊢ t :: A -> Γ ⊢ u :: A
Jmapt {n} {t} {u} {A} {Γ} tp (tt ,fir, Jp) = tt ,fir, tp2 ∙ Jp
  where
    tp2 : check (Γ , u , A) == check (Γ , t , A)
    tp2 = cong (λ ξ -> check (Γ , ξ , A)) (sym tp)


JmapC : ∀{n t τ} -> {Γ Δ : Ctx n} -> (Γ == Δ) -> Γ ⊢ t :: τ -> Δ ⊢ t :: τ
JmapC {n} {t} {τ} {Γ} {Δ} Γ=Δ (tt ,fir, Jp) = tt ,fir, tp2 ∙ Jp
  where
    tp2 : check (Δ , t , τ) == check (Γ , t , τ)
    tp2 = cong (λ Α -> check (Α , t , τ)) (sym Γ=Δ)



\end{code}
We show that the typechecker behaves exactly as the typing rules stated above require.
This means that, for every rule, we can prove implications up and down: from
the hypothesis to the derivation and also, from a valid derivation back to
the hypothesis.

\medskip

\noindent
Since such derivation rules describe implications, they can be formalized using functions:

\begin{code}[hide]




----------------------------------------------------------------------
-- SynCheck
checkToSyn : ∀{m} -> {Γ : Ctx m} -> {t : Term} -> {A : Ty} -> Γ ⊢ t :: A -> Σ (λ (p : FIR (Γ , t) syn) -> fir p == A)
checkToSyn {Γ = Γ} {t} {A} p =
  let pp : FIR (Γ , t) (syn ◆ testTypeEq A)
      pp = fir p ,fir, firProof p

      p01 , p02 = dosplit◆ (syn) (testTypeEq A) pp

  in p01 , testVarTypeBack' p02

synToCheck : ∀{m} -> {Γ : Ctx m} -> {t : Term} -> (p : FIR (Γ , t) syn) -> Γ ⊢ t :: (fir p)
synToCheck {Γ = Γ} {t} p =
  let p01 : FIR (Γ , t) (syn ◆ testTypeEq (fir p))
      p01 = p eval◆ varreflfir

  in  fir p01 ,fir, firProof p01




----------------------------------------------------------------------
-- Check proofs (Var)
----------------------------------------------------------------------





module _ {A B : 𝒰₀} where

  isRight : ∀{C : 𝒰₀} -> {x : A + B} -> {f : B -> A + C} -> {y : B} -> (x == right y) -> (x >>= f) == (f y)
  isRight {x = left x} {y} p = ⊥-elim (subst {P = case-right } (sym p) tt)
  isRight {x = right z} {f = f} {y} p = cong f (right-inj p)



-- i'th var has i'th type

iVarType : ∀{m} {Γ : Ctx m} (i : Fin m) -> FIR (Γ , V (fnat i) , Γ i) check
iVarType {m} {Γ} i = tt ,fir, firProof p00
  where
    p00 : FIR (fnat i) (testFin m ◆ (right ∘ Γ) ◆ testTypeEq (Γ i))
    p00 = testfinfir i eval◆ ~~ eval◆ varreflfir


\end{code}


% ----------------------------------------------------------------------
% BEGIN MEGA THEOREM

\begin{theorem}
The typechecker respects the typing rules given above. 
\begin{enumerate}[(i)]
\item The constant rule.
\begin{code}
cconst⇓ : ∀{c τ} -> {Γ : Ctx n}  -> ι (ctype c) == τ
                                 -> Γ ⊢ (cconst c) :: τ
\end{code}
\begin{code}[hide]
cconst⇓ p = tt ,fir, testVarPath (sym p)
\end{code}
\begin{code}
cconst⇑ : ∀{c τ} -> {Γ : Ctx n}  -> Γ ⊢ (cconst c) :: τ
                                 -> ι (ctype c) == τ
\end{code}
\begin{code}[hide]
cconst⇑ {c = c} {B} {Γ} p =
  let p01 , p02 = checkToSyn p
  in  p02
\end{code}

\item The variable rule. Here, in the case of $\AF{V⇑}$, the existence of an index $j$
can be stipulated since we know that the natural number $i$ accesses a valid variable.
The property of $i < n$ is implicitly contained in $i$ being used as an index into $Γ$.

\begin{code}
V⇓ : ∀{i τ} -> {Γ : Ctx n}  -> Γ i == τ
                            -> Γ ⊢ V (⍛ i) :: τ
\end{code}
\begin{code}[hide]
V⇓ {i = i} {A} {Γ} p =
  let
      J : Γ ⊢ V (⍛ i) :: Γ i
      J = iVarType i

      J2 : Γ ⊢ V (⍛ i) :: A
      J2 = subst {P = λ ξ -> Γ ⊢ V (⍛ i) :: ξ} p J

  in J2



----------------------------------------------------------------------
-- Weakening
----------------------------------------------------------------------



----------------------------------------------------------------------
-- Backchecking

validDeBrujin : ∀{n} -> (Γ : Ctx n) -> {i : ℕ} -> {A : Ty} -> Γ ⊢ (V i) :: A -> i < n
validDeBrujin {n} Γ {i} {A} (tt ,fir, p) with compare i n
...                            | less i<n = i<n
...                            | equal i=n = ⊥-elim (subst {P = case-right} (sym p) tt)
validDeBrujin {n} Γ {i} {A} (tt ,fir, p)  | greater i>n = ⊥-elim (subst {P = case-right} (sym p) tt)

\end{code}

% V⇑3 : ∀{i τ} -> {Γ : Ctx n} -> (Γ ⊢ V i :: τ) -> Σ (λ i -> Γ i == τ)
% V⇑3 {n = n} {i} {τ} {Γ}  p =
%   let
%       iz : Fin (n)
%       iz = fin i (validDeBrujin Γ (p))

%       p02p : FIR i (testFin n ◆ (right ∘ Γ) ◆ testTypeEq τ)
%       p02p = tt ,fir, firProof p

%       p01p : testTypeEq τ (Γ iz) == right tt
%       p01p = firProof $ firsub {f = (testFin n)} (testfinfin iz) (firfmap (diassoc (testFin n) (right ∘ Γ) (testTypeEq τ)) p02p)

%   in iz , (sym (testVarTypeBack p01p))


\begin{code}
V⇑ : ∀{i τ} -> {Γ : Ctx n}  -> Γ ⊢ (V i) :: τ
                            -> Σ (λ j -> (Γ j == τ) × (⍛ j == i))
\end{code}
\begin{code}[hide]
V⇑ {n = n} {i} {τ} {Γ} p =
  let
      iz : Fin (n)
      iz = fin i (validDeBrujin Γ (p))


      p02p : FIR i (testFin n ◆ (right ∘ Γ) ◆ testTypeEq τ)
      p02p = tt ,fir, firProof p

      p01p : testTypeEq τ (Γ iz) == right tt
      p01p = firProof $ firsub {f = (testFin n)} (testfinfin iz) (firfmap (diassoc (testFin n) (right ∘ Γ) (testTypeEq τ)) p02p)

  in iz , (sym (testVarTypeBack p01p)) , refl



----------------------------------------------------------------------
-- Lambda helpers

\end{code}


\item The lambda rule. Here it is useful to consider the cases of a lambda
term having a ground type ($\AF{Λ⇑ι}$) or a function type ($\AF{Λ⇑⇒}$)
individually.
\begin{AgdaAlign}
\begin{code}
Λ⇓   : ∀{t σ τ}     -> {Γ : Ctx n}  -> (σ ,, Γ) ⊢ t :: τ
                                    -> Γ ⊢ (Λ σ t) :: σ ⇒ τ
\end{code}
\begin{code}[hide]
Λ⇓ {n} {t} {σ} {τ} {Γ} p =
  let p01 : Σ $ λ (q : FIR ((σ ,, Γ) , t) syn) -> fir q == τ
      p01 = checkToSyn p

      p02 , p03 = p01

      p04 : FIR (σ ,, Γ , t) (syn ◆ (λ B2 -> right (σ ⇒ B2)) ◆ testTypeEq (σ ⇒ τ))
      p04 = p02 eval◆ ~~ firmap (cong (σ ⇒_) p03) eval◆ (varreflfir)

  in tt ,fir, firProof p04
\end{code}


% lambdaType2 : ∀{m} {A B : Ty} -> {Γ : Ctx m} -> {t : Term} -> (A ,, Γ) ⊢ t :: B -> Γ ⊢ (Λ A t) :: A ⇒ B
% lambdaType2 {A = A} {B = B} {Γ} {t} p =
%   let p01 : Σ $ λ (q : FIR ((A ,, Γ) , t) syn) -> fir q == B
%       p01 = checkToSyn p

%       p02 , p03 = p01

%       p04 : FIR (A ,, Γ , t) (syn ◆ (λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A ⇒ B))
%       p04 = p02 eval◆ ~~ firmap (cong (A ⇒_) p03) eval◆ (varreflfir)

%   in tt ,fir, firProof p04

\begin{code}[hide]
lambdaType = Λ⇓

\end{code}
\begin{code}
Λ⇑ι  : ∀{t σ c}     -> {Γ : Ctx n}  -> Γ ⊢ (Λ σ t) :: (ι c)
                                    -> ⊥
\end{code}
\begin{code}[hide]
Λ⇑ι {n} {t} {σ} {C} {Γ} p =
  let
      p04 : FIR (σ ,, Γ , t) (syn ◆ (λ B2 -> right (σ ⇒ B2)) ◆ testTypeEq (ι C))
      p04 = fir (p) ,fir, firProof (p)

      p05 : FIR (σ ,, Γ , t) (syn ◆ ((λ B2 -> right (σ ⇒ B2)) ◆ testTypeEq (ι C)))
      p05 = firfmap (diassoc syn (λ B2 -> right (σ ⇒ B2)) (testTypeEq (ι C))) p04


      p06 , tt ,fir, p07 = dosplit◆ syn ((λ B2 -> right (σ ⇒ B2)) ◆ (testTypeEq (ι C))) p05

      p08 : (ι C) == (σ ⇒ fir p06)
      p08 = testVarTypeBack p07

  in subst {P = case-ι} p08 tt
\end{code}



\begin{code}
Λ⇑⇒  : ∀{t σ σ₂ τ}  -> {Γ : Ctx n}
                    -> Γ ⊢ (Λ σ t) :: (σ₂ ⇒ τ)
                    -> (σ₂ ,, Γ ⊢ t :: τ) × (σ₂ == σ)
\end{code}
\begin{code}[hide]
Λ⇑⇒ {t = t} {A} {A2} {B} {Γ} (tt ,fir, pp) =
  let p : FIR ((A ,, Γ) , t) (syn ◆ (λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B))
      p = tt ,fir, pp

      (XX ,fir, r1) , (tt ,fir, r2) = dosplit◆ (syn) ((λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B))
                                      (firfmap (diassoc (syn) (λ B2 -> right (A ⇒ B2)) (testTypeEq (A2 ⇒ B))) p)

      p002 : XX & (λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B) == right tt
      p002 = r2

      p003 : A2 ⇒ B == A ⇒ XX
      p003 = testVarTypeBack p002

      p004 : B == XX
      p004 = cong ⇒2 p003

      p0041 : A2 == A
      p0041 = cong ⇒1 p003

      p005 : FIR ((A ,, Γ) , t) (syn)
      p005 = (XX ,fir, r1)

      p001 : FIR ((A2 ,, Γ ) , t) (syn ◆ testTypeEq B)
      p001 = p005
             firamap (cong (λ ξ -> (ξ ,, Γ) , t) (sym p0041))
             firmap (sym p004)
             eval◆ varreflfir {a = B}

  in (tt ,fir, firProof p001) , p0041


addVarLambda2 : ∀{n} {A A2 B : Ty} -> {Γ : Ctx n} -> {t : Term} -> Γ ⊢ (Λ A t) :: (A2 ⇒ B) -> ((A ,, Γ) ⊢ t :: B) × (A ⇒ B == A2 ⇒ B)
addVarLambda2 {A = A} {A2 = A2} {B = B} {Γ} {t} (tt ,fir, pp) =
  let p : FIR ((A ,, Γ) , t) (syn ◆ (λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B))
      p = tt ,fir, pp

      (XX ,fir, r1) , (tt ,fir, r2) = dosplit◆ (syn) ((λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B))
                                      (firfmap (diassoc (syn) (λ B2 -> right (A ⇒ B2)) (testTypeEq (A2 ⇒ B))) p)

      p002 : XX & (λ B2 -> right (A ⇒ B2)) ◆ testTypeEq (A2 ⇒ B) == right tt
      p002 = r2

      p003 : A2 ⇒ B == A ⇒ XX
      p003 = testVarTypeBack p002

      p004 : B == XX
      p004 = cong ⇒2 p003

      p0041 : A2 == A
      p0041 = cong ⇒1 p003

      p005 : FIR ((A ,, Γ) , t) (syn)
      p005 = (XX ,fir, r1)

      p001 : FIR ((A ,, Γ ) , t) (syn ◆ testTypeEq B)
      p001 = p005
             firmap (sym p004)
             eval◆ varreflfir {a = B}

  in (tt ,fir, firProof p001) , (cong (_⇒ B) (sym p0041))
\end{code}

\begin{code}[hide]
lambdaNoFunc = Λ⇑ι
addVarLambda = Λ⇑⇒
\end{code}

\begin{code}
Λ⇑   : ∀{t σ ψ}     -> {Γ : Ctx n}
                    -> (Γ ⊢ Λ σ t :: ψ)
                    -> Σ (λ τ -> (σ ,, Γ ⊢ t :: τ) × ((σ ⇒ τ) == ψ))
\end{code}
\begin{code}[hide]
Λ⇑ {t = t} {A} {ι _} {Γ} p = ⊥-elim $ lambdaNoFunc p
Λ⇑ {t = t} {σ} {σ₂ ⇒ τ} {Γ} ΛT = τ , addVarLambda2 ΛT
\end{code}
\end{AgdaAlign}




% ----------------------------------------------------------------------
% -- App Helpers

\item The application rule.
\begin{AgdaAlign}
\begin{code}
app⇓ : ∀{s t σ τ}  -> {Γ : Ctx n}
                   -> (Γ ⊢ t :: σ ⇒ τ) -> (Γ ⊢ s :: σ)
                   -> Γ ⊢ app t s :: τ
\end{code}
\begin{code}[hide]
app⇓ {s = x} {f} {A} {B} {Γ} fp xp =
  let

      p06 : Σ $ λ (q : FIR (Γ , f) syn) -> fir q == A ⇒ B
      p06 = checkToSyn fp


      p08 : FIR (Γ , f) (syn ◆ testFunctionType)
      p08 = fst p06 firmap snd p06 eval◆ testFunctionTypeFir

      p09 : FIR (A , B) (λ {(A2 , B2) -> check (Γ , x , A2) >> right B2})
      p09 = B ,fir, cong (_>> right B) (firProof (xp))

      p10 : FIR (Γ , f) (syn ◆ testFunctionType ◆ λ {(A2 , B2) -> check (Γ , x , A2) >> right B2})
      p10 = p08 eval◆ p09

      p11 : FIR (Γ , app f x) syn
      p11 = fir p10 ,fir, firProof p10

  in synToCheck p11

app⇓tl : ∀{m A B} {Γ : Ctx m} -> Γ ⊩ A ⇒ B -> Γ ⊩ A -> Γ ⊩ B
app⇓tl (f , fp) (x , xp) = app f x , app⇓ fp xp
\end{code}
\begin{code}
app⇑ : ∀{s t τ}    -> {Γ : Ctx n}
                   -> Γ ⊢ app t s :: τ
                   -> Σ (λ σ -> (Γ ⊢ t :: σ ⇒ τ) × (Γ ⊢ s :: σ))
\end{code}
\begin{code}[hide]
app⇑ {n} {x} {f} {B} {Γ} p =
  let
      α = λ {(A2 , B2) -> check (Γ , x , A2) >> right B2}

      p00 : Σ (λ (q : FIR (Γ , app f x) syn) -> fir q == B)
      p00 = checkToSyn p

      p01 : FIR (Γ , f) (syn ◆ testFunctionType ◆ α)
      p01 = fir (fst p00) ,fir, firProof (fst p00)

      p02 = snd p00

      p03 , p04 = dosplit◆ (syn ◆ testFunctionType) α p01
      ((A2 , B2) ,fir, p03p) = p03

      p05 , p06 = dosplit◆ syn testFunctionType p03

      ((A2 , B2) , p07) = testFTback p06

      p08 : fir p05 == A2 ⇒ B2
      p08 = p07

      p09 : FIR (Γ , f , A2 ⇒ B2) check
      p09 = (synToCheck p05) firamap (cong (λ ξ -> (Γ , f , ξ)) p08)


      p081 : (Γ , f) & syn ◆ testFunctionType == right (A2 , B2)
      p081 = cong (_>>= testFunctionType) (firProof p05 ∙ cong right p08)

      p11 : FIR (A2 , B2) α
      p11 = firsub {f = syn ◆ testFunctionType} {g = α} (p081) p01

      p11-1 : FIR (Γ , x , A2) (check ◆ (λ _ -> right B2))
      p11-1 = fir p11 ,fir, firProof p11

      p12 , p13 = dosplit◆ check (λ _ -> (right B2)) p11-1

      p13 : right B2 == right (fir p11)
      p13 = firProof p13

      p14 : B2 == B
      p14 = (right-inj p13) ∙ p02

      --------------------------------------

      p15 : FIR (Γ , f , A2 ⇒ B) check
      p15 = p09 firamap (p14 |ctx| (λ ξ -> Γ , f , A2 ⇒ ξ))

  in A2 , p15 , p12


\end{code}
\end{AgdaAlign}

\end{enumerate}
\end{theorem}

\begin{proof}
These statements are proven using the $\AR{FIR}$ type and the related
$\AF{dosplit◆}$ and $\AF{eval◆}$ functions.
\end{proof}

% END MEGA PROOF
%----------------------------------------------------------------------

\noindent
The typing properties of $\lamto$ can now be used to prove further statements,
such as the following.


% ----------------------------------------------------------------------
% -- Type uniqueness


\begin{theorem}
  If a term $t$ is well-typed, then its type is uniquely determined.
\begin{code}
uniqueT : ∀{t τ υ} -> {Γ : Ctx n}  -> (T : Γ ⊢ t :: τ) -> (U : Γ ⊢ t :: υ)
                                   -> τ == υ
\end{code}
\end{theorem}
\begin{code}[hide]
uniqueT {n} {cconst x} {τ} {υ} {Γ} T U = sym (cconst⇑ T) ∙ cconst⇑ U
uniqueT {n} {V x} {τ} {υ} {Γ} T U =
  let
      i , Pi , i=x = V⇑ T
      j , Pj , j=x = V⇑ U

  in (sym Pi) ∙ cong Γ (finEqual2 i j {p = i=x ∙ (sym j=x) }) ∙ Pj
uniqueT {n} {Λ X t} {τ} {υ} {Γ} ΛT ΛU =
  let
      B , T , XB=τ = Λ⇑ ΛT
      C , U , XC=υ = Λ⇑ ΛU

      B=C = uniqueT T U
  in sym XB=τ ∙ cong (X ⇒_) B=C ∙ XC=υ
uniqueT {n} {app f x} {τ} {υ} {Γ} T U =
  let
      B , F₁ , X₁ = app⇑ T
      C , F₂ , X₂ = app⇑ U

      p = uniqueT F₁ F₂

  in cong (⇒2) p
\end{code}


\begin{code}[hide]
ΛT= : ∀{t ρ σ} -> (ρ == σ) -> Λ ρ t == Λ σ t
ΛT= {t} p = cong (λ ξ -> Λ ξ t) p
\end{code}

%----------------------------------------------------------------------
%-- Add Var / Weakening

\section{Weakening}
Given a term $Γ ⊢ t :: τ$, it can be modified to be valid in contexts
which are weaker than $Γ$, that is, contexts which contain additional variables.
Using list operations, such a weakened context is denoted by $(j ↓ σ)\:Γ$,
meaning the context obtained by inserting the type $σ$ at position $j$ into $Γ$.

Considering now the term $t$, we need to update it
accordingly, because the variables which it refers to in $Γ$ have different
indices in $(j ↓ σ)\:Γ$. Concretely, variables $V\:i$ before the point of
insertion ($i < j$) are still correct. But variables with $i ≥ j$
need to skip the type $σ$ at $j$.

In order to implement this, we first define translation of indices.

\begin{code}[hide]
private
  module hidden where
\end{code}

\begin{definition}
  The \textbf{up-translation of an index $i$ at an insertion point $j$} is denoted by $i ↥ j$. Depending on
  whether $i$ comes before or after $j$, it is either kept the same or increased by one.
\begin{code}
    _↥_ : (i j : ℕ) -> ℕ
    _↥_ i j with  compare i j
    ...           | less i<j     = i
    ...           | equal i=j    = (suc i)
    ...           | greater i>j  = (suc i)
\end{code}
\end{definition}

\noindent
This operation can now be extended to terms.

\begin{definition}
  The \textbf{up-translation of a term} is defined by induction. Constant terms are unaffected.
  For variables, the up-translation of indices is used. For lambda abstractions, the term inside
  is translated, but since the lambda introduces a new variable itself, the insertion
  point $j$ has to be incremented. For applications, both the function and its argument
  are translated.
\begin{code}
    _⇈_ : Term -> ℕ -> Term
    _⇈_ (cconst x)  j  = cconst x
    _⇈_ (V i)       j  = V (i ↥ j)
    _⇈_ (Λ σ t)     j = Λ σ (t ⇈ suc j)
    _⇈_ (app f x)   j = app (f ⇈ j) (x ⇈ j)
\end{code}
\end{definition}

\begin{code}[hide]
open import TypeTheory.Lambda.Base
  using (_↥_)
open import TypeTheory.Lambda.Core {param = param}
  using (_⇈_)
\end{code}


%----------------------------------------------------------------------
%-- Weakening helpers


\begin{code}[hide]
choose-Var-proof : ∀{n} {A : Ty} -> (Γ : Ctx n) -> (i : ℕ) -> Γ ⊢ (V i) :: A
                  -> (B : Ty) -> (j : Fin (suc n)) -> (( j ↓ B ) Γ) ⊢ V (i ↥ (⍛ j)) :: A
choose-Var-proof {A = A} Γ i Vi B j =
  let
      i₂ , Γi₂=A , _ = V⇑ Vi
      [j↓B]Γi₂↥j=A = insertLShift Γ j i₂ Γi₂=A B
      Vi↥j = V⇓ [j↓B]Γi₂↥j=A
  in Vi↥j
\end{code}

The operation of up-translating a term is exactly what is needed when
weakening a context. This is stated as a theorem.

\begin{theorem}[Weakening]\label{th:weak}
  For a term $Γ ⊢ t :: τ$, well-typedness in a weakened context $(j ↓ σ)\:Γ$
  is achieved by up-translating $t$ at $j$.
\begin{code}
weak : ∀{τ t}  -> {Γ : Ctx n}
               -> (Γ ⊢ t :: τ)
               -> (σ : Ty) -> (j : Fin (suc n))
               -> (j ↓ σ) Γ ⊢ (t ⇈ ⍛ j) :: τ
\end{code}
\end{theorem}
\begin{code}[hide]
weak {n} {A} {cconst x} {Γ} p B j = cconst⇓ (cconst⇑ p)
weak {n} {A} {V i} {Γ} p B j = choose-Var-proof Γ i p B j
weak {n} {ι x} {Λ ψ t} {Γ} T Z j = ⊥-elim (lambdaNoFunc T)
weak {n} {ψ ⇒ ξ} {Λ τ r} {Γ} ΛR σ j =
  let
      R , ψ=τ = addVarLambda ΛR
      pΓ = sym (funExt (insertLComma Γ j σ))
      -- r₂ = r ⇈ suc (⍛ j)

      σR = weak R σ (fsuc j)
      σR₂ = JmapC pΓ σR

      P = Λ⇓ σR₂

  in Jmapt (ΛT= ψ=τ) P

weak {n} {B} {app f x} {Γ} p Z j =
  let A , p1 , p2 = app⇑ p

      f₂ = f ⇈ ⍛ j
      x₂ = x ⇈ ⍛ j

      p05 : (j ↓ Z) Γ ⊢ f₂ :: A ⇒ B
      p05 = weak p1 Z j

      p07 : (j ↓ Z) Γ ⊢ x₂ :: A
      p07 = weak p2 Z j

  in app⇓ p05 p07

\end{code}

% We extract the case where the insertion is done at the beginning of the list.
% \begin{corollary}
%   Following.
% \begin{code}
% weak₀ : ∀{n A t} -> {Γ : Ctx n} -> (Γ ⊢ t :: A) -> (B : Ty) -> B ,, Γ ⊢ (t ⇈ 0) :: A
% \end{code}
% \end{corollary}
% \begin{proof}
% \leavevmode
% \begin{code}
% weak₀ {A = A} {t} {Γ} T B =
%   let
%       P = weak T B fzero
%       P2 = JmapC ((funExt (insertLZero Γ B))) P

%   in P2
% \end{code}
% \end{proof}




\begin{code}[hide]




--------------------------------------
-- example
⊤-isDisc : isDiscrete ⊤
⊤-isDisc tt tt = yes refl


-- abstract
module _ where
  TisSet : isSet (TypeError + ⊤)
  TisSet = hedberg (Either-isDisc TypeError-isDec ⊤-isDisc)

module _ where
  Jmapt= : ∀{n t u A} -> {Γ : Ctx n} -> (Jt : Γ ⊢ t :: A) -> (Ju : Γ ⊢ u :: A) -> (p : t == u) -> PathP (λ i -> Γ ⊢ p i :: A) Jt Ju
  Jmapt= {n} {t} {u} {A} {Γ} (tt ,fir, tp) (tt ,fir, up) p i = tt ,fir, p3 i
    where



      f : Term -> Either TypeError ⊤
      f x = check (Γ , x , A)

      tpu : f u == right tt
      tpu = subst {P = λ ξ -> f ξ == right tt} (p) tp

      p1 : tpu == up
      p1 = TisSet (f u) (right tt) tpu up


      p3 : PathP (λ i -> f (p i) == right tt) tp up
      p3 = compi (λ ξ -> f ξ == right tt) (p) tp up p1



  JmapT= : ∀{n t τ υ} -> {Γ : Ctx n} -> (Jτ : Γ ⊢ t :: τ) -> (Jυ : Γ ⊢ t :: υ) -> (p : τ == υ) -> PathP (λ i -> Γ ⊢ t :: p i) Jτ Jυ
  JmapT= {n} {t} {τ} {υ} {Γ} (tt ,fir, Jτ) (tt ,fir, Jυ) p i = tt ,fir, p3 i
    where

      f : Ty -> Either TypeError ⊤
      f α = check (Γ , t , α)

      tpu : f υ == right tt
      tpu = subst {P = λ ξ -> f ξ == right tt} (p) Jτ

      p1 : tpu == Jυ
      p1 = TisSet (f υ) (right tt) tpu Jυ

      p3 : PathP (λ i -> f (p i) == right tt) Jτ Jυ
      p3 = compi (λ ξ -> f ξ == right tt) (p) Jτ Jυ p1


  JmapC= : ∀{n t τ} -> {Γ Δ : Ctx n} -> (JΓ : Γ ⊢ t :: τ) -> (JΔ : Δ ⊢ t :: τ) -> (p : Γ == Δ) -> PathP (λ i -> p i ⊢ t :: τ) JΓ JΔ
  JmapC= {n} {t} {τ} {Γ} {Δ} (tt ,fir, JΓ) (tt ,fir, JΔ) p i = tt ,fir, p3 i
    where

      f : Ctx n -> Either TypeError ⊤
      f Ε = check (Ε , t , τ)

      tpu : f Δ == right tt
      tpu = subst {P = λ ξ -> f ξ == right tt} (p) JΓ

      p1 : tpu == JΔ
      p1 = TisSet (f Δ) (right tt) tpu JΔ

      p3 : PathP (λ i -> f (p i) == right tt) JΓ JΔ
      p3 = compi (λ ξ -> f ξ == right tt) (p) JΓ JΔ p1


  Jmapt=tl : ∀{n A} -> {Γ : Ctx n} -> (T : Γ ⊩ A) -> (U : Γ ⊩ A) -> (p : fst T == fst U) -> T == U
  Jmapt=tl {n} {A} {Γ} (t , T) (u , U) p i = p i , Jmapt= T U p i

Jmapt-tl : ∀{n u τ} -> {Γ : Ctx n} -> (T : Γ ⊩ τ) -> (p : fst T == u) -> Γ ⊩ τ
Jmapt-tl {n} {u} {τ} {Γ} (t , T) p = u , Jmapt p T


\end{code}


