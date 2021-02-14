
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Fir where


open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.Basics
open import TypeTheory.Lambda.Base.Path
open import TypeTheory.Lambda.Base.Either
-- open TypeNotation hiding (_×_)

\end{code}


\medskip

Our use-case of these potentially failing functions is the implementation
of the typechecker. But having implemented it, we will also need to prove
properties about its behaviour. In order to be able to do this, we introduce
a type called $\AR{FIR}$ (``function is right''). An element of $\AR{FIR}\:a\:f$
proofs that the function $f$ succeeds when given the argument $a$.

\begin{definition}
  The type $\AR{FIR}$ is implemented by the following record:
\begin{code}
record FIR {A B X : 𝒰₀} (a : A) (f : A -> X + B) : 𝒰₀ where
  constructor _,fir,_
  field
    fir : B
    firProof : f a == right fir
\end{code}
\end{definition}

It is useful in the following way: We can define a function $\AF{dosplit◆}$,
which, given a proof that the composition $f\:\AF{>=>}\:g$ succeeds, returns seperate
proofs for $\AR{FIR}\:a\:f$ and $\AR{FIR}\:b\:g$. Similarly, we define a function
\AF{eval◆} for joining both proofs back together.


\begin{code}[hide]
open FIR public

module _ {X : 𝒰₀} where

  Er : 𝒰₀ -> 𝒰₀
  Er = X +_




  record FirMor {A B : 𝒰₀} {f : A -> Er B} {a : A} (p q : FIR a f) : 𝒰₀ where
    constructor firmor
    field
      fireq : fir p == fir q

  open FirMor public


  ~~ : ∀{A B : 𝒰₀} {f : A -> B} {a : A} -> FIR a (right {A = X} ∘ f)
  ~~ {f = f} {a = a} = f a ,fir, refl

  infixl 50 _◆_
  _◆_ : ∀{A B C : 𝒰₀} -> (f : A -> Er B) -> (g : B -> Er C) -> A -> Er C
  f ◆ g = λ a -> f a >>= g





  --------------------------------------
  -- Evaluation


  infixl 50 _eval◆_
  _eval◆_ : ∀{A B C : 𝒰₀} -> {a : A} -> {f : A -> Er B} -> {g : B -> Er C}
            -> (p : FIR a f) -> (q : FIR (fir p) g)
            -> FIR a (f ◆ g)
  _eval◆_ {g = g} (p ,fir, pp) (q ,fir, qq) = (q) ,fir, (cong (λ ξ -> ξ >>= (λ x -> g x)) pp) ∙ qq


  --------------------------------------
  -- Map


  infixl 50 _firmap_
  _firmap_ : ∀{A B : 𝒰₀} -> {a : A} {b : B} -> {f : A -> Er B}
              -> (p : FIR a f) -> (q : fir p == b) -> FIR a f
  _firmap_ {b = b} (p ,fir, pp) q = b ,fir, pp ∙ cong right q


  infixl 50 _firamap_
  _firamap_ : ∀{A B : 𝒰₀} -> {a : A} {a' : A} -> {f : A -> Er B}
            -> (p : FIR a f) -> (q : a == a') -> FIR a' f
  _firamap_ {a' = a'} {f} (p ,fir, pp) q = p ,fir, subst {P = λ ξ -> f ξ == right p} q pp


  --------------------------------------
  -- Right Split
  firsub : ∀{A B C : 𝒰₀} -> {a : A} {x : B} -> {f : A -> Er B} {g : B -> Er C}
           -> (q : f a == right x) -> (p : FIR a (f ◆ g)) ->  FIR x g
  firsub {a = a} {x} {f} {g} q (p ,fir, pp) = p ,fir, subst {P = λ ξ -> (ξ >>= g) == right p} (q) (pp)

  --------------------------------------
  -- Morphisms

  private
    diassoc' : {A B C D : 𝒰₀} -> (f : A -> Er B) -> (g : B -> Er C) -> (h : C -> Er D)
               -> (a : A) -> a & (f ◆ g) ◆ h == a & f ◆ (g ◆ h)
    diassoc' f g h a with f a
    ...  | left x = refl
    ...  | right y = refl

  diassoc : {A B C D : 𝒰₀} -> (f : A -> Er B) -> (g : B -> Er C) -> (h : C -> Er D) -> (f ◆ g) ◆ h == f ◆ (g ◆ h)
  diassoc {A} {B} {C} {D} f g h = funExt (diassoc' f g h)

  firfmap : {A B : 𝒰₀} -> {a : A} -> {f g : A -> Er B} -> (p : f == g) -> FIR a f -> FIR a g
  firfmap {a = a} {f} {g} p (q ,fir, qq) = q ,fir, cong (_$ a) (sym p) ∙ qq




  --------------------------------------
  -- Splitting

  mustBeRight : ∀{A B : 𝒰₀} -> (x : Er A) -> {f : A -> Er B} -> {z : B} -> ((x >>= f) == right z) -> Σ (λ y -> x == right y)
  mustBeRight (left x) p = ⊥-elim ((subst {P = case-right} (sym p) tt))
  mustBeRight (right x) p = x , refl

  record Split◆1 {A B C : 𝒰₀} (a : A) (f : A -> Er B) (g : B -> Er C) (c : C) : 𝒰₀ where
    constructor split◆
    field
      -sb- : B
      a-sb : f a == right -sb-
      sb-c : g -sb- == right c

  Split◆ : {A B C : 𝒰₀} -> (a : A) (f : A -> Er B) (g : B -> Er C) -> 𝒰₀
  Split◆ a f g = Σ $ λ (p : FIR a f) -> FIR (fir p) g

  dosplit◆1 : ∀{A B C : 𝒰₀} -> {a : A} -> (f : A -> Er B) -> (g : B -> Er C) -> {c : C}
             -> a & (f ◆ g) == right c -> Split◆1 a f g c
  dosplit◆1 {A} {B} {C} {a} f g {c} p with mustBeRight (f a) p
  ...    | (b , a-b) = split◆ b a-b (subst {P = λ x -> ((x >>= g) == right c)} a-b p)

  dosplit◆ : ∀{A B C : 𝒰₀} -> {a : A} -> (f : A -> Er B) -> (g : B -> Er C)
           -> FIR a (f ◆ g) -> Split◆ a f g
  dosplit◆ {A} {B} {C} {a} f g p with mustBeRight (f a) (firProof p)
  ...    | (b , a-b) = b ,fir, a-b , (fir p) ,fir, (subst {P = λ x -> ((x >>= g) == right (fir p))} a-b (firProof p))


  dosplit◆2 : ∀{A B C D : 𝒰₀} -> {a : A} -> (f : A -> Er B) -> (g : B -> Er C) -> (h : C -> Er D)
            -> FIR a (f ◆ g ◆ h) -> Split◆ a f (g ◆ h)
  dosplit◆2 {a = a} f g h p =
    let fg' , h' = dosplit◆ (f ◆ g) h p
        f'  , g' = dosplit◆ f g fg'
    in  f' , (g' eval◆ h')


  dosplit◆3 : ∀{A B C D E : 𝒰₀} -> {a : A}
            -> (f : A -> Er B) -> (g : B -> Er C) -> (h : C -> Er D) -> (i : D -> Er E)
            -> FIR a (f ◆ g ◆ h ◆ i) -> Split◆ a f (g ◆ h ◆ i)
  dosplit◆3 f g h i fghi =
    let fg' , hi' = dosplit◆2 (f ◆ g) h i fghi
        f'  , g'  = dosplit◆ f g fg'
        h'  , i'  = dosplit◆ h i hi'
    in  f' , (g' eval◆ h' eval◆ i')



  -- dosplit⟨⟩ : ∀{A B C D : 𝒰₀} -> {ab : A × B} -> (f : A -> Er C) -> (g : B -> Er D)
  --           -> FIR ab ⟨ f , g ⟩ -> FIR (fst ab) f × FIR (snd ab) g
  -- dosplit⟨⟩ {C = C} {ab = (a , b)} f g ((c , d) ,fir, p) =
  --   let q , qq = mustBeRight (f a) p

  --       nnn : (g b >>= (λ b' -> right (q , b'))) == right (q , d)
  --       nnn = subst {P = λ (ξ : Er C) -> (ξ >>= (λ a' -> g b >>= (λ b' -> right (a' , b')))) == right (q , d)} (qq) {!!}

  --       r , rr = mustBeRight (g b) (nnn)
  --   in           q ,fir, qq , r ,fir, rr




  -- record Split* {A B C : 𝒰₀} (a : A) (f : A -> Er B) (g : A -> Er C) (z : B × C) : 𝒰₀ where
  --   constructor split*
  --   field
  --     *b : f a == right (fst z)
  --     *c : g a == right (snd z)

  -- dosplit* : ∀{A B C : 𝒰₀} -> {a : A} -> (f : A -> Er B) -> (g : A -> Er C) -> {c : B × C} -> a & (f * g) == right c -> Split* a f g c
  -- dosplit* {A} {B} {C} {a} f g {(b , c)} p with f a
  -- dosplit* {A} {B} {C} {a} f g {(b , c)} p | left x = ⊥-elim $ leftNotRight p
  -- dosplit* {A} {B} {C} {a} f g {(b , c)} p | right x with g a
  -- dosplit* {A} {B} {C} {a} f g {b , c} p | right x | left x₁ = {!!}
  -- dosplit* {A} {B} {C} {a} f g {b , c} p | right x | right x₁ = split* {!!} {!!} 



  --------------------------------------
  -- Bypass
  -- bypassFst : ∀{A B C : 𝒰₀} -> {a : A} -> {c : C} -> (f : A -> Er B)
  --           -> FIR (a , c) ⟨ f , right ⟩
  --           -> FIR (a , c) ⟨ f , right ⟩
  -- bypassFst {B = B} {a = a} {c = c} (f) fr' =
  --   let (b ,fir, pb) , (c2 ,fir, c2p) = dosplit⟨⟩ f right fr'

  --   in  (b , c) ,fir, cong (λ (ξ : Er B) -> ξ >>= (λ a' -> right (a' , c))) pb


  -- getRight : ∀{B} -> B -> Er B -> B
  -- getRight b (left _ ) = b
  -- getRight b (right x) = x

  -- bypassFstMor : ∀{A B C : 𝒰₀} -> {a : A} -> {c : C} -> (f : A -> Er B)
  --              -> (p : FIR (a , c) ⟨ f , right ⟩)
  --              -> FirMor p (bypassFst f p)
  -- bypassFstMor {B = B} {a = a} {c = c} f p =
  --   let (b ,fir, pb) , (c2 ,fir, c2p) = dosplit⟨⟩ f right p


  --       bla : fir p == (b , c)
  --       bla = {!!} -- cong (λ ξ -> (b , ξ)) $ cong (getRight c) $ (sym c2p) -- cong (getRight (b , c)) $ cong (λ (ξ : Er B) -> ξ >>= (λ a' -> right (a' , c))) (sym pb)

  --   in  firmor bla -- (b , c) ,fir, cong (λ (ξ : Er B) -> ξ >>= (λ a' -> right (a' , c))) pb




\end{code}
