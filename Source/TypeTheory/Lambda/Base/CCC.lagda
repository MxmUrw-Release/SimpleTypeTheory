
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base.Import

module TypeTheory.Lambda.Base.CCC where

open import TypeTheory.Lambda.Base.Path
open import TypeTheory.Lambda.Base.Category
open import TypeTheory.Lambda.Base.Basics
  renaming (_×_ to _|×|_)


\end{code}

%----------------------------------------------------------------------
\section{Universal properties}
%----------------------------------------------------------------------

In a category, the objects do not possess any internal structure. Still,
different objects may be characterized by considering what arrows go
into or come out of them.

By requiring the existence of certain unique arrows, the
universal properties of different kinds of objects are formulated.

For example, the universal property of being a product object captures
exactly the usual notions of products (e.g. products of groups or
products of vector spaces).

We will consider three kinds of objects: terminal objects, products and
exponentials.

\subsection*{Terminal object}

\begin{code}[hide]
module _ {i j} (𝒞 : Category i j) where
  open Category 𝒞
\end{code}
\begin{definition}
An object $X$ is \textbf{terminal} if, for every object $A$, there is a unique
arrow $A ⇁ X$.
\begin{code}
  isTerminal : Obj -> 𝒰 (lmax i j)
  isTerminal X = ∀ A -> Σ (λ (h : A ⇁ X) -> Π (λ (k : A ⇁ X) -> h == k))
\end{code}
\end{definition}

\begin{remark}
In this definition we implicitly work inside some category $𝒞$. The ``$Obj$''
and the arrow ``$⇁$'' refer to objects and arrows of this category. Still, when
using the above function, the category has to be explicitly given as an argument.
\end{remark}

\begin{definition}
A category $𝒞$ \textbf{has a terminal object} if there exists an object which is terminal. This object
is called $𝟏$. The unique arrow is called $\AF{!}$, and the proof of uniqueness is called $\AF{!{-}uprop}$.
\begin{code}
record hasTerminal {i j} (𝒞 : Category i j) : 𝒰 (lsuc (lmax i j)) where
  open Category 𝒞
  field
    𝟏            : Obj
    𝟏isTerminal  : isTerminal 𝒞 𝟏

  ! : {X : Obj} -> X ⇁ 𝟏
  ! {X}            = fst (𝟏isTerminal X)

  !-uprop : ∀{X} -> {f : X ⇁ 𝟏} -> ! == f
  !-uprop {X} {f}  = snd (𝟏isTerminal X) f
\end{code}
\end{definition}

\begin{code}[hide]

  !! = !
  T1 = 𝟏
  T1isTerminal = 𝟏isTerminal

\end{code}


\begin{example}
The category $𝐓𝐲𝐩𝐞_ℓ$ has a terminal object. It is $\AD{⊤}$, lifted to the level
$ℓ$ by $\AF{Lift}$. The unique function to $\AD{⊤}$ is the one which ignores
its argument and simply returns $\AF{tt}$.
\begin{code}[hide]
module _ {ℓ} where
  open Category (𝐓𝐲𝐩𝐞 ℓ)
  open hasTerminal
\end{code}
\begin{code}
  Type-hasTerminal                 : hasTerminal (𝐓𝐲𝐩𝐞 ℓ)
  𝟏            (Type-hasTerminal)  = Lift ⊤
  𝟏isTerminal  (Type-hasTerminal)  = λ A -> !₀ , !₀-uprop
    where
        !₀ : {A : Obj} -> (A ⇁ Lift ⊤)
        !₀ = λ _ -> (lift tt)

        createObjectPaths : {A : Obj} -> (g : A -> Lift ⊤) -> (a : A) -> g a == !₀ a
        createObjectPaths g a with (g a)
        ...                      | (lift tt) = refl

        !₀-uprop : {A : Obj} -> (g : A -> Lift ⊤) -> g == !₀
        !₀-uprop g = funExt (createObjectPaths g)
\end{code}
\end{example}

%----------------------------------------------------------------------
\subsection*{Products}
%----------------------------------------------------------------------

\begin{code}[hide]
module _ {i j} (𝒞 : Category i j) where
  open Category 𝒞
\end{code}
In order to define the product of two objects $X$ and $Y$ in a category $𝒞$,
we consider, without explicitly constructing it, another category, where the
objects are wedges to $X$ and $Y$ and the morphisms between them are arrows
which make a certain diagram commute.

\begin{definition}
  A \textbf{wedge} to $X$ and $Y$ is an object $\AFd{wObj}$ together with a pair of arrows to $X$ and $Y$.

  \begin{center}
  \begin{tikzcd}[row sep = tiny]
                                       & X \\
    \AF{wObj} \ar[ur, "wπ₁"] \ar[dr, swap, "wπ₂"] &   \\
                                        & Y
  \end{tikzcd}
  \end{center}

\begin{code}
  record Wedge (X Y : Obj) : 𝒰 (lmax i j) where
    constructor wedge
    field
      wObj  : Obj
      wπ₁   : wObj ⇁ X
      wπ₂   : wObj ⇁ Y
\end{code}
\end{definition}

\begin{definition}
  Given two wedges to $X$ and $Y$, a \textbf{morphism of wedges} between them is
  a morphism $f$ between their objects such that the following diagram commutes.

  \begin{center}
    \begin{tikzcd}[column sep = small]
                                                & X &                 \\
      P \ar[ur, "p₁"] \ar[dr, swap, "p₂"] \ar[rr, "f"] &   & \ar[ul, swap, "q₁"] \ar[dl, "q₂"] Q \\
                                                & Y &
    \end{tikzcd}
  \end{center}

\begin{code}
  WedgeMorph : {X Y : Obj} -> Wedge X Y -> Wedge X Y -> 𝒰 (j)
  WedgeMorph (wedge P p₁ p₂) (wedge Q q₁ q₂)
    = Σ (λ (f : P ⇁ Q) -> (f ◇ q₁ == p₁) |×| (f ◇ q₂ == p₂))
\end{code}
\end{definition}
\begin{remark}
Here, we renamed the product type $\_×\_$ to $\AF{\_|×|\_}$, in order to use this
name for the product object.
\end{remark}

\begin{definition}
  A wedge $Z$ is called the \textbf{product of X with Y} if it is terminal in
  the category of wedges to $X$ and $Y$.

  That is, if for every wedge $A$ there is a unique morphism $h : A ⇁ Z$.
\begin{code}
  isProduct : {X Y : Obj} -> Wedge X Y -> 𝒰 (lmax i j)
  isProduct {X} {Y} Z = ∀ A  -> Σ (λ (h : WedgeMorph A Z)
                             -> Π (λ (k : WedgeMorph A Z)
                             -> fst h == fst k))
\end{code}
\end{definition}

\begin{definition}
A category $𝒞$ \textbf{has all products} if there is a binary operation $\_×\_$ on
objects, together with projection functions $π₁$ and $π₂$, such that for every
pair of objects $X$ and $Y$ the wedge defined by $(X×Y , π₁ , π₂)$ is a product.
\begin{AgdaAlign}
\begin{code}
record hasProducts {ℓ ℓ'} (𝒞 : Category ℓ ℓ') : 𝒰 (lsuc (lmax ℓ ℓ')) where
  open Category 𝒞

  infixr 100 _×_
  field
    _×_         : Obj -> Obj -> Obj
    π₁          : ∀{A B} -> A × B ⇁ A
    π₂          : ∀{A B} -> A × B ⇁ B
    ×isProduct  : ∀{A B} -> isProduct 𝒞 (wedge (A × B) π₁ π₂)
\end{code}
For two arrows $f : A ⇁ B$ and $g : A ⇁ C$, we denote the unique arrow into
$A × B$ by $⟨ f , g ⟩$.
\begin{code}
  ⟨_,_⟩ : {A B C : Obj} -> (A ⇁ B) -> (A ⇁ C) -> (A ⇁ B × C)
  ⟨_,_⟩ {A = A} f g = fst (fst (×isProduct (wedge A f g)))
\end{code}
The proof of its property of being a product is called
$\AF{⟨,⟩{-}prop}$.
\begin{code}
  ⟨,⟩-prop  : ∀{A B C : Obj} -> (f : A ⇁ B) -> (g : A ⇁ C)
            -> (⟨ f , g ⟩ ◇ π₁ == f) |×| (⟨ f , g ⟩ ◇ π₂ == g)
  ⟨,⟩-prop {A} f g = snd (fst (×isProduct (wedge A f g)))
\end{code}
  And the proof of uniqueness is called $\AF{⟨,⟩-uprop}$.
\begin{code}
  ⟨,⟩-uprop  : ∀{A B C : Obj}
             -> {f : A ⇁ B} -> {g : A ⇁ C} -> (h : A ⇁ B × C)
             -> (h ◇ π₁ == f) |×| (h ◇ π₂ == g)
             -> ⟨ f , g ⟩ == h
  ⟨,⟩-uprop  {A} {f = f} {g} h hprop
             = snd (×isProduct (wedge A f g)) (h , hprop)
\end{code}
\end{AgdaAlign}
\end{definition}


\begin{definition}
  For morphisms $f : A ⇁ C$ and $g : B ⇁ D$ we define the \textbf{morphism
    between the products $A × B$ and $C × D$} by:
\begin{code}
  _××_ : ∀{A B C D} -> (A ⇁ C) -> (B ⇁ D) -> (A × B ⇁ C × D)
  _××_ f g = ⟨ π₁ ◇ f , π₂ ◇ g ⟩
\end{code}
\end{definition}
\begin{code}[hide]
  infixr 100 _××_
\end{code}




\begin{code}[hide]


  --------------------------------------
  -- Lemmatas
  ⟨,⟩-comp : ∀{A B C D E} -> (f : A ⇁ B) -> (g : A ⇁ D) -> (h : B ⇁ C) -> (i : D ⇁ E) -> ⟨ f , g ⟩ ◇ (h ×× i) == ⟨ f ◇ h , g ◇ i ⟩
  ⟨,⟩-comp {A} {B} {C} {D} {E} f g h i =
    let
        P1 = ⟨ f , g ⟩ ◇ ⟨ π₁ ◇ h , π₂ ◇ i ⟩ ◇ π₁        ≡⟨ asc ⟨ f , g ⟩ ⟨ π₁ ◇ h , π₂ ◇ i ⟩ π₁ ⟩
             ⟨ f , g ⟩ ◇ (⟨ π₁ ◇ h , π₂ ◇ i ⟩ ◇ π₁)      ≡⟨ fst (⟨,⟩-prop (π₁ ◇ h) (π₂ ◇ i)) |ctx| (⟨ f , g ⟩ ◇_) ⟩
             ⟨ f , g ⟩ ◇ (π₁ ◇ h)                        ≡⟨ sym (asc ⟨ f , g ⟩ π₁ h) ⟩
             ⟨ f , g ⟩ ◇ π₁ ◇ h                          ≡⟨ fst (⟨,⟩-prop f g) |ctx| (_◇ h) ⟩
             f ◇ h                                       ∎


        P2 = ⟨ f , g ⟩ ◇ ⟨ π₁ ◇ h , π₂ ◇ i ⟩ ◇ π₂        ≡⟨ asc ⟨ f , g ⟩ ⟨ π₁ ◇ h , π₂ ◇ i ⟩ π₂ ⟩
             ⟨ f , g ⟩ ◇ (⟨ π₁ ◇ h , π₂ ◇ i ⟩ ◇ π₂)      ≡⟨ snd (⟨,⟩-prop (π₁ ◇ h) (π₂ ◇ i)) |ctx| (⟨ f , g ⟩ ◇_) ⟩
             ⟨ f , g ⟩ ◇ (π₂ ◇ i)                        ≡⟨ sym (asc ⟨ f , g ⟩ π₂ i) ⟩
             ⟨ f , g ⟩ ◇ π₂ ◇ i                          ≡⟨ snd (⟨,⟩-prop f g) |ctx| (_◇ i) ⟩
             g ◇ i                                       ∎

    in sym (⟨,⟩-uprop (⟨ f , g ⟩ ◇ (h ×× i)) (P1 , P2))

  ××-comp : ∀{X A B C D E} -> (f : A ⇁ B) -> (g : X ⇁ D) -> (h : B ⇁ C) -> (i : D ⇁ E) -> (f ×× g) ◇ (h ×× i) == (f ◇ h) ×× (g ◇ i)
  ××-comp {X} {A} {B} {C} {D} {E} f g h i =
    let
        P = (f ×× g) ◇ (h ×× i)             ≡⟨ ⟨,⟩-comp (π₁ ◇ f) (π₂ ◇ g) h i ⟩
            ⟨ π₁ ◇ f ◇ h , π₂ ◇ g ◇ i ⟩     ≡⟨ (asc π₁ f h) |ctx| ⟨_, π₂ ◇ g ◇ i ⟩ ⟩
            ⟨ π₁ ◇ (f ◇ h) , π₂ ◇ g ◇ i ⟩   ≡⟨ (asc π₂ g i) |ctx| ⟨ π₁ ◇ (f ◇ h) ,_⟩ ⟩
            ⟨ π₁ ◇ (f ◇ h) , π₂ ◇ (g ◇ i) ⟩ ∎
    in P

  ××-id : ∀{A B} -> id {A} ×× id {B} == id
  ××-id {A} {B} =
    let
        P1 = id {A × B} ◇ π₁  ≡⟨ unit-l π₁ ⟩
             π₁              ≡⟨ sym (unit-r π₁) ⟩
             π₁ ◇ id {A}      ∎

        P2 = id {A × B} ◇ π₂  ≡⟨ unit-l π₂ ⟩
             π₂              ≡⟨ sym (unit-r π₂) ⟩
             π₂ ◇ id {B}      ∎

    in ⟨,⟩-uprop id (P1 , P2)

  ⟨,⟩-id : ∀{A B} -> ⟨ π₁ , π₂ ⟩ == id {A × B}
  ⟨,⟩-id = ⟨,⟩-uprop id (unit-l π₁ , unit-l π₂)

  comp-⟨,⟩ : ∀{A B C D} -> (f : A ⇁ B) -> (g : B ⇁ C) -> (h : B ⇁ D) -> f ◇ ⟨ g , h ⟩ == ⟨ f ◇ g , f ◇ h ⟩
  comp-⟨,⟩ f g h =
    let
        P1 = f ◇ ⟨ g , h ⟩ ◇ π₁        ≡⟨ asc f ⟨ g , h ⟩ π₁ ⟩
             f ◇ (⟨ g , h ⟩ ◇ π₁)      ≡⟨ fst (⟨,⟩-prop g h) |ctx| (f ◇_) ⟩
             f ◇ g                     ∎

        P2 = f ◇ ⟨ g , h ⟩ ◇ π₂        ≡⟨ asc f ⟨ g , h ⟩ π₂ ⟩
             f ◇ (⟨ g , h ⟩ ◇ π₂)      ≡⟨ snd (⟨,⟩-prop g h) |ctx| (f ◇_) ⟩
             f ◇ h                     ∎

    in sym (⟨,⟩-uprop (f ◇ ⟨ g , h ⟩) (P1 , P2))



\end{code}


\begin{example}
The category $𝐓𝐲𝐩𝐞_ℓ$ has products. They are given by the product type
$\AF{\_|×|\_}$ together with the projections $\AF{fst}$ and $\AF{snd}$.
\begin{code}[hide]
module _ {ℓ} where
  open Category (𝐓𝐲𝐩𝐞 ℓ)
  open hasProducts
\end{code}
\begin{code}
  Type-hasProducts                 : hasProducts (𝐓𝐲𝐩𝐞 ℓ)
  _×_            (Type-hasProducts)  = _|×|_
  π₁             (Type-hasProducts)  = fst
  π₂             (Type-hasProducts)  = snd
  ×isProduct     (Type-hasProducts) {X} {Y} (wedge A a₁ a₂) =
    let
        h : A -> X |×| Y
        h a = a₁ a , a₂ a

        H : WedgeMorph (𝐓𝐲𝐩𝐞 ℓ) (wedge A a₁ a₂) (wedge (X |×| Y) fst snd)
        H = h , (refl , refl)

        proof : ∀ K -> fst H == fst K
        proof K 𝒊 a = (fst (snd K) (~ 𝒊) a , snd (snd K) (~ 𝒊) a)

    in H , proof
\end{code}
\end{example}



%----------------------------------------------------------------------
\subsection*{Exponentials}
%----------------------------------------------------------------------

In the category $𝐓𝐲𝐩𝐞_ℓ$ we have the special case that the type of
morphisms between two objects $X\:Y : 𝒰_ℓ$ is itself a type $X \to Y : 𝒰_ℓ$, and
thus an object of $𝐓𝐲𝐩𝐞_ℓ$.
The same happens in $\textbf{Set}$, where the functions from $X$ to $Y$ form a
set, sometimes being denoted by $\fexp{Y}{X}$. 

Unlike product objects, such exponential objects are not as widespread. For example,
in $\textbf{Grp}$, the group homomorphisms between two groups do not
necessarily form a group themselves.

In order to define the property of an object being \textit{like morphisms from $X$ to
$Y$}, we consider the category of evaluation structures between $X$ and $Y$.
(Again, without an explicit construction.)

\begin{code}[hide]
module _ {ℓ ℓ'} (𝒞 : Category ℓ ℓ') (Products : hasProducts 𝒞) where
  open Category 𝒞
  open hasProducts Products
\end{code}

\begin{definition}
  An \textbf{evaluation structure between $X$ and $Y$} is an object $\AFd{eObj}$ together
  with an evaluation map $\AFd{eEv}$ for it.
\begin{code}
  record Eval (X Y : Obj) : 𝒰 (lmax ℓ ℓ') where
    constructor eval
    field
      eObj  : Obj
      eEv   : eObj × X ⇁ Y
\end{code}
\end{definition}

\begin{definition}
  A \textbf{morphism of evaluation structures between $X$ and $Y$} is given by a morphism $f$
  between their objects which makes the following diagram commute.

  \[
    \begin{tikzcd}
      A × X \ar[rd, "a"] \ar[dd, swap, "f ×× \AF{id}"] &   \\
                                            & Y \\
      B × X \ar[ru, swap, "b"]                    &
    \end{tikzcd}
  \]
  
\begin{code}
  EvalMorphism : {X Y : Obj} -> Eval X Y -> Eval X Y -> 𝒰 ℓ'
  EvalMorphism (eval A a) (eval B b) = Σ (λ (f : A ⇁ B) -> (f ×× id) ◇ b == a)
\end{code}
\end{definition}

\begin{definition}
  An evaluation structure $Z$ between $X$ and $Y$ is called the \textbf{exponential object of $Y$
  with $X$} if it is terminal in the category of evaluation structures.

  That is, if for every evaluation structure $A$ there exists a unique morphism from $A$ to $Z$.
\begin{code}
  isExp : {X Y : Obj} -> Eval X Y -> 𝒰 (lmax ℓ ℓ')
  isExp Z = ∀ A ->  Σ (λ (h : EvalMorphism A Z)
                ->  Π (λ (k : EvalMorphism A Z)
                ->  fst h == fst k))
\end{code}
\end{definition}


\begin{definition}
  A category $𝒞$ \textbf{has exponentials} if there is a binary operation on objects $\AFd{\_\widehat{\ }\_}$,
  and for every pair of objects $X$ and $Y$, an evaluation map for $Y \ehat X$, such that the resulting
  evaluation structure is the exponential object of $Y$ with $X$.
\begin{AgdaAlign}
\begin{code}
record hasExponentials  {ℓ ℓ'} (𝒞 : Category ℓ ℓ') (Products : hasProducts 𝒞)
                        : 𝒰 (lsuc (lmax ℓ ℓ')) where
  open Category 𝒞
  open hasProducts Products

  field
    _^_     : Obj -> Obj -> Obj
    ev      : ∀{X Y} -> X ^ Y × Y ⇁ X
    ^isExp  : ∀{X Y} -> isExp 𝒞 Products (eval (X ^ Y) ev)
\end{code}
For an arrow $f : A × Y ⇁ X$, the operation of getting the unique arrow $A ⇁ X
\ehat Y$ is called currying.
\begin{code}
  curry : {A X Y : Obj} -> (A × Y ⇁ X) -> (A ⇁ X ^ Y)
  curry {A} f = fst (fst (^isExp (eval A f)))
\end{code}
The proofs of being a morphism of evaluation structures and of uniqueness are
called $\AF{curry{-}prop}$ and $\AF{curry{-}uprop}$ respectively.
\begin{code}
  curry-prop  : {A X Y : Obj}
              -> (f : A × Y ⇁ X)
              -> (curry f ×× id) ◇ ev == f
  curry-prop {A} f = snd (fst (^isExp (eval A f)))

  curry-uprop  : {A X Y : Obj}
               -> {f : A × Y ⇁ X} -> (g : A ⇁ X ^ Y)
               -> (g ×× id) ◇ ev == f
               -> curry f == g
  curry-uprop {A} {X} {Y} {f} g p = snd (^isExp (eval A f)) (g , p)
\end{code}
\end{AgdaAlign}
\end{definition}

\begin{code}[hide]
  curry-comp : ∀{A B C D} -> (f : A ⇁ B) -> (g : B × C ⇁ D) -> curry ((f ×× id) ◇ g) == f ◇ curry g
  curry-comp {A} {B} {C} {D} f g =
    let

        P = ((f ◇ curry g) ×× id) ◇ ev           ≡⟨ sym (unit-l id) |ctx| (λ ξ -> ((f ◇ curry g) ×× ξ) ◇ ev) ⟩
            ((f ◇ curry g) ×× (id ◇ id)) ◇ ev     ≡⟨ sym (××-comp f id (curry g) id) |ctx| (_◇ ev) ⟩
            (f ×× id) ◇ (curry g ×× id) ◇ ev      ≡⟨ asc (f ×× id) (curry g ×× id) ev ⟩
            (f ×× id) ◇ ((curry g ×× id) ◇ ev)    ≡⟨ curry-prop g |ctx| ((f ×× id) ◇_) ⟩
            (f ×× id) ◇ g                        ∎

    in curry-uprop (f ◇ curry g) P


  infixl 130 _^_
\end{code}



\begin{example}
\begin{code}[hide]
module _ {ℓ} where
  open Category (𝐓𝐲𝐩𝐞 ℓ)
  open hasProducts (Type-hasProducts {ℓ})
  open hasExponentials
\end{code}
The category $𝐓𝐲𝐩𝐞_ℓ$ has exponential objects. For two types $B$ and $A$, they are given by the
function type $A \to B$.

We first define the evaluation function $\AF{ev₀}$, which applies an argument to a function.
\begin{code}
  ev₀ : {A B : 𝒰 ℓ} -> ((A -> B) × A) -> B
  ev₀ (f , x) = f x
\end{code}

Now we can prove that, indeed, all exponential objects exist. Currying is done by waiting for two
arguments, and then combining them into a tuple. The $\AF{curry{-}prop}$ is
trivially true. Uniqueness follows from the property of morphisms of
evaluation structures.

\newpage
\begin{code}
  Type-hasExponentials : hasExponentials (𝐓𝐲𝐩𝐞 ℓ) (Type-hasProducts)
  _^_     Type-hasExponentials = λ B A -> (A -> B)
  ev      Type-hasExponentials = ev₀
  ^isExp  Type-hasExponentials
          = λ {(eval A f) -> ((curry₀ f , curry-prop₀ f) , curry-uprop₀)}
    where
      curry₀ : ∀{A B C} -> (A × B -> C) -> A -> (B -> C)
      curry₀ f = λ a b -> f (a , b)

      curry-prop₀ : ∀{A B C} -> (f : A × B -> C) -> (curry₀ f ×× id) ◇ ev₀ == f
      curry-prop₀ f = refl

      curry-uprop₀  : ∀{A B C} -> {f : A × B -> C}
                    -> (k : EvalMorphism  (𝐓𝐲𝐩𝐞 ℓ) (Type-hasProducts)
                                          (eval A f) (eval (B -> C) ev₀))
                    -> (curry₀ f == fst k)
      curry-uprop₀ {f = f} k 𝒊 a b = snd k (~ 𝒊) (a , b)
\end{code}
\end{example}


%----------------------------------------------------------------------
\section{Cartesian closed categories}
%----------------------------------------------------------------------

We have now explored exactly the kinds of objects which will be of further
interest to us when we are going to provide a model for the lambda calculus.

\medskip

\noindent
There is a special term for referring to such categories:

\begin{definition}
A category $𝒞$ is called \textbf{cartesian closed} (short: it is a CCC) if it has a terminal object,
all products and all exponentials.
\begin{code}
record isCCC {i j : ULevel} (𝒞 : Category i j) : 𝒰 (lsucc (lmax i j)) where
  field
    Terminal      : hasTerminal 𝒞
    Products      : hasProducts 𝒞
    Exponentials  : hasExponentials 𝒞 Products
\end{code}
\end{definition}

\noindent
Combining the previous examples, we can show:

\begin{example}
\begin{code}[hide]
module _ {ℓ} where
  open Category (𝐓𝐲𝐩𝐞 ℓ)
  open hasProducts
  open hasExponentials
  open isCCC
\end{code}
  The category $𝐓𝐲𝐩𝐞_ℓ$ is cartesian closed.
\begin{code}
  Type-isCCC : isCCC (𝐓𝐲𝐩𝐞 ℓ)
  Terminal      Type-isCCC = Type-hasTerminal
  Products      Type-isCCC = Type-hasProducts
  Exponentials  Type-isCCC = Type-hasExponentials
\end{code}
\end{example}

