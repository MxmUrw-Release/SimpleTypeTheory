
\begin{code}[hide]

{-# OPTIONS --cubical #-}

open import TypeTheory.Lambda.Base.Import

module TypeTheory.Lambda.Base.Category where

\end{code}


\section{What is a category?}
When studying different mathematical objects,
a common pattern on what such theories are made of emerges:
A mathematical structure is being accompanied by a notion of morphisms.

Examples may be found in different fields: in Algebra, where groups, rings,
fields are studied, each structure comes with the definition of an appropriate,
structure preserving homomorphism. In Linear Algebra, the morphisms between
vector spaces are called linear maps. In Topology, topological spaces have
continuous functions as morphisms between them, and in Analysis, there are
smooth functions between smooth manifolds.

\medskip

These morphisms, even though very different in their detailed definitions, have
something in common: they all behave like functions - in so far that they have
the following properties:
\begin{enumerate}
\item Composition: Morphisms with matching domain and codomain may be composed.
\item Identity: There is a morphism which behaves like the identity function.
\end{enumerate}

In category theory, we study the case of having objects of a certain kind and
morphisms behaving like functions between them. In order to do this, we consider all those
objects and morphisms between them as a single structure, and call such a
structure a category.

\medskip

This means that, for example, there is the category \textbf{Grp} of
groups and group homomorphisms. Similarly there are the categories $\symbf{Ring}$, $\symbf{Fld}$,
\textbf{Top} and \textbf{Diff} \citep{nlab:database_of_categories}. And, as the archetypal category, there is
\textbf{Set}, the category of sets and functions between them. 

\medskip

For introductory texts on category theory, see e.g.\ \citet{Awodey:2010} or
\citet{Smith:2018}. The definitions in this chapter are based on
the definitions found there.

\begin{definition}
  A \textbf{category} is given by:
  \begin{enumerate}
  \item A type of objects $\AFd{Obj}$, and for every two objects $A\:B : \AFd{Obj}$, a type of
    morphisms $\AFd{Hom}\:A\:B$.
  \item An identity morphism $\AFd{id}$, and a composition operation $\AFd{\_◇\_}$.
  \item Proofs  that the identity morphism is a left and right identity (unit) 
    and that composition is associative.
  \end{enumerate}
  We formalize this as a record:
\begin{code}
record Category (ℓ ℓ' : ULevel) : 𝒰 (lsucc (lmax ℓ ℓ')) where
  field
    Obj     : 𝒰 ℓ
    Hom     : Obj -> Obj -> 𝒰 ℓ'

    id      : ∀{A} -> Hom A A
    _◇_     : ∀{A B C} -> Hom A B -> Hom B C -> Hom A C

    unit-l  : ∀{A B} -> (f : Hom A B) -> id ◇ f == f
    unit-r  : ∀{A B} -> (f : Hom A B) -> f ◇ id == f
    asc     : ∀{A B C D}
              -> (f : Hom A B) -> (g : Hom B C) -> (h : Hom C D)
              -> (f ◇ g) ◇ h == f ◇ (g ◇ h)
\end{code}
\end{definition}

\begin{remark}
  Usually, the composition operation is defined to compose backwards, like
  function composition does. In order to be more consistent with
  diagrams, we choose forward composition and denote it by $\AF{\_◇\_}$,
  instead of $\AF{\_∘\_}$.
\end{remark}

\begin{notation}
The morphisms between objects are also called arrows.
We write this type as follows.
\begin{code}
  _⇁_ : Obj -> Obj -> 𝒰 ℓ'
  A ⇁ B = Hom A B
\end{code}
\end{notation}

\begin{code}[hide]
  infixl 80 _◇_
  infixr 70 _⇁_
\end{code}

\begin{example}
For every universe level $ℓ$, the types and functions between them form a category.
\begin{code}
open Category
𝐓𝐲𝐩𝐞 : ∀ ℓ -> Category (lsuc ℓ) ℓ
Obj     (𝐓𝐲𝐩𝐞 ℓ) = 𝒰 ℓ
Hom     (𝐓𝐲𝐩𝐞 ℓ) = λ A B -> (A -> B)
id      (𝐓𝐲𝐩𝐞 ℓ) = idf
(_◇_)   (𝐓𝐲𝐩𝐞 ℓ) = λ f g -> g ∘ f
unit-l  (𝐓𝐲𝐩𝐞 ℓ) = λ _ -> refl
unit-r  (𝐓𝐲𝐩𝐞 ℓ) = λ _ -> refl
asc     (𝐓𝐲𝐩𝐞 ℓ) = λ _ _ _ -> refl
\end{code}
\end{example}

\begin{remark}[Diagrams]
  Often it is helpful to visualize configurations of arrows by drawing diagrams:
  \[
    \begin{tikzcd}
      A \ar[r, "f"] \ar[d, "h"] & B \ar[d, "g"] \\
      C \ar[r, "i"]             & D
    \end{tikzcd}
  \]
  Such a diagram is said to \textbf{commute}, if, whereever possible, different paths from one object to another
  are equal. In this case, $f ◇ g = h ◇ i$ must hold.
\end{remark}
