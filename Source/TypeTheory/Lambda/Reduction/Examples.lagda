
\section{Example: Church numerals}

\begin{code}[hide]
{-# OPTIONS --cubical  #-}

open import TypeTheory.Lambda.Base hiding (_$_)
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Reduction.Examples {i j} where
\end{code}


As an example of working in $\lamto$, we present a small formalization of
natural numbers, using \textit{Church numerals} \citep{Selinger:Lambda}.

We choose $\AD{Bool}$ as the type of ground types and also as the type of
constants, mapped via the identity function.
\begin{code}
param : LambdaParam i j
param = lambdaParam Bool Bool-isDisc Bool idf
\end{code}

\begin{code}[hide]
open import TypeTheory.Lambda.Core {param = param} hiding (_$$_)
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction.NormalFormProofs {param = param}
\end{code}

\noindent
We call the two resulting types $α$ and $β$, and their only terms $a$ and $b$ respectively.
\begin{code}
α β : Ty
α = ι true
β = ι false

a b : Term
a = cconst true
b = cconst false
\end{code}

\noindent
For better legibility when constructing terms, we introduce the following notation:
\begin{code}
_⇨_   = Λ
_$_   = app
\end{code}
Since the normalization algorithm only works on well-typed terms, we do not work directly
with terms, but with proofs of their well-typedness. Therefore, we also introduce a shorter
notation for applying a well-typed function to a well-typed term:
\begin{code}
_#_   = app⇓
\end{code}
Now the identity function on $α$ can be written as follows:
\begin{code}
idα : [] ⊢ α ⇨ V 0 :: α ⇒ α
idα = tt ,fir, refl
\end{code}
And, given a well-typed constant $\AF{aa}$:
\begin{code}
aa : [] ⊢ a :: α
aa = tt ,fir, refl
\end{code}
We can show that applying the identity function to it does nothing:
\begin{code}
th1 : idα # aa =β= aa
th1 = refl
\end{code}

\begin{code}[hide]
infixr 50 _⇨_
infixl 60 _$_
infixl 60 _#_
\end{code}

The natural numbers are defined as higher order functions. The $n$-th numeral is
encoded as the function which maps a function $f$ to its $n$-times repeated composition
with itself, $f \mapsto \fexp{f}{n}$. We call this type $\AF{NN}$.
\begin{code}
NN : Ty
NN = (α ⇒ α) ⇒ (α ⇒ α)
\end{code}
The first 4 natural numbers are defined as follows:
\begin{code}
n0 : [] ⊢ (α ⇒ α) ⇨ (α) ⇨ V 0 :: NN
n1 : [] ⊢ (α ⇒ α) ⇨ (α) ⇨ V 1 $ V 0 :: NN
n2 : [] ⊢ (α ⇒ α) ⇨ (α) ⇨ V 1 $ (V 1 $ V 0) :: NN
n3 : [] ⊢ (α ⇒ α) ⇨ (α) ⇨ V 1 $ (V 1 $ (V 1 $ V 0)) :: NN
\end{code}
They all typecheck correctly:
\begin{code}
n0 = tt ,fir, refl
n1 = tt ,fir, refl
n2 = tt ,fir, refl
n3 = tt ,fir, refl
\end{code}
We can define a successor function:
\begin{code}
nsuc : [] ⊢ NN ⇨ (α ⇒ α) ⇨ α ⇨ V 1 $ (V 2 $ V 1 $ V 0) :: NN ⇒ NN
nsuc = tt ,fir, refl
\end{code}
And check that $\AF{suc}(\AF{suc}\:0) = 2$.
\begin{code}
th2 : nsuc # (nsuc # n0) =β= n2
th2 = refl
\end{code}
We can also define addition and multiplication:
\begin{code}
++ : []  ⊢   NN ⇨  NN ⇨  (α ⇒ α) ⇨ α ⇨ (V 3 $ V 1) $ (V 2 $ V 1 $ V 0)
         ::  NN ⇒  NN ⇒  NN
++ = tt ,fir, refl

** : []  ⊢   NN ⇨  NN ⇨  (α ⇒ α) ⇨ α ⇨ (V 3 $ (V 2 $ V 1) $ V 0)
         ::  NN ⇒  NN ⇒  NN
** = tt ,fir, refl
\end{code}
And test their properties.
\begin{code}
th3 : (++ # n1 # n2) =β= n3
th3 = refl

th4 : (** # n0 # n1) =β= n0
th4 = refl

th5 : (** # n2 # n3) =β= (++ # n3 # n3)
th5 = refl
\end{code}

\begin{code}[hide]
nnor = nor
\end{code}

\begin{remark}
Here, $\AF{\#}$ is used to apply the functions $\AF{++}$ and $\AF{**}$ to two
arguments.
\end{remark}

All of these correct statements typecheck, while false propositions would not.
This shows that $\lamto$ is powerful enough to encode basic arithmetic.


