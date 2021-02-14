
\begin{code}[hide]

{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Introduction.Introduction where

open import TypeTheory.Lambda.Base.Import
  hiding (Bool ; ⊤ ; ⊥ ; _+_ ; _∧_ ; ℕ ; Π ; Σ ; idf ; refl ; sym
         ; trans ; _∙_ ; cong ; funExt ; _∘_ ; ⊥-elim)

open import Agda.Builtin.String

\end{code}

\section{About Agda}
Agda is a dependently typed, functional programming language with a syntax
similar to Haskell. It is being actively developed, with recent features
including support for Cubical Type Theory, and a new, light-weight syntax for
implicit arguments.

\medskip

This thesis was written using Literal Agda source files, which combine
\LaTeX-markup and Agda code. While many parts of the code remain hidden in this
final document, everything is still checked and formally verified to be correct
by the Agda typechecker.

\medskip

Some of the newer features are not yet available in the official Agda binaries.
Instead, we use a self-compiled build of Agda from the
master branch of its git repository \citep{AgdaSource}. The hash of the commit
with which the code was tested is \texttt{fe6337817cd295f1b7a928b4865f1}.

\medskip

During development, some code from standard libraries was used. These are
the agda-prelude \citep{AgdaPrelude} and the demo library for CTT \citep{AgdaCubical}.
Additionally, a standalone implementation of Cubical Type Theory by Anders Mörtberg
\citep{MortbergCTT} and the accompanying proofs provided a reference for how
basic properties of types could be proven in CTT. Most prominently, a proof of the
Hedberg-Lemma, being indirectly used in many places, was taken from there.

\section{Introduction to Agda}
We now start with a general treatment of types, then switch over to the language
of Agda for the introduction of concepts usually found in dependent type theories.

As a general reference, see \citet{IntroTT}. More in-depth information about
Agda may be found in its online documentation \citep{AgdaDocs}.

\subsection*{Types and terms}
The basic building blocks of a type theory are types and terms. A type is
defined by specifying how terms of this type can be constructed. We write
\[
  t : T
\]
if the term $t$ has type $T$. There are two perspectives on how a type
can be interpreted.

\medskip

The first perspective on types is to view them as being similar to sets, and accordingly, terms
of a type are called it's elements or inhabitants. But there are some differences to be aware of:
\begin{enumerate}
\item Sets are defined by the elements they \textit{contain}, while types, by how
  inhabitants \textit{can be constructed}. This means that we cannot simply
  reason about the entirety of terms ``in'' a type, for example by counting them.
\item Since terms are defined together with their type, they have no independent
  existence. It follows that a term can never be an element of multiple
  different types. Because of this, the question of whether $t : T$ holds is
  decidable (while $t ∈ T$ in general is not), and a statement of this kind can
  be checked by the typechecker.
\end{enumerate}

\medskip

The second perspective stems from the fact that propositions are also encodable
in types. From this point of view, constructing an element $p : P$ is like
constructing a verifiable proof $p$ of the proposition $P$.

\subsection*{Universes}
In dependent type theories, types themselves have a type. Such a ``type of
types'' is called a universe and being written as $𝒰$. Because of having $𝒰 : 𝒰$
would lead to inconsistencies, there is usually a hierarchy of universes,
denoted by universe levels $ℓ$, such that $𝒰_ℓ : 𝒰_{ℓ + 1}$. 

\begin{remark}
  In Agda, $𝒰$ is a function which takes a level parameter. Because of this, we
  write $𝒰\:ℓ$ instead of $𝒰_ℓ$. Still, for simplicity, we define the name of the first
  universe to be $𝒰₀$.

  The types we usually work with do not contain other types inside of them,
  which means that they are small enough to live inside $𝒰₀$. Only categories
  are, for maximum generality, defined in a universe polymorphic way.
\end{remark}

\subsection*{Defining simple types in Agda}
In Agda, a type can be defined using the $\AK{data}$ keyword. It expects a name
and a universe in which this type should live. In the following
$\AK{where}$-block, the constructors of this type need to be listed.

\begin{example}
  A type with two constructors, remniscent of a set with two elements, can be
  defined as follows. The type is called $\AD{Bool}$, it lives in $𝒰₀$ and
  has two constructors: $\AIC{true}$ and $\AIC{false}$.
\begin{code}
data Bool : 𝒰₀ where
  true   : Bool
  false  : Bool
\end{code}
\end{example}

\noindent
Continuing this way, we define a type with only one constructor, as well as a
type without constructors at all.

\newpage

\begin{example}
\leavevmode
\begin{enumerate}[i)]
\item The type \AD{⊤} is called top. It has a single constructor $\AIC{tt}$.
\begin{code}
data ⊤ : 𝒰₀ where
  tt : ⊤
\end{code}
\item The type \AD{⊥} is called bottom. It has no constructors.
\begin{code}
data ⊥ : 𝒰₀ where
\end{code}
\end{enumerate}
\end{example}

\noindent
Following the interpretation of types as sets, these correspond, respectively, to the
singleton set $\{*\}$ and the empty set $\emptyset$. If, instead, we view types as
propositions, then $⊤$ can be seen as truthhood, i.e., a trivially true proposition,
whose proof can always be given by $\AIC{tt}$. The bottom type $⊥$ then is falsehood,
for which no proof can be given.

\subsection*{Statements}
Having defined types and terms, they can now be used in statements. Statements
simply assign a name to some term, but usually the type of this term has to
be explictly given as well. Depending on the context they are used in, they may
serve as simple renamings, definitions, or theorems and their proofs.

\begin{example}
  We define $𝟚$ to be an alternative name for $\AD{Bool}$.
\begin{code}
𝟚 : 𝒰₀
𝟚 = Bool
\end{code}
  We define $\AF{el1}$ as an alternative name for $\AIC{true}$.
\begin{code}
el₁ : 𝟚
el₁ = true
\end{code}
\end{example}

\noindent
Here, the types $𝟚$ and $\AD{Bool}$ are definitionaly equal: the typechecker
does not differentiate between these expressions. Speaking on a meta-theoretic
level about Agda, we say $𝟚 \equiv \AD{Bool}$. This definitional equality is
not the same as the (path-) equality, written $a = b$, which will be introduced
later.

\subsection*{Functions}
Given two types $A$ and $B$, the type of functions between them is written as $A
\to B$. A function term can be either constructed by a lambda expression, or
directly as part of a statement.
\begin{example}
  The identity function for $\AD{Bool}$ can be defined in the following,
  definitionally equal ways.
\begin{code}
idB₁ : Bool -> Bool
idB₁ = λ b -> b

idB₂ : Bool -> Bool
idB₂ b = b
\end{code}
  A function is applied to arguments by writing them after each other. 
\begin{code}
true₂ : Bool
true₂ = idB₁ true
\end{code}
\end{example}
\begin{remark}
Function application always takes precedence over other operations (except
the evaluation of parentheses).
\end{remark}

\noindent
A function can be defined by pattern matching on the constructors of the
argument type.
\begin{example}
  Boolean negation is defined by pattern matching:
\begin{code}
negate : Bool -> Bool
negate true   = false
negate false  = true
\end{code}
\end{example}

\noindent
Functions with multiple arguments are usually defined as higher order functions,
that is, as functions which return functions.
\begin{example}
  The boolean conjunction is a function of type $\AD{Bool} \to (\AD{Bool} \to
  \AD{Bool})$. That is, a function taking a boolean and returning a function
  which takes another boolean, and returns the result. The function arrow
  associates to the right, consequently, the parentheses can be omitted.
\begin{code}
and : Bool -> Bool -> Bool
and true   true   = true
and true   false  = false
and false  true   = false
and false  false  = false
\end{code}
\end{example}

\begin{remark}
  Names can be turned into infix operators by writing an underscore where
  arguments are supposed to be placed, for example we define:
\begin{code}
_∧_ : Bool -> Bool -> Bool
a ∧ b = and a b
\end{code}
  Furthermore, names can contain every possible mix of characters: different
  tokens are only distinguished by the whitespace between them. Accordingly, $\AB{a∧b}$
  is a name, while $a\;\AF{∧}\;b$ is the application of the function $\AF{∧}$ to the
  terms $a$ and $b$. We often choose names such as $\AB{a=b}$ or $\AB{i<n}$ for terms
  which prove such statements.
\end{remark}

\medskip

The logical interpretation of a function $P \to Q$ is that of an
implication: Being able to construct such a function means that a
proof of $P$ can be turned into a proof of $Q$.
A proposition $P$ is false if $P \to ⊥$ can be proven, since this means that a
proof of $P$ would give us a proof of $⊥$, of which we know that it cannot exist.

\subsection*{Data types with arguments}
When defining a type, constructors may take arguments. This effectively turns them
into functions, and the syntax is the same.
\begin{example}
  The type $ℕ$ of natural numbers is defined as an inductive data type with two
  constructors: A natural number is either zero, or it is the successor of
  another natural number.
\begin{code}
data ℕ : 𝒰₀ where
  zero  : ℕ
  suc   : ℕ -> ℕ
\end{code}
\end{example}
\noindent
The meaning of \textit{inductive} here is that a constructor recursively
takes arguments of the type which it constructs.

\medskip

Constructors are applied exactly like functions:
\begin{example}
  The number 4 can be encoded as follows:
\begin{code}
four : ℕ
four = suc (suc (suc (suc zero)))
\end{code}
\end{example}

\noindent
Pattern matching on constructors allows us to bring their arguments into scope by giving
them a name.
\begin{example}
  The operation of addition on $ℕ$ can be defined by recursion.
\begin{code}
_+ℕ_ : ℕ -> ℕ -> ℕ
zero     +ℕ b = b
(suc a)  +ℕ b = suc (a +ℕ b)
\end{code}
\end{example}

\begin{remark}
By default, Agda allows only total functions. In order to enforce this, it has a termination
checker which verifies that at least one argument of a recursive function call gets smaller
in every iteration. Here, this is the case for the first argument, since $a$ is smaller than
$\AF{suc}\:a$.
\end{remark}

\subsection*{Functions with type parameters}
Functions can take type parameters.
\begin{example}
  The identity function can be defined for all types by letting it
  take a type parameter.
\begin{code}
idf₁ : (A : 𝒰₀) -> A -> A
idf₁ A a = a
\end{code}
\end{example}
\begin{example}
  This function can be made universe polymorphic by requiring an additional
  level parameter. Here we pattern match with underscores, indicating that these
  arguments are not used in the function body.
\begin{code}
idf₂ : (ℓ : ULevel) -> (A : 𝒰 ℓ) -> A -> A
idf₂ _ _ a = a
\end{code}
\end{example}
\begin{remark}
Agda provides a way to make arguments implicit by enclosing them with curly
braces. Then, when calling such a function, these arguments do not have to be
given, instead, Agda tries to infer their values from the context.
\begin{code}
idf : {ℓ : ULevel} -> {A : 𝒰 ℓ} -> A -> A
idf a = a
\end{code}
Sometimes it is still necessary to give such arguments, or to pattern match
against them. In both cases this can be done by using curly braces.
\end{remark}

\subsection*{Global implicits}
Agda has a new syntax which allows us to declare global implicit variables.
They define variable names which can be used in function definitions as if
they were implicit variables. This feature currently does not work with data
types, where implicit arguments still have to be named individually.

\begin{example}
In order to declare $ℓ$ and $ℓ'$ as always being universe levels, we write:
\begin{code}
variable
  {ℓ ℓ'} : ULevel
\end{code}
\end{example}


\subsection*{Data types with type parameters}
\begin{code}[hide]
module def1 where
\end{code}
Data types can take level and type parameters as well. These are stated directly after the name.
\begin{example}
  Using this, we can define the product and the sum type.
\begin{enumerate}[(i)]
\item 
  For two types $A$ and $B$, we define the product $A × B$ as the type which can
  be constructed by providing an element of $A$ and an element of $B$. Because $A$ and
  $B$ can live in different universes $𝒰_ℓ$ and $𝒰_{ℓ'}$, the resulting type
  has to live in the one which is larger, namely $𝒰_{\AF{lmax}\:ℓ\:ℓ'}$.
\begin{code}
  data _×_ {ℓ ℓ'} (A : 𝒰 ℓ) (B : 𝒰 ℓ') : 𝒰 (lmax ℓ ℓ') where
    _,_ : A -> B -> A × B
\end{code}
\item
  For two types $A$ and $B$, we define the sum $A + B$ as the type which can be
  constructed by either providing an element of $A$, or an element of $B$. The
  same note about universe levels applies.
\begin{code}
  data _+_ {ℓ ℓ'} (A : 𝒰 ℓ) (B : 𝒰 ℓ') : 𝒰 (lmax ℓ ℓ') where
    left   : A -> A + B
    right  : B -> A + B
\end{code}
\end{enumerate}
\end{example}
The corresponding notions in set theory are the cartesian product and the
disjoint union of sets.

Viewed as an operation on propositions $P$ and $Q$, the logical
interpretation of $P × Q$ is $P ∧ Q$, and of $P + Q$ it is $P ∨ Q$. That said,
the behaviour of $P + Q$ is slightly different from it's logical counterpart. An
element $p : P + Q$ contains additional information about which proposition out of
these two was proven \citep{HoTTBook}.


\subsection*{Record types}
Data types with only a single constructor are effectively tuples,
containing (multiple) values. They can be defined more conveniently using
record syntax. It differs from the data syntax in that the values, called fields, are
given explicit names. These names define projection functions which can be used to
access the respective values.
\begin{example}
  The product type can be defined as a record. As before, the constructor is
  called $\AIC{\_,\_}$ and has the type $A \to B \to A × B$. Additionally, the
  projection functions $\AFd{fst} : \AD{A}\,\AR{×}\,\AD{B} \to \AD{A}$ and
  $\AFd{snd} : \AD{A}\,\AR{×}\,\AD{B} \to \AD{B}$ are defined.
\begin{code}
record _×_ {ℓ ℓ'} (A : 𝒰 ℓ) (B : 𝒰 ℓ') : 𝒰 (lmax ℓ ℓ') where
  constructor _,_
  field
    fst  : A
    snd  : B
\end{code}
\end{example}

Terms of a record type can be constructed using a dedicated copattern syntax.
For this, the value of every field has to specified, in a way similar to pattern
matching.
\begin{example}
  The pair of natural numbers $(0, 1)$ can be defined as follows.
\begin{code}[hide]
open _×_
\end{code}
\begin{code}
pair : ℕ × ℕ
fst  pair = zero
snd  pair = suc zero
\end{code}
\end{example}

\subsection*{Dependent types}
A dependent type is a function which returns a type. It is also called a type
family \citep{nlab:dependent_type}.
\begin{example}
  $\AF{T₁}$ is a type family, depending on an argument of type $\AD{Bool}$.
\begin{code}
T₁ : Bool -> 𝒰₀
T₁ true   = ⊤
T₁ false  = ℕ
\end{code}
\end{example}
Using type families, we can define functions whose resulting type depends on the
arguments given.
\begin{example}
  $\AF{f₁}$ is a dependent function which takes a boolean argument and returns
  a term of $\AIC{⊤}$ if the argument was true, and a natural number if it was false.
\begin{code}
f₁ : (a : Bool) -> T₁ a
f₁ true   = tt
f₁ false  = four
\end{code}
\end{example}

\begin{remark}
  The level and type polymorphic functions introduced before also represent special cases of dependent functions.
\end{remark}

\subsection*{Dependent product}

This operation of creating a function type out of a type family can be extracted
into a new type: the dependent product.

\begin{example}
  Given a type family $B$ of type $A \to 𝒰_{ℓ'}$, the \textbf{dependent product} is the
  type of functions which for every $a : A$ return a term of type $B\:a$. The
  universe levels refer to the global implicits defined before.
\begin{code}
Π : {A : 𝒰 ℓ} -> (B : A -> 𝒰 ℓ') -> 𝒰 (lmax ℓ ℓ')
Π {A = A} B = (a : A) -> B a
\end{code}
\end{example}

Usually, this type is written as follows:
\[
  \prod_{a : A} B\:a
\]


The logical interpretation of the dependent product is that of the universal
quantifier. A function of type $\prod_{x:X}P\:x$ has to give a proof of $P\:x$
for every possible $x : X$. This means that dependent products express the notion of
universal quantification, ${∀(x \in X).\:P(x)}$.

\medskip

In Agda, we can write $Π\:B$ or $Π\:(λ\:a \to B\:a)$ or $Π\:(λ\:(a : A) \to
B\:a)$, but usually we skip the product sign, and write it as the dependent
function type $(a : A) \to B\:a$. Agda also allows an optional $∀$ sign:
$f₂ : ∀(a : A) \to B\:a$.

\subsection*{Dependent sum}
The dependent sum is defined as a pair. Accordingly, we re-use the
terminology from above.

\newpage
\begin{example}
  The \textbf{dependent sum} of a type family $B : A \to 𝒰_{ℓ'}$ is defined as a pair, where
  the type of the second element depends on the value of the first.
\begin{code}
record Σ {ℓ ℓ'} {A : 𝒰 ℓ} (B : A -> 𝒰 ℓ') : 𝒰 (lmax ℓ ℓ') where
  constructor _,_
  field
    fst : A
    snd : B fst
\end{code}
\end{example}

This type is usually written as follows:
\[
  \sum_{a : A} B\:a
\]

In order to be able to construct a term of type $\sum_{x:X}P\:x$, we have to
find some $x : X$, for which $P\:x$ is provable. Dually to the dependent product
type, the logical interpretation of the dependent sum type is that of the
existential quantifier $∃(x ∈ X).\:P(x)$.

\medskip

In Agda, we write this type as $Σ\:B$ or $Σ\:(λ\:a \to B\:a)$ or $Σ\:(λ (a : A) \to
B\:a)$.

\subsection*{Equality}
In dependent type theories, types can capture the notion of equality of elements.
It is expressible by the following type family:
\[
  \AF{\_=\_} : ∀\{ℓ\} \to \{A : 𝒰_ℓ\} \to A \to A \to 𝒰_ℓ
\]
For a type $A : 𝒰_ℓ$ and elements $a\:b : A$, equality is therefore proven by constructing an
element of $a == b$.

\medskip

Depending on the specific type theory in use, the implementation of this type family
varies. In Cubical Type Theory it is modeled by paths, as described in \citet{CubicalTT}.
Here, we only show the most basic principles of CTT, focusing more on the practical aspects
of writing equality proofs.

\medskip

On a topological space $X$, a path $p$ is defined as a continuous function $p : [0,1] \to X$.
Analoguously, in CTT, there is a type $\AF{I}$ with formal elements $\AF{i0}$ and $\AF{i1}$.
Equalities on a type $A$ are treated similar to functions $\AF{I} \to A$.

\medskip

For example, by reflexivity, the equality $a = a$ must always hold. This is formalized by a
constant path.
\begin{example}
  The constant path is called $\AF{refl}$. Paths are using the same syntax as functions.
\begin{code}
refl : ∀{ℓ} -> {A : 𝒰 ℓ} -> {a : A} -> a == a
refl {ℓ} {A} {a} = λ 𝒊 -> a
\end{code}
\end{example}
\begin{remark}
Even though paths use the same syntax as functions, their behaviour is not the same. For example, we
cannot pattern match on $𝒊$ and write different implementations for $\AF{i0}$ and $\AF{i1}$.
\end{remark}

But there are operations on $\AF{I}$ which can be used to construct new paths. For example,
we can write $\AF{\textasciitilde{}}\:\AF{𝒊}$. In the topological space analogy, this corresponds to $1 - 𝒊$,
but here, its effective meaning is that of invertion, mapping $\AF{i0}$ to $\AF{i1}$
and vice versa. Using this, we can express the symmetry of equality.

\begin{example}
  The operation of inverting a path is called $\AF{sym}$.
\begin{code}
sym : ∀{ℓ} -> {A : 𝒰 ℓ} -> {a b : A} -> a == b -> b == a
sym p 𝒊 = p (~ 𝒊)
\end{code}
\end{example}
\noindent
Using further cubical primitives, the composition of paths, corresponding to transitivity
can be formalized:
\begin{example}
  The operation of composing paths is called $\AF{trans}$. It has the following type:
\begin{code}
trans : ∀{ℓ} -> {A : 𝒰 ℓ} -> {a b c : A} → a == b → b == c → a == c
\end{code}
\begin{code}[hide]
trans {A = A} {a = x} p q i = primComp (λ _ → A) _ (λ { j (i = i0) → x
                                                   ; j (i = i1) → q j }) (p i)
\end{code}
\end{example}
\begin{notation}
The composition of two paths $p : a = b$ and $q : b = c$ is usually denoted by $p ∙ q$. For this we write:
\end{notation}
\begin{code}
_∙_ = trans
\end{code}
Another common way to modify an equality is to map a function over it.
\begin{example}
If $a = b$, then it is valid to apply a function $f$ to both sides. This operation is
called $\AF{cong}$.
\begin{code}
cong : ∀{ℓ ℓ'}  -> {A : 𝒰 ℓ} -> {B : 𝒰 ℓ'} -> {a b : A}
                -> (f : A -> B)
                -> a == b -> f a == f b
cong f p 𝒊 = f (p 𝒊)
\end{code}
\end{example}

All of the operations introduced so far ($\AF{refl}$, $\AF{sym}$, $\AF{trans}$ and $\AF{cong}$) can be
expressed in many dependent type theories, regardless of the specific implementation of equality. Thus,
when using these, proofs can be written in an implementation independent way. Nevertheless, sometimes it is
very useful to drop down to the explicit path notation, for example, when mapping a binary function over
two paths simultaneously.

\medskip

The next operation, functional extensionality, cannot be proven in standard ITT or HoTT. There, it can
only be assumed as an axiom, i.e., as a function without implementation. In CTT, the proof is straightforward:
\newpage
\begin{example}
  Functional extensionality means that the equality of two functions $f$ and $g$ can be derived from
  the fact that they return the same result for every input.
\begin{code}
funExt : ∀{ℓ ℓ'}  -> {A : 𝒰 ℓ} -> {B : 𝒰 ℓ'}
                  -> {f g : A -> B}
                  -> (∀(a : A) -> f a == g a)
                  -> f == g
funExt p 𝒊 a = p a 𝒊
\end{code}
\end{example}


\subsection*{Proofs}
Now we can state theorems and proof them. For example, the associativity of the addition of natural numbers.
\begin{example}
  Associativity is proven by the following function:
\begin{code}
assoc : (a b c : ℕ) -> (a +ℕ b) +ℕ c == a +ℕ (b +ℕ c)
assoc zero b c      = refl
assoc (suc a') b c  = cong suc (assoc a' b c)
\end{code}
  The proof can be explained as follows (we write $+$ instead of $\AF{ℕ+}$).

  \smallskip

  \noindent
  We consider the cases $a \equiv 0$ and $a \equiv (\AF{suc}\:a')$ separately:
  \begin{itemize}
  \item For $a \equiv 0$, the goal reduces to $(0 + b) + c = 0 + (b + c)$.

  By the definition of $\AF{\_+ℕ\_}$, $0 + b$ is simply $b$.

  Analoguously, $0 + (b + c)$ reduces to $b + c$.

  Therefore, the goal is $b + c = b + c$.

  We conclude with $\AF{refl}$.

\item For $a \equiv \AF{suc}\:a'$, the goal is $((\AF{suc}\:a') + b) + c = (\AF{suc}\:a') + (b + c)$.

  After evaluating the definition of $+ℕ$ two times on the left side and one time on the right side,
  the goal reduces to:
  \[
    \AF{suc}\:((a' + b) + c) = \AF{suc}\:(a' + (b + c))
  \]

  By calling $\AF{assoc}\:a'\:b\:c$, we get a proof of:
  \[
    (a' + b) + c = a' + (b + c)
  \]

  We use $\AF{cong}\:\AF{suc}$ in order to apply $\AF{suc}$ to both sides. This finishes the proof.
  \end{itemize}
\end{example}

\subsection*{Longer proofs}
For a slightly more complex example, we introduce the definition of the ordering relation $\AF{\_<\_}$
on $\AD{ℕ}$. For $n\:m:ℕ$, a proof of $n < m$ is given by the following type:
\[
\sum_{k:ℕ} (m = \AF{suc}\:k + n)
\]
\begin{definition}
  In Agda, the ordering relation $\AF{\_<\_}$ on $ℕ$ is defined by the following record.
\begin{code}
record _<_ (n m : ℕ) : 𝒰₀ where
  constructor diff
  field
    diff-k : ℕ
    diff-p : m == suc diff-k +ℕ n
\end{code}
\end{definition}


\begin{code}[hide]

pred : ℕ → ℕ
pred zero     = zero
pred (suc n)  = n

-- CITE: from mort-ctt
zNotS : {n : ℕ} → (ℕ.zero == suc n) → ⊥
zNotS {n} p = subst {P = P} p zero
  where P : ℕ → 𝒰₀
        P zero     = ℕ
        P (suc _)  = ⊥
-- CITE end
add-suc-r : (k a : ℕ) -> (k +ℕ (suc a)) == suc (k +ℕ a)
add-suc-r zero a     = refl
add-suc-r (suc k) a  = cong suc (add-suc-r k a)

_∘_ : ∀{ℓ} -> {A B C : 𝒰 ℓ} -> (B -> C) -> (A -> B) -> A -> C
_∘_ f g x = f (g x)
\end{code}

\begin{remark}
Later, we will need use some of its properties, including the fact that
the ordering still holds after taking the successor or predecessor of both sides.
\begin{code}
suc-monotone   : {k l : ℕ} -> k < l -> suc k < suc l
pred-monotone  : {k l : ℕ} -> suc k < suc l -> k < l
\end{code}
\begin{code}[hide]
suc-monotone {k} {l} (diff d pd) = diff d (cong suc (pd ∙ (sym (add-suc-r d k))))
pred-monotone {i} {n} (diff k p) = diff k ((cong pred p) ∙ (add-suc-r k i))
\end{code}
Another property is antireflexivity, which can be proven using an operation called \textit{substitution}.
\begin{code}
less-antirefl : {n : ℕ} -> n < n -> ⊥
\end{code}
\begin{code}[hide]
less-antirefl {zero} (diff k kp)  = zNotS kp
less-antirefl {suc n} (kp)        = less-antirefl (pred-monotone kp)
\end{code}
\end{remark}

\noindent
For an example of a longer proof, we now show the antisymmetry of $\AF{\_<\_}$.
\begin{example}
  The ordering relation $\AF{\_<\_}$ is antisymmetric.
\begin{code}
less-antisym : {n m : ℕ} -> n < m -> m < n -> ⊥
less-antisym {n} {m} (diff k kp) (diff l lp) =
  let
      proof : n == suc (suc (l +ℕ k) +ℕ n)
      proof =  n                          ≡⟨ lp ⟩
               suc (l +ℕ m)               ≡⟨ cong (λ ξ -> suc (l +ℕ ξ)) kp ⟩
               suc (l +ℕ (suc (k +ℕ n)))  ≡⟨ cong suc (add-suc-r l (k +ℕ n)) ⟩
               suc (suc (l +ℕ (k +ℕ n)))  ≡⟨ cong (suc ∘ suc) (sym (assoc l k n)) ⟩
               suc (suc ((l +ℕ k) +ℕ n))  ∎

      n<n : n < n
      n<n = diff (suc (l +ℕ k)) proof

  in less-antirefl n<n
\end{code}
This proof uses a $\AK{let}\dots\AK{in}$ clause to introduce two local bindings called
$\AF{proof}$ and $\AF{n<n}$. Then $\AF{less-antirefl}$ is called to get a proof of $⊥$.

\smallskip

In the definition of $\AF{proof}$, the operators $\AF{\_≡⟨\_⟩}$ and $∎$ provide a readable syntax for
chaining paths together. The terms on the left side represent the intermediate steps
of the derivation, just like it would be written manually. Internally, they are
are discarded after typechecking, and the paths on the right side are composed using $\AF{\_∙\_}$.

\end{example}

As seen here, even small proofs get rather long very fast. Therefore, we will
hide them most of the time, explaining the idea behind statements instead.

\subsection*{Contradictions}

Using functions like $\AF{less-antisym}$, we can, if given correct arguments, show that they
lead to a contradiction. From such a contradiction, anything can be derived \citep{HoTTBook}.

In Agda, when there are no valid constructors for an argument,
empty parentheses can be used instead of a name. Then no function body
has to be written.
\begin{code}
⊥-elim : {A : 𝒰 ℓ} → ⊥ → A
⊥-elim ()
\end{code}

\subsection*{Comparing elements}
Generally, for two elements $a$ and $b$ of a type $A$, the question of whether
they are equal is not decidable. But sometimes it is necessary to require such
a property, for example when defining the typechecker.

In order to formalize this, we first define the concept of decidability.

\begin{definition}
  A type, viewed as a proposition, is called \textbf{decidable} if either a proof or a
  refutation can be given.
\begin{code}
data isDec {ℓ} (A : 𝒰 ℓ) : 𝒰 ℓ where
  yes  : A         -> isDec A
  no   : (A -> ⊥)  -> isDec A
\end{code}
\end{definition}

\noindent
Now we can define what it means for a type to have comparable elements:
\begin{definition}
  A type is called \textbf{discrete} if for every pair of elements, equality
  is decidable.
\begin{code}
isDiscrete : (A : 𝒰 ℓ) -> 𝒰 ℓ
isDiscrete A = (x y : A) -> isDec (x == y)
\end{code}
\end{definition}








