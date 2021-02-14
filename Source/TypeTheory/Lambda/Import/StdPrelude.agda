{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Import.StdPrelude where


open import Agda.Primitive

open import Agda.Primitive public using (lzero ; lsuc)
  renaming (Level to ULevel; _⊔_ to lmax)

open import Agda.Builtin.Unit public

open import Agda.Builtin.Nat public
  using (zero; suc; _*_)
  renaming (Nat to ℕ ; _+_ to _S+_)

--------------------------------------------------------------------
-- Functions

id : ∀ {a} {A : Set a} → A → A
id x = x
{-# INLINE id #-}

const : ∀ {a b} {A : Set a} {B : Set b} → A → B → A
const x _ = x
{-# INLINE const #-}


flip : ∀ {a b c} {A : Set a} {B : Set b} {C : A → B → Set c} → (∀ x y → C x y) → ∀ y x → C x y
flip f x y = f y x
{-# INLINE flip #-}

infixr 9 _∘_
_∘_ : ∀ {a b c} {A : Set a} {B : A → Set b} {C : ∀ x → B x → Set c}
        (f : ∀ {x} (y : B x) → C x y) (g : ∀ x → B x) →
        ∀ x → C x (g x)
(f ∘ g) x = f (g x)
{-# INLINE _∘_ #-}


infixr -20 _$_
_$_ : ∀ {a b} {A : Set a} {B : A → Set b} → (∀ x → B x) → ∀ x → B x
f $ x = f x


--------------------------------------------------------------------
-- Either


data Either {a b} (A : Set a) (B : Set b) : Set (a ⊔ b) where
  left  : A → Either A B
  right : B → Either A B


infixl 50 _+_
_+_ = Either

{-# FOREIGN GHC type AgdaEither a b = Either #-}
{-# COMPILE GHC Either = data MAlonzo.Code.Prelude.Sum.AgdaEither (Left | Right) #-}

either : ∀ {a b c} {A : Set a} {B : Set b} {C : Set c} →
           (A → C) → (B → C) → Either A B → C
either f g (left  x) = f x
either f g (right x) = g x

-- lefts : ∀ {a b} {A : Set a} {B : Set b} → List (Either A B) → List A
-- lefts = concatMap λ { (left x) → [ x ]; (right _) → [] }

-- rights : ∀ {a b} {A : Set a} {B : Set b} → List (Either A B) → List B
-- rights = concatMap λ { (left _) → []; (right x) → [ x ] }

mapEither : ∀ {a₁ a₂ b₁ b₂} {A₁ : Set a₁} {A₂ : Set a₂} {B₁ : Set b₁} {B₂ : Set b₂} →
            (A₁ → A₂) → (B₁ → B₂) → Either A₁ B₁ → Either A₂ B₂
mapEither f g = either (left ∘ f) (right ∘ g)

mapLeft : ∀ {a₁ a₂ b} {A₁ : Set a₁} {A₂ : Set a₂} {B : Set b} →
            (A₁ → A₂) → Either A₁ B → Either A₂ B
mapLeft f = either (left ∘ f) right

mapRight : ∀ {a b₁ b₂} {A : Set a} {B₁ : Set b₁} {B₂ : Set b₂} →
            (B₁ → B₂) → Either A B₁ → Either A B₂
mapRight f = either left (right ∘ f)


-----------------------------
-- Monad

record Functor {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<$>_ _<$_
  field
    fmap : ∀ {A B} → (A → B) → F A → F B
  _<$>_ = fmap

  _<$_ : ∀ {A B} → A → F B → F A
  x <$ m = fmap (const x) m

open Functor {{...}} public

{-# DISPLAY Functor.fmap  _ = fmap  #-}
{-# DISPLAY Functor._<$>_ _ = _<$>_ #-}
{-# DISPLAY Functor._<$_  _ = _<$_  #-}


record Applicative {a b} (F : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixl 4 _<*>_ _<*_ _*>_
  field
    pure  : ∀ {A} → A → F A
    _<*>_ : ∀ {A B} → F (A → B) → F A → F B
    overlap {{super}} : Functor F

  _<*_ : ∀ {A B} → F A → F B → F A
  a <* b = ⦇ const a b ⦈

  _*>_ : ∀ {A B} → F A → F B → F B
  a *> b = ⦇ (const id) a b ⦈

open Applicative {{...}} public

{-# DISPLAY Applicative.pure  _ = pure  #-}
{-# DISPLAY Applicative._<*>_ _ = _<*>_ #-}
{-# DISPLAY Applicative._<*_  _ = _<*_  #-}
{-# DISPLAY Applicative._*>_  _ = _*>_  #-}

record Monad {a b} (M : Set a → Set b) : Set (lsuc a ⊔ b) where
  infixr 1 _=<<_
  infixl 1 _>>=_ _>>_
  field
    _>>=_ : ∀ {A B} → M A → (A → M B) → M B
    overlap {{super}} : Applicative M

  _>>_ : ∀ {A B} → M A → M B → M B
  m₁ >> m₂ = m₁ >>= λ _ → m₂

  _=<<_ : ∀ {A B} → (A → M B) → M A → M B
  _=<<_ = flip _>>=_


return : ∀ {a b} {A : Set a} {M : Set a → Set b} {{_ : Monad M}} → A → M A
return = pure

monadAp : ∀ {a b} {A B : Set a} {M : Set a → Set b}
          {{_ : Functor M}} →
          (M (A → B) → ((A → B) → M B) → M B) →
          M (A → B) → M A → M B
monadAp _>>=_ mf mx = mf >>= λ f → fmap f mx

open Monad {{...}} public

{-# DISPLAY Monad._>>=_  _ = _>>=_  #-}
{-# DISPLAY Monad._=<<_  _ = _=<<_  #-}
{-# DISPLAY Monad._>>_   _ = _>>_   #-}

module _ {a b} {A : Set a} where
  instance
    FunctorEither : Functor (Either {b = b} A)
    fmap {{FunctorEither}} f (left x) = left x
    fmap {{FunctorEither}} f (right x) = right (f x)

    ApplicativeEither : Applicative (Either {b = b} A)
    pure  {{ApplicativeEither}} = right
    _<*>_ {{ApplicativeEither}} (right f) (right x) = right (f x)
    _<*>_ {{ApplicativeEither}} (right _) (left e)  = left e
    _<*>_ {{ApplicativeEither}} (left e)  _         = left e

    MonadEither : Monad (Either {b = b} A)
    _>>=_  {{MonadEither}} m f = either left f m

