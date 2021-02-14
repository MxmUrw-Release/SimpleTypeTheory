
{-# OPTIONS --cubical  #-}

open import TypeTheory.Lambda.Base hiding (_$_)
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Reduction.Presentation {i j} where

param : LambdaParam i j
param = lambdaParam Bool Bool-isDisc Bool idf

open import TypeTheory.Lambda.Core {param = param} hiding (_$$_)
open import TypeTheory.Lambda.Typing {param = param}
open import TypeTheory.Lambda.Reduction.NormalFormProofs {param = param}

X Y : Ty
X = ι true
Y = ι false

a b : Term
a = cconst true
b = cconst false


_⇨_   = Λ
_$_   = app
_#_   = app⇓

infixr 50 _⇨_
infixl 60 _$_
infixl 60 _#_













-------------------------------------------------------------------------------
--
-- Teil I
--
--














test0 : ℕ
test0 = 3 S+ 2













test1 : TypeError + ⊤
test1 = check' (X ⇒ Y ,, (X ,, [])) (app (Λ X (app (V 1) (V 0))) (V 3)) Y


















----------------------------------------------------------------
-- Natürliche Zahlen
NN : Ty
NN = (X ⇒ X) ⇒ (X ⇒ X)



-- Die Zahlen 0 bis 5
n0 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 0 :: NN
n1 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 1 $ V 0 :: NN
n2 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 1 $ (V 1 $ V 0) :: NN
n3 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 1 $ (V 1 $ (V 1 $ V 0)) :: NN
n4 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 1 $ (V 1 $ (V 1 $ (V 1 $ V 0))) :: NN
n5 : [] ⊢ (X ⇒ X) ⇨ (X) ⇨ V 1 $ (V 1 $ (V 1 $ (V 1 $ (V 1 $ V 0)))) :: NN

n0 = tt ,fir, refl
n1 = tt ,fir, refl
n2 = tt ,fir, refl
n3 = tt ,fir, refl
n4 = tt ,fir, refl
n5 = tt ,fir, refl







-- Addition
++ : []  ⊢   NN ⇨  NN ⇨  (X ⇒ X) ⇨ X ⇨ (V 3 $ V 1) $ (V 2 $ V 1 $ V 0)
         ::  NN ⇒  NN ⇒  NN
++ = tt ,fir, refl

-- Multiplikation
** : []  ⊢   NN ⇨  NN ⇨  (X ⇒ X) ⇨ X ⇨ (V 3 $ (V 2 $ V 1) $ V 0)
         ::  NN ⇒  NN ⇒  NN
** = tt ,fir, refl


-- Kleine Rechnungen
test2 : Term
test2 = nor (++ # n1 # n2)


test3 : Term
test3 = nor (** # n0 # n1)


test4 : Term
test4 = nor (** # n2 # n5)
