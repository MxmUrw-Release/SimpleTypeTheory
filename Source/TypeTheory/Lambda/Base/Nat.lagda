

We define the natural numbers ℕ as.

\begin{code}[hide]


{-# OPTIONS --cubical #-}

module TypeTheory.Lambda.Base.Nat where



open import TypeTheory.Lambda.Base.Import
open import TypeTheory.Lambda.Base.TypeProperties


----------------------------------------------------------------------
-- Operations

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


iNotSi : {i : ℕ} -> i == suc i -> ⊥
iNotSi {zero}     = zNotS
iNotSi {suc i} p  = iNotSi {i = i} (cong pred p)

add-zero-r : (k : ℕ) -> (k S+ 0) == k
add-zero-r zero     = refl
add-zero-r (suc k)  = cong suc (add-zero-r k)

add-suc-r : (k a : ℕ) -> (k S+ (suc a)) == suc (k S+ a)
add-suc-r zero a     = refl
add-suc-r (suc k) a  = cong suc (add-suc-r k a)

assoc : (a b c : ℕ) -> (a S+ b) S+ c == a S+ (b S+ c)
assoc zero b c     = refl
assoc (suc a) b c  = cong suc (assoc a b c)

comm : (a b : ℕ) -> a S+ b == b S+ a
comm zero b     = sym (add-zero-r b)
comm (suc a) b  = cong suc (comm a b) ∙ (sym (add-suc-r b a))

add-inj : (k l a : ℕ) -> (k S+ a == l S+ a) -> k == l
add-inj k l zero p     = (sym (add-zero-r k)) ∙ p ∙ (add-zero-r l)
add-inj k l (suc a) p  = add-inj k l a (cong pred ((sym (add-suc-r k a)) ∙ p ∙ (add-suc-r l a)))

----------------------------------------------------------------------
-- isSet


-- CITE: from mort-ctt
ℕPath-isDec : (n m : ℕ) → isDec (Path n m)
ℕPath-isDec zero zero        = yes refl
ℕPath-isDec zero (suc m)     = no zNotS
ℕPath-isDec (suc n) zero     = no (zNotS ∘ sym)
ℕPath-isDec (suc n) (suc m)  = mapDec (cong suc) (cong pred) (ℕPath-isDec n m)

ℕ-isDisc = ℕPath-isDec

-- CITE: mort-ctt
ℕ-isSet : isSet ℕ
ℕ-isSet = hedberg ℕPath-isDec


----------------------------------------------------------------------
-- ℕOrd (_<_)

--------------------------------------
-- Definition
-- CITE: agda-prelude (LessNat)
record ℕOrd (n m : ℕ) : 𝒰₀ where
  constructor diff
  field
    diff-k : ℕ
    diff-p : m == suc diff-k S+ n
open ℕOrd

syntax ℕOrd n m = n < m

_>_ : ℕ -> ℕ -> 𝒰₀
m > n = n < m


--------------------------------------
-- Operations

pred-monotone : {i n : ℕ} -> (lep : (suc i) < (suc n)) -> i < n
pred-monotone {i} {n} (diff k p) = diff k ((cong pred p) ∙ (add-suc-r k i))

suc-monotone : ∀{k l : ℕ} -> k < l -> suc k < suc l
suc-monotone {k} {l} (diff d pd) = diff d (cong suc (pd ∙ (sym (add-suc-r d k))))

less-antirefl : ∀{n : ℕ} -> n < n -> ⊥
less-antirefl {zero} (diff k kp) = zNotS kp
less-antirefl {suc n} (kp) = less-antirefl (pred-monotone kp)

less-antisym : ∀{n m : ℕ} -> n < m -> m < n -> ⊥
less-antisym {n} {m} (diff k kp) (diff l lp) = less-antirefl (diff (suc (l S+ k)) proof)
  where
    proof : n == suc (suc (l S+ k) S+ n)
    proof = n                          ≡⟨ lp ⟩
            suc (l S+ m)               ≡⟨ cong (λ ξ -> suc (l S+ ξ)) kp ⟩
            suc (l S+ (suc (k S+ n)))  ≡⟨ cong suc (add-suc-r l (k S+ n)) ⟩
            suc (suc (l S+ (k S+ n)))  ≡⟨ cong (suc ∘ suc) (sym (assoc l k n)) ⟩
            suc (suc ((l S+ k) S+ n))  ∎



-- Comparison
-- CITE: agda-prelude
data Comparison (a b : ℕ) : 𝒰₀ where
  less     : (a < b) -> Comparison a b
  equal    : (a == b) -> Comparison a b
  greater  : (b < a) -> Comparison a b

compare : (a b : ℕ) -> Comparison a b
compare zero zero = equal refl
compare (suc a) zero = greater (diff a (cong suc (sym (add-zero-r a))))
compare zero (suc b) = less (diff b (cong suc (sym (add-zero-r b))))
compare (suc a) (suc b) with compare a b
...                        | less (kp) = less (suc-monotone kp)
...                        | equal p = equal (cong suc p)
...                        | greater (kp) = greater (suc-monotone kp)



choose : {A : 𝒰₀} -> (m n : ℕ) -> (m < n -> A) -> A -> A
choose m n a b with compare m n
... | less p     = a p
... | equal _    = b
... | greater _  = b


lessEqual-⊥ : {i j : ℕ} -> (i < j) -> (i == j) -> ⊥
lessEqual-⊥ {i} {j} i<j i=j = less-antirefl (subst {P = λ x -> x < j} i=j i<j)


lessGreater-⊥ : {i j : ℕ} -> (i < j) -> (i > j) -> ⊥
lessGreater-⊥ i<j i>j = less-antisym i>j i<j

lessZero-⊥ : {i : ℕ} -> (i < 0) -> ⊥
lessZero-⊥ (diff k kp) = zNotS kp


data EqComp {A : 𝒰₀} (a b : A) : 𝒰₀ where
  equal : (a == b) -> EqComp a b
  noteq : (a == b -> ⊥) -> EqComp a b

compare-eq : (a b : ℕ) -> EqComp a b
compare-eq a b with compare a b
compare-eq a b | less x = noteq $ lessEqual-⊥ x
compare-eq a b | equal x = equal x
compare-eq a b | greater x = noteq $ (lessEqual-⊥ x ∘ sym)




--------------------------------------
-- Ord Jungling

mkNotZero : {i j : ℕ} -> i < j -> 0 < j
mkNotZero {zero} (d) = d
mkNotZero {suc i} (diff k kp) = mkNotZero (diff (suc k) (kp ∙ cong suc (add-suc-r k i)))

-- abstract
killLeSuc2 : {j x n : ℕ} -> (p : j < x) -> (q : x < (suc n)) -> j < n
killLeSuc2 {j} {x} {n} (diff k p) (diff l q) = diff (l S+ k) proof
  where
    proof : n == suc (l S+ k S+ j)
    proof = n                      ≡⟨ cong pred q ⟩
            (l S+ x)               ≡⟨ cong (λ ξ -> (l S+ ξ)) p ⟩
            l S+ suc (k S+ j)      ≡⟨ (add-suc-r l (k S+ j))  ⟩
            suc (l S+ (k S+ j))    ≡⟨ cong suc (sym (assoc l k j)) ⟩
            suc (l S+ k S+ j)      ∎

killLeSuc = killLeSuc2


eq-to-leq : {i j : ℕ} -> i == j -> i < suc j
eq-to-leq {i} {j} p = diff zero (cong suc (sym p))

lt-to-leq : {i j : ℕ} -> i < j -> i < suc j
lt-to-leq {i} {j} (diff k kp) = diff (suc k) (cong suc kp)

0<suc : {i : ℕ} -> 0 < suc i
0<suc {i} = diff i (cong suc (sym (add-zero-r i)))


--------------------------------------
-- Type Properties

ℕOrd-isProp : {a b : ℕ} -> isProp (a < b)
ℕOrd-isProp {a} {b} (diff k kp) (diff l lp) i = diff (k=l i) (kp=kl i)
  where

    --------------------------------------
    -- Part I.
    -- Prove equality of the first component
    -- of the tuple.
    --
    k=l : k == l
    k=l = add-inj k l a (cong pred ((sym kp) ∙ lp))


    --------------------------------------
    -- Part II.
    -- Prove (dependent) equality of the
    -- second part of the tuple. That is,
    -- of the equation b == S x + a.
    eq : ℕ -> 𝒰₀
    eq x = b == suc x S+ a

    xlp : b == suc l S+ a
    xlp = subst {P = eq} k=l kp

    xlp=lp : xlp == lp
    xlp=lp = ℕ-isSet b (suc l S+ a) xlp lp

    kp=xlp : PathP (λ i -> eq (k=l (i))) kp xlp
    kp=xlp i = (subst-prop {P = eq} l k=l kp) (~ i)


    kp=kl : PathP (λ i -> b == suc (k=l i) S+ a) kp lp
    kp=kl i j = primComp (λ _ -> ℕ)
                         _
                         (λ { h (i = i0) -> kp (j)
                            ; h (i = i1) -> xlp=lp h (j)
                            ; h (j = i0) -> b
                            ; h (j = i1) -> suc (k=l i) S+ a
                         })
                         (kp=xlp i (j))




\end{code}
