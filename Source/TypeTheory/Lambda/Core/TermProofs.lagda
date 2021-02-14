
\begin{code}[hide]

{-# OPTIONS --cubical #-}


open import TypeTheory.Lambda.Base
open import TypeTheory.Lambda.Param

module TypeTheory.Lambda.Core.TermProofs {i j} {param : LambdaParam i j} where

open import TypeTheory.Lambda.Core.Type {param = param}
open import TypeTheory.Lambda.Core.Term {param = param}
open import TypeTheory.Lambda.Core.TermSub {param = param}
open import TypeTheory.Lambda.Core.TermSingSub {param = param}

open LambdaParam param

----------------------------------------------------------------------
-- Term proofs






sucVsub0 : (s : Term) -> (i : ℕ) -> V (suc i) [ 0 / s ] == V i
sucVsub0 s i with compare-eq (suc i) 0
sucVsub0 s i | equal x = ⊥-elim (zNotS (sym x))
sucVsub0 s i | noteq x = refl




/suc : (i : ℕ) -> (t : Term) -> (j : ℕ) -> (suc i / (t ⇈ 0)) j == extT (i / t) j
/suc i t zero with compare zero (suc i)
... | p = refl
/suc i t (suc j) with compare (suc j) (suc i)
/suc i t (suc j) | less p with compare j i
/suc i t (suc j) | less p | less q with compare j i
/suc i t (suc j) | less p | less q | less r with compare j 0
/suc i t (suc j) | less p | less q | less r | less s = ⊥-elim (lessZero-⊥ s)
/suc i t (suc j) | less p | less q | less r | equal s = refl
/suc i t (suc j) | less p | less q | less r | greater s = refl
/suc i t (suc j) | less p | less q | equal x = ⊥-elim (lessEqual-⊥ q x)
/suc i t (suc j) | less p | less q | greater x = ⊥-elim (lessGreater-⊥ q x)
/suc i t (suc j) | less p | equal q = ⊥-elim (lessEqual-⊥ (pred-monotone p) q)
/suc i t (suc j) | less p | greater q = ⊥-elim (lessGreater-⊥ (pred-monotone p) q)
/suc i t (suc j) | equal p with compare j i
/suc i t (suc j) | equal p | less x = ⊥-elim (lessEqual-⊥ x (cong pred p))
/suc i t (suc j) | equal p | equal x = refl
/suc i t (suc j) | equal p | greater x = ⊥-elim (lessEqual-⊥ x (sym (cong pred p)))
/suc i t (suc j) | greater p with compare j i
/suc i t (suc j) | greater p | less q = ⊥-elim (lessGreater-⊥ (pred-monotone p) q)
/suc i t (suc j) | greater p | equal q = ⊥-elim (lessEqual-⊥ (pred-monotone p) (sym q))
/suc i t (suc j) | greater p | greater q with compare j i
/suc i t (suc j) | greater p | greater q | less r = ⊥-elim (lessGreater-⊥ q r)
/suc i t (suc j) | greater p | greater q | equal r = ⊥-elim (lessEqual-⊥ q (sym r))
/suc i t (suc 0) | greater p | greater q | greater r = ⊥-elim (lessZero-⊥ q)
/suc i t (suc (suc j)) | greater p | greater q | greater r with compare j 0
/suc i t (suc (suc j)) | greater p | greater q | greater r | less s = ⊥-elim (lessZero-⊥ s)
/suc i t (suc (suc j)) | greater p | greater q | greater r | equal s = refl
/suc i t (suc (suc j)) | greater p | greater q | greater r | greater s = refl

/same : (i : ℕ) -> (t : Term) -> (i / t) i == t
/same i t with compare i i
/same i t | less x = ⊥-elim $ lessEqual-⊥ x refl
/same i t | equal x = refl
/same i t | greater x = ⊥-elim $ lessEqual-⊥ x refl

/diff : (i j : ℕ) -> (p : j == i -> ⊥) -> (t : Term) -> (i / t) j == V (j ↧ i)
/diff i j p t with compare-eq j i
/diff i j p t | equal x = ⊥-elim $ p x
/diff i j p t | noteq x = refl -- λ 𝒊 -> V (i ↧ j ((contraEq x p) 𝒊))




↥↥ : (x i j : ℕ) -> (j < suc i) -> x ↥ i ↥ j == x ↥ j ↥ suc i
↥↥ x i j j<si with compare x i
↥↥ x i j j<si | less p with compare x j
↥↥ x i j j<si | less p | less q with compare x (suc i)
↥↥ x i j j<si | less p | less q | less r = refl
↥↥ x i j j<si | less p | less q | equal r = ⊥-elim (lessGreater-⊥ p (pred-monotone (eq-to-leq (sym r))))
↥↥ x i j j<si | less p | less q | greater r = ⊥-elim (lessGreater-⊥ p (pred-monotone (lt-to-leq r)))
↥↥ x i j j<si | less p | equal q with compare (suc x) (suc i)
↥↥ x i j j<si | less p | equal q | less r = refl
↥↥ x i j j<si | less p | equal q | equal r = ⊥-elim (lessEqual-⊥ p (cong pred r))
↥↥ x i j j<si | less p | equal q | greater r = ⊥-elim (lessGreater-⊥ p (pred-monotone r))
↥↥ x i j j<si | less p | greater q with compare (suc x) (suc i)
↥↥ x i j j<si | less p | greater q | less r = refl
↥↥ x i j j<si | less p | greater q | equal r = ⊥-elim (lessEqual-⊥ p (cong pred r))
↥↥ x i j j<si | less p | greater q | greater r = ⊥-elim (lessGreater-⊥ p (pred-monotone r))
↥↥ x i j j<si | equal p with compare x j
↥↥ x i j j<si | equal p | less q = ⊥-elim (less-antirefl (killLeSuc q (subst {P = λ ξ -> j < suc ξ} (sym p) j<si)))
↥↥ x i j j<si | equal p | equal q with compare (suc x) (suc i) | compare (suc x) j
↥↥ x i j j<si | equal p | equal q | less r    | _ = ⊥-elim (lessEqual-⊥ (pred-monotone r) p)
↥↥ x i j j<si | equal p | equal q | equal r   | less s    = ⊥-elim (lessGreater-⊥ s (eq-to-leq (sym q)))
↥↥ x i j j<si | equal p | equal q | equal r   | equal s   = refl
↥↥ x i j j<si | equal p | equal q | equal r   | greater s = refl
↥↥ x i j j<si | equal p | equal q | greater r | _ = ⊥-elim (lessEqual-⊥ (pred-monotone r) (sym p))
↥↥ x i j j<si | equal p | greater q with compare (suc x) (suc i) | compare (suc x) j
↥↥ x i j j<si | equal p | greater q | less r    | _ = ⊥-elim (lessEqual-⊥ (pred-monotone r) p)
↥↥ x i j j<si | equal p | greater q | equal r   | less s    = ⊥-elim (lessGreater-⊥ s (lt-to-leq q))
↥↥ x i j j<si | equal p | greater q | equal r   | equal s   = refl
↥↥ x i j j<si | equal p | greater q | equal r   | greater s = refl
↥↥ x i j j<si | equal p | greater q | greater r | _ = ⊥-elim (lessEqual-⊥ (pred-monotone r) (sym p))
↥↥ x i j j<si | greater p with compare x j
↥↥ x i j j<si | greater p | less q = ⊥-elim (lessGreater-⊥ p (killLeSuc q j<si))
↥↥ x i j j<si | greater p | equal q with compare (suc x) (suc i) | compare (suc x) j
↥↥ x i j j<si | greater p | equal q | less r    | _ = ⊥-elim (lessGreater-⊥ p (pred-monotone r))
↥↥ x i j j<si | greater p | equal q | equal r   | _ = ⊥-elim (lessEqual-⊥ p (sym (cong pred r)))
↥↥ x i j j<si | greater p | equal q | greater r | less s    = ⊥-elim (lessGreater-⊥ s (eq-to-leq (sym q)))
↥↥ x i j j<si | greater p | equal q | greater r | equal s   = refl
↥↥ x i j j<si | greater p | equal q | greater r | greater s = refl
↥↥ x i j j<si | greater p | greater q with compare (suc x) (suc i) | compare (suc x) j
↥↥ x i j j<si | greater p | greater q | less r    | _ = ⊥-elim (lessGreater-⊥ p (pred-monotone r))
↥↥ x i j j<si | greater p | greater q | equal r   | _ = ⊥-elim (lessEqual-⊥ p (sym (cong pred r)))
↥↥ x i j j<si | greater p | greater q | greater r | less s    = ⊥-elim (lessGreater-⊥ q (pred-monotone (lt-to-leq s)))
↥↥ x i j j<si | greater p | greater q | greater r | equal s   = refl
↥↥ x i j j<si | greater p | greater q | greater r | greater s = refl

⇈⇈ : (s : Term) -> (i j : ℕ) -> (j < suc i) -> (s ⇈ i) ⇈ j == (s ⇈ j) ⇈ suc i
⇈⇈ (cconst x) i j j<si = refl
⇈⇈ (V x) i j j<si = cong V (↥↥ x i j j<si)
⇈⇈ (Λ X s) i j j<si = cong (Λ X) (⇈⇈ s (suc i) (suc j) (suc-monotone j<si))
⇈⇈ (app f x) i j j<si = λ 𝒊 -> app (⇈⇈ f i j j<si 𝒊) (⇈⇈ x i j j<si 𝒊)

⇈⇈0 : (s : Term) -> (i : ℕ) -> (s ⇈ i) ⇈ 0 == (s ⇈ 0) ⇈ suc i
⇈⇈0 s i = ⇈⇈ s i 0 0<suc


↧<↥ : (x j i : ℕ) -> (x == j -> ⊥) -> (j < suc i) -> (x < suc i)-> (x ↧ j) ↥ i == x ↧ j
↧<↥ x j i x!=j j<si _ with compare x j
↧<↥ x j i x!=j j<si _ | less p with compare x i
↧<↥ x j i x!=j j<si _ | less p | less q = refl
↧<↥ x j i x!=j j<si _ | less p | equal q =
  let
      r0 : i < j
      r0 = subst {P = (λ ξ -> ξ < j)} q p

      r1 : i < i
      r1 = killLeSuc r0 j<si

  in ⊥-elim (lessGreater-⊥ r1 r1)
↧<↥ x j i x!=j j<si _ | less p | greater q = ⊥-elim (lessGreater-⊥ q (killLeSuc p j<si))
↧<↥ x j i x!=j j<si _ | equal p = ⊥-elim (x!=j p)
↧<↥ zero j i x!=j j<si _ | greater p = ⊥-elim (lessZero-⊥ p)
↧<↥ (suc x) j i x!=j j<si x<si | greater p with compare x i
↧<↥ (suc x) j i x!=j j<si x<si | greater p | less q = refl
↧<↥ (suc x) j i x!=j j<si x<si | greater p | equal q = ⊥-elim (lessEqual-⊥ (pred-monotone x<si) q)
↧<↥ (suc x) j i x!=j j<si x<si | greater p | greater q = ⊥-elim (lessGreater-⊥ (pred-monotone x<si) q)

↧≥↥ : (x j i : ℕ) -> (x == j -> ⊥) -> (j < suc i) -> (i < x) -> (suc x == j -> ⊥) -> (x ↧ j) ↥ i == (suc x ↧ j)
↧≥↥ x j i x!=j j<si i<x sx!=j with compare x j
↧≥↥ x j i x!=j j<si i<x sx!=j | less p with compare x i | compare (suc x) j
↧≥↥ x j i x!=j j<si i<x sx!=j | less p | less    q | _ = ⊥-elim (lessGreater-⊥ i<x q)
↧≥↥ x j i x!=j j<si i<x sx!=j | less p | equal   q | _ = ⊥-elim (lessEqual-⊥ i<x (sym q))
↧≥↥ x j i x!=j j<si i<x sx!=j | less p | greater q | less r = refl
↧≥↥ x j i x!=j j<si i<x sx!=j | less p | greater q | equal r = refl
↧≥↥ x j i x!=j j<si i<x sx!=j | less p | greater q | greater r = ⊥-elim (lessEqual-⊥ (killLeSuc p r) refl)
↧≥↥ x j i x!=j j<si i<x sx!=j | equal p = ⊥-elim (x!=j p)
↧≥↥ zero j i x!=j j<si i<x sx!=j | greater p = ⊥-elim (lessZero-⊥ p)
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p with compare x i | compare (suc (suc x)) j
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | less    q | _ = ⊥-elim (lessEqual-⊥ (killLeSuc q i<x) refl)
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | equal q | less r    = ⊥-elim (lessGreater-⊥ (lt-to-leq p) r)
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | equal q | equal r   = ⊥-elim (lessEqual-⊥ (lt-to-leq p) (sym r))
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | equal q | greater r = refl
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | greater q | less r    = ⊥-elim (lessGreater-⊥ (lt-to-leq p) r)
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | greater q | equal r   = ⊥-elim (lessEqual-⊥ (lt-to-leq p) (sym r))
↧≥↥ (suc x) j i x!=j j<si i<x sx!=j | greater p | greater q | greater r = refl



V[]⇈ : (x : ℕ) (s : Term) (j i : ℕ) -> j < (suc i) -> V x [ j / s ] ⇈ i == V x ⇈ suc i [ j / s ⇈ i ]
V[]⇈ x s j i j<si with compare x (suc i)
V[]⇈ x s j i j<si | less p with compare-eq x j
V[]⇈ x s j i j<si | less p | equal q = refl
V[]⇈ x s j i j<si | less p | noteq q = cong V (↧<↥ x j i q j<si p)
V[]⇈ x s j i j<si | equal p with compare-eq x j | compare-eq (suc x) j
V[]⇈ x s j i j<si | equal p | equal q | _ = ⊥-elim (lessEqual-⊥ j<si (sym q ∙ p))
V[]⇈ x s j i j<si | equal p | noteq q | equal r =
  let
      x<j = pred-monotone (eq-to-leq r)
      x<i = killLeSuc x<j j<si
      i<x = pred-monotone (eq-to-leq (sym p))
  in ⊥-elim (lessGreater-⊥ x<i i<x)
V[]⇈ x s j i j<si | equal p | noteq q | noteq r = cong V (↧≥↥ x j i q j<si (pred-monotone (eq-to-leq (sym p))) r)
V[]⇈ x s j i j<si | greater p with compare-eq x j | compare-eq (suc x) j
V[]⇈ x s j i j<si | greater p | equal q | _ = ⊥-elim (lessGreater-⊥ j<si (killLeSuc p (eq-to-leq q)))
V[]⇈ x s j i j<si | greater p | noteq q | equal r = ⊥-elim (lessGreater-⊥ j<si (killLeSuc p (lt-to-leq (pred-monotone (eq-to-leq r)))))
V[]⇈ x s j i j<si | greater p | noteq q | noteq r = cong V (↧≥↥ x j i q j<si (pred-monotone (lt-to-leq (p))) r)




[]⇈t : (r s : Term) -> (i j : ℕ) -> (j<i : j < (suc i)) -> (r [ j / s ] ⇈ i) == (r ⇈ suc i) [ j / (s ⇈ i) ]
[]⇈t (cconst x) s i j j<i = refl
[]⇈t (V x) s i j j<i = V[]⇈ x s j i j<i
[]⇈t (Λ X r) s i j j<i =
  let
      p00 : (r [ extT (j / s) ] ⇈ suc i) == r [ (suc j) / s ⇈ 0 ] ⇈ suc i
      p00 = cong (λ ξ -> r [ ξ ] ⇈ suc i) (sym (funExt (/suc j s)))

      p01 : r [ suc j / s ⇈ 0 ] ⇈ suc i == r ⇈ (suc (suc i)) [ suc j / (s ⇈ 0) ⇈ suc i ]
      p01 = []⇈t r (s ⇈ 0) (suc i) (suc j) (suc-monotone j<i)

      q00 : r ⇈ (suc (suc i)) [ suc j / s ⇈ 0 ⇈ (suc i) ] == r ⇈ (suc (suc i)) [ suc j / s ⇈ i ⇈ 0 ]
      q00 = cong (λ ξ -> r ⇈ (suc (suc i)) [ suc j / ξ ] ) (sym (⇈⇈0 s i))

      q01 : r ⇈ (suc (suc i)) [ suc j / s ⇈ i ⇈ 0 ] == r ⇈ (suc (suc i)) [ extT (j / s ⇈ i) ]
      q01 = cong (λ ξ -> r ⇈ (suc (suc i)) [ ξ ]) (funExt (/suc j (s ⇈ i)))

      p = p00 ∙ p01 ∙ q00 ∙ q01

  in cong (Λ X) p
[]⇈t (app f x) s i j j<i = λ 𝒊 -> app ([]⇈t f s i j j<i 𝒊) ([]⇈t x s i j j<i 𝒊)


[]⇈ : (r s : Term) -> (i : ℕ) -> (r [ 0 / s ] ⇈ i) == (r ⇈ suc i) [ 0 / (s ⇈ i) ]
[]⇈ r s i = []⇈t r s i 0 0<suc


V[]⇈> : (x i : ℕ) -> (u : Term) -> (j : ℕ) -> (j < suc i) -> (V x [ i / u ] ⇈ j) == (V x ⇈ j) [ suc i / (u ⇈ j) ]
V[]⇈> x i u j j<si with compare-eq x i | compare x j
V[]⇈> x i u j j<si | equal p | less q with compare x (suc i)
V[]⇈> x i u j j<si | equal p | less q | less x₁ = ⊥-elim (less-antirefl (killLeSuc q (killLeSuc j<si (suc-monotone (eq-to-leq (sym p))))))
V[]⇈> x i u j j<si | equal p | less q | equal x₁ = refl
V[]⇈> x i u j j<si | equal p | less q | greater x₁ = ⊥-elim (lessGreater-⊥ j<si (killLeSuc x₁ (lt-to-leq q)))
V[]⇈> x i u j j<si | equal p | equal   q with compare-eq (suc x) (suc i)
V[]⇈> x i u j j<si | equal p | equal q | equal x₁ = refl
V[]⇈> x i u j j<si | equal p | equal q | noteq x₁ = ⊥-elim (x₁ (cong suc p))
V[]⇈> x i u j j<si | equal p | greater q with compare-eq (suc x) (suc i)
V[]⇈> x i u j j<si | equal p | greater q | equal x₁ = refl
V[]⇈> x i u j j<si | equal p | greater q | noteq x₁ = ⊥-elim (x₁ (cong suc p))
V[]⇈> x i u j j<si | noteq p | less q with compare-eq x (suc i)
V[]⇈> x i u j j<si | noteq p | less q | equal r = ⊥-elim (lessGreater-⊥ (killLeSuc q j<si) (pred-monotone (eq-to-leq (sym r))))
V[]⇈> x i u j j<si | noteq p | less q | noteq r with compare x i
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s with compare x j | compare x (suc i)
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s | less t | less v = refl
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s | less t | equal v = refl
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s | less t | greater v = ⊥-elim (lessGreater-⊥ v (lt-to-leq s))
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s | equal t | v   = ⊥-elim (lessEqual-⊥ q t)
V[]⇈> x i u j j<si | noteq p | less q | noteq r | less s | greater t | v = ⊥-elim (lessGreater-⊥ q t)
V[]⇈> x i u j j<si | noteq p | less q | noteq r | equal s = ⊥-elim (p s)
V[]⇈> x i u j j<si | noteq p | less q | noteq r | greater s = ⊥-elim (lessGreater-⊥ s (killLeSuc q j<si))
V[]⇈> x i u j j<si | noteq p | equal q   with compare-eq (suc x) (suc i)
V[]⇈> x i u j j<si | noteq p | equal q | equal r = ⊥-elim (p (cong pred r))
V[]⇈> x i u j j<si | noteq p | equal q | noteq r with compare x i
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | less s with compare x j
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | less s | less t = ⊥-elim (lessEqual-⊥ t q)
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | less s | equal t = refl
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | less s | greater t = refl
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | equal s = ⊥-elim (p s)
V[]⇈> x i u j j<si | noteq p | equal q | noteq r | greater s = ⊥-elim (less-antirefl (killLeSuc j<si (suc-monotone (killLeSuc s (eq-to-leq q)))))
V[]⇈> x i u j j<si | noteq p | greater q with compare-eq (suc x) (suc i)
V[]⇈> x i u j j<si | noteq p | greater q | equal r = ⊥-elim (p (cong pred r))
V[]⇈> x i u j j<si | noteq p | greater q | noteq r with compare x i
V[]⇈> x i u j j<si | noteq p | greater q | noteq r | less s with compare x j
V[]⇈> x i u j j<si | noteq p | greater q | noteq r | less s | less t = ⊥-elim (lessGreater-⊥ q t)
V[]⇈> x i u j j<si | noteq p | greater q | noteq r | less s | equal t = refl
V[]⇈> x i u j j<si | noteq p | greater q | noteq r | less s | greater t = refl
V[]⇈> x i u j j<si | noteq p | greater q | noteq r | equal s = ⊥-elim (p s)
V[]⇈> zero i u j j<si | noteq p | greater q | noteq r | greater s = ⊥-elim (lessZero-⊥ s)
V[]⇈> (suc x) i u j j<si | noteq p | greater q | noteq r | greater s with compare x j
V[]⇈> (suc x) i u j j<si | noteq p | greater q | noteq r | greater s | less t = ⊥-elim (less-antirefl (killLeSuc t q))
V[]⇈> (suc x) i u j j<si | noteq p | greater q | noteq r | greater s | equal t = refl
V[]⇈> (suc x) i u j j<si | noteq p | greater q | noteq r | greater s | greater t = refl

[]⇈> : (s : Term) -> (i : ℕ) -> (u : Term) -> (j : ℕ) -> (j < suc i) -> (s [ i / u ] ⇈ j) == (s ⇈ j) [ suc i / (u ⇈ j) ]
[]⇈> (cconst x) i u j j<si = refl
[]⇈> (V x) i u j j<si = V[]⇈> x i u j j<si
[]⇈> (Λ x s) i u j j<si =
  let
      p : s [ extT (i / u) ] ⇈ suc j == s ⇈ suc j [ extT (suc i / u ⇈ j) ]
      p =
          s [ extT (i / u) ] ⇈ suc j             ≡⟨ sym (funExt (/suc i u)) |ctx| (λ ξ -> s [ ξ ] ⇈ suc j) ⟩
          s [ suc i / u ⇈ 0 ] ⇈ suc j           ≡⟨ []⇈> s (suc i) (u ⇈ 0) (suc j) (suc-monotone j<si) ⟩
          s ⇈ suc j [ suc (suc i) / u ⇈ 0 ⇈ suc j ]   ≡⟨ sym (⇈⇈0 u j) |ctx| (λ ξ -> s ⇈ suc j [ suc (suc i) / ξ ]) ⟩
          s ⇈ suc j [ suc (suc i) / u ⇈ j ⇈ 0 ]       ≡⟨ funExt (/suc (suc i) (u ⇈ j)) |ctx| (λ ξ -> s ⇈ suc j [ ξ ]) ⟩
          s ⇈ suc j [ extT (suc i / u ⇈ j) ]          ∎

  in cong (Λ x) p
[]⇈> (app f x) i u j j<si = λ 𝒊 -> app ([]⇈> f i u j j<si 𝒊) ([]⇈> x i u j j<si 𝒊)

[]⇈>₀ : (s : Term) -> (i : ℕ) -> (u : Term) -> (s [ i / u ] ⇈ 0) == (s ⇈ 0) [ suc i / (u ⇈ 0) ]
[]⇈>₀ s i u = []⇈> s i u 0 0<suc




⇈=/ : (u : Term) -> (i : ℕ) -> (s : Term) -> u ⇈ i [ i / s ] == u
⇈=/ (cconst x) i s = refl
⇈=/ (V x) i s with compare x i
⇈=/ (V x)       i s | less p with compare-eq x i
⇈=/ (V x)       i s | less p | equal q = ⊥-elim (lessEqual-⊥ p q)
⇈=/ (V x)       i s | less p | noteq q with compare x i
⇈=/ (V x)       i s | less p | noteq q | less r = refl
⇈=/ (V x)       i s | less p | noteq q | equal r = refl
⇈=/ (V zero)    i s | less p | noteq q | greater r = ⊥-elim (lessZero-⊥ r)
⇈=/ (V (suc x)) i s | less p | noteq q | greater r = ⊥-elim (lessGreater-⊥ p r)
⇈=/ (V x)       i s | equal p with compare (suc x) i
⇈=/ (V x) i s | equal p | less q    = ⊥-elim (lessGreater-⊥ q (eq-to-leq (sym p)))
⇈=/ (V x) i s | equal p | equal q   = ⊥-elim (iNotSi (p ∙ sym q))
⇈=/ (V x) i s | equal p | greater q with compare (suc x) i
⇈=/ (V x) i s | equal p | greater q | less r = ⊥-elim (lessGreater-⊥ q r)
⇈=/ (V x) i s | equal p | greater q | equal r = ⊥-elim (lessEqual-⊥ q (sym r))
⇈=/ (V x) i s | equal p | greater q | greater r = refl
⇈=/ (V x)       i s | greater p with compare-eq (suc x) i
⇈=/ (V x) i s | greater p | equal q = ⊥-elim (lessGreater-⊥ p (pred-monotone (eq-to-leq q)))
⇈=/ (V x) i s | greater p | noteq q with compare (suc x) i
⇈=/ (V x) i s | greater p | noteq q | less r = ⊥-elim (lessGreater-⊥ p (pred-monotone (lt-to-leq r)))
⇈=/ (V x) i s | greater p | noteq q | equal r = ⊥-elim (lessGreater-⊥ p (pred-monotone (eq-to-leq r)))
⇈=/ (V x) i s | greater p | noteq q | greater r = refl
⇈=/ (Λ x u) i s =
  let
      p1 : u ⇈ (suc i) [ extT (i / s) ] == u ⇈ (suc i) [ suc i / s ⇈ 0 ]
      p1 = cong (λ ξ -> u ⇈ (suc i) [ ξ ]) (sym (funExt (/suc i s)))

  in cong (Λ x) (p1 ∙ ⇈=/ u (suc i) (s ⇈ 0))
⇈=/ (app f x) i s = λ 𝒊 -> app (⇈=/ f i s 𝒊) (⇈=/ x i s 𝒊)





Vsubrot : (s u : Term) -> (x j i : ℕ) -> (j < suc i) -> V x [ j / s ] [ i / u ] == V x [ suc i / u ⇈ j ] [ j / (s [ i / u ])]
Vsubrot s u       x j i j<si with compare-eq x j
Vsubrot s u       x j i j<si | equal p with compare-eq x (suc i)
Vsubrot s u       x j i j<si | equal p | equal q = ⊥-elim (lessEqual-⊥ j<si (sym p ∙ q))
Vsubrot s u       x j i j<si | equal p | noteq q with compare-eq (x ↧ suc i) j
Vsubrot s u       x j i j<si | equal p | noteq q | equal r = refl
Vsubrot s u       x j i j<si | equal p | noteq q | noteq r with compare x (suc i)
Vsubrot s u       x j i j<si | equal p | noteq q | noteq r | less v = ⊥-elim (r p)
Vsubrot s u       x j i j<si | equal p | noteq q | noteq r | equal v = ⊥-elim (r p)
Vsubrot s u zero    j i j<si | equal p | noteq q | noteq r | greater v = ⊥-elim (lessZero-⊥ v)
Vsubrot s u (suc x) j i j<si | equal p | noteq q | noteq r | greater v = ⊥-elim (lessGreater-⊥ (killLeSuc j<si v) (pred-monotone (eq-to-leq p)))
Vsubrot s u       x j i j<si | noteq p with compare-eq (x ↧ j) i | compare-eq x (suc i)
Vsubrot s u       x j i j<si | noteq p | equal q | equal r with compare x j
Vsubrot s u       x j i j<si | noteq p | equal q | equal r | less v    = ⊥-elim (iNotSi (sym q ∙ r))
Vsubrot s u       x j i j<si | noteq p | equal q | equal r | equal v   = ⊥-elim (iNotSi (sym q ∙ r))
Vsubrot s u zero    j i j<si | noteq p | equal q | equal r | greater v = ⊥-elim (lessZero-⊥ v)
Vsubrot s u (suc x) j i j<si | noteq p | equal q | equal r | greater v = sym (⇈=/ u j (s [ i / u ]))
Vsubrot s u       x j i j<si | noteq p | equal q | noteq r with compare x j
Vsubrot s u       x j i j<si | noteq p | equal q | noteq r | less v    = ⊥-elim (less-antirefl (killLeSuc (subst {P = λ ξ -> ξ < j} q v) j<si))
Vsubrot s u       x j i j<si | noteq p | equal q | noteq r | equal v   = ⊥-elim (p v)
Vsubrot s u zero    j i j<si | noteq p | equal q | noteq r | greater v = ⊥-elim (lessZero-⊥ v)
Vsubrot s u (suc x) j i j<si | noteq p | equal q | noteq r | greater v = ⊥-elim (r (cong suc q))
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r with compare x j
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r | less v with compare x i
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r | less v | less w = ⊥-elim (lessGreater-⊥ w (pred-monotone (eq-to-leq (sym r))))
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r | less v | equal w = ⊥-elim (q w)
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r | less v | greater w = ⊥-elim (lessGreater-⊥ j<si (subst {P = λ ξ -> ξ < j} r v))
Vsubrot s u       x j i j<si | noteq p | noteq q | equal r | equal v = ⊥-elim (p v)
Vsubrot s u zero    j i j<si | noteq p | noteq q | equal r | greater v = ⊥-elim (lessZero-⊥ v)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | equal r | greater v = ⊥-elim (q (cong pred r))
Vsubrot s u       x j i j<si | noteq p | noteq q | noteq r with compare x j
Vsubrot s u       x j i j<si | noteq p | noteq q | noteq r | less v    with compare x i | compare x (suc i)
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ with compare-eq x j
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | equal x₃ = ⊥-elim (p x₃)
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | noteq x₃ with compare x j
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | noteq x₃ | less x₄ = refl
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | noteq x₃ | equal x₄ = ⊥-elim (p x₄)
Vsubrot s u zero    j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | noteq x₃ | greater x₄ = ⊥-elim (lessZero-⊥ x₄)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | less x₂ | noteq x₃ | greater x₄ = ⊥-elim (lessGreater-⊥ v x₄)
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | equal x₂ = ⊥-elim (lessGreater-⊥ x₁ (pred-monotone (eq-to-leq (sym x₂))))
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | less x₁ | greater x₂ = ⊥-elim (lessGreater-⊥ x₁ (pred-monotone (lt-to-leq x₂)))
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | equal x₁ | _ = ⊥-elim (q x₁)
Vsubrot s u x j i j<si | noteq p | noteq q | noteq r | less v | greater x₁ | y = ⊥-elim (lessGreater-⊥ x₁ (killLeSuc v j<si))
Vsubrot s u       x j i j<si | noteq p | noteq q | noteq r | equal v   = ⊥-elim (p v)
Vsubrot s u zero    j i j<si | noteq p | noteq q | noteq r | greater v = ⊥-elim (lessZero-⊥ v)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v with compare x i | compare (suc x) (suc i)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ with compare-eq (suc x) j
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ | equal x₃ = ⊥-elim (p x₃)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ | noteq x₃ with compare (suc x) j
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ | noteq x₃ | less x₄ = ⊥-elim (lessGreater-⊥ v x₄)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ | noteq x₃ | equal x₄ = ⊥-elim (p x₄)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | less x₂ | noteq x₃ | greater x₄ = refl
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | equal x₂ = ⊥-elim (r x₂)
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | less x₁ | greater x₂ = ⊥-elim (lessGreater-⊥ x₁ (pred-monotone x₂))
Vsubrot s u (suc x) j i j<si | noteq p | noteq q | noteq r | greater v | equal x₁ | z = ⊥-elim (q x₁)
Vsubrot s u (suc zero) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | z = ⊥-elim (lessZero-⊥ x₁)
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | less x₂ = ⊥-elim (lessGreater-⊥ x₁ (pred-monotone x₂))
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | equal x₂ = ⊥-elim (r x₂)
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ with compare-eq (suc x) j
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ | equal x₃ = ⊥-elim (less-antirefl (killLeSuc j<si (killLeSuc x₂ (suc-monotone (eq-to-leq x₃)))))
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ | noteq x₃ with compare (suc x) j
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ | noteq x₃ | less x₄ = ⊥-elim (less-antirefl (killLeSuc x₄ v))
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ | noteq x₃ | equal x₄ = ⊥-elim (x₃ x₄)
Vsubrot s u (suc (suc x)) j i j<si | noteq p | noteq q | noteq r | greater v | greater x₁ | greater x₂ | noteq x₃ | greater x₄ = refl


subrot : ∀(r s u : Term) -> (j i : ℕ) -> (j < suc i) -> r [ j / s ] [ i / u ] == r [ suc i / u ⇈ j ] [ j / (s [ i / u ])]
subrot (cconst x) (s) (u) j i j<si = refl
subrot (V x) (s) (u) j i j<si = Vsubrot s u x j i j<si
subrot (Λ X r) (s) (u) j i j<si =
  let
      P : r [ extT (j / s) ] [ extT (i / u) ] == r [ extT (suc i / u ⇈ j) ] [ extT (j / s [ i / u ]) ]
      P =
          r [ extT (j / s) ] [ extT (i / u) ]         ≡⟨ sym (funExt (/suc j s)) |ctx| (λ ξ -> r [ ξ ] [ extT (i / u)]) ⟩
          r [ suc j / s ⇈ 0 ] [ extT (i / u) ]       ≡⟨ sym (funExt (/suc i u)) |ctx| (λ ξ -> r [ suc j / s ⇈ 0 ] [ ξ ]) ⟩
          r [ suc j / s ⇈ 0 ] [ suc i / u ⇈ 0 ]      ≡⟨ subrot r (s ⇈ 0) (u ⇈ 0) (suc j) (suc i) (suc-monotone j<si) ⟩
          r [ suc (suc i) / u ⇈ 0 ⇈ (suc j) ] [ suc j / s ⇈ 0 [ suc i / u ⇈ 0 ] ]   ≡⟨ sym ([]⇈>₀ s i u) |ctx| (λ ξ -> r [ suc (suc i) / u ⇈ 0 ⇈ (suc j) ] [ suc j / ξ ]) ⟩
          r [ suc (suc i) / u ⇈ 0 ⇈ (suc j) ] [ suc j / s [ i / u ] ⇈ 0 ]            ≡⟨ funExt (/suc j (s [ i / u ])) |ctx| (λ ξ -> r [ suc (suc i) / u ⇈ 0 ⇈ (suc j) ] [ ξ ]) ⟩
          r [ suc (suc i) / u ⇈ 0 ⇈ (suc j) ] [ extT (j / s [ i / u ]) ]             ≡⟨ sym (⇈⇈0 u j) |ctx| (λ ξ -> r [ suc (suc i) / ξ ] [ extT (j / s [ i / u ]) ]) ⟩
          r [ suc (suc i) / u ⇈ j ⇈ 0 ] [ extT (j / s [ i / u ]) ]                   ≡⟨ funExt (/suc (suc i) (u ⇈ j)) |ctx| (λ ξ -> r [ ξ ] [ extT (j / s [ i / u ]) ]) ⟩
          r [ extT (suc i / u ⇈ j) ] [ extT (j / s [ i / u ]) ]                      ∎

  in cong (Λ X) P
subrot (app f x) (s) (u) j i j<si = λ 𝒊 -> app (subrot f s u j i j<si 𝒊) (subrot x s u j i j<si 𝒊)


subrot0 : ∀(r s u : Term) -> (i : ℕ) -> r [ 0 / s ] [ i / u ] == r [ suc i / u ⇈ 0 ] [ 0 / (s [ i / u ])]
subrot0 r s u i = subrot r s u 0 i 0<suc

\end{code}

