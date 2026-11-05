import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def hsInner {n : ℕ}
    (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ i : Fin n, inner ℝ (A (EuclideanSpace.single i 1)) (B (EuclideanSpace.single i 1))

noncomputable def hsInnerSA {n : ℕ}
    (A B : selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) : ℝ :=
  hsInner (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
          (B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))

def conePolarSA {n : ℕ}
    (K : Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {P | ∀ M ∈ K, hsInnerSA M P ≤ 0}

def negPsdCone (n : ℕ) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {A | ∀ x, inner ℝ ((A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x) x ≤ 0}

def psdCone (n : ℕ) :
    Set (selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))) :=
  {A | ∀ x, 0 ≤ inner ℝ ((A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) x) x}

theorem FCA_chap_A_ex_15 {n : ℕ} :
  (conePolarSA (psdCone n) = negPsdCone n) ∧
  (∀ M : selfAdjoint (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    ∃ Mp Mn : selfAdjoint _,
      Mp ∈ psdCone n ∧ Mn ∈ negPsdCone n ∧
      M = Mp + Mn ∧ hsInnerSA Mp Mn = 0) := by
  sorry
