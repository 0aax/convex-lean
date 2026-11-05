import Mathlib

open MeasureTheory

def IsSymmetricSet {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

noncomputable def supportFun
  {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup ((fun y => inner ℝ x y) '' K)

def logMinkowski
  (lam : ℝ)
  (K L : ConvexBody (EuclideanSpace ℝ (Fin n))) :
  Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ u, inner ℝ x u ≤ (supportFun K u) ^ (1 - lam) * (supportFun L u) ^ lam}

def log_brunn_minkowski : Prop :=
  ∀ (n : ℕ) (K L : ConvexBody (EuclideanSpace ℝ (Fin n))),
    IsSymmetricSet K.carrier →
    IsSymmetricSet L.carrier →
      ∀ (c : ℝ), (c ∈ Set.Icc 0 1) →
        volume (logMinkowski c K L) ≥ (volume K.carrier) ^ (1 - c) * (volume L.carrier) ^ c
