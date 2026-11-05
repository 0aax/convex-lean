import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

def conv {n : ℕ} (S : Set (EuclideanSpace ℝ (Fin n))) : Set (EuclideanSpace ℝ (Fin n))
    := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → (EuclideanSpace ℝ (Fin n))) (_ : ∀ i, x i ∈ S),
         {v : (EuclideanSpace ℝ (Fin n)) |
          ∃ (a : (EuclideanSpace ℝ (Fin k))),
          (a.ofLp ∈ (probSimplex k)) ∧ (v = ∑ i, a i • x i)}

set_option maxHeartbeats 1000000 in
theorem CAMA_chap_3_1_3_4 {n : ℕ}
  (C : Set (EuclideanSpace ℝ (Fin n))) :
  (convexHull ℝ C) = (conv C) := by
  sorry
