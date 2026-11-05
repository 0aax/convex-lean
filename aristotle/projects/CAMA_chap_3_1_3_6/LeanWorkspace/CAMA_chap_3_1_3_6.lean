import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

set_option maxHeartbeats 1000000 in
theorem CAMA_chap_3_1_3_6 {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n))) :
  ∀ x ∈ (convexHull ℝ S),
  ∃ (v : Fin (n + 1) → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin (n + 1))),
  (∀ i, v i ∈ S) ∧ (a.ofLp ∈ probSimplex (n + 1)) ∧ (x = ∑ i, a i • v i) := by
  sorry
