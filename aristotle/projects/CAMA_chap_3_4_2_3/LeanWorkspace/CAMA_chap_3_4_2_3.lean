import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

theorem CAMA_chap_3_4_2_3 {n : ℕ}
    (S C : Set (EuclideanSpace ℝ (Fin n)))
    (hC : C = convexHull ℝ S) :
    ∀ x ∈ C ∩ frontier C,
      ∃ (v : Fin n → EuclideanSpace ℝ (Fin n)) (a : EuclideanSpace ℝ (Fin n)),
        (∀ i, v i ∈ S) ∧ (a.ofLp ∈ probSimplex n) ∧ x = ∑ i, a i • v i := by
  sorry
