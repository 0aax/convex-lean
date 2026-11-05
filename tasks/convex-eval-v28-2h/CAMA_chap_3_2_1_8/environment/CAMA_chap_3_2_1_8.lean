import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def affineHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Set E
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → E) (_ : ∀ i, x i ∈ C),
     {v : E |
      ∃ (a : Fin k → ℝ), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

theorem CAMA_chap_3_2_1_8
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C) :
  (affineHull (intrinsicInterior ℝ C) = affineHull C) ∧
  (affineHull (closure C) = affineHull C) ∧
  (intrinsicInterior ℝ (intrinsicInterior ℝ C) = intrinsicInterior ℝ C) ∧
  (intrinsicInterior ℝ (closure C) = intrinsicInterior ℝ C) ∧
  (closure (intrinsicInterior ℝ C) = closure C) := by
  sorry
