import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_1_1_2
  (c : ℝ)
  (C : Set E)
  (f : E → ℝ)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C) :
  StrongConvexOn C c f ↔ ConvexOn ℝ C (fun x => f x - (c/2) * ‖x‖^2) := by
  sorry
