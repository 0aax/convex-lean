import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_1_1
  (C : Set E)
  (x : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx : x ∉ C) :
  ∃ (s : E), (s ≠ 0) ∧
    BddAbove ((fun y => inner ℝ s y) '' C) ∧
    sSup ((fun y => inner ℝ s y) '' C) < inner ℝ s x := by
  sorry
