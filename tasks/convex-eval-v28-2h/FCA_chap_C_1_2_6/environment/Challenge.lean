import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def gaugeFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x : E) : EReal :=
  sInf {l : EReal | ∃ (l' : ℝ),
                        (l = (l' : EReal)) ∧
                        (l' > 0) ∧
                        (∃ y ∈ C, (x = l' • y))}

theorem FCA_chap_C_1_2_6
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let g : E → EReal := fun x => gaugeFun C x
  (IsCompact C) ↔ (∀ x, x ≠ 0 → g x > 0) := by
  sorry
