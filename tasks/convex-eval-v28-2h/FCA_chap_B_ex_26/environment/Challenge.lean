import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_26 (f : E → ℝ) (L : ℝ) (hL_pos : L > 0)
    (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f) :
    List.TFAE [
      ∀ (x x' : E), ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖,
      ∀ (x x' : E),
        f x' ≥ f x + inner ℝ (gradient f x) (x' - x) +
          1 / (2 * L) * ‖gradient f x - gradient f x'‖ ^ 2,
      ∀ (x x' : E),
        inner ℝ (gradient f x - gradient f x') (x - x') ≥
          1 / L * ‖gradient f x - gradient f x'‖ ^ 2] := by
  sorry
