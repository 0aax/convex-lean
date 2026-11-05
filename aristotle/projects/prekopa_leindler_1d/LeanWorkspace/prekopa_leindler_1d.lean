import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Set


theorem prekopa_leindler_1d
  {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  {f g h : ℝ → ℝ≥0∞}
  (hf : Measurable f) (hg : Measurable g)
  (hh : Measurable h)
  (hyp : ∀ x y : ℝ,
    h ((1 - lam) * x + lam * y) ≥
      (f x) ^ (1 - lam) * (g y) ^ lam) :
  ∫⁻ z, h z ≥
    (∫⁻ z, f z) ^ (1 - lam) *
    (∫⁻ z, g z) ^ lam := by
  sorry
