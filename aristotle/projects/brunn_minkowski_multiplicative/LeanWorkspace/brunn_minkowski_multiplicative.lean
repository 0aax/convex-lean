import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem brunn_minkowski_multiplicative {n : ℕ}
  (hn : 0 < n)
  {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  (A B : Set (EuclideanSpace ℝ (Fin n)))
  (hA_compact : IsCompact A) (hB_compact : IsCompact B) :
  volume ((1 - lam) • A + lam • B) ≥
    (volume A) ^ (1 - lam) * (volume B) ^ lam := by
  sorry
