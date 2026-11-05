import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem brunn_minkowski {n : ℕ}
  (hn : 0 < n)
  (A B : Set (EuclideanSpace ℝ (Fin n)))
  (hA_compact : IsCompact A)
  (hB_compact : IsCompact B)
  (hA_nonempty : A.Nonempty)
  (hB_nonempty : B.Nonempty) :
  Real.rpow ((volume (A + B)).toReal) (1 / (n : ℝ)) ≥
    Real.rpow ((volume A).toReal) (1 / (n : ℝ)) +
    Real.rpow ((volume B).toReal) (1 / (n : ℝ)) := by
  sorry
