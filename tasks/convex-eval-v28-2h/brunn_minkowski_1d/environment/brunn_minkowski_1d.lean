import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem brunn_minkowski_1d
    (A B : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA_ne : A.Nonempty) (hB_ne : B.Nonempty) :
    volume (A + B) ≥ volume A + volume B := by
  sorry
