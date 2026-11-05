import Mathlib

open MeasureTheory Metric

def kneser_poulsen : Prop :=
  ∀ (m n : ℕ) (a b : Fin m → EuclideanSpace ℝ (Fin n)) (r : Fin m → ℝ),
    (r > 0) →
    (∀ i j : Fin m, ‖a i - a j‖ ≤ ‖b i - b j‖) →
    volume (⋃ i : Fin m, ball (a i) (r i)) ≤ volume (⋃ i : Fin m, ball (b i) (r i))
