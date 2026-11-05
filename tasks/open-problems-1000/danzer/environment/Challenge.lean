import Mathlib

open MeasureTheory

def IsDanzerSet
  {d : ℕ}
  (Y : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∀ K : ConvexBody (EuclideanSpace ℝ (Fin d)), (volume K.carrier) = 1 -> Y ∩ K ≠ ∅

def IsBoundedDensity
  {d : ℕ}
  (Y : Set (EuclideanSpace ℝ (Fin d))) : Prop :=
  ∃ C : ℕ, ∀ x : EuclideanSpace ℝ (Fin d), Set.encard ((Euclidean.ball x 1) ∩ Y) ≤ C

def danzer_bounded_density : Prop :=
  ∀ (d : ℕ),
    d ≥ 2 →
    ¬∃ (Y : Set (EuclideanSpace ℝ (Fin d))), IsDanzerSet Y ∧ IsBoundedDensity Y

theorem danzer_bounded_density_POS : danzer_bounded_density := by
  sorry

theorem danzer_bounded_density_NEG : ¬ danzer_bounded_density := by
  sorry
