import Mathlib
open MeasureTheory Pointwise

def IsSymmetricSet (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ x, x ∈ K ↔ -x ∈ K

def IsSymmetricConvexDisc (K : Set (EuclideanSpace ℝ (Fin 2))) : Prop :=
  Convex ℝ K
  ∧ IsCompact K
  ∧ (interior K).Nonempty
  ∧ IsSymmetricSet K

def IsPacking (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))) : Prop :=
  ∀ i j, i ≠ j → Disjoint (interior (g i '' K)) (interior (g j '' K))

def packedRegion (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → (EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  ⋃ i, g i '' K

noncomputable def packingDensityOf (K : Set (EuclideanSpace ℝ (Fin 2)))
    (g : ℕ → EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Filter.limsup
    (fun r : ℝ =>
      (volume (packedRegion K g ∩ Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal /
        (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r)).toReal)
    Filter.atTop

noncomputable def packingDensity (K : Set (EuclideanSpace ℝ (Fin 2))) : ℝ :=
  sSup {d | ∃ g : ℕ → EuclideanSpace ℝ (Fin 2) ≃ᵢ EuclideanSpace ℝ (Fin 2),
    IsPacking K g ∧ d = packingDensityOf K g}

def reinhardt : Prop :=
  ∀ (K : Set (EuclideanSpace ℝ (Fin 2))),
    IsSymmetricConvexDisc K →
    packingDensity K ≥ ((8 - 4 * Real.sqrt 2 - Real.log 2) / (2 * Real.sqrt 2 - 1) : ℝ)

theorem reinhardt_POS : reinhardt := by
  sorry

theorem reinhardt_NEG : ¬ reinhardt := by
  sorry
