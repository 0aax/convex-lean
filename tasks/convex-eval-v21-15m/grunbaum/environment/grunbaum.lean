import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def barycenter {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  (K : Set E) : E :=
  (MeasureTheory.volume.real K)⁻¹ • ∫ x in K, x

theorem grunbaum {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (w : EuclideanSpace ℝ (Fin n))
  (hK_compact : IsCompact K)
  (hK_convex : Convex ℝ K)
  (hK_int : Set.Nonempty (interior K))
  (hK_centered : barycenter K = 0)
  (hw : w ≠ 0) :
  (volume (K ∩ {x | 0 ≤ inner ℝ w x})).toReal ≥
    Real.exp (-1) * (volume K).toReal := by
  sorry
