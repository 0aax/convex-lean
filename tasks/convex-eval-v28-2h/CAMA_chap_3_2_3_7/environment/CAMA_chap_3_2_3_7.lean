import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def IsFaceOf {E : Type*} [AddCommGroup E] [Module ℝ E]
  (F K : Set E) : Prop :=
  Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ K F

theorem CAMA_chap_3_2_3_7
  (C : Set E)
  (F : Set E)
  (hF : IsFaceOf F C)
  (hC₀ : Set.Nonempty C)
  (hC₁ : Convex ℝ C) :
  ∀ (x : E), x ∈ (Set.extremePoints ℝ F) →
  x ∈ (Set.extremePoints ℝ C) := by
  sorry
