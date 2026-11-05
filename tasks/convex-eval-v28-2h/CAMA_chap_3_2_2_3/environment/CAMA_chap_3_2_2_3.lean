import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

theorem CAMA_chap_3_2_2_3
  (C : Set E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (IsCompact C) ↔ ∀ x ∈ C, (asymptoticConeAt C x) = {0} := by
  sorry
