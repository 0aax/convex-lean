import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

theorem CAMA_chap_3_2_2_1
  (C : Set E)
  (x₁ x₂ : E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hx₁ : x₁ ∈ C)
  (hx₂ : x₂ ∈ C) :
  (asymptoticConeAt C x₁) = (asymptoticConeAt C x₂) := by
  sorry
