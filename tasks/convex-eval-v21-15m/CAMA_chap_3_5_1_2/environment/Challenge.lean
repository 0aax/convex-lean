import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_5_1_2
  (d : E)
  (S : Set E)
  (x : E) :
  (d ∈ posTangentConeAt S x) ↔
  ∃ (dk : ℕ → E), ∃ (tk : ℕ → ℝ),
  (Filter.Tendsto dk Filter.atTop (𝓝 d)) ∧
  (Filter.Tendsto tk Filter.atTop (𝓝 0)) ∧
  (∀ i, tk i > 0) ∧
  (∀ k, x + (tk k) • (dk k) ∈ S) := by
  sorry
