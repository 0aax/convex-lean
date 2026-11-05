import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def cone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (x : Fin m → E) : Set E :=
  {v : E | ∃ (α : Fin m → ℝ) (_ : ∀ i, α i ≥ 0), v = ∑ i, α i • x i}

theorem CAMA_chap_3_4_3_1 {m : ℕ}
  (b : E)
  (s : Fin m → E) :
  {x : E | ∀ j, inner ℝ (s j) x ≤ 0} ⊆
  {x | inner ℝ b x ≤ 0} ↔ b ∈ cone s := by
  sorry
