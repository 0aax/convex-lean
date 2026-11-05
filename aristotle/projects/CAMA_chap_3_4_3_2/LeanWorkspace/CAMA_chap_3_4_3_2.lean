import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def cone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (x : Fin m → E) : Set E :=
  {v : E | ∃ (α : Fin m → ℝ) (_ : ∀ i, α i ≥ 0), v = ∑ i, α i • x i}

theorem CAMA_chap_3_4_3_2 {m n : ℕ}
  (b : EuclideanSpace ℝ (Fin n))
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  let P := b ∈ cone s
  let Q := ∃ (x : EuclideanSpace ℝ (Fin n)), (inner ℝ b x > 0) ∧ (∀ j, inner ℝ (s j) x ≤ 0)
  (P ∨ Q) ∧ ¬(P ∧ Q) := by
  sorry
