import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def cone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {m : ℕ} (x : Fin m → E) : Set E :=
  {v : E | ∃ (α : Fin m → ℝ) (_ : ∀ i, α i ≥ 0), v = ∑ i, α i • x i}

theorem CAMA_chap_3_4_3_3 {m n : ℕ}
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  IsClosed (cone s) := by
  sorry
