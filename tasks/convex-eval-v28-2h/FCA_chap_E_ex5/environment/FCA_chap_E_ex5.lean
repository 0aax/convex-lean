import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_ex5 {k : ℕ}
  (s : ℕ → E)
  (b : ℕ → ℝ) :
  let P := {x : E | ∀ i ∈ Finset.range k, inner ℝ (s i) x ≤ (b i)}
  (P ≠ ∅) ↔
    (∀ (α : ℕ → ℝ),
      ((∀ i ∈ Finset.range k, α i ≥ 0) ∧
      (∑ i ∈ Finset.range k, (α i) • (s i) = 0)) →
        (∑ i ∈ Finset.range k, (α i) • (b i) ≥ 0)) := by
  sorry
