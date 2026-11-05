import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_19
  (m : ℕ)
  (fi : ℕ → E → ℝ)
  (hfi_convex : ∀ i ∈ Finset.range m, ConvexOn ℝ Set.univ (fi i))
  (hm : m ≥ 1) :
  let f := fun x => sInf {v | ∃ i ∈ Finset.range m, (fi i x) = v}
  ∃ (g h : E → ℝ),
    (ConvexOn ℝ Set.univ g) ∧ (ConvexOn ℝ Set.univ h) ∧
    (∀ x, f x = g x - h x) := by
  sorry
