import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem FCA_chap_A_ex_8 {n : ℕ} (m : ℕ) (hm : m ≤ n) :
  let Pi_m : Set (EuclideanSpace ℝ (Fin n)) :=
    {α | (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ ∑ i, α i = (m : ℝ)}
  Set.extremePoints ℝ Pi_m =
    {α : EuclideanSpace ℝ (Fin n) | (∀ i, α i = 0 ∨ α i = 1) ∧ ∑ i, α i = (m : ℝ)} := by
  sorry
