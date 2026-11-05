import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem Duchi_L2_3_1 {n : ℕ}
    (x y : Fin n → ℝ)
    (hx_sorted : Antitone x)
    (hy_sorted : Antitone y)
    (σ : Equiv.Perm (Fin n)) :
    ((∑ i, x i * (y ∘ σ) i) ≤ ∑ i, x i * y i) ∧
      ((∑ i, x i * (y ∘ σ) i) = ∑ i, x i * y i ↔
        ∃ τ : Equiv.Perm (Fin n), x ∘ τ = x ∧ (y ∘ σ) ∘ τ = y) := by
  sorry
