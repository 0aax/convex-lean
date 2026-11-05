import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem Duchi_T10_2_1
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_closed : LowerSemicontinuous f)
  (x₀ : EuclideanSpace ℝ (Fin n))
  (ε δ : ℝ)
  (hε : 0 ≤ ε)
  (hx₀_fin : f x₀ < ⊤)
  (hx₀_near : ∀ y, f x₀ ≤ f y + ↑ε)
  (hδ : 0 < δ)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∃ (x_hat : EuclideanSpace ℝ (Fin n)),
  (‖x_hat - x₀‖ ≤ ε / δ) ∧
  (f x_hat ≤ f x₀) ∧
  (∀ x, f x_hat ≤ f x + ↑(δ * ‖x - x_hat‖)) ∧
  (∀ x, f x + ↑(δ * ‖x - x_hat‖) = f x_hat → x = x_hat) := by
  sorry
