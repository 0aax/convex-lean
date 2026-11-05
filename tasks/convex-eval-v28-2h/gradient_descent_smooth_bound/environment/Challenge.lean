import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def gradientDescentStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (η : ℝ) : EuclideanSpace ℝ (Fin n) :=
  x - η • (gradient f x)

def IsGradientDescentSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Prop :=
  (∀ t, x (t + 1) = gradientDescentStep f (x t) η)

set_option maxHeartbeats 1000000 in
theorem gradient_descent_smooth_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0) (ht_one : t ≥ 1)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_gd_seq : IsGradientDescentSequence f x (1 / β))
  (hx_star : IsMinOn f Set.univ x_star) :
  f (x t) - f x_star ≤ (2 * β) * ‖x 0 - x_star‖ ^ 2 / t := by
  sorry
