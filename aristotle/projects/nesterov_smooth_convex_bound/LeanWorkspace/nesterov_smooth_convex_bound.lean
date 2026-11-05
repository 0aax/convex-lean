import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {n : ℕ}

noncomputable def nesterovStepAlphaZero {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (y : EuclideanSpace ℝ (Fin n))
  (β lambda : ℝ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let lambda_next := (1 + (Real.sqrt (1 + 4 * lambda^2))) / 2
  let γ := (1 - lambda) / lambda_next
  let y_next := x - (1 / β) • (gradient f x)
  let x_next := (1 - γ) • y_next + γ • y
  (y_next, x_next)

def IsNesterovSequenceAlphaZero {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ)
  (lambda : ℕ → ℝ) : Prop :=
  (∀ t, y (t + 1) = (nesterovStepAlphaZero f (x t) (y t) β (lambda t)).1) ∧
  (∀ t, x (t + 1) = (nesterovStepAlphaZero f (x t) (y t) β (lambda t)).2) ∧
  (lambda 0 = 0) ∧
  (∀ t, lambda (t + 1) = (1 + (Real.sqrt (1 + 4 * (lambda t)^2))) / 2)

theorem nesterov_smooth_convex_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n)) (y : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (lambda : ℕ → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0) (ht_one : t ≥ 1)
  (hxy_init : x 0 = (y 0))
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_nesterov_seq : IsNesterovSequenceAlphaZero f x y β lambda)
  (hx_star : IsMinOn f Set.univ x_star) :
  f (y t) - f x_star
  ≤ (2 * β) * ‖x 0 - x_star‖^2 / t^2 := by
  sorry
