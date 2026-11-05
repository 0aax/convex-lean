import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped Gradient RealInnerProductSpace


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

theorem gradient_descent_smooth_strongly_convex_bound {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (α β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (hf_strongly_convex : StrongConvexOn Set.univ α f)
  (h_gd_seq : IsGradientDescentSequence f x (2 / (α + β)))
  (hx_star : IsMinOn f Set.univ x_star) :
  let κ := β / α
  f (x t) - f x_star ≤ (β / 2) * Real.exp (- (4 * t)/ (κ + 1)) * ‖x 0 - x_star‖ ^ 2 := by
  sorry
