import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open RealInnerProductSpace


noncomputable def nesterovStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) (y : EuclideanSpace ℝ (Fin n))
  (α β : ℝ) : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
  let κ := β / α
  let κ_term := (Real.sqrt κ - 1) / (Real.sqrt κ + 1)
  let y_next := x - (1 / β) • (gradient f x)
  let x_next := (1 + κ_term) • y_next - κ_term • y
  (y_next, x_next)

def IsNesterovSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (α β : ℝ) : Prop :=
  (∀ t, y (t + 1) = (nesterovStep f (x t) (y t) α β).1) ∧
  (∀ t, x (t + 1) = (nesterovStep f (x t) (y t) α β).2)

theorem nesterov_smooth_strongly_convex_bound {n t : ℕ}
    (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n))
    (y : ℕ → EuclideanSpace ℝ (Fin n))
    (α β : ℝ)
    (x_star : EuclideanSpace ℝ (Fin n))
    (hβ_pos : β > 0)
    (hα_pos : α > 0)
    (hxy_init : x 0 = (y 0))
    (hf_strongly_convex : StrongConvexOn Set.univ α f)
    (hf_differentiable : Differentiable ℝ f)
    (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
    (h_nesterov_seq : IsNesterovSequence f x y α β)
    (hx_star : IsMinOn f Set.univ x_star) :
    let κ := β / α
    f (y t) - f x_star
    ≤ ((α + β) / 2) * ‖x 0 - x_star‖ ^ 2 * Real.exp (-1 * t / (Real.sqrt κ)) := by
  sorry
