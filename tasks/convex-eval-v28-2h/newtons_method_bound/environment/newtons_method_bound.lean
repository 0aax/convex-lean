import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def hessianOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : E)
  : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

def IsLipschitzHess {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (L : ℝ) : Prop :=
  ∀ x y, (hessianOperator f x - hessianOperator f y).opNorm ≤ L * ‖x - y‖

noncomputable def newtonStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (hessianOperator f x).inverse (gradient f x)

def IsNewtonsMethodSequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (∀ t, x (t + 1) = newtonStep f (x t))

theorem newtons_method_bound {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (M μ : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hM : M > 0) (hμ : μ > 0)
  (hx_init : ‖x 0 - x_star‖ ≤ μ / (2 * M))
  (hf_in_c2 : ContDiff ℝ 2 f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lipschitz_hessian : IsLipschitzHess f M)
  (hf_pos_hessian : ∀ v, inner ℝ v (hessianOperator f x_star v) ≥ μ * ‖v‖^2)
  (h_ps_seq : IsNewtonsMethodSequence f x)
  (hx_star : IsMinOn f Set.univ x_star) :
  (∀ k, ∀ v, v ≠ 0 → 0 < inner ℝ v (hessianOperator f (x k) v)) ∧
  (∀ k, ‖x (k + 1) - x_star‖ ≤ (M / μ) * ‖x k - x_star‖ ^ 2) ∧
  Filter.Tendsto x Filter.atTop (𝓝 x_star) := by
  sorry
