import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def proximalMapping {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : Set E :=
  {w : E | f w < ⊤ ∧ ∀ z, f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}

noncomputable def istaSet {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (xt : EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Set (EuclideanSpace ℝ (Fin n)) :=
  proximalMapping (fun x => ((g x : ℝ) : EReal)) η (xt - η • (gradient f xt))

noncomputable def fistaSet {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (β : ℝ)
  (xt : EuclideanSpace ℝ (Fin n)) : Set (EuclideanSpace ℝ (Fin n)) :=
  istaSet f g xt (1 / β)

def IsFISTASequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (lambda : ℕ → ℝ)
  (β : ℝ) : Prop :=
  let γ := fun t => (1 - lambda t) / (lambda (t + 1))
  (lambda 0 = 0) ∧
  (x 0 = y 0) ∧
  (∀ t, lambda (t + 1) = (1 + Real.sqrt (1 + 4 * (lambda t)^2)) / 2) ∧
  (∀ t, y (t + 1) ∈ fistaSet f g β (x t)) ∧
  (∀ t, x (t + 1) = (1 - γ t) • y (t + 1) + (γ t) • y t)

theorem FISTA_bound
  {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (lambda : ℕ → ℝ)
  (β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (ht_one : t ≥ 1)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_ista_seq : IsFISTASequence f g x y lambda β)
  (hx_star : IsMinOn (f + g) Set.univ x_star) :
  f (y (t + 1)) + g (y (t + 1)) - (f x_star + g x_star)
  ≤ (2 * β) * ‖x 0 - x_star‖ ^ 2 / (t + 1 : ℝ) ^ 2 := by
  sorry
