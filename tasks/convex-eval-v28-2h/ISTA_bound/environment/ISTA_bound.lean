import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

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

def IsISTASequence {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℝ) : Prop :=
  (∀ t, x (t + 1) ∈ istaSet f g (x t) η)

theorem ISTA_bound
  {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (ht_one : t ≥ 1)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hf_differentiable : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_ista_seq : IsISTASequence f g x (1 / β))
  (hx_star : IsMinOn (f + g) Set.univ x_star) :
  f (x t) + g (x t) - (f x_star + g x_star) ≤ β * ‖x 0 - x_star‖ ^ 2 / (2 * (t + 1)) := by
  sorry
