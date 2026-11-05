import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

noncomputable def projSubgradientStep {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (x : EuclideanSpace ℝ (Fin n))
  (g : EuclideanSpace ℝ (Fin n))
  (η : ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : EuclideanSpace ℝ (Fin n) :=
  let y_next := x - η • g
  pC y_next 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty

noncomputable def projGradientDescentStep {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : EuclideanSpace ℝ (Fin n))
  (η : ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : EuclideanSpace ℝ (Fin n) :=
  projSubgradientStep 𝓧 x (g x) η h𝓧_nonempty h𝓧_compact h𝓧_convex

def IsProjectedGradientDescentSequence {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (η : ℕ → ℝ)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧) : Prop :=
  (∀ x' ∈ 𝓧, HasGradientAt f (g x') x') ∧
  (∀ t, x (t + 1) = projGradientDescentStep 𝓧 g (x t) (η t) h𝓧_nonempty h𝓧_compact h𝓧_convex)

theorem projected_gradient_descent_smooth_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (β : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (hx_init : x 0 ∈ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_beta_smooth : LipschitzOnWith (Real.toNNReal β) (gradient f) 𝓧)
  (h_gd_seq : IsProjectedGradientDescentSequence 𝓧 f g x (fun s => 1 / β)
              h𝓧_nonempty h𝓧_compact h𝓧_convex)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f (x t) - f x_star ≤ ((3 * β) * ‖x 0 - x_star‖^2 + f (x 0) - f x_star) / (t + 1) := by
  sorry
