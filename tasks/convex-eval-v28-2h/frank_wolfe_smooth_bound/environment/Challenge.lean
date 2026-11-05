import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def frankWolfeStep {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (x : E)
  (y : E)
  (γ : ℝ) : E :=
  (1 - γ) • x + γ • y

def IsFrankWolfeSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (γ : ℕ → ℝ) : Prop :=
  (∀ t, x t ∈ 𝓧) ∧
  (∀ t, y t ∈ 𝓧) ∧
  (∀ t, 0 ≤ γ t ∧ γ t ≤ 1) ∧
  (∀ t, x (t + 1) = frankWolfeStep (x t) (y t) (γ t)) ∧
  (∀ x' ∈ 𝓧, DifferentiableAt ℝ f x') ∧
  (∀ t, IsMinOn (fun z => fderiv ℝ f (x t) z) 𝓧 (y t))

def IsSmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (β : ℝ) : Prop :=
  ∀ x ∈ 𝓧, ∀ y ∈ 𝓧, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ β * ‖x - y‖

theorem frank_wolfe_smooth_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (β : ℝ) (x_star : E)
  (hβ_pos : β > 0) (ht_pos : t ≥ 1)
  (hx_init : x 0 ∈ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_beta_smooth : IsSmoothOn 𝓧 f β)
  (h_fw_seq : IsFrankWolfeSequence 𝓧 f x y (fun s => 2 / (s + 2)))
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  let R := sSup {v | ∃ a ∈ 𝓧, ∃ b ∈ 𝓧, v = ‖a - b‖}
  f (x t) - f x_star ≤ (2 * β * R^2) / (t + 2) := by
  sorry
