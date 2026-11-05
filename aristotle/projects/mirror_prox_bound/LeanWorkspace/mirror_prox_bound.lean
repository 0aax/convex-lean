import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def bregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (y : E) : ℝ :=
  (f x) - (f y) - (fderiv ℝ f y (x - y))

def bregmanDivergenceProjSet {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (phi : E → ℝ)
  (y : E) : Set E :=
  {x : E |
  (x ∈ 𝓧 ∩ 𝓓) ∧
  (∀ z ∈ 𝓧 ∩ 𝓓, bregmanDivergence phi x y ≤ bregmanDivergence phi z y)}

def IsSmoothOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (β : ℝ) : Prop :=
  ∀ x ∈ 𝓧, ∀ y ∈ 𝓧, ‖fderiv ℝ f x - fderiv ℝ f y‖ ≤ β * ‖x - y‖

def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓓 : Set E)
  (phi : E → ℝ) : Prop :=
  (StrictConvexOn ℝ 𝓓 phi) ∧
  (DifferentiableOn ℝ phi 𝓓) ∧
  (∀ (ℓ : E →L[ℝ] ℝ), ∃ y ∈ 𝓓, fderiv ℝ phi y = ℓ) ∧
  (∀ b ∈ frontier 𝓓, Filter.Tendsto (fun x => ‖fderiv ℝ phi x‖) (𝓝[𝓓] b) Filter.atTop)

def IsMirrorProxSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (x_prime : ℕ → E)
  (y_prime : ℕ → E)
  (η : ℝ) : Prop :=
  (IsMinOn phi (𝓧 ∩ 𝓓) (x 0)) ∧
  (∀ t, x (t + 1) ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi (x_prime (t + 1))) ∧
  (∀ t, y (t + 1) ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi (y_prime (t + 1))) ∧
  (∀ t, (y_prime t) ∈ 𝓓) ∧ (∀ t, (x_prime t) ∈ 𝓓) ∧
  (∀ t, fderiv ℝ phi (y_prime (t + 1)) = fderiv ℝ phi (x t) - η • (fderiv ℝ f (x t))) ∧
  (∀ t, fderiv ℝ phi (x_prime (t + 1)) = fderiv ℝ phi (x t) - η • (fderiv ℝ f (y (t + 1))))

theorem mirror_prox_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (x_prime : ℕ → E)
  (y_prime : ℕ → E)
  (ρ β R : ℝ)
  (x_star : E)
  (hR : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v})
  (hR_pos : R > 0)
  (ht : t ≥ 1) (hρ : ρ > 0)
  (hβ : β > 0)
  (hx_0 : x 0 ∈ 𝓧 ∩ 𝓓)
  (h_mirror_seq : IsMirrorProxSequence 𝓧 𝓓 f phi x y x_prime y_prime (ρ / β))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓_convex : Convex ℝ 𝓓)
  (h𝓓_open : IsOpen 𝓓)
  (h𝓓_contains : 𝓧 ⊆ closure 𝓓)
  (h_inter_nonempty : Set.Nonempty (𝓧 ∩ 𝓓))
  (hphi_differentiable : DifferentiableOn ℝ phi 𝓓)
  (hphi_mirror_map : IsMirrorMap 𝓓 phi)
  (hphi_strong_convex : StrongConvexOn (𝓧 ∩ 𝓓) ρ phi)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_smooth : IsSmoothOn 𝓧 f β)
  (hf_grad : ∀ z ∈ 𝓧, DifferentiableAt ℝ f z)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, (y (s + 1))) - f x_star ≤
  β * (R ^ 2) / (ρ * t) := by
  sorry
