import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def condExpGivenIterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω)
  (x : Ω → E)
  (g : Ω → E →L[ℝ] ℝ) : Ω → E →L[ℝ] ℝ :=
  MeasureTheory.condExp (MeasurableSpace.comap x inferInstance) μ g

noncomputable def bregmanDivergence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (y : E) : ℝ :=
  (f x) - (f y) - (fderiv ℝ f y (x - y))

def IsSubgradientOn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : E)
  (w : E →L[ℝ] ℝ) : Prop :=
  ∀ y ∈ 𝓧, f x + w (y - x) ≤ f y

def IsMirrorMap {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (𝓓 : Set E)
  (phi : E → ℝ) : Prop :=
  (StrictConvexOn ℝ 𝓓 phi) ∧
  (DifferentiableOn ℝ phi 𝓓) ∧
  (∀ (ℓ : E →L[ℝ] ℝ), ∃ y ∈ 𝓓, fderiv ℝ phi y = ℓ) ∧
  (∀ b ∈ frontier 𝓓, Filter.Tendsto (fun x => ‖fderiv ℝ phi x‖) (𝓝[𝓓] b) Filter.atTop)

def IsStochasticSubgradientOracle {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω)
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : Ω → E)
  (g : Ω → E →L[ℝ] ℝ) : Prop :=
  (Integrable g μ) ∧
  (∀ᵐ ω ∂μ, IsSubgradientOn 𝓧 f (x ω) (condExpGivenIterate μ x g ω))

def IsStochasticMirrorDescentSequence {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {Ω : Type*} [MeasurableSpace Ω]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (phi : E → ℝ)
  (x : ℕ → (Ω → E))
  (g : ℕ → (Ω → E →L[ℝ] ℝ))
  (η : ℕ → ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ ω, x 0 ω ∈ 𝓧 ∩ 𝓓) ∧
  (∀ ω, IsMinOn phi (𝓧 ∩ 𝓓) (x 0 ω)) ∧
  (∀ t ω, x t ω ∈ 𝓧 ∩ 𝓓) ∧
  (∀ t ω,
    IsMinOn
      (fun z =>
        (η t) * g t ω z +
        bregmanDivergence phi z (x t ω))
      (𝓧 ∩ 𝓓)
      (x (t + 1) ω))

theorem stochastic_mirror_descent_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → Ω → E)
  (g : ℕ → Ω → E →L[ℝ] ℝ)
  (B R : ℝ)
  (x0 : E)
  (hx0 : ∀ ω, x 0 ω = x0)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi x0 = v})
  (hR_pos : 0 < R)
  (hB_pos : 0 < B)
  (ht : 0 < t)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (havg_ae :
      AEMeasurable
        (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω)) μ)
  (h_mirror_seq :
    IsStochasticMirrorDescentSequence 𝓧 𝓓 phi x g
      (fun _ => (R / B) * Real.sqrt (2 / (t : ℝ))))
  (h_stoch_oracle : ∀ s, IsStochasticSubgradientOracle μ 𝓧 f (x s) (g s))
  (hB_int : ∀ s, Integrable (fun ω => ‖g s ω‖ ^ (2 : ℕ)) μ)
  (hB_sq : ∀ s, ∫ ω, ‖g s ω‖ ^ (2 : ℕ) ∂μ ≤ B ^ 2)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓_convex : Convex ℝ 𝓓)
  (h𝓓_open : IsOpen 𝓓)
  (h𝓓_contains : 𝓧 ⊆ closure 𝓓)
  (h_inter_nonempty : Set.Nonempty (𝓧 ∩ 𝓓))
  (hphi_differentiable : DifferentiableOn ℝ phi 𝓓)
  (hphi_mirror_map : IsMirrorMap 𝓓 phi)
  (hphi_strong_convex : StrongConvexOn (𝓧 ∩ 𝓓) 1 phi)
  (hf_convex : ConvexOn ℝ 𝓧 f) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ
    - sInf (f '' 𝓧)
    ≤ R * B * Real.sqrt (2 / (t : ℝ)) := by
  sorry
