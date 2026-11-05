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

theorem stochastic_gradient_descent_bound
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → Ω → E)
  (g : ℕ → Ω → E →L[ℝ] ℝ)
  (α B : ℝ)
  (x_star : E)
  (x0 : E)
  (hx0 : ∀ ω, x 0 ω = x0)
  (hB_sq : ∀ t, ∫ ω, ‖g t ω‖ ^ (2 : ℕ) ∂μ ≤ B ^ 2)
  (hB_pos : B > 0) (hα_pos : α > 0)
  (hB_int : ∀ s, Integrable (fun ω => ‖g s ω‖ ^ (2 : ℕ)) μ)
  (ht : t > 0)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (hweighted_ae :
      AEMeasurable
        (fun ω => f (∑ s ∈ Finset.range t,
           ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • x s ω)) μ)
  (h_sgd_seq :
    IsStochasticMirrorDescentSequence 𝓧 Set.univ
      (fun v => (1 / 2 : ℝ) * ‖v‖ ^ (2 : ℕ))
      x g
      (fun s => 2 / (α * ((s : ℝ) + 2))))
  (h_stoch_oracle : ∀ s, IsStochasticSubgradientOracle μ 𝓧 f (x s) (g s))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_strongly_convex : StrongConvexOn 𝓧 α f)
  (hf_subgradients : ∀ x ∈ 𝓧, ∃ w : E →L[ℝ] ℝ, IsSubgradientOn 𝓧 f x w)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  ∫ ω,
    f (∑ s ∈ Finset.range t,
         ((2 * ((s : ℝ) + 1)) / ((t : ℝ) * ((t : ℝ) + 1))) • (x s ω))
      ∂μ
    - f x_star
    ≤ (2 * B ^ 2) / (α * ((t : ℝ) + 1)) := by
  sorry
