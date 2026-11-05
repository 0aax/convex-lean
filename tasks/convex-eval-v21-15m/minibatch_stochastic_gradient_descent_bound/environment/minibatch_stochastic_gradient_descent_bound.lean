import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal RealInnerProductSpace

variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

def IsMinibatchStochasticGradientDescentSequence {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (m : ℕ)
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (x : ℕ → (Ω → EuclideanSpace ℝ (Fin n)))
  (g : ℕ → Fin m → (Ω → EuclideanSpace ℝ (Fin n)))
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ ω, x 0 ω ∈ 𝓧) ∧
  (∀ ω, IsMinOn (fun v => 1/2 * ‖v‖ ^ 2) 𝓧 (x 0 ω)) ∧
  (∀ t ω, x (t + 1) ω ∈ projectionMapping 𝓧
                    ((x t ω) - (η / (m : ℝ)) • ∑ i, (g t i ω)))

theorem minibatch_stochastic_gradient_descent_bound
  {m n t : ℕ}
  {Ω : Type*}
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  (μ : Measure Ω)
  [IsProbabilityMeasure μ]
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (β B R : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (x0 : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧, 1 / 2 * (‖a‖ ^ 2 - ‖x0‖ ^ 2) = v})
  (hR_pos : R > 0)
  (hB_pos : B > 0)
  (hβ_pos : β > 0)
  (ht_pos : t > 0)
  (hm_pos : m > 0)
  (h_minibatch_sgd_seq :
    let σ := Real.sqrt ((2 * B ^ 2) / (m : ℝ))
    let η := (R / σ) * Real.sqrt (2 / (t : ℝ))
    IsMinibatchStochasticGradientDescentSequence m 𝓧 x g (1 / (β + (1 / η))))
  (hx_meas : ∀ s, Measurable (x s))
  (hg_meas : ∀ s i, Measurable (g s i))
  (hg_bound : ∀ s i ω, ‖g s i ω‖ ≤ B)
  (hg_unbiased : ∀ s i,
    μ[g s i | MeasurableSpace.comap (x s) inferInstance] =ᵐ[μ] fun ω => gradient f (x s ω))
  (hg_indep : ∀ s,
    ProbabilityTheory.iCondIndepFun (MeasurableSpace.comap (x s) inferInstance)
      (hx_meas s).comap_le (fun (i : Fin m) => g s i) μ)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_smooth : LipschitzOnWith (Real.toNNReal β) (gradient f) 𝓧)
  (hf_differentiable : ∀ z ∈ 𝓧, DifferentiableAt ℝ f z)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (havg_succ_ae :
    AEMeasurable
      (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)) μ) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f x_star ≤
  (2 * R * B) / (Real.sqrt (m * t : ℝ)) + (β * R ^ 2) / (t : ℝ) := by
  sorry
