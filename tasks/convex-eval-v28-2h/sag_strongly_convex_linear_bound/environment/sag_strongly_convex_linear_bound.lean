import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def finiteSumObjective {m n : ℕ}
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun z => (1 / (m : ℝ)) * ∑ i, f i z

def IsCenteredSAGIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  let f_sum := finiteSumObjective f
  (∀ i ω, g 0 i ω = gradient (f i) (x 0 ω) - gradient f_sum (x 0 ω)) ∧
  (∀ t ω, g (t + 1) (I t ω) ω = gradient (f (I t ω)) (x t ω)) ∧
  (∀ t i ω, i ≠ I t ω → g (t + 1) i ω = g t i ω) ∧
  (∀ t ω, x (t + 1) ω = x t ω - η • ((1 / (m : ℝ)) • ∑ i, g (t + 1) i ω))

def IsSAGSequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ t i, Measurable (g t i)) ∧
  (∀ t, Measurable (I t)) ∧
  IsCenteredSAGIterates f x g I η ∧
  ProbabilityTheory.iIndepFun I μ ∧
  (∀ t, ProbabilityTheory.IndepFun (I t) (fun ω => (x t ω, fun i => g t i ω)) μ) ∧
  (∀ t i, μ ((I t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

theorem sag_strongly_convex_linear_bound {k m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (α β : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hβ_pos : β > 0)
  (hα_pos : α > 0)
  (hα_le_β : α ≤ β)
  (hm_pos : m > 0)
  (h_sag_seq : IsSAGSequence μ f x g I (1 / (16 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_strongly_convex : StrongConvexOn Set.univ α (finiteSumObjective f))
  (hx_star : IsMinOn (finiteSumObjective f) Set.univ x_star)
  (hf_sum_x_int : ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ) :
  let f_sum := finiteSumObjective f
  ∫ ω, f_sum (x k ω) ∂μ - f_sum x_star ≤
    (1 - min (α / (16 * β)) (1 / (8 * (m : ℝ)))) ^ k *
      ((3 / 2) * (f_sum x0 - f_sum x_star) +
        ((4 * β) / (m : ℝ)) * ‖x0 - x_star‖ ^ 2) := by
  sorry
