import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def proximalMapping {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal)
  (lam : ℝ)
  (x : E) : Set E :=
  {w : E | f w < ⊤ ∧ ∀ z, f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}

noncomputable def finiteSumObjective {m n : ℕ}
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) :
    EuclideanSpace ℝ (Fin n) → ℝ :=
  fun z => (1 / (m : ℝ)) * ∑ i, f i z

def IsSAGAIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ i ω, g 0 i ω = gradient (f i) (x 0 ω)) ∧
  (∀ t ω, g (t + 1) (I t ω) ω = gradient (f (I t ω)) (x t ω)) ∧
  (∀ t i ω, i ≠ I t ω → g (t + 1) i ω = g t i ω) ∧
  (∀ t ω,
    let w := x t ω - η • (g (t + 1) (I t ω) ω - g t (I t ω) ω + ((1 / (m : ℝ)) • ∑ i, g t i ω))
    x (t + 1) ω ∈ proximalMapping (liftRealtoEReal h) η w)

def IsSAGASequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ t, Measurable (x t)) ∧
  (∀ t i, Measurable (g t i)) ∧
  (∀ t, Measurable (I t)) ∧
  IsSAGAIterates f h x g I η ∧
  ProbabilityTheory.iIndepFun I μ ∧
  (∀ t, ProbabilityTheory.IndepFun
    (I t)
    (fun ω => (x t ω, fun i => g t i ω)) μ) ∧
  (∀ t i, μ ((I t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

theorem saga_strongly_convex_distance_bound
  {k m n : ℕ}
  {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω)
  [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
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
  (h_saga_seq :
    IsSAGASequence μ f h x g I (1 / (2 * (α * (m : ℝ) + β))))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_each_strongly_convex :
    ∀ i, StrongConvexOn Set.univ α (f i))
  (hh_convex : ConvexOn ℝ Set.univ h)
  (hx_star : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ x_star)
  (hf_sum_x_int :
    ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ)
  (hx_dist_int :
    ∀ t, Integrable (fun ω => ‖x t ω - x_star‖ ^ 2) μ) :
  let f_sum := finiteSumObjective f
  ∫ ω, ‖x k ω - x_star‖ ^ 2 ∂μ ≤
    (1 - α / (2 * (α * (m : ℝ) + β))) ^ k *
      (‖x0 - x_star‖ ^ 2 +
        ((m : ℝ) / (α * (m : ℝ) + β)) *
          (f_sum x0 -
            inner ℝ (gradient f_sum x_star) (x0 - x_star) -
            f_sum x_star)) := by
  sorry
