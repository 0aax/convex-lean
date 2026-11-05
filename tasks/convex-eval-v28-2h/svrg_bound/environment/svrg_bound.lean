import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def IsSVRGIterates {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (k : ℕ)
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  let f_sum := fun z => (1 / (m : ℝ)) • ∑ i, f i z
  (∀ s ω, x s 0 ω = y s ω) ∧
  (∀ s t ω, t < k →
    x s (t + 1) ω =
      (x s t ω) - η • (gradient (f (I s t ω)) (x s t ω) -
                       gradient (f (I s t ω)) (y s ω) +
                       gradient f_sum (y s ω))) ∧
  (∀ s ω, y (s + 1) ω = (1 / (k : ℝ)) • ∑ i ∈ Finset.range k, x s i ω)

def IsSVRGSequence {m n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (k : ℕ)
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (η : ℝ) : Prop :=
  (∀ s t, Measurable (x s t)) ∧
  (∀ s, Measurable (y s)) ∧
  (∀ s t, Measurable (I s t)) ∧
  (IsSVRGIterates k f x y I η) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ × ℕ) => I p.1 p.2) μ) ∧
  (∀ s t,
    ProbabilityTheory.IndepFun
      (I s t)
      (fun ω => (x s t ω, y s ω))
      μ) ∧
  (∀ s t i, μ ((I s t) ⁻¹' {i}) = (m : ENNReal)⁻¹)

theorem svrg_bound {k m n s : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (α β : ℝ)
  (y0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hy0 : ∀ ω, y 0 ω = y0)
  (hβ_pos : β > 0) (hα_pos : α > 0) (hm_pos : m > 0)
  (hk : k > 0 ∧ k = Nat.ceil (20 * (β / α)))
  (h_mirror_seq : IsSVRGSequence μ k f x y I (1 / (10 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_strongly_convex :
    StrongConvexOn Set.univ α (fun z => (1 / (m : ℝ)) * ∑ i, f i z))
  (hx_star : IsMinOn (fun z => (1 / (m : ℝ)) • ∑ i, f i z) Set.univ x_star)
  (hf_sum_y_int : ∀ s, Integrable (fun ω => (1 / (m : ℝ)) • ∑ i, f i (y s ω)) μ)
  (hf_sum_x_int : ∀ s t, Integrable (fun ω => (1 / (m : ℝ)) • ∑ i, f i (x s t ω)) μ) :
  let f_sum := fun z => (1 / (m : ℝ)) • ∑ i, f i z
  ∫ ω, f_sum (y s ω) ∂μ - f_sum x_star ≤
    ((9 / 10) ^ s) * (f_sum y0 - f_sum x_star) := by
  sorry
