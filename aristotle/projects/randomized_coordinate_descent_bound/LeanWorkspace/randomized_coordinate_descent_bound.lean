import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def randomizedCoordDescentStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (I : Fin n)
  (η : ℝ) : EuclideanSpace ℝ (Fin n) :=
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (1 : ℝ)
  let g : ℝ := (fderiv ℝ f x) e
  let upd : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (η * g)
  x - upd

def IsRandomizedCoordDescentSequence {n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (η : ℝ) : Prop :=
  (∀ s, Measurable (x s)) ∧
  (∀ s, Measurable (I s)) ∧
  (∀ s ω, x (s + 1) ω = randomizedCoordDescentStep f (x s ω) (I s ω) η) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ) => I p) μ) ∧
  (∀ s i, μ ((I s) ⁻¹' {i}) = (n : ENNReal)⁻¹)

theorem randomized_coordinate_descent_bound {n t : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (R L : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hR_pos : R > 0)
  (hL_pos : L > 0)
  (ht_pos : t > 0)
  (hR_sq : (1 / 2) * ‖x_star - x0‖ ^ 2 ≤ R ^ 2)
  (h_rcd_seq :
    IsRandomizedCoordDescentSequence μ f x I
      ((R / L) * (Real.sqrt (2 * n / t))))
  (hf_diff : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lipschitz : LipschitzWith (Real.toNNReal L) f)
  (hx_star : IsMinOn f Set.univ x_star) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f x_star ≤
    R * L * Real.sqrt (2 * n / t) := by
  sorry
