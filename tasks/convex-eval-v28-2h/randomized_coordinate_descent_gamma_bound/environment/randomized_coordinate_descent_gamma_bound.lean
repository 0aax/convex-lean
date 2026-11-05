import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

noncomputable def randomizedCoordDescentStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (I : Fin n)
  (η : ℝ) : EuclideanSpace ℝ (Fin n) :=
  let e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (1 : ℝ)
  let g : ℝ := (fderiv ℝ f x) e
  let upd : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single I (η * g)
  x - upd

def IsRandomizedCoordDescentGammaSequence {n : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ : ℝ) : Prop :=
  (∀ s, Measurable (x s)) ∧
  (∀ s, Measurable (I s)) ∧
  (∀ s ω, x (s + 1) ω = randomizedCoordDescentStep f (x s ω) (I s ω) ((β (I s ω))⁻¹)) ∧
  (ProbabilityTheory.iIndepFun (fun (p : ℕ) => I p) μ) ∧
  (∀ s (i : Fin n), μ ((I s) ⁻¹' {i}) =
    ENNReal.ofReal ((Real.rpow (β i) γ) / ∑ j, (Real.rpow (β j) γ)))

theorem randomized_coordinate_descent_gamma_bound {n t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ R : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hβ_pos : ∀ i, β i > 0)
  (hγ_pos : γ ≥ 0)
  (hR_pos : R > 0)
  (ht_pos : t > 0)
  (hR_sq : R ^ 2 = sSup {v | ∃ x', (f x' ≤ f x0) ∧
                                   (v = ∑ i, (Real.rpow (β i) (1 - γ)) * (x' i - x_star i) ^ 2)})
  (h_rcd_gamma_seq : IsRandomizedCoordDescentGammaSequence μ f x I β γ)
  (hf_diff : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_smooth : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
    let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)
    ‖(fderiv ℝ f (x + u • ei)) (EuclideanSpace.single i (1:ℝ)) -
    (fderiv ℝ f x) (EuclideanSpace.single i (1:ℝ))‖ ≤ β i * |u|)
  (hx_star : IsMinOn f Set.univ x_star) :
  ∫ ω, f (x t ω) ∂μ - f x_star ≤
  (2 * (R ^ 2) * (∑ i, Real.rpow (β i) γ)) / (t : ℝ) := by
  sorry
