import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open MeasureTheory ProbabilityTheory


def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

def IsAlphaStronglyConvex {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (α : ℝ) : Prop :=
  (∀ x ∈ 𝓧, ∃ g, InDomIsSubgradientAt 𝓧 f x g) ∧
  (∀ x ∈ 𝓧, ∀ y ∈ 𝓧, ∀ g, (InDomIsSubgradientAt 𝓧 f x g) →
    f x - f y ≤ inner ℝ g (x - y) - (α / 2) * (N (x - y))^2)

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

theorem randomized_coordinate_descent_gamma_stronglyconvex_bound {n t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ α : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hβ_pos : ∀ i, β i > 0)
  (hα_pos : α > 0)
  (hγ_pos : γ ≥ 0)
  (ht_pos : t > 0)
  (h_rcd_gamma_seq : IsRandomizedCoordDescentGammaSequence μ f x I β γ)
  (hf_diff : Differentiable ℝ f)
  (hf_convex : IsAlphaStronglyConvex Set.univ f
    (fun v => Real.sqrt (∑ i, (Real.rpow (β i) (1 - γ)) * (v i) ^ 2)) α)
  (hf_smooth : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
    let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)
    ‖(fderiv ℝ f (x + u • ei)) (EuclideanSpace.single i (1:ℝ)) -
    (fderiv ℝ f x) (EuclideanSpace.single i (1:ℝ))‖ ≤ β i * |u|)
  (hx_star : IsMinOn f Set.univ x_star) :
  let k := (α)⁻¹ * (∑ i, Real.rpow (β i) γ)
  ∫ ω, f (x t ω) ∂μ - f x_star ≤
  (1 - ((n : ℝ) * k)⁻¹) ^ t * (f x0 - f x_star) := by
  sorry
