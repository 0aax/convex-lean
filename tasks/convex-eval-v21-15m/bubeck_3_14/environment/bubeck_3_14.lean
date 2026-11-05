import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def InDomIsSubgradientAt {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (w : EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ y ∈ 𝓧, f y ≥ f x + inner ℝ (y - x) w

def IsSubgradientOracle {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ z ∈ 𝓧, InDomIsSubgradientAt 𝓧 f z (G z)

def IsBlackBoxSpanProcedure {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
  (x : ℕ → EuclideanSpace ℝ (Fin n)) : Prop :=
  (x 0 = 0) ∧
  (∀ s, x s ∈ 𝓧) ∧
  (∀ s, x (s + 1) ∈ Submodule.span ℝ ((fun j => G (x j)) '' Set.Iic s))

theorem bubeck_3_14 {n t : ℕ}
  (β : ℝ)
  (ht : 2 * t + 1 ≤ n)
  (ht_pos : 0 < t)
  (hβ : β > 0) :
  ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    (ConvexOn ℝ Set.univ f) ∧
    (Differentiable ℝ f) ∧
    (LipschitzWith (Real.toNNReal β) (gradient f)) ∧
    (IsMinOn f Set.univ x_star) ∧
    (‖x_star‖ > 0) ∧
    (IsSubgradientOracle Set.univ f G) ∧
    (∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
      (IsBlackBoxSpanProcedure Set.univ G x) →
        ∀ s, s < t →
          f (x s) - f x_star ≥ ((3 * β) / 32) * (‖x 0 - x_star‖ ^ 2 / (((t : ℝ) + 1) ^ 2))) := by
  sorry
