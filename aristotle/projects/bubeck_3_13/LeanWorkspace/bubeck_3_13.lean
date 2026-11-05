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

theorem bubeck_3_13 {n t : ℕ}
  (L R α : ℝ)
  (ht : t ≤ n)
  (ht_pos : 0 < t)
  (hL : L > 0)
  (hR : R > 0)
  (hα : α > 0) :
  (∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
     (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
     x_star ∈ Metric.closedBall 0 R ∧
     ConvexOn ℝ (Metric.closedBall 0 R) f ∧
     LipschitzOnWith (Real.toNNReal L) f (Metric.closedBall 0 R) ∧
     IsMinOn f (Metric.closedBall 0 R) x_star ∧
     IsSubgradientOracle (Metric.closedBall 0 R) f G ∧
     (∀ z ∈ Metric.closedBall 0 R, ‖G z‖ ≤ L) ∧
     ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
       IsBlackBoxSpanProcedure (Metric.closedBall 0 R) G x →
       ∀ s, s < t →
         f (x s) - f x_star ≥ R * L / (2 * (1 + Real.sqrt (t : ℝ)))) ∧
  (∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
     (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
     x_star ∈ Metric.closedBall 0 (L / (2 * α)) ∧
     StrongConvexOn (Metric.closedBall 0 (L / (2 * α))) α f ∧
     LipschitzOnWith (Real.toNNReal L) f (Metric.closedBall 0 (L / (2 * α))) ∧
     IsMinOn f (Metric.closedBall 0 (L / (2 * α))) x_star ∧
     IsSubgradientOracle (Metric.closedBall 0 (L / (2 * α))) f G ∧
     (∀ z ∈ Metric.closedBall 0 (L / (2 * α)), ‖G z‖ ≤ L) ∧
     ∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
       IsBlackBoxSpanProcedure (Metric.closedBall 0 (L / (2 * α))) G x →
       ∀ s, s < t →
         f (x s) - f x_star ≥ L ^ 2 / (8 * α * (t : ℝ))) := by
  sorry
