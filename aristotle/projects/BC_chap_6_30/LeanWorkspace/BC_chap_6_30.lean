import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem BC_chap_6_30
  (K : Set E) (x : E)
  (hK_nonempty : Set.Nonempty K)
  (hK_closed : IsClosed K)
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K) :
  ∃ (a b : E),
    ((a ∈ K) ∧ (b ∈ polarCone K) ∧ (x = a + b)) ∧
    (inner ℝ a b = 0) ∧
    (‖x‖ ^ 2 = (Metric.infDist x K) ^ 2 + (Metric.infDist x (polarCone K)) ^ 2) := by
  sorry
