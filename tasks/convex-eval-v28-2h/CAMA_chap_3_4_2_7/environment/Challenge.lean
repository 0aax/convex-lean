import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsConvexCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
  ∀ (α : ℝ), α ≥ 0 → ∀ (β : ℝ), β ≥ 0 → α • x + β • y ∈ C

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem CAMA_chap_3_4_2_7
  (K : Set E)
  (hK_convex_cone : IsConvexCone K)
  (hK_nonempty : Set.Nonempty K) :
  polarCone (polarCone K) = closure K := by
  sorry
