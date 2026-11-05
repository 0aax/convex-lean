import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsConvexCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
  ∀ (α : ℝ), α ≥ 0 → ∀ (β : ℝ), β ≥ 0 → α • x + β • y ∈ C

noncomputable def pC {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) (C : Set E)
    (hC₁ : IsClosed C) (hC₂ : Convex ℝ C) (hC₃ : Set.Nonempty C) : E
    := Classical.choose (exists_norm_eq_iInf_of_complete_convex hC₃ hC₁.isComplete hC₂ x)

lemma convexCone_isConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] {C : Set E} (hC : IsConvexCone C) : Convex ℝ C := by
  intro x hx y hy a b ha hb hab
  exact hC x hx y hy a ha b hb

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem CAMA_chap_3_3_2_3
  (K : Set E)
  (x y : E)
  (hK₀ : IsConvexCone K)
  (hK₁ : IsClosed K)
  (hK₂ : Set.Nonempty K) :
  y = pC x K hK₁ (convexCone_isConvex hK₀) hK₂ ↔
  (y ∈ K) ∧ (x - y ∈ polarCone K) ∧ (inner ℝ (x - y) y = 0) := by
  sorry
