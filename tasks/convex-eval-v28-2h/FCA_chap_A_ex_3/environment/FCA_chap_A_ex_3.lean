import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsConvexCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C,
  ∀ (α : ℝ), α ≥ 0 → ∀ (β : ℝ), β ≥ 0 → α • x + β • y ∈ C

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

theorem FCA_chap_A_ex_3 :
  ∃ (K₁ K₂ : Set (EuclideanSpace ℝ (Fin 3))),
    IsClosed K₁ ∧ IsConvexCone K₁ ∧
    IsClosed K₂ ∧ IsConvexCone K₂ ∧
    ¬ IsClosed (setAdd K₁ K₂) := by
  sorry
