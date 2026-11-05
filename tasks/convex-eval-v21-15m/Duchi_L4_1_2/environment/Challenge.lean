import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def dualCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {s | ∀ x ∈ K, inner (𝕜 := ℝ) s x ≥ 0}

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

theorem Duchi_L4_1_2 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K)
  (hKint : Set.Nonempty (interior K)) :
  (∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0) ∧
  (dualCone K ∩ (Neg.neg '' dualCone K) = {0}) ∧
  (Convex ℝ (interior K) ∧ IsCone (interior K)) ∧
  (∀ (x₀ x₁ : EuclideanSpace ℝ (Fin n)),
    Set.Nonempty ({z | ∃ k ∈ interior K, z = x₀ + k} ∩
      {z | ∃ k ∈ interior K, z = x₁ + k})) := by
  sorry
