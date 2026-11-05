import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def dualCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (K : Set E) : Set E :=
  {s | ∀ x ∈ K, inner (𝕜 := ℝ) s x ≥ 0}

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

noncomputable def gammaMin {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (u : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sInf {v | ∃ l ∈ dualCone K, ‖l‖ = 1 ∧ v = inner (𝕜 := ℝ) l u}

theorem Duchi_L4_1_3 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K)
  (hK_nonempty : K.Nonempty) :
  (∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0) ∧
  (closure K = dualCone (dualCone K)) ∧
  (IsClosed K → K = dualCone (dualCone K)) ∧
  ((∃ l ∈ dualCone K, ‖l‖ = 1) →
    (∀ u, gammaMin K u ≥ 0 ↔ u ∈ closure K)) ∧
  ((Set.Nonempty (interior K) ∧ ∃ l ∈ dualCone K, ‖l‖ = 1) →
    ∀ u, gammaMin K u > 0 ↔ u ∈ interior K) := by
  sorry
