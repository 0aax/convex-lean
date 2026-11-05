import Mathlib

open Pointwise

def hadwiger_covering_conjecture : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (K : Set (EuclideanSpace ℝ (Fin n))),
      ((interior K).Nonempty) →
      (Convex ℝ K) →
      (IsCompact K) →
      ∃ (Xi : Fin (2 ^ n) → EuclideanSpace ℝ (Fin n))
        (ci : Fin (2 ^ n) → ℝ),
        (∀ i, ci i ∈ Set.Ioo (0 : ℝ) 1) ∧
        K ⊆ ⋃ i, (Xi i +ᵥ (ci i) • K)
