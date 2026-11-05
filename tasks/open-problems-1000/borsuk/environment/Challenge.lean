import Mathlib

def borsuk_partition : Prop :=
  ∀ (n : ℕ), n ≤ 62 →
    ∀ (A : Set (EuclideanSpace ℝ (Fin n))),
      (0 < Metric.diam A) →
        ∃ (A_i : Fin (n + 1) → Set (EuclideanSpace ℝ (Fin n))),
          (⋃ i, A_i i) = A ∧
          ∀ i, Metric.diam (A_i i) < Metric.diam A

theorem borsuk_partition_POS : borsuk_partition := by
  sorry

theorem borsuk_partition_NEG : ¬ borsuk_partition := by
  sorry
