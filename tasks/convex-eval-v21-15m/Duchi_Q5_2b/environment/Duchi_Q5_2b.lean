import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def IsLogConcave {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  ∀ (x y : EuclideanSpace ℝ (Fin n)), ∀ (t : ℝ), t ∈ Set.Icc 0 1 →
    f (t • x + (1 - t) • y) ≥ (Real.rpow (f x)  t) * (Real.rpow (f y) (1 - t))

theorem Duchi_Q5_2b {n : ℕ}
  (p q : EuclideanSpace ℝ (Fin n) → ℝ)
  (hp_lc : IsLogConcave p)
  (hq_lc : IsLogConcave q)
  (hp_int : Integrable p)
  (hq_int : Integrable q) :
  IsLogConcave (fun z => ∫ x, p x * q (z - x)) := by
  sorry
