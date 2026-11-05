import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


def IsJointlyLogConcave {n m : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ) : Prop :=
  (∀ x y, 0 ≤ f x y) ∧
  ∀ x₁ x₂ y₁ y₂ t, t ∈ Set.Icc 0 1 →
    f (t • x₁ + (1 - t) • x₂) (t • y₁ + (1 - t) • y₂) ≥
      Real.rpow (f x₁ y₁) t * Real.rpow (f x₂ y₂) (1 - t)

def IsLogConcave {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  (∀ x, 0 ≤ f x) ∧
  ∀ (x y : EuclideanSpace ℝ (Fin n)), ∀ (t : ℝ), t ∈ Set.Icc 0 1 →
    f (t • x + (1 - t) • y) ≥ (Real.rpow (f x)  t) * (Real.rpow (f y) (1 - t))

theorem Duchi_Q5_2a {n m : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
  (hf_lc : IsJointlyLogConcave f)
  (hf_int : ∀ x, Integrable (f x)) :
  IsLogConcave (fun x => ∫ y, f x y) := by
  sorry
