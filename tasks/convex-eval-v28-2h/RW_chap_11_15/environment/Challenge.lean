import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem RW_chap_11_15
  (f : E → EReal)
  (C : Set E)
  (hC_convex : Convex ℝ C) :
  ((∃ (A : E →L[ℝ] E) (a : E) (α : ℝ),
      ∀ x ∈ C,
        f x =
          (((1 / 2 : ℝ) * inner ℝ x (A x) +
              inner ℝ a x + α) : EReal)) ↔
    ∀ x₀ ∈ C, ∀ x₁ ∈ C,
      ∃ (A : E →L[ℝ] E) (a : E) (α : ℝ),
        ∀ x ∈ {x : E | ∃ t ∈ Set.Icc (0 : ℝ) 1,
            x = (1 - t) • x₀ + t • x₁},
          f x =
            (((1 / 2 : ℝ) * inner ℝ x (A x) +
                inner ℝ a x + α) : EReal)) := by
  sorry
