import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_A_ex_12
  (hE : 2 ≤ Module.finrank ℝ E)
  (hF : 1 ≤ Module.finrank ℝ F) :
  (∀  (A : AffineMap ℝ E F)
    (C : Set E) (x : E),
    Convex ℝ C → Function.Injective A →
    x ∈ Set.extremePoints ℝ C →
    A x ∈ Set.extremePoints ℝ (A '' C)) ∧
  (∃  (A : AffineMap ℝ E F)
    (C : Set E) (x : E),
    Convex ℝ C ∧ ¬ Function.Injective A ∧
    x ∈ Set.extremePoints ℝ C ∧
    A x ∉ Set.extremePoints ℝ (A '' C)) := by
  sorry
