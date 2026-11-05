import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

theorem Duchi_Q1_1 :
  (∀ (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
      [UniformConvexSpace E] (C : Set E) (x : E),
      IsClosed C → Convex ℝ C → C.Nonempty →
      ∃! y, y ∈ projectionMapping C x) ∧
  (∀ (n : ℕ), 2 ≤ n →
    ∃ (C : Set (PiLp 1 (fun (_ : Fin n) => ℝ)))
      (x y₁ y₂ : PiLp 1 (fun (_ : Fin n) => ℝ)),
      IsClosed C ∧ Convex ℝ C ∧
      y₁ ≠ y₂ ∧ y₁ ∈ projectionMapping C x ∧ y₂ ∈ projectionMapping C x) ∧
  (∀ (n : ℕ), 2 ≤ n →
    ∃ (C : Set (PiLp ⊤ (fun (_ : Fin n) => ℝ)))
      (x y₁ y₂ : PiLp ⊤ (fun (_ : Fin n) => ℝ)),
      IsClosed C ∧ Convex ℝ C ∧
      y₁ ≠ y₂ ∧ y₁ ∈ projectionMapping C x ∧ y₂ ∈ projectionMapping C x) := by
  sorry
