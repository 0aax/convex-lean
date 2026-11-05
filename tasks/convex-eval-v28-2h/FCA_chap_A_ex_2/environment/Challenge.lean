import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def argmax {E : Type*}  (f : E → ℝ) (C : Set E)
  : Set E
  := {x : E | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

def exposedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) (s : E) : Set E :=
  argmax (fun y => inner ℝ s y) C

theorem FCA_chap_A_ex_2 :
  let C : Set (EuclideanSpace ℝ (Fin 2)) :=
    {p | p 0 > 0 ∧ p 1 > 0 ∧ p 0 * p 1 ≥ 1}
  (C = ⋂ (t : ℝ) (_ : t > 0), {p : EuclideanSpace ℝ (Fin 2) | p 0 + t ^ 2 * p 1 ≥ 2 * t}) ∧
  ({s : EuclideanSpace ℝ (Fin 2) |
      Set.Nonempty (exposedFace C s) ∧ exposedFace C s ≠ C}
    = {s : EuclideanSpace ℝ (Fin 2) | s 0 < 0 ∧ s 1 < 0}) := by
  sorry
