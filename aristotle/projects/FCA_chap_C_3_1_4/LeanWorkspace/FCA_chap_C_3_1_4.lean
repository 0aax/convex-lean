import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def argmax {E : Type*}  (f : E → ℝ) (C : Set E)
  : Set E
  := {x : E | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

def exposedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) (s : E) : Set E :=
  argmax (fun y => inner ℝ s y) C

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

theorem FCA_chap_C_3_1_4
  (C : Set E)
  (x d : E)
  (hC_nonempty : C.Nonempty)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx : x ∈ C)
  (hd : d ≠ 0) :
  x ∈ exposedFace C d ↔ d ∈ convexNormalCone x C := by
  sorry
