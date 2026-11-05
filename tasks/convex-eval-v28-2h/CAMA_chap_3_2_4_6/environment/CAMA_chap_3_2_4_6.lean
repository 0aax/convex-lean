import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def argmax {E : Type*}  (f : E → ℝ) (C : Set E)
  : Set E
  := {x : E | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

theorem CAMA_chap_3_2_4_6
  (C : Set E)
  (s : E)
  (hC₀ : IsCompact C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (sSup (Set.image (fun x ↦ inner ℝ s x) C) =
  sSup (Set.image (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) ∧
  (argmax (fun x ↦ inner ℝ s x) C =
  convexHull ℝ (argmax (fun x ↦ inner ℝ s x) (Set.extremePoints ℝ C))) := by
  sorry
