import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem CAMA_chap_3_5_2_5
  (C : Set E)
  (x : E)
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  posTangentConeAt C x = polarCone (convexNormalCone x C) := by
  sorry
