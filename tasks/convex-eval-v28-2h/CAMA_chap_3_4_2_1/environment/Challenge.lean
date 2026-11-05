import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def affineHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x = t}

def hyperplaneHalfspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x ≤ t}

def IsSupportingHyperplane {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s : E) (t : ℝ)
  (C : Set E) : Prop :=
  C ⊆ hyperplaneHalfspace s t

def SupportingHyperplaneAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s x : E) (r : ℝ)
  (C : Set E) : Prop :=
  (s ≠ 0) ∧ (x ∈ C) ∧
  (IsSupportingHyperplane s r C) ∧
  (x ∈ affineHyperplane s r)

theorem CAMA_chap_3_4_2_1
  (C : Set E)
  (x : E)
  (hC_convex : Convex ℝ C)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hx : x ∈ frontier C) :
  ∃ (r : ℝ) (s : E), SupportingHyperplaneAt s x r C := by
  sorry
