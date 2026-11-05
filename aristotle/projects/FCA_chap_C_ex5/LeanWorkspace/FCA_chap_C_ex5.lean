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

def polarBody {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ 1}

def SupportingHyperplaneAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (s x : E) (r : ℝ)
  (C : Set E) : Prop :=
  (s ≠ 0) ∧ (x ∈ C) ∧
  (IsSupportingHyperplane s r C) ∧
  (x ∈ affineHyperplane s r)

theorem FCA_chap_C_ex5 (C : Set E)
  (hC_compact : IsCompact C)
  (hC_convex : Convex ℝ C)
  (hC_origin_int : 0 ∈ interior C) :
  let C_circ := polarBody C
  ∀ (s x : E),
  List.TFAE [
    SupportingHyperplaneAt s x 1 C,
    SupportingHyperplaneAt x s 1 C_circ,
    (x ∈ frontier C) ∧ (s ∈ frontier C_circ) ∧ (inner ℝ s x = 1)
  ] := by
  sorry
