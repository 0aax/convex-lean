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

theorem FCA_chap_C_3_2_7
  (C : Set E)
  (d s : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_compact : IsCompact C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ interior C) :
  let C' := polarBody C
  let Hs := {y | inner ℝ s y = 1}
  let Hd := {y | inner ℝ d y = 1}
  List.TFAE [
    ∃ (s' : E) (t' : ℝ), (SupportingHyperplaneAt s' d t' C) ∧
                                                 (affineHyperplane s' t' = Hs),
    ∃ (d' : E) (t' : ℝ), (SupportingHyperplaneAt d' s t' C') ∧
                                                 (affineHyperplane d' t' = Hd),
    (d ∈ frontier C) ∧ (s ∈ frontier C') ∧ (inner ℝ s d = 1),
    (d ∈ C) ∧ (s ∈ C') ∧ (inner ℝ s d = 1)
  ] := by
  sorry
