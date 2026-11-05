import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def genCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : Set E) : Set E :=
  {v : E | ∃ (k : ℕ) (α : ℕ → ℝ) (x : ℕ → E),
   (∀ i ∈ Finset.range k, α i ≥ 0) ∧
   (∀ i ∈ Finset.range k, x i ∈ S) ∧
   (v = ∑ i ∈ Finset.range k, (α i) • (x i))}

def translateSet {E : Type*} [NormedAddCommGroup E]
  (C : Set E) (x : E)
  : Set E
  := {v : E | ∃ c ∈ C, v = (c - x)}

theorem CAMA_chap_3_5_2_1
  (C : Set E)
  (x : E)
  (hx_inC : x ∈ C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  posTangentConeAt C x = closure (genCone (translateSet C x)) := by
  sorry
