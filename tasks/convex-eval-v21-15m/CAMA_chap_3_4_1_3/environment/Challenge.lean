import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_1_3
  (C₁ C₂ : Set E)
  (hC₁ : Set.Nonempty C₁ ∧ Convex ℝ C₁ ∧ IsClosed C₁)
  (hC₂ : Set.Nonempty C₂ ∧ Convex ℝ C₂ ∧ IsClosed C₂)
  (h_disjoint : C₁ ∩ C₂ = ∅) :
  (Bornology.IsBounded C₂) → (∃ (s : E),
    BddAbove ((fun y => inner ℝ s y) '' C₁) ∧
    BddBelow ((fun y => inner ℝ s y) '' C₂) ∧
    (∃ y₂ ∈ C₂, IsMinOn (fun y => inner ℝ s y) C₂ y₂) ∧
    sSup ((fun y => inner ℝ s y) '' C₁) < sInf ((fun y => inner ℝ s y) '' C₂)) := by
  sorry
