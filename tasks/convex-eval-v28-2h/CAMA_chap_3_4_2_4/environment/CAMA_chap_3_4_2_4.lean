import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def hyperplaneHalfspace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (s : E) (t : ℝ) : Set E :=
  {x | inner ℝ s x ≤ t}

def halfspacesContaining {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]  (C : Set E) : Set (E × ℝ)
    := {(s, r) : E × ℝ | C ⊆ hyperplaneHalfspace s r}

theorem CAMA_chap_3_4_2_4
  (C : Set E)
  (hC₀ : Convex ℝ C)
  (hC₁ : Set.Nonempty C)
  (hC₂ : C ⊂ Set.univ) :
  closure C = ⋂ v ∈ (halfspacesContaining C), hyperplaneHalfspace v.1 v.2 := by
  sorry
