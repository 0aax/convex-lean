import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def affineHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Set E
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → E) (_ : ∀ i, x i ∈ C),
     {v : E |
      ∃ (a : Fin k → ℝ), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_2_2_3
  (S : Set E)
  (s : E)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S) :
  let σS := supportFunction S
  ((s ∈ affineHull S) ↔ (∀ d, σS d + σS (-1 • d) = 0 → inner ℝ s d = σS d)) ∧
  ((s ∈ intrinsicInterior ℝ S) ↔ ((s ∈ affineHull S) ∧
                                  (∀ d, σS d + σS (-1 • d) > 0 → inner ℝ s d < σS d))) ∧
  ((s ∈ interior S) ↔ (∀ d, d ≠ 0 → inner ℝ s d < σS d)) := by
  sorry
