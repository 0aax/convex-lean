import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_2_1_3
  (S : Set E)
  (hS : Set.Nonempty S) :
  let support_fun := supportFunction S
  (∀ x, support_fun x ≠ ⊤) ↔
  (Bornology.IsBounded S) := by
  sorry
