import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

def supportSublevelSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : Set E :=
  {v : E | ∀ (w : E), (((inner ℝ v w) : ℝ) : EReal) ≤ h w}

theorem FCA_chap_C_2_2_2
  (S : Set E)
  (s : E)
  (hS : Set.Nonempty S) :
  let sf_S := supportFunction S
  (s ∈ closure (convexHull ℝ S)) ↔
  s ∈ supportSublevelSet sf_S := by
  sorry
