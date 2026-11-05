import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def polarBody {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {y | ∀ x ∈ K, inner ℝ x y ≤ 1}

noncomputable def gaugeFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x : E) : EReal :=
  sInf {l : EReal | ∃ (l' : ℝ),
                        (l = (l' : EReal)) ∧
                        (l' > 0) ∧
                        (∃ y ∈ C, (x = l' • y))}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_2_4
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let γC := gaugeFun C
  let C' := polarBody C
  let σC' := supportFunction C'
  (∀ (x : E), γC x = σC' x) ∧ IsClosed C' ∧ Convex ℝ C' ∧ 0 ∈ C' := by
  sorry
