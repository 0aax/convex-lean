import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_2_2_1
  (S : Set E)
  (hS : Set.Nonempty S) :
  let sf_S := supportFunction S
  let sf_clS := supportFunction (closure S)
  let sf_coS := supportFunction (convexHull ℝ S)
  let sf_barcoS := supportFunction (closure (convexHull ℝ S))
  ∀ (x : E),
  (sf_S x = sf_clS x) ∧
  (sf_clS x = sf_coS x) ∧
  (sf_S x = sf_barcoS x) := by
  sorry
