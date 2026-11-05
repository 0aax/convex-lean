import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def sublevelSet {E : Type*}
  (r : ℝ) (f : E → EReal) :
  Set E :=
  {x : E | f x ≤ r}

theorem FCA_chap_B_1_2_2
  (f : E → EReal)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  List.TFAE [
    LowerSemicontinuousOn f Set.univ,
    IsClosed (epigraph f),
    ∀ (r : ℝ), IsClosed (sublevelSet r f)
  ] := by
  sorry
