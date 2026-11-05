import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def strictEpigraph {E : Type*}
  (f : E → EReal) : Set (E × ℝ)
  := {p : E × ℝ | f p.1 < p.2}

theorem FCA_chap_B_1_1_6
  (f : E → EReal)
  (hf_nonemptyDomain : ∃ x, f x < ⊤)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  List.TFAE [
    (∀ (x y : E), ∀ (t : ℝ), 0 ≤ t ∧ t ≤ 1 →
      f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y),
    Convex ℝ (epigraph f),
    Convex ℝ (strictEpigraph f)
  ] := by
  sorry
