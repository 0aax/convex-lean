import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

theorem FCA_chap_B_2_1_2
  {ι : Type*}
  (J : Set ι)
  (hJ : J.Nonempty)
  (f : ι → E → EReal)
  (hx₀ : ∃ x₀, sSup {y | ∃ j ∈ J, f j x₀ = y} < ⊤)
  (f_ne_bot : ∀ j x, ⊥ < f j x) :
  let g := fun x => sSup {y | ∃ j ∈ J, f j x = y}
  ((∀ j ∈ J, ConvexEReal (f j)) → InConvRn g) ∧
    ((∀ j ∈ J, ConvexEReal (f j) ∧ LowerSemicontinuous (f j)) →
      InClosedConvRn g) := by
  sorry
