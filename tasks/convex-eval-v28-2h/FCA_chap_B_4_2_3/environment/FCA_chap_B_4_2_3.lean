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

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

theorem FCA_chap_B_4_2_3
  {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let f_real := fun x ↦ (f x).toReal
  let non_diff_points :=
    {x | x ∈ interior (effDom f) ∧ ¬DifferentiableAt ℝ f_real x}
  (∀ x ∈ effDom f, f x = (f_real x : EReal)) ∧ volume non_diff_points = 0 := by
  sorry
