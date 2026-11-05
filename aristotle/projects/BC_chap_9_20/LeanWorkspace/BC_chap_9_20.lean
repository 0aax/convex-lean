import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def IsProperLSCConvex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) : Prop :=
  (IsProper f) ∧ (LowerSemicontinuous f) ∧ (ConvexEReal f)

theorem BC_chap_9_20
  (f : E → EReal)
  (hf : IsProperLSCConvex f) :
  ∃ (p u : E), ∀ (y : E),
    (p ∈ effDom f) ∧
    ((inner ℝ (y - p) u) + f p ≤ f y) := by
  sorry
