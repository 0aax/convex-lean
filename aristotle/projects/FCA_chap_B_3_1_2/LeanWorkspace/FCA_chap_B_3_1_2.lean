import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

theorem FCA_chap_B_3_1_2
  [FiniteDimensional ℝ E]
  (f : E → EReal)
  (S : Set E)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (hS_convex : Convex ℝ S)
  (hS_compact : IsCompact S)
  (hS_subset : S ⊆ intrinsicInterior ℝ (effDom f)) :
  ∃ L ≥ 0, ∀ x ∈ S, ∀ x' ∈ S,
  abs ((f x).toReal - (f x').toReal) ≤ L * ‖x - x'‖ := by
  sorry
