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

def affineHull {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Set E
  := ⋃ (k : ℕ) (_ : k > 0) (x : (Fin k) → E) (_ : ∀ i, x i ∈ C),
     {v : E |
      ∃ (a : Fin k → ℝ), (∑ i, a i = 1) ∧ (v = ∑ i, a i • x i)}

def parallelSubspace {E : Type*} [NormedAddCommGroup E]
  (S : Set E) : Set E :=
  {v : E | ∃ x, ∃ y, (x ∈ S) ∧ (y ∈ S) ∧ (v = x - y)}

theorem FCA_chap_B_1_2_1
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ (x₀ : E), (x₀ ∈ intrinsicInterior ℝ (effDom f)) →
  ∃ (s : E), ∀ (x : E),
  (s ∈ parallelSubspace (affineHull (effDom f))) ∧
  (f x ≥ f x₀ + inner ℝ s (x - x₀)) := by
  sorry
