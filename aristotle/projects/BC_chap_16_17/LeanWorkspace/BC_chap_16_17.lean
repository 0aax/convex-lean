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

def convexSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  {s | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

def cont {X : Type*} [TopologicalSpace X]
  (f : X → EReal) : Set X :=
  {x : X | f x ≠ ⊤ ∧ f x ≠ ⊥ ∧ ContinuousAt f x}

def opDom {E : Type*} (A : E → Set E) : Set E :=
  {x : E | Set.Nonempty (A x)}

theorem BC_chap_16_17
  (f : E → EReal)
  (x : E)
  (hx : x ∈ effDom f)
  (hf_proper : IsProper f)
  (hf_convex : ConvexEReal f) :
  ((Set.Nonempty (interior (effDom f))) →
    (x ∈ frontier (effDom f)) →
      (convexSubdifferential f x = ∅) ∨ ¬(Bornology.IsBounded (convexSubdifferential f x))) ∧
  ((x ∈ cont f) →
    ((Set.Nonempty (convexSubdifferential f x)) ∧
    (IsCompact (Set.image (toWeakSpace ℝ E) (convexSubdifferential f x))))) ∧
  ((x ∈ cont f) →
    (∃ (ρ : ℝ),
      (0 < ρ) ∧
      (Bornology.IsBounded (⋃ v ∈ Metric.ball x ρ, convexSubdifferential f v)))) ∧
  ((Set.Nonempty (cont f)) →
    intrinsicInterior ℝ (effDom f) ⊆ opDom (convexSubdifferential f)) := by
  sorry
