import Mathlib

namespace ConvexAnalysis

/-- The effective domain of an extended-real-valued function. For a function that never
takes the value `⊥`, this is precisely the set where it is finite. -/
def effectiveDomain {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- The epigraph with real height coordinate of an extended-real-valued function. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- A proper convex function never takes the value `-∞`, is finite somewhere, and has
a convex epigraph. This is the class `Conv ℝⁿ` in Hiriart-Urruty and Lemaréchal. -/
def IsProperConvex {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (effectiveDomain f).Nonempty ∧ Convex ℝ (epigraph f)

end ConvexAnalysis
