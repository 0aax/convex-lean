import Mathlib

namespace ConvexAnalysis

/-- The effective domain of an extended-real-valued function. For a proper function,
these are precisely the points where its value is a real number. -/
def effectiveDomain {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- An extended-real-valued function is proper if it never takes the value `-∞`
and its effective domain is nonempty. -/
def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (effectiveDomain f).Nonempty

/-- The epigraph with real height coordinates. Convexity of this set expresses
convexity of an extended-real-valued function. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

end ConvexAnalysis
