import Mathlib

namespace ConvexAnalysis

variable {E : Type*}

/-- An extended-real-valued function is proper if it never takes the value `-∞`
and takes a finite value somewhere. -/
def IsProper (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ ∃ x, f x < ⊤

/-- The epigraph of an extended-real-valued function, with real height coordinate. -/
def epigraph (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- The sublevel set at a real level `r`. -/
def sublevelSet (f : E → EReal) (r : ℝ) : Set E :=
  {x | f x ≤ (r : EReal)}

/-- The asymptotic (or recession) function of a proper lower semicontinuous
convex function, expressed as a supremum of directional difference quotients.

For such a function, the supremum over positive `t` is independent of the
finite base point `x` (Hiriart-Urruty and Lemaréchal, equation B.3.2.2).
Taking the supremum over all finite base points avoids choosing one. -/
noncomputable def asymptoticFunction [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) (d : E) : EReal :=
  ⨆ (x : E) (_ : f x ≠ ⊥) (_ : f x ≠ ⊤) (t : ℝ) (_ : 0 < t),
    (f (x + t • d) - f x) / (t : EReal)

end ConvexAnalysis
