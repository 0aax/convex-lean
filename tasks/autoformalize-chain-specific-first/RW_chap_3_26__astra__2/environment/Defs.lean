import Mathlib

namespace ConvexAnalysis

/-- The effective domain of an extended-real-valued function. -/
def effectiveDomain {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- A proper function never takes the value `-∞` and is finite somewhere. -/
def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, f x ≠ ⊥) ∧ (effectiveDomain f).Nonempty

/-- The epigraph uses real heights, even when the function can take infinite values. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- The sublevel set at a real level. -/
def sublevelSet {E : Type*} (f : E → EReal) (r : ℝ) : Set E :=
  {x | f x ≤ (r : EReal)}

/-- The asymptotic (or recession) function, given by the supremum of secant slopes.
For a proper lower-semicontinuous convex function, the supremum over positive `t`
is independent of the base point in the effective domain, so the additional
supremum over base points agrees with the usual formula at any such point. -/
noncomputable def asymptoticFunction {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) (d : E) : EReal :=
  ⨆ (x : E) (_ : x ∈ effectiveDomain f) (t : ℝ) (_ : 0 < t),
    (f (x + t • d) - f x) / (t : EReal)

end ConvexAnalysis
