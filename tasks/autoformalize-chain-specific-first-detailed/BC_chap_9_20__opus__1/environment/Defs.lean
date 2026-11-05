import Mathlib

/-!
# Shared definitions of the convex-analysis formalization project

Extended-real-valued functions `f : E → EReal` (functions that may take the value `+∞`).
-/

section ExtendedRealFunctions

variable {E : Type*}

/-- The (effective) domain of an extended-real-valued function, `dom f := {x | f x < +∞}`. -/
def effDom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- The epigraph of an extended-real-valued function, `epi f := {(x, r) ∈ E × ℝ | f x ≤ r}`. -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p : E × ℝ | f p.1 ≤ p.2}

/-- An extended-real-valued function is convex when its epigraph is a convex set. -/
def ConvexEReal [AddCommMonoid E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- An extended-real-valued function is proper when it never takes the value `-∞` and is not
identically `+∞`. -/
def ProperEReal (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

end ExtendedRealFunctions
