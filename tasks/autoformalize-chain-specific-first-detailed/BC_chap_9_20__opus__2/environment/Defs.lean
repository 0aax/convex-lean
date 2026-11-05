import Mathlib

/-!
# Shared definitions of the formalization project

## Extended-real-valued functions

A function that may take the value `+∞` is a function `f : E → EReal`; the value `+∞` is `⊤`.
-/

/-- The (effective) domain of an extended-real-valued function: `dom f := {x | f x < +∞}`. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- The epigraph `epi f := {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- An extended-real-valued function is convex when its epigraph is a convex set. -/
def ConvexEReal {E : Type*} [AddCommMonoid E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- An extended-real-valued function is proper when it never takes the value `-∞` and is not
identically `+∞`, i.e. its effective domain is nonempty. -/
def ProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty
