import Mathlib

/-!
# Project definitions

Shared definitions for extended-real-valued convex functions, following
Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Chapter B, §1.1.

A convex function in the sense of HUL (Definition B.1.1.3) is a map
`f : ℝⁿ → ℝ ∪ {+∞}`, not identically `+∞`, satisfying Jensen's inequality.  We model the
codomain `ℝ ∪ {+∞}` inside `EReal = ℝ ∪ {±∞}` (the value `-∞ = ⊥` being excluded by a
hypothesis), so that the same definitions also serve sources working with `ℝ ∪ {±∞}`.
The ambient space is an arbitrary real vector space `E` (e.g. `EuclideanSpace ℝ (Fin n)`).
-/

variable {E : Type*}

/-- The *effective domain* `dom f = {x | f x < +∞}` of an extended-real-valued function
(HUL, Definition B.1.1.4). -/
def effectiveDomain (f : E → EReal) : Set E := {x | f x < ⊤}

/-- The *epigraph* `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function
(HUL, Definition B.1.1.5). -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

section Module

variable [AddCommGroup E] [Module ℝ E]

/-- Jensen's inequality for an extended-real-valued function (HUL, Definition B.1.1.3):
for all `x, x'` and all `α ∈ ]0, 1[`, `f (α x + (1 - α) x') ≤ α f x + (1 - α) f x'`,
read as an inequality in `EReal`. -/
def IsConvexFunction (f : E → EReal) : Prop :=
  ∀ x x' : E, ∀ a : ℝ, 0 < a → a < 1 →
    f (a • x + (1 - a) • x') ≤ (a : EReal) * f x + ((1 - a : ℝ) : EReal) * f x'

/-- Membership in the class `Conv E` of HUL (Definition B.1.1.3): `f` takes its values in
`ℝ ∪ {+∞}` (never `-∞`), is not identically `+∞`, and satisfies Jensen's inequality.
In the terminology of Rockafellar–Wets such an `f` is a *proper* convex function. -/
structure IsProperConvexFunction (f : E → EReal) : Prop where
  /-- `f` never takes the value `-∞`. -/
  ne_bot : ∀ x, f x ≠ ⊥
  /-- `f` is not identically `+∞`, i.e. `dom f ≠ ∅`. -/
  exists_ne_top : ∃ x, f x ≠ ⊤
  /-- `f` satisfies Jensen's inequality. -/
  convex : IsConvexFunction f

end Module
