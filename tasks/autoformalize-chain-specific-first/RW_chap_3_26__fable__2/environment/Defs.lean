import Mathlib

/-!
# Definitions shared by the formalization project

Extended-real-valued convex analysis in the style of Hiriart-Urruty & Lemaréchal
(*Fundamentals of Convex Analysis*, Chapter B).  Functions take values in `EReal`
(`ℝ ∪ {-∞, +∞}`); the book's class `Conv ℝⁿ` corresponds to functions that are
convex (convex epigraph) and proper (never `-∞`, not identically `+∞`), and
`\overline{Conv} ℝⁿ` adds closedness, i.e. lower semicontinuity.
-/

namespace ConvexAnalysis

variable {E : Type*}

/-- The sublevel set `S_r(f) = {x | f x ≤ r}` of `f` at the (real) level `r` (HUL, Chapter B, (1.1.4)). -/
def sublevelSet (f : E → EReal) (r : ℝ) : Set E := {x | f x ≤ (r : EReal)}

/-- The effective domain `dom f = {x | f x < +∞}` of an extended-real-valued function
(HUL, Chapter B, Def. 1.1.4). -/
def effectiveDomain (f : E → EReal) : Set E := {x | f x < ⊤}

/-- `f` is proper: it never takes the value `-∞` and is not identically `+∞`
(i.e. its effective domain is nonempty).  HUL's functions take values in `ℝ ∪ {+∞}` and are
assumed not identically `+∞`, so `Conv ℝⁿ` is exactly the class of proper convex functions. -/
def IsProper (f : E → EReal) : Prop := (∀ x, f x ≠ ⊥) ∧ (effectiveDomain f).Nonempty

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function
(HUL, Chapter B, Def. 1.1.5). -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

section Module

variable [AddCommGroup E] [Module ℝ E]

/-- An extended-real-valued function is convex when its epigraph is a convex subset of `E × ℝ`
(HUL, Chapter B, Prop. 1.1.6 (ii), equivalent to the analytic Definition 1.1.3). -/
def IsConvexFun (f : E → EReal) : Prop := Convex ℝ (epigraph f)

/-- The asymptotic (or recession) function `f'∞` of `f` (HUL, Chapter B, Prop. 3.2.1 /
Def. 3.2.2):
`f'∞ d = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t`, where `x₀` is any point of `dom f`.
For `f` closed proper convex this quantity does not depend on the choice of `x₀ ∈ dom f`,
so we take the supremum over all `x₀ ∈ dom f` to obtain a definition intrinsic to `f`. -/
noncomputable def asymptoticFunction (f : E → EReal) (d : E) : EReal :=
  ⨆ (x : E) (_ : x ∈ effectiveDomain f) (t : ℝ) (_ : 0 < t), (f (x + t • d) - f x) / (t : EReal)

end Module

end ConvexAnalysis
