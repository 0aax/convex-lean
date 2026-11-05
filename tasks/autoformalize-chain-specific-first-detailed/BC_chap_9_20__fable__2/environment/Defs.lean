import Mathlib

/-!
# Shared definitions

Extended-real-valued functions `f : E → EReal` model the functions `ℝⁿ → ℝ ∪ {+∞}` of
Hiriart-Urruty & Lemaréchal, the extended-real functions of Rockafellar & Wets, and the
functions of Bauschke & Combettes.  The definitions below are shared by every source.
-/

/-- The effective domain `dom f = {x | f x < +∞}` of an extended-real-valued function
(Hiriart-Urruty & Lemaréchal, Definition B.1.1.4; Rockafellar & Wets §1.A). -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function
(Hiriart-Urruty & Lemaréchal, Definition B.1.1.5). -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function: convexity of its epigraph.  For functions
never taking the value `−∞` this agrees with the inequality
`f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y` (Hiriart-Urruty & Lemaréchal,
Proposition B.1.1.6). -/
def ConvexEReal {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- A proper extended-real-valued function: never `−∞` and not identically `+∞`
(Rockafellar & Wets, Definition 1.4).  Hiriart-Urruty & Lemaréchal's class `Conv ℝⁿ`
(Definition B.1.1.3) is exactly the proper convex functions. -/
def IsProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty
