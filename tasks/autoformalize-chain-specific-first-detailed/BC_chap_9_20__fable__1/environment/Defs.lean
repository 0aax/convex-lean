import Mathlib

/-!
# Shared definitions

Definitions shared by the formalized results of the corpus.

Functions that may take the value `+∞` in a source (functions into `ℝ ∪ {+∞}`, indicator
functions, conjugates, support functions, anything "proper" or "closed") are modelled as
`f : E → EReal`.  Convexity of such a function is convexity of its epigraph, which is the
correct notion for every extended-real-valued function.
-/

noncomputable section

section ERealFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The (effective) domain `dom f = {x | f x < +∞}` of an extended-real-valued function
(Hiriart-Urruty–Lemaréchal, FCA Definition B.1.1.4; Rockafellar–Wets 1(2);
Bauschke–Combettes (1.3)). -/
def effDom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function
(FCA Definition B.1.1.5). -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function: convexity of its epigraph
(FCA Proposition B.1.1.6 (ii); Rockafellar–Wets Definition 2.1). -/
def ConvexEReal (f : E → EReal) : Prop := Convex ℝ (epigraph f)

/-- Properness of an extended-real-valued function: `f` never takes the value `-∞` and is not
identically `+∞` (Rockafellar–Wets p. 5; Bauschke–Combettes p. 7).  Hiriart-Urruty–Lemaréchal's
class `Conv ℝⁿ` (FCA Definition B.1.1.3) is exactly `ProperEReal f ∧ ConvexEReal f`, since
their functions take values in `ℝ ∪ {+∞}` and are not identically `+∞`. -/
def ProperEReal (f : E → EReal) : Prop := (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

end ERealFunctions

section Subdifferential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The subdifferential `∂f(x)` of an extended-real-valued function `f` at `x`: the set of
subgradients `s`, i.e. of those `s` with `f y ≥ f x + ⟨s, y - x⟩` for all `y`
(FCA Proposition B.1.2.1 and Chapter D; Bauschke–Combettes Definition 16.1;
Rockafellar–Wets Proposition 8.12 for proper convex functions). -/
def subdifferential (f : E → EReal) (x : E) : Set E :=
  {s | ∀ y, f x + ((inner ℝ s (y - x) : ℝ) : EReal) ≤ f y}

end Subdifferential

end
