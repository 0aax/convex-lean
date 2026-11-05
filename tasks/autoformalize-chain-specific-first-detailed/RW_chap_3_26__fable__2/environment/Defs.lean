import Mathlib

/-!
# Shared definitions

Definitions shared by the results formalized from the corpus.  Extended-real-valued
functions `f : E → EReal` model the sources' functions into `ℝ ∪ {+∞}` (and `ℝ̄`).
-/

open Set

noncomputable section

/-- The effective domain of an extended-real-valued function: the points where `f` is finite
from above, `dom f = {x | f x < +∞}` (Hiriart-Urruty–Lemaréchal, Def. B.1.1.4;
Rockafellar–Wets 1(3); Bauschke–Combettes Def. 1.4). -/
def effDom {E : Type*} (f : E → EReal) : Set E := {x | f x < ⊤}

/-- `f` is proper: it never takes the value `-∞` and is not identically `+∞`
(Rockafellar–Wets p. 5; Bauschke–Combettes Def. 1.4; this is the standing requirement
"not identically `+∞`" in Hiriart-Urruty–Lemaréchal's `Conv ℝⁿ`, Def. B.1.1.3). -/
def IsProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- The epigraph `epi f = {(x, r) : f x ≤ r}` of an extended-real-valued function, as a
subset of `E × ℝ` (Hiriart-Urruty–Lemaréchal, Def. B.1.1.5). -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function, as convexity of its epigraph
(Hiriart-Urruty–Lemaréchal, Def. B.1.1.6; Rockafellar–Wets Def. 2.1). -/
def ConvexEReal {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The sublevel set `S_r(f) = {x : f x ≤ r}` of `f` at the (finite) level `r`
(Hiriart-Urruty–Lemaréchal §B.1.1, `lev_{≤ r} f` in Rockafellar–Wets 1(2)). -/
def sublevelSet {E : Type*} (f : E → EReal) (r : ℝ) : Set E := {x | f x ≤ (r : EReal)}

/-- The extended-real-valued function "whose epigraph is `S`": `x ↦ inf {r : (x, r) ∈ S}`.
The infimum is `+∞` when no `(x, r)` lies in `S`, so it is taken in `EReal`. -/
def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((↑) : ℝ → EReal) '' {r : ℝ | (x, r) ∈ S})

/-- The asymptotic (recession, horizon) function `f'_∞` of `f`, defined geometrically by
`epi f'_∞ = (epi f)_∞`: its epigraph is the asymptotic cone (Mathlib's `asymptoticCone`,
the sequential horizon cone of Rockafellar–Wets Def. 3.3) of the epigraph of `f`
(Hiriart-Urruty–Lemaréchal Prop. B.3.2.1 / Def. B.3.2.2; Rockafellar–Wets Def. 3.17).
It has no base point; the difference-quotient formula
`f'_∞(d) = sup_{t > 0} (f (x₀ + t d) - f x₀) / t` is a theorem about it. -/
def asymptoticFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal) :
    E → EReal :=
  funFromSet (asymptoticCone ℝ (epigraph f))

end
