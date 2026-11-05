import Mathlib

/-!
# Shared definitions for the formalization project

Extended-real-valued functions `f : E → EReal` model the sources' functions into
`ℝ ∪ {+∞}` (Hiriart-Urruty & Lemaréchal, Rockafellar & Wets, Bauschke & Combettes).
The value `⊥ = -∞` is excluded by a properness hypothesis only where a source assumes it.
-/

open Filter Topology

noncomputable section

/-- The effective domain `dom f = {x | f x < +∞}` of an extended-real-valued function. -/
def effDom {E : Type*} (f : E → EReal) : Set E := {x | f x < ⊤}

/-- `f` is proper: it never takes the value `-∞` and is not identically `+∞`
(Rockafellar–Wets' "proper"; Hiriart-Urruty & Lemaréchal's
"`f : ℝⁿ → ℝ ∪ {+∞}` not identically `+∞`"). -/
def IsProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function: convexity of its epigraph. -/
def ConvexEReal {E : Type*} [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The sublevel set `S_r(f) = {x | f x ≤ r}` of `f` at the (real) level `r`. -/
def sublevelSet {E : Type*} (f : E → EReal) (r : ℝ) : Set E := {x | f x ≤ (r : EReal)}

/-- The horizon cone (asymptotic cone, recession cone) of a set `C`, in its sequential form
(Rockafellar–Wets, Definition 3.3): the limits `d` of `λₙ • xₙ` with `xₙ ∈ C` and `λₙ ↘ 0`.
For a nonempty closed convex set it is the asymptotic cone `C_∞` of
Hiriart-Urruty & Lemaréchal (Definition A.2.2.2) and the recession cone `rec C` of
Bauschke & Combettes. -/
def horizonCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (C : Set E) : Set E :=
  {d | ∃ (x : ℕ → E) (l : ℕ → ℝ), (∀ n, x n ∈ C) ∧ (∀ n, 0 < l n) ∧
    Tendsto l atTop (𝓝 0) ∧ Tendsto (fun n => l n • x n) atTop (𝓝 d)}

/-- The function `x ↦ inf {t | (x, t) ∈ S}` determined by a subset `S ⊆ E × ℝ`
(so that `epigraph (funFromSet S) = S` whenever `S` is a closed epigraph). -/
def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf ((fun t : ℝ => (t : EReal)) '' {t : ℝ | (x, t) ∈ S})

/-- The asymptotic function (recession function, horizon function) `f'_∞` of `f`, defined
through the epigraph: `epi f'_∞ = (epi f)_∞` (Hiriart-Urruty & Lemaréchal, Proposition B.3.2.1
and Definition B.3.2.2; Rockafellar–Wets, Definition 3.17; Bauschke & Combettes,
Proposition 9.29). The difference-quotient formula
`f'_∞ d = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t` is a theorem about it, not its definition. -/
def asymptoticFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → EReal) :
    E → EReal :=
  funFromSet (horizonCone (epigraph f))

end
