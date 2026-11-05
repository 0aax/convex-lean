import Mathlib

/-!
# Shared definitions of the formalization project

Extended-real-valued functions `f : E → EReal` (functions into `ℝ ∪ {±∞}`), their effective
domain, epigraph, properness and convexity, and the horizon (asymptotic, recession) cone and
function.
-/

open Filter Topology

section ExtendedRealFunctions

variable {E : Type*}

/-- The effective domain `dom f = {x | f x < +∞}` of an extended-real-valued function. -/
def effDom (f : E → EReal) : Set E := {x | f x < ⊤}

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function. -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ p.2}

/-- Properness: `f` never takes the value `-∞` and is not identically `+∞`. -/
def ProperEReal (f : E → EReal) : Prop := (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- Convexity of an extended-real-valued function, defined as convexity of its epigraph. -/
def ConvexEReal [AddCommGroup E] [Module ℝ E] (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The function whose epigraph is described by a set `S ⊆ E × ℝ`:
`x ↦ inf {r ∈ ℝ | (x, r) ∈ S}`, which is `+∞` when there is no such `r`. -/
noncomputable def funFromSet (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf ((fun r : ℝ => (r : EReal)) '' {r | (x, r) ∈ S})

end ExtendedRealFunctions

section Horizon

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The horizon cone of a set (Rockafellar–Wets, Definition 3.3):
`C^∞ = {d | ∃ xᵛ ∈ C, λᵛ ↘ 0, λᵛ • xᵛ → d}` when `C ≠ ∅`, and `C^∞ = {0}` when `C = ∅`.
For a nonempty closed convex set it is the asymptotic (recession) cone
`{d | x + t • d ∈ C for all t > 0}` for any `x ∈ C`. -/
def horizonCone (C : Set E) : Set E :=
  {d | (C = ∅ ∧ d = 0) ∨
    ∃ (x : ℕ → E) (lam : ℕ → ℝ), (∀ ν, x ν ∈ C) ∧ (∀ ν, 0 < lam ν) ∧ Antitone lam ∧
      Tendsto lam atTop (𝓝 0) ∧ Tendsto (fun ν => lam ν • x ν) atTop (𝓝 d)}

/-- The asymptotic (horizon, recession) function `f'_∞` of `f`, defined through its epigraph:
`epi f'_∞ = (epi f)^∞`. -/
noncomputable def asymptoticFun (f : E → EReal) : E → EReal :=
  funFromSet (horizonCone (epigraph f))

end Horizon
