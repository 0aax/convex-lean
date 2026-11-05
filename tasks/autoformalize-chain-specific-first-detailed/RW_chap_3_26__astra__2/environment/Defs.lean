import Mathlib

open scoped Topology

/-- The effective domain of an extended-real-valued function. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- A proper function never takes the value `-∞` and has nonempty effective domain. -/
def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, (⊥ : EReal) < f x) ∧ (effDom f).Nonempty

/-- The epigraph, with real heights, also for functions taking either infinite value. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- Extended-real convexity is convexity of the epigraph.
This also applies to improper functions, as in Bauschke--Combettes, Definition 8.1. -/
def ConvexEReal {E : Type*} [AddCommMonoid E] [Module ℝ E]
    (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The sequential horizon cone: limits of points of the set scaled by positive
real numbers decreasing to zero. For nonempty closed convex sets this agrees with
the asymptotic cone of Hiriart-Urruty--Lemaréchal, Definition A.2.2.2; see also
Rockafellar--Wets, Definition 3.3 and Theorem 3.6. -/
def horizonCone {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : Set E) : Set E :=
  {d | ∃ (x : ℕ → E) (lam : ℕ → ℝ),
    (∀ k, x k ∈ C) ∧
    (∀ k, 0 < lam k) ∧
    Antitone lam ∧
    Filter.Tendsto lam Filter.atTop (𝓝 (0 : ℝ)) ∧
    Filter.Tendsto (fun k => lam k • x k) Filter.atTop (𝓝 d)}

/-- The function obtained by taking the infimum of each vertical fibre of a set.
The infimum is in `EReal`: an empty fibre gives `+∞`, and a fibre unbounded below
gives `-∞`. -/
noncomputable def funFromSet {E : Type*} (C : Set (E × ℝ)) : E → EReal :=
  fun x => sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ C})

/-- The asymptotic (horizon) function is obtained from the horizon cone of the
epigraph. For proper lower semicontinuous convex functions this is the recession
function of Hiriart-Urruty--Lemaréchal, Definition B.3.2.2, by Proposition B.3.2.1
and Rockafellar--Wets, Theorem 3.21. -/
noncomputable def asymptoticFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : E → EReal :=
  funFromSet (horizonCone (epigraph f))
