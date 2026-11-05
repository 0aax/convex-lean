import Mathlib

/-- The effective domain of an extended-real-valued function. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- A proper function never takes the value `-∞` and has nonempty effective domain. -/
def IsProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- The epigraph has real heights, even when the function has extended-real values. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- Convexity of an extended-real-valued function is convexity of its epigraph.
This definition also applies to improper functions. -/
def ConvexEReal {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The lower-bound function of a set, as in Hiriart-Urruty--Lemaréchal,
Fundamentals of Convex Analysis, B.1.3(g), equation (1.3.5).
The infimum is taken in `EReal`: an empty vertical fiber gives `⊤`, and a fiber
unbounded below gives `⊥`. -/
noncomputable def funFromSet {E : Type*} (C : Set (E × ℝ)) : E → EReal :=
  fun x => sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ C})

/-- The asymptotic (horizon) function, defined through the epigraph without a base point.

Mathlib's `asymptoticCone ℝ C` is the general horizon cone: in a normed real space,
its elements are limits of `λ n • x n`, where `x n ∈ C`, the scalars `λ n` are
positive and decrease to zero. Thus the cone is available even for nonconvex sets.
For nonempty epigraphs this gives Rockafellar--Wets, Definition 3.17. For proper
lower semicontinuous convex functions it agrees with the asymptotic function of
Hiriart-Urruty--Lemaréchal, B.3.2.1--B.3.2.2; see also Rockafellar--Wets, Theorem 3.21.
-/
noncomputable def asymptoticFun {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : E → EReal :=
  funFromSet (asymptoticCone ℝ (epigraph f))
