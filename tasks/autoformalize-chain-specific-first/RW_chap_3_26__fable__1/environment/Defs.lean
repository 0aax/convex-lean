import Mathlib

/-!
# Shared definitions for the formalization project

Convex-analytic notions used across the corpus that are not (yet) in Mathlib.

Extended-real-valued functions are modelled as `f : E → EReal`.  A function of the class
`Conv E` of Hiriart-Urruty–Lemaréchal (closed, convex, proper, with values in `ℝ ∪ {+∞}`) is
described by the hypotheses `Convex ℝ (epigraph f)`, `LowerSemicontinuous f`,
`∀ x, f x ≠ ⊥` and `∃ x, f x ≠ ⊤`.
-/

section Epigraph

variable {E : Type*}

/-- The epigraph `epi f = {(x, r) ∈ E × ℝ | f x ≤ r}` of an extended-real-valued function
(Hiriart-Urruty–Lemaréchal, *Fundamentals of Convex Analysis*, §B.1.1). -/
def epigraph (f : E → EReal) : Set (E × ℝ) := {p | f p.1 ≤ p.2}

end Epigraph

section AsymptoticFun

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]

/-- The asymptotic (or recession) function `f'∞` of `f : E → EReal`
(Hiriart-Urruty–Lemaréchal, *Fundamentals of Convex Analysis*, Prop. B.3.2.1 and Def. B.3.2.2):
the function whose epigraph is the asymptotic cone `(epi f)∞` of the epigraph of `f`, i.e.
`f'∞ d = inf {p ∈ ℝ | (d, p) ∈ (epi f)∞}` (with `inf ∅ = +∞`).

For `f` closed, convex and proper this coincides with the analytic formula (B.3.2.2)
`f'∞ d = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t = lim_{t → +∞} (f (x₀ + t • d) - f x₀) / t`,
valid for any `x₀ ∈ dom f`. -/
noncomputable def asymptoticFun (f : E → EReal) (d : E) : EReal :=
  ⨅ (p : ℝ) (_ : (d, p) ∈ asymptoticCone ℝ (epigraph f)), (p : EReal)

end AsymptoticFun
