import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

def directionalSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  let f' := fun (d : E) => directionalDeriv f x d
  {s : E | ∀ d, inner ℝ s d ≤ f' d}

theorem FCA_chap_D_ex2
  (f : E → ℝ)
  (x : E)
  (hf : InConvRn (liftRealtoEReal f)) :
  (sInf {c : ℝ | (c ≥ 0) ∧ (∀ d, f (x + d) ≥ (f x) - c * ‖d‖)}
  = sInf (Set.image (fun v => ‖v‖) (directionalSubdifferential (liftRealtoEReal f) x))) ∧
  (∀ (ε : ℝ), (ε > 0) →
  (ε⁻¹ * (sSup (Set.image (fun d => f (x + d) - (f x)) {d | ‖d‖ ≤ ε})) ≥
  sSup (Set.image (fun v => ‖v‖) (directionalSubdifferential (liftRealtoEReal f) x)))) ∧
  ((directionalSubdifferential (liftRealtoEReal f) x) =
  ⋂ ε > 0, closure (convexHull ℝ {v | ∃ d,
                                      (‖d‖ < ε) ∧
                                      (v ∈ (directionalSubdifferential (liftRealtoEReal f) (x + d)))})) := by
  sorry
