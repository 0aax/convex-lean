import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def convexNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (x : E) (C : Set E) : Set E :=
  {s : E | ∀ y ∈ C, inner ℝ s (y - x) ≤ 0}

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

def sublevelSetFun {E : Type*}
  (f : E → EReal)
  (x : E) : Set E :=
  {y : E | f y ≤ f x}

theorem FCA_chap_D_1_3_5
    (f : E → ℝ)
    (x d : E)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_subdiff : 0 ∉ directionalSubdifferential (liftRealtoEReal f) x) :
    let S := sublevelSetFun (liftRealtoEReal f) x
    (d ∈ convexNormalCone x S) ↔
    (∃ (t : ℝ) (s : E),
    (t ≥ 0) ∧ (s ∈ directionalSubdifferential (liftRealtoEReal f) x) ∧ (d = t • s)) := by
  sorry
