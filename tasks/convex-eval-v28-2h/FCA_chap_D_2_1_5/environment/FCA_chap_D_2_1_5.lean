import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def argmax {E : Type*}  (f : E → ℝ) (C : Set E)
  : Set E
  := {x : E | (x ∈ C) ∧ (∀ y ∈ C, f y ≤ f x)}

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def exposedFace {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) (s : E) : Set E :=
  argmax (fun y => inner ℝ s y) C

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

theorem FCA_chap_D_2_1_5
  (f : E → ℝ)
  (x d : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := fun (d : E) =>
    directionalDeriv (liftRealtoEReal f) x d
  exposedFace (directionalSubdifferential (liftRealtoEReal f) x) d =
    directionalSubdifferential f' d := by
  sorry
