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

theorem FCA_chap_D_1_3_4
  (f : E → ℝ)
  (x : E)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_subdiff : 0 ∉ directionalSubdifferential (liftRealtoEReal f) x) :
  let S := sublevelSetFun (liftRealtoEReal f) x
  (posTangentConeAt S x = {d | directionalDeriv (liftRealtoEReal f) x d ≤ 0}) ∧
  (interior (posTangentConeAt S x) = {d | directionalDeriv (liftRealtoEReal f) x d < 0}) ∧
  Set.Nonempty (interior (posTangentConeAt S x)) := by
  sorry
