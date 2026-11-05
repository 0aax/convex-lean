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

theorem FCA_chap_D_1_1_6
  (f : E → ℝ)
  (x : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let σ := fun (d : E) => directionalDeriv (liftRealtoEReal f) x d
  let σ' := fun (d : E) => directionalDeriv σ 0 d
  (∀ (δ : E), σ' δ = σ δ) ∧
  (∀ (δ : E), (σ δ = σ 0 + σ' δ) ∧ (σ δ = σ' δ)) ∧
  (directionalSubdifferential σ 0 = directionalSubdifferential (liftRealtoEReal f) x) := by
  sorry
