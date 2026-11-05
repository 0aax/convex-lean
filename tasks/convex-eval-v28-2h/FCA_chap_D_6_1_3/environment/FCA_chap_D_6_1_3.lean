import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsStrictMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), x₀ ≠ x₁ → v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

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

theorem FCA_chap_D_6_1_3
  (f : E → ℝ)
  (C : Set E)
  (hC_convex : Convex ℝ C)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  (StrictConvexOn ℝ C f ↔
  ∀ x₁ ∈ C, ∀ x₂ ∈ C, (x₁ ≠ x₂) →
  ∀ s ∈ directionalSubdifferential (liftRealtoEReal f) x₁,
  f x₂ > f x₁ + inner ℝ s (x₂ - x₁)) ∧
  (StrictConvexOn ℝ C f ↔
  IsStrictMonotone (fun x => {s | x ∈ C ∧ s ∈ directionalSubdifferential (liftRealtoEReal f) x})) := by
  sorry
