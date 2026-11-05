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

theorem FCA_chap_D_2_3_4 (f : E → ℝ)
    (x₁ x₂ : E)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    ∀ (s : ℝ → E),
    (∀ α ∈ Set.Icc (0 : ℝ) 1, s α ∈ directionalSubdifferential (liftRealtoEReal f) ((1 - α) • x₁ + α • x₂)) →
    IntervalIntegrable (fun α => inner ℝ (s α) (x₂ - x₁)) MeasureTheory.volume 0 1 ∧
    f x₂ - f x₁ = ∫ α in (0 : ℝ)..1, inner ℝ (s α) (x₂ - x₁) := by
  sorry
