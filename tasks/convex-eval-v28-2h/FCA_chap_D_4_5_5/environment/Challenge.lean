import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

theorem FCA_chap_D_4_5_5
  (f₁ f₂ : E → ℝ)
  (y₁ y₂ : E)
  (hf_convex : ConvexOn ℝ Set.univ f₁ ∧ ConvexOn ℝ Set.univ f₂)
  (hf_minorized : ∃ (s : E) (b : ℝ),
                 ∀ x, (inner ℝ s x + b ≤ f₁ x) ∧ (inner ℝ s x + b ≤ f₂ x)) :
  let infconv := infimalConv (liftRealtoEReal f₁) (liftRealtoEReal f₂)
  (infconv (y₁ + y₂) = (f₁ y₁ + f₂ y₂ : EReal)) →
  directionalSubdifferential infconv (y₁ + y₂) =
  (directionalSubdifferential (liftRealtoEReal f₁) y₁) ∩ (directionalSubdifferential (liftRealtoEReal f₂) y₂) := by
  sorry
