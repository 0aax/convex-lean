import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

noncomputable def infimalConv {E : Type*} [NormedAddCommGroup E]
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (x : E) : EReal
  := sInf {z : EReal | ∃ y : E,
  z = (f₁ y + f₂ (x - y))}

theorem FCA_chap_B_2_3_3
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (hf_convex : InConvRn f₁ ∧ InConvRn f₂)
  (h_common_affine_minorant : ∃ (s : E) (b : ℝ),
    (∀ x, f₁ x ≥ (inner ℝ s x) - b) ∧
    (∀ x, f₂ x ≥ (inner ℝ s x) - b)) :
  InConvRn (infimalConv f₁ f₂) := by
  sorry
