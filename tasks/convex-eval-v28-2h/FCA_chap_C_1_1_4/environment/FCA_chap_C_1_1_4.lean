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

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

def IsSubadditive {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ (x₁ : E), ∀ (x₂ : E),
  f (x₁ + x₂) ≤ (f x₁) + (f x₂)

theorem FCA_chap_C_1_1_4
  (σ : E → EReal)
  (hσ : ∃ x, σ x ≠ ⊤)
  (hσbot : ∀ x, σ x ≠ ⊥) :
  (IsSublinear σ) ↔
  ((IsERealPosHomogeneous σ) ∧ (IsSubadditive σ)) := by
  sorry
