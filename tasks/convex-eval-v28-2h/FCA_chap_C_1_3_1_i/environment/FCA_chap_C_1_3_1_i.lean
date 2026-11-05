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

theorem FCA_chap_C_1_3_1_i
  (σ₁ σ₂ : E → EReal)
  (t₁ t₂ : ℝ)
  (hσ : IsSublinear σ₁ ∧ IsSublinear σ₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  let σ := fun x => t₁ * (σ₁) x + t₂ * (σ₂) x
  (∃ x, σ x ≠ ⊤) →
  (IsSublinear σ) ∧
  ((LowerSemicontinuous σ₁ ∧ LowerSemicontinuous σ₂)
    → LowerSemicontinuous σ) := by
  sorry
