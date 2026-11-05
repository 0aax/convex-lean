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

def InSubspaceSpanVec {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (m : ℕ)
  (x : ℕ → E)
  (x' : E) : Prop :=
  ∃ (z : ℕ → E),
  ∃ (s : ℕ → ℝ),
  (∀ i ∈ Finset.range m, ∃ j ∈ Finset.range m, z i = x j) ∧
  (x' = ∑ i ∈ Finset.range m, (s i) • (z i))

def IsLinearOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (𝓧 : Set E)
  (σ : E → EReal) : Prop :=
  (∀ (x₁ x₂ : E), ∀ (t₁ t₂ : ℝ),
  x₁ ∈ 𝓧 → x₂ ∈ 𝓧 → t₁ • x₁ + t₂ • x₂ ∈ 𝓧 →
  (σ (t₁ • x₁ + t₂ • x₂)) = t₁ * (σ x₁) + t₂ * (σ x₂))

theorem FCA_chap_C_1_1_6
  {m : ℕ}
  (σ : E → EReal)
  (x : ℕ → E)
  (hσ : IsSublinear σ)
  (h_eq_0 : ∀ j ∈ Finset.range m, σ (x j) + σ (-1 • (x j)) = 0)
  (hm : 0 < m) :
  let 𝓧 := {v | InSubspaceSpanVec m x v}
  (IsLinearOn 𝓧 σ) := by
  sorry
