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

theorem FCA_chap_B_3_1_1
  (f : E → EReal)
  (x₀ : E)
  (δ m M : ℝ)
  (hf_convex : InConvRn f)
  (hf_bound : ∀ x ∈ Metric.ball x₀ (2 * δ), (m : EReal) ≤ f x ∧ f x ≤ M) :
  ∀ y ∈ Metric.ball x₀ δ, ∀ y' ∈ Metric.ball x₀ δ,
  |(f y).toReal - (f y').toReal| ≤ ((M - m) / δ) * ‖y - y'‖ := by
  sorry
