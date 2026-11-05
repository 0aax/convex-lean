import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsLocallyBoundedAt {E : Type*} [NormedAddCommGroup E]
  (T : E → Set E)
  (x_bar : E) : Prop :=
  ∃ U ∈ 𝓝 x_bar, ∃ R > (0 : ℝ),
    ∀ x ∈ U, ∀ v ∈ T x, ‖v‖ ≤ R

def IsMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsMaximalMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  IsMonotone T ∧
  ∀ (x_hat v_hat : E),
    v_hat ∉ T x_hat →
    ∃ (x_tilde v_tilde : E),
      v_tilde ∈ T x_tilde ∧
      inner ℝ (v_hat - v_tilde) (x_hat - x_tilde) < 0

theorem RW_chap_12_38
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let domT : Set E := {x | (T x).Nonempty}
  let D : Set E := closure domT
  (∀ x_bar, IsLocallyBoundedAt T x_bar ↔ x_bar ∉ frontier D) ∧
  (∀ x_bar, x_bar ∈ domT →
    (IsLocallyBoundedAt T x_bar ↔ Bornology.IsBounded (T x_bar))) := by
  sorry
