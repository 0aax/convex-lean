import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def idMap {E : Type*} (x : E) : Set E := {x}

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

def IsNonexpansive {E : Type*} [NormedAddCommGroup E]
  (S : E → Set E) : Prop :=
  ∀ (z₀ z₁ w₀ w₁ : E), w₀ ∈ S z₀ → w₁ ∈ S z₁ →
    ‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖

def subMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u - v}

theorem RW_chap_12_16
  (F : E → Set E)
  (hF : IsNonexpansive F)
  (hF_nonempty : ∀ x, (F x).Nonempty) :
  let D := subMap idMap F
  IsMaximalMonotone D := by
  sorry
