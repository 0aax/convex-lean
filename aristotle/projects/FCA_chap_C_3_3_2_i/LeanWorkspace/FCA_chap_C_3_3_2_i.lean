import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_3_2_i
  (S₁ S₂ : Set E)
  (t₁ t₂ : ℝ)
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  let σ₁ := supportFunction S₁
  let σ₂ := supportFunction S₂
  let S₁' := {x | ∃ s ∈ S₁, x = t₁ • s}
  let S₂' := {x | ∃ s ∈ S₂, x = t₂ • s}
  let S := closure {x | ∃ s₁ ∈ S₁', ∃ s₂ ∈ S₂', x = s₁ + s₂}
  ∀ x, (t₁ * (σ₁ x) + t₂ * (σ₂ x)) = (supportFunction S x) := by
  sorry
