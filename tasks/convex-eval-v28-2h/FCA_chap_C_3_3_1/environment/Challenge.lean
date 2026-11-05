import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_3_1
  (S₁ S₂ : Set E)
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂) :
  let σ₁ := supportFunction S₁
  let σ₂ := supportFunction S₂
  S₁ ⊆ S₂ ↔ ∀ d, σ₁ d ≤ σ₂ d := by
  sorry
