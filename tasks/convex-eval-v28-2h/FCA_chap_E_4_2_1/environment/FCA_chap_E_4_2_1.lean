import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter Metric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_4_2_1
  (f : E → ℝ)
  (c : ℝ)
  (hc : c > 0)
  (hf_strong : StrongConvexOn Set.univ c f) :
  (∀ s, conjugate (liftRealtoEReal f) s < ⊤) ∧
  (∃ (g : E → ℝ),
  (∀ s, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
  (Differentiable ℝ g) ∧
  (∀ s₁ s₂, ‖gradient g s₁ - gradient g s₂‖ ≤ (1 / c) * ‖s₁ - s₂‖)) := by
  sorry
