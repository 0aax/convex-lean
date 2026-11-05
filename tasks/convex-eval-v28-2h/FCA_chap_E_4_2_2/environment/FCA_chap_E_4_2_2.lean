import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open InnerProductSpace Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_4_2_2
  (f : E → ℝ)
  (L : ℝ)
  (hL : L > 0)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lip_grad : ∀ (x₁ x₂ : E),
                 ‖gradient f x₁ - gradient f x₂‖ ≤ L * ‖x₁ - x₂‖) :
  (∀ (C : Set E),
  (C ⊆ effDom ((conjugate (liftRealtoEReal f)))) →
  (Convex ℝ C) →
  (∃ (g : E → ℝ),
  (∀ s ∈ C, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
  (StrongConvexOn C (1 / L) g)) ∧
  (∀ (x₁ x₂ : E),
  inner ℝ (gradient f x₁ - gradient f x₂) (x₁ - x₂) ≥
  (1 / L) * ‖gradient f x₁ - gradient f x₂‖ ^ 2)) := by
  sorry
