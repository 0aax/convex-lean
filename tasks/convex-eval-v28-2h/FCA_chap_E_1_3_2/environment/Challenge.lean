import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

noncomputable def setIndicator {E : Type*}
  (H : Set E)
  (x : E)
  : EReal := by
  classical
  exact if x ∈ H then 0 else ⊤

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_1_3_2
  (f : E → EReal)
  (H : Subspace ℝ E)
  (hf_nondegenerate : IsNondegenerate f ∧ ∃ (x : E), x ∈ H ∧ f x ≠ ⊤) :
  let pH : E → E :=
  fun x => Submodule.orthogonalProjection H x
  let g := fun x => f x + (setIndicator (H : Set E)) x
  IsNondegenerate g ∧
  ∀ (s : E), conjugate g s = conjugate (f ∘ pH) (pH s) := by
  sorry
