import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_1_3_1_iv
  (f : E → EReal)
  (A : E ≃ₗ[ℝ] E)
  (hf_nondegenerate : IsNondegenerate f) :
  let g := fun x => f (A x)
  let A_adjoint_inverse : (E →ₗ[ℝ] E) :=
                          (A.symm : E →ₗ[ℝ] E).adjoint
  ∀ s, conjugate g s = conjugate f (A_adjoint_inverse s) := by
  sorry
