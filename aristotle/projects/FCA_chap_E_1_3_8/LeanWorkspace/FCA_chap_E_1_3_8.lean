import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

noncomputable def IsOneCoerciveFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ C : ℝ, ∀ᶠ x in Filter.comap norm Filter.atTop, (C : EReal) ≤ (norm x)⁻¹ * (f x)

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_1_3_8
  (f : E → EReal)
  (hf_nondegenerate : IsNondegenerate f) (hf_coercive : IsOneCoerciveFun f) :
  ∀ s, conjugate f s < ⊤ := by
  sorry
