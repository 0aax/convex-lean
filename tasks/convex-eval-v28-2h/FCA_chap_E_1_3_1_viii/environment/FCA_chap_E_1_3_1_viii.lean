import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def Minorizes {E : Type*}
  (f : E → EReal) (g : E → EReal) : Prop :=
  ∀ x, f x ≤ g x

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_1_3_1_viii
  (f₁ : E → EReal) (f₂ : E → EReal) (α : ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂) :
  Set.Nonempty (effDom f₁ ∩ effDom f₂) →
  α ∈ Set.Ioo 0 1 →
  Minorizes
    (conjugate (fun x => α * (f₁) x + (1 - α) * (f₂) x))
    (fun s => α * conjugate f₁ s
              + (1 - α) * conjugate f₂ s) := by
  sorry
