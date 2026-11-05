import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def sublevelSet {E : Type*}
  (r : ℝ) (f : E → EReal) :
  Set E :=
  {x : E | f x ≤ r}

def IsLevelBounded {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded (sublevelSet α f)

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

noncomputable def IsOneCoerciveFun {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ C : ℝ, ∀ᶠ x in Filter.comap norm Filter.atTop, (C : EReal) ≤ (norm x)⁻¹ * (f x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_1_3_9
  (f : E → EReal)
  (x₀ : E)
  (hf_nondegenerate : IsNondegenerate f)
  (hf_convex : InConvRn f) :
  (x₀ ∈ interior (effDom f) →
  IsLevelBounded (fun x => conjugate f x - inner ℝ x₀ x)) ∧
  ((∀ x, f x ≠ ⊤) → IsOneCoerciveFun (conjugate f)) := by
  sorry
