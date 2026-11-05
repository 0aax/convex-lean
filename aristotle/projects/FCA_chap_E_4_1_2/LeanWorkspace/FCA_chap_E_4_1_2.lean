import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

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

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_4_1_2
  (f : E → EReal)
  (g : E → ℝ)
  (hf_closed_convex : InClosedConvRn f)
  (hg_eq : ∀ x ∈ interior (effDom f),
    (f x) = (g x : EReal))
  (hg_diff : DifferentiableOn ℝ g (interior (effDom f)))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let Ω := interior (effDom f)
  let gradImage := Set.image (gradient g) Ω
  ∀ (C : Set E),
  (C ⊆ gradImage) → (Convex ℝ C) →
  ∀ s₁ ∈ C, ∀ s₂ ∈ C, s₁ ≠ s₂ →
  ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
  (conjugate f (α • s₁ + (1 - α) • s₂)) <
  (α * (conjugate f s₁) + (1 - α) * (conjugate f s₂)) := by
  sorry
