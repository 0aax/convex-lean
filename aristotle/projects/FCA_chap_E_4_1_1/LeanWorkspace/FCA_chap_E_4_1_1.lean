import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

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

theorem FCA_chap_E_4_1_1
  (f : E → EReal)
  (hf_closed_convex : InClosedConvRn f)
  (hf_proper : ∃ x, f x < ⊤)
  (hf_strict : ∀ x y, x ≠ y → f x < ⊤ → f y < ⊤ →
    ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
    f (α • x + (1 - α) • y) < α * (f x) + (1 - α) * (f y))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let domConj := effDom ((conjugate f))
  Set.Nonempty (interior domConj)∧
  (∃ (g : E → ℝ),
  ((∀ s ∈ interior domConj, (conjugate f s) = (g s : EReal))) ∧
  (ContDiffOn ℝ 1 g (interior domConj))) := by
  sorry
