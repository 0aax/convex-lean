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

def convexSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  {s | ∀ y, f y ≥ f x + inner ℝ s (y - x)}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_ex15
  (f g : E → EReal)
  (hf : InClosedConvRn f)
  (hg : InClosedConvRn g)
  (hf_proper : (effDom f).Nonempty)
  (hg_proper : (effDom g).Nonempty)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (∀ (s : E),
    (conjugate f s + conjugate g (-s) ≤ 0) ↔
    (∃ (r : ℝ), ∀ x, (r + inner ℝ s x ≤ f x) ∧
                      ((r + inner ℝ s x) ≥ -1 * (g x)))) ∧
  (∀ (x' : E),
    ((f x') = -1 * (g x')) →
    {s | conjugate f s + conjugate g (-s) ≤ 0} =
      (convexSubdifferential f x') ∩
      {s | -s ∈ convexSubdifferential g x'}) := by
  sorry
