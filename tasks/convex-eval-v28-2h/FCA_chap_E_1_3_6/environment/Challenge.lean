import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
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

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def Minorizes {E : Type*}
  (f : E → EReal) (g : E → EReal) : Prop :=
  ∀ x, f x ≤ g x

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def biconjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (u : E) : EReal :=
  conjugate (conjugate f) u

theorem FCA_chap_E_1_3_6
  (f : E → EReal)
  (g : E → EReal)
  (hf_nondegenerate : IsNondegenerate f)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (((Minorizes (biconjugate f) g) ∧ (Minorizes g f)) → (∀ s, conjugate g s = conjugate f s)) ∧
  ((biconjugate f = f) ↔ (InClosedConvRn f)) := by
  sorry
