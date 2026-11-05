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

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

theorem FCA_chap_E_ex4
  (G : Set E)
  (f g : E → EReal)
  (hf_closed_convex : InClosedConvRn f)
  (hri_subset : intrinsicInterior ℝ (effDom f) ⊆ G)
  (hG_subset : G ⊆ effDom f)
  (hfg : ∀ (x : E), f x ≤ g x)
  (h_eq_on_ri : ∀ (x : E),
    x ∈ intrinsicInterior ℝ (effDom f) →
    g x = f x)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (sInf (Set.image g G)) = (sInf (Set.image g Set.univ)) ∧
  (sInf (Set.image g Set.univ)) = (sInf (Set.image f Set.univ)) := by
  sorry
