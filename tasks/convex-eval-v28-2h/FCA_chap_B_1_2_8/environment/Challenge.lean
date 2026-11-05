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

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

def affineMinorantValuesE {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal)
    (x : E) : Set EReal :=
  {v : EReal | ∃ (z : E × ℝ),
    (v = (inner ℝ z.1 x - z.2 : ℝ)) ∧ (∀ y, (inner ℝ z.1 y) - z.2 ≤ f y)}

theorem FCA_chap_B_1_2_8
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let cl_f := lscHull f
  ∀ x, cl_f x = sSup (affineMinorantValuesE f x) := by
  sorry
