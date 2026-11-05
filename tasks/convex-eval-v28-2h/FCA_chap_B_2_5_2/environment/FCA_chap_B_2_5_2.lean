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

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

noncomputable def closedConvexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : E → EReal :=
  funFromSet (closure (convexHull ℝ (epigraph h)))

noncomputable def convexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (g : E → EReal) : E → EReal :=
  funFromSet (convexHull ℝ (epigraph g))

theorem FCA_chap_B_2_5_2
  (g : E → EReal)
  (hg_nondegenerate : IsNondegenerate g)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  let f₁ := closedConvexHullFun g
  let f₂ := fun x => sSup {z : EReal |
    ∃ (h : E → EReal),
      InClosedConvRn h ∧ Minorizes h g ∧ z = h x}
  let f₃ := fun x => sSup {z : EReal |
    ∃ (s : E) (b : ℝ),
      (∀ y, inner ℝ s y - b ≤ g y) ∧ z = inner ℝ s x - b}
  (InClosedConvRn f₁) ∧ (InClosedConvRn f₂) ∧
  (InClosedConvRn f₃) ∧
  (∀ x, (f₁ x = f₂ x) ∧ (f₂ x = f₃ x)) ∧
  (∀ x, f₁ x = lscHull (convexHullFun g) x) := by
  sorry
