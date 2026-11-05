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

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def Minorizes {E : Type*}
  (f : E → EReal) (g : E → EReal) : Prop :=
  ∀ x, f x ≤ g x

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

noncomputable def convexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (g : E → EReal) : E → EReal :=
  funFromSet (convexHull ℝ (epigraph g))

theorem FCA_chap_B_2_5_1
  (g : E → EReal)
  (hg_nondegenerate : IsNondegenerate g)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  let f₁ := convexHullFun g
  let f₂ := fun x => sSup {z : EReal | ∃ (h : E → EReal),
                                          InConvRn h ∧ Minorizes h g ∧ z = h x}
  let f₃ := fun x => sInf (⋃ k, {z | ∃ (α : EuclideanSpace ℝ (Fin k))
                                    (x₀ : Fin k → E),
                                    α.ofLp ∈ probSimplex k ∧ (∀ j, x₀ j ∈ effDom g) ∧
                                    x = ∑ j, α j • x₀ j ∧
                                    z = ∑ j, ((α j : ℝ) : EReal) * g (x₀ j)})
  InConvRn f₁ ∧ InConvRn f₂ ∧ InConvRn f₃ ∧
    ∀ x, f₁ x = f₂ x ∧ f₂ x = f₃ x := by
  sorry
