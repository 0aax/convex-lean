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

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

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

theorem FCA_chap_B_2_5_4
  {n m : ℕ}
  (g : ℕ → (E → EReal))
  (hg_convex : ∀ i, i < m → InConvRn (g i))
  (hg_minorized : ∃ (s : E) (b : ℝ),
    ∀ i, i < m → ∀ x, inner ℝ s x + b ≤ g i x)
  (g_ne_bot : ∀ x₁ x₂, ⊥ < g x₁ x₂) :
  let g' := convexHullFun
    (fun x => sInf (⋃ j ∈ Finset.range m, {g j x}))
  let g_combo := fun x => sInf {v |
    ∃ α ∈ probSimplex m,
      ∃ (x' : ℕ → E),
        (∀ j < m, x' j ∈ effDom ((g j))) ∧
        (x = ∑ j, (α j) • (x' j)) ∧
        (v = ∑ j, (α j) * (g j (x' j)))}
  ∀ x, g' x = g_combo x := by
  sorry
