import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

noncomputable def setIndicator {E : Type*}
  (H : Set E)
  (x : E)
  : EReal := by
  classical
  exact if x ∈ H then 0 else ⊤

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

noncomputable def convexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (g : E → EReal) : E → EReal :=
  funFromSet (convexHull ℝ (epigraph g))

theorem FCA_chap_C_ex10
  [Nontrivial E]
  (f : E → EReal)
  (A : Set E)
  (hf_minorized : ∃ (s : E) (b : ℝ),
    ∀ x, (inner ℝ s x + b : ℝ) ≤ f x)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let fA := fun x => f x + setIndicator A x
  let clco_f := lscHull ((convexHullFun f))
  (closure (convexHull ℝ (epigraph fA)) ⊆
    {p | (p.1 ∈ closure (convexHull ℝ A)) ∧ (clco_f p.1 ≤ p.2)}) ∧
  (∃ (f' : E → EReal)
      (A' : Set E),
      (IsClosed A') ∧ (Convex ℝ A') ∧
      (∃ (s' : E) (b' : ℝ),
        ∀ x, (inner ℝ s' x + b' : ℝ) ≤ f' x) ∧
      let fA' := fun x => f' x + setIndicator A' x
      let clco_f' := lscHull ((convexHullFun f'))
      closure (convexHull ℝ (epigraph fA')) ≠
        {p | (p.1 ∈ closure (convexHull ℝ A')) ∧ (clco_f' p.1 ≤ p.2)}) ∧
  (∀ (a : E) (b : ℝ),
    let f_aff : E → EReal := fun x => (inner ℝ a x + b : ℝ)
    let fA_aff := fun x => f_aff x + setIndicator A x
    let clco_f_aff := lscHull ((convexHullFun f_aff))
    closure (convexHull ℝ (epigraph fA_aff)) =
      {p | (p.1 ∈ closure (convexHull ℝ A)) ∧ (clco_f_aff p.1 ≤ p.2)}) := by
  sorry
