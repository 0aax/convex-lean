import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

def IsSublinearRW {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (0 ∈ effDom f ∧ IsERealPosHomogeneous f) ∧
  ConvexEReal f

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

noncomputable def closedConvexHullFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : E → EReal :=
  funFromSet (closure (convexHull ℝ (epigraph h)))

def horizonCone {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E) : Set E :=
  {x : E | ∃ (xseq : ℕ → E) (l : ℕ → ℝ),
    (∀ i, xseq i ∈ C) ∧
    (Filter.Tendsto l Filter.atTop (𝓝[>] 0)) ∧
    (Filter.Tendsto
      (fun i => (l i) • (xseq i))
      Filter.atTop
      (𝓝 x))}

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

def supportSublevelSet {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (h : E → EReal) : Set E :=
  {v : E | ∀ (w : E), (((inner ℝ v w) : ℝ) : EReal) ≤ h w}

theorem RW_chap_8_24
  (D : Set E)
  (h : E → EReal) :
  (IsSublinearRW (supportFunction D) ∧
    LowerSemicontinuous (supportFunction D) ∧
    (D.Nonempty → IsProper (supportFunction D)) ∧
    closure (convexHull ℝ D) =
      supportSublevelSet (supportFunction D)) ∧
  ((0 ∈ effDom h ∧ IsERealPosHomogeneous h) →
    let D' := supportSublevelSet h
    IsClosed D' ∧
    Convex ℝ D' ∧
    (D'.Nonempty → ∀ (w : E), supportFunction D' w = closedConvexHullFun h w) ∧
    (D' = ∅ →
      ¬ IsProper (closedConvexHullFun h) ∧
      ∀ (w : E), closedConvexHullFun h w = ⊥ ∨ closedConvexHullFun h w = ⊤)) ∧
  ((D.Nonempty ∧ IsClosed D ∧ Convex ℝ D) →
    IsProper (supportFunction D) ∧
    LowerSemicontinuous (supportFunction D) ∧
    IsSublinearRW (supportFunction D) ∧
    supportSublevelSet (supportFunction D) = D) ∧
  ((IsProper h ∧ LowerSemicontinuous h ∧ IsSublinearRW h) →
    let D' := supportSublevelSet h
    D'.Nonempty ∧
    IsClosed D' ∧
    Convex ℝ D' ∧
    (∀ (w : E), h w = supportFunction D' w) ∧
    (polarCone (horizonCone D') = closure (effDom h))) := by
  sorry
