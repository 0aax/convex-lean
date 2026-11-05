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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

def horizonCone {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E) : Set E :=
  {x : E | ∃ (xseq : ℕ → E) (l : ℕ → ℝ),
    (∀ i, xseq i ∈ C) ∧
    (Filter.Tendsto l Filter.atTop (𝓝[>] 0)) ∧
    (Filter.Tendsto
      (fun i => (l i) • (xseq i))
      Filter.atTop
      (𝓝 x))}

noncomputable def asymptoticFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : E → EReal :=
  funFromSet (horizonCone (epigraph f))

theorem FCA_chap_B_3_2_6
  [Nontrivial E]
  (f : E → ℝ)
  (hf_closed_conv : InClosedConvRn (liftRealtoEReal f)) :
  let f'_infinity := asymptoticFun (liftRealtoEReal f)
  ((∃ L ≥ 0, ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖) ↔
    ∀ x, f'_infinity x < ⊤) ∧
  ((∃ L ≥ 0, ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖) →
    ((sInf {L : ℝ | 0 ≤ L ∧ ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖} : ℝ) : EReal) =
      sSup (f'_infinity '' Metric.sphere (0 : E) 1)) := by
  sorry
