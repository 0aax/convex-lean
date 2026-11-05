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

theorem FCA_chap_B_3_2_8_i
  {n m : ℕ}
  (fm : ℕ → (E → EReal))
  (t : ℕ → ℝ)
  (x₀ : ℕ → E)
  (hf_closed_conv : ∀ i ∈ Finset.range m, InClosedConvRn (fm i))
  (hf_finite : ∀ i ∈ Finset.range m, fm i (x₀ i) < ⊤)
  (ht_pos : ∀ i ∈ Finset.range m, t i > 0)
  (fm_ne_bot : ∀ x₁ x₂, ⊥ < fm x₁ x₂) :
  let f := fun v => ∑ i ∈ Finset.range m, (t i) * (fm i v)
  let f'_sum_infinity := fun d =>
    ∑ i ∈ Finset.range m, asymptoticFun (fun v => (t i) * (fm i v)) d
  (effDom f).Nonempty → ∀ d,
  asymptoticFun f d = f'_sum_infinity d := by
  sorry
