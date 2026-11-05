import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

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

theorem FCA_chap_B_3_2_8_iii
  (f : F → EReal)
  (A₀ : E →ₗ[ℝ] F)
  (b : F)
  (hf_closed_conv : InClosedConvRn f)
  (h_dom_nonempty : Set.Nonempty
    (effDom f ∩ Set.image (fun x ↦ A₀ x + b) Set.univ))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let fA := fun v ↦ f (A₀ v + b)
  let fA'_infinity := asymptoticFun fA
  ∀ d,
    asymptoticFun f (A₀ d) = fA'_infinity d := by
  sorry
