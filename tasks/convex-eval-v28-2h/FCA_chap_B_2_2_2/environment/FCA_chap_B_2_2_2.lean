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

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def perspective {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) (u : ℝ) (x : E) : EReal :=
  if u > 0 then u * f (u⁻¹ • x) else ⊤

theorem FCA_chap_B_2_2_2
  (f : E → EReal)
  (x' : E)
  (hf_convex : InClosedConvRn f)
  (hx : x' ∈ intrinsicInterior ℝ (effDom f))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let pers : WithLp 2 (ℝ × E) → EReal := fun z => perspective f z.ofLp.1 z.ofLp.2
  let x : WithLp 2 (ℝ × E) := WithLp.toLp 2 (1, x')
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 < 0 → lscHull pers z = ⊤) ∧
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 > 0 →
    lscHull pers z = (z.ofLp.1 : EReal) * f ((z.ofLp.1)⁻¹ • z.ofLp.2)) ∧
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 ≥ 0 →
    Filter.Tendsto (fun (α : ℝ) => pers (z + α • (x - z)))
      (𝓝[>] 0) (𝓝 (lscHull pers z))) := by
  sorry
