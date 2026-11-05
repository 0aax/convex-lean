import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

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

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

noncomputable def gaugeFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x : E) : EReal :=
  sInf {l : EReal | ∃ (l' : ℝ),
                        (l = (l' : EReal)) ∧
                        (l' > 0) ∧
                        (∃ y ∈ C, (x = l' • y))}

theorem FCA_chap_C_1_2_5
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let g : E → EReal := fun x => gaugeFun C x
  let rC : ℝ → Set E :=
    fun r => Set.image (fun x => r • x) C
  ((∀ x, g x ≥ 0) ∧ (IsSublinear g) ∧
    (LowerSemicontinuous g)) ∧
  ((∀ x, g x ≠ ⊤) ↔ (0 ∈ interior C)) ∧
  (∀ (r : ℝ), r > 0 → ({x | g x ≤ r} = rC r)) ∧
  (∀ (z : E),
    z ∈ C → {x | g x = 0} = asymptoticConeAt C z) := by
  sorry
