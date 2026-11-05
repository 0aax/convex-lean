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

noncomputable def verticalSlice {E : Type*}
  (S : Set (E × ℝ)) (x : E) : Set ℝ :=
  {r : ℝ | (x, r) ∈ S}

noncomputable def funFromSet {E : Type*} (S : Set (E × ℝ)) : E → EReal :=
  fun x => sInf (((fun r : ℝ => (r : EReal)) '' verticalSlice S x))

def IsMinorizedAt {E : Type*}
  (C : Set (E × ℝ)) (x : E) : Prop :=
  let K := {r : ℝ | ∃ (z : E × ℝ), (z ∈ C) ∧ (x = z.1) ∧ (r = z.2)}
  ∃ (k₀ : ℝ), ∀ r ∈ K, r ≥ k₀

omit [FiniteDimensional ℝ E] in
theorem FCA_chap_B_1_3_1
  (C : Set (E × ℝ))
  (hC_nonempty : Nonempty C)
  (hC_minorized : ∀ x, IsMinorizedAt C x) :
  (Convex ℝ C → InConvRn (funFromSet C)) ∧
  (Convex ℝ C ∧ IsClosed C → InClosedConvRn (funFromSet C)) := by
  sorry
