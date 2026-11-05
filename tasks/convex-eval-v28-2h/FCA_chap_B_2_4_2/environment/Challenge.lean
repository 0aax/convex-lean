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

noncomputable def imageFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (x : E) : EReal :=
  sInf (Set.image g {y : F | A y = x})

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem FCA_chap_B_2_4_2
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (hg_convex : InConvRn g)
  (hg_bounded : ∀ x, imageFun A g x > ⊥) :
  InConvRn (imageFun A g) := by
  sorry
