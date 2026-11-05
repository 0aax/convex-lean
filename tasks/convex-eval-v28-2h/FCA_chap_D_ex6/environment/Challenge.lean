import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def hessianOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : E)
  : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

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

theorem FCA_chap_D_ex6
  (f : EuclideanSpace ℝ (Fin 2) → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hf_smooth : ContDiff ℝ 2 f)
  (hf_det : ∀ x, LinearMap.det (hessianOperator f x).toLinearMap = 1) :
  ∃ (A : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2))
  (b : EuclideanSpace ℝ (Fin 2)) (c : ℝ),
  (∀ x, hessianOperator f x = A) ∧
  (∀ x, f x = (1 / 2) * inner ℝ (A x) x + inner ℝ b x + c) := by
  sorry
