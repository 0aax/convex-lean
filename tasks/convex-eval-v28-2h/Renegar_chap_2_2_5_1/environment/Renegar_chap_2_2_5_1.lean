import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def hessianOperator {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ) (x : E)
  : E →L[ℝ] E :=
  fderiv ℝ (fun y => gradient f y) x

noncomputable def localInnerProd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x u v : E) : ℝ :=
  inner ℝ u (hessianOperator f x v)

noncomputable def localNorm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] (f : E → ℝ) (x v : E) : ℝ :=
  Real.sqrt (localInnerProd f x v v)

noncomputable def localBall {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  (f : E → ℝ)
  (x v : E) (r : ℝ) : Set E :=
  {y : E | localNorm f x (y - v) < r}

theorem Renegar_chap_2_2_5_1 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (hf_1 : ∀ x ∈ Df, localBall f x x 1 ⊆ Df ∧
    (∀ y ∈ localBall f x x 1, ∀ v ≠ 0,
      (localNorm f x v)⁻¹ * (localNorm f y v) ≤
      (1 - (localNorm f x (y - x)))⁻¹)) :
  ∀ x ∈ Df, localBall f x x 1 ⊆ Df ∧
    (∀ y ∈ localBall f x x 1, ∀ v ≠ 0,
    1 - (localNorm f x (y - x)) ≤ (localNorm f x v)⁻¹ * (localNorm f y v)) := by
  sorry
