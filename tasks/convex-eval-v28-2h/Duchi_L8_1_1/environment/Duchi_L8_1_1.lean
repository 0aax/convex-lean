import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def BlowsUpOnBoundary {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ frontier 𝓧, ∀ M : ℝ, ∀ᶠ y in 𝓝[interior 𝓧] x, M ≤ F y

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

def HasPosDefHessianOn {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ x ∈ interior 𝓧, ∀ (h : EuclideanSpace ℝ (Fin n)), h ≠ 0 →
    0 < inner ℝ h ((hessianOperator f x) h)

noncomputable def jerkOperator {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n))
  : EuclideanSpace ℝ (Fin n) →L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  fderiv ℝ (fun y => hessianOperator f y) x

def IsSelfConcordant {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (M : ℝ) : Prop :=
  ConvexOn ℝ (interior 𝓧) f ∧
  ContDiffOn ℝ 3 f (interior 𝓧) ∧
  (∀ x ∈ interior 𝓧, ∀ h,
    |inner ℝ h (jerkOperator f x h h)| ≤ M * (localNorm f x h)^3) ∧
  (∀ y ∈ interior 𝓧, ∀ v ≠ 0,
    0 < inner ℝ v ((hessianOperator f y) v))

theorem Duchi_L8_1_1 {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_diff : ContDiffOn ℝ 3 f (interior 𝓧))
  (hf_sc : IsSelfConcordant 𝓧 f 2)
  (hf_strict_convex : HasPosDefHessianOn 𝓧 f)
  (hf_boundary : BlowsUpOnBoundary 𝓧 f)
  (h𝓧_int : Set.Nonempty (interior 𝓧))
  (hf_bdd_below : BddBelow (f '' interior 𝓧)) :
  ∃ x₀ ∈ interior 𝓧, IsMinOn f (interior 𝓧) x₀ := by
  sorry
