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

noncomputable def dualNorm {n : ℕ}
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {v | ∃ x, (N x ≤ 1) ∧ (v = inner ℝ g x)}

noncomputable def newtonStep {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  x - (hessianOperator f x).inverse (gradient f x)

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

def IsStandardSelfConcordantBarrier {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsSelfConcordant 𝓧 f 2 ∧ BlowsUpOnBoundary 𝓧 f

noncomputable def newtonDecrement {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dualNorm (localNorm f x) (gradient f x)

theorem newton_decrement_bound
  {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hx : x ∈ interior 𝓧)
  (h_dec : newtonDecrement f x ≤ 1 / 4)
  (hf : IsStandardSelfConcordantBarrier 𝓧 f) :
  newtonDecrement f (newtonStep f x)
    ≤ 2 * (newtonDecrement f x) ^ 2 := by
  sorry
