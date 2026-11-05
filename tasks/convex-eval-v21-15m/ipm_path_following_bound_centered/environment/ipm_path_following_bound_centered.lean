import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def ft {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : EuclideanSpace ℝ (Fin n))
  (a : ℝ) : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => a * inner ℝ c x + F x

noncomputable def dualNorm {n : ℕ}
  (N : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n)) : ℝ :=
  sSup {v | ∃ x, (N x ≤ 1) ∧ (v = inner ℝ g x)}

def sublevelSet {E : Type*}
  (r : ℝ) (f : E → EReal) :
  Set E :=
  {x : E | f x ≤ r}

def IsLevelBounded {E : Type*} [NormedAddCommGroup E]
  (f : E → EReal) : Prop :=
  ∀ α : ℝ, Bornology.IsBounded (sublevelSet α f)

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

def IsNuSelfConcordantBarrier {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ) (ν : ℝ) : Prop :=
  1 ≤ ν ∧
  IsSelfConcordant 𝓧 F 2 ∧
  ConcaveOn ℝ (interior 𝓧) (fun x => Real.exp ((-1 / ν) * (F x))) ∧
  BlowsUpOnBoundary 𝓧 F

noncomputable def newtonDecrement {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  dualNorm (localNorm f x) (gradient f x)

noncomputable def setIndicator {E : Type*}
  (H : Set E)
  (x : E)
  : EReal := by
  classical
  exact if x ∈ H then 0 else ⊤

def LevelBoundedOn {n : ℕ}
  (S : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  IsLevelBounded (fun x => liftRealtoEReal f x + setIndicator S x)

noncomputable def pathFollowingStep {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t ν : ℝ) (x c : EuclideanSpace ℝ (Fin n))
  : ℝ × EuclideanSpace ℝ (Fin n) :=
  let t_next := (1 + 1 / (13 * Real.sqrt ν)) * t
  let x_next := x - (hessianOperator F x).inverse (t_next • c + gradient F x)
  (t_next, x_next)

noncomputable def xCentered {n : ℕ}
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t : ℕ → ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (ν : ℝ)
  (c : EuclideanSpace ℝ (Fin n)) : ℕ → EuclideanSpace ℝ (Fin n)
| 0 => newtonStep (ft F c (t 0)) x0
| k + 1 => (pathFollowingStep F (t k) ν (xCentered F t x0 ν c k) c).2

theorem ipm_path_following_bound_centered
  {n k : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t : ℕ → ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (ν : ℝ)
  (c : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0_mem : x0 ∈ interior 𝓧)
  (h_dec0 : newtonDecrement (ft F c (t 0)) x0 ≤ 1 / 4)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn (fun x => inner ℝ c x) 𝓧 x_star)
  (ht_pos : ∀ j, 0 < t j)
  (ht_rec : ∀ j, t (j + 1) =
    (1 + 1 / (13 * Real.sqrt ν)) * t j)
  (h𝓧_closed : IsClosed 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_frontier_nonempty : Set.Nonempty (frontier 𝓧))
  (hF : IsNuSelfConcordantBarrier 𝓧 F ν)
  (hFt_levelBounded :
    ∀ a > 0, LevelBoundedOn (interior 𝓧) (ft F c a))
  (hxC_mem : ∀ j, xCentered F t x0 ν c j ∈ interior 𝓧) :
  inner ℝ c (xCentered F t x0 ν c k) - inner ℝ c x_star
  ≤ (2 * ν) / (t 0) *
    Real.exp (-(↑k : ℝ) / (1 + 13 * Real.sqrt ν)) := by
  sorry
