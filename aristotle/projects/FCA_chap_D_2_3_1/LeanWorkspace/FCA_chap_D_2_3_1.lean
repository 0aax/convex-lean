import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

def directionalSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E) : Set E :=
  let f' := fun (d : E) => directionalDeriv f x d
  {s : E | ∀ d, inner ℝ s d ≤ f' d}

theorem FCA_chap_D_2_3_1
  (f : E → ℝ)
  (x y : E) (t : ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) (ht : 0 ≤ t ∧ t ≤ 1) :
  let x' := fun (v : ℝ) => v • y + (1 - v) • x
  let phi := fun (v : EuclideanSpace ℝ (Fin 1)) => f (x' (v 0))
  let t_asvec : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 _).symm (fun _ => t)
  let subdiff := {v : ℝ | ∃ v' ∈ directionalSubdifferential (liftRealtoEReal phi) t_asvec, v' 0 = v}
  subdiff =
  {z : ℝ | ∃ s ∈ (directionalSubdifferential (liftRealtoEReal f) (x' t)), z = inner ℝ s (y - x)} := by
  sorry
