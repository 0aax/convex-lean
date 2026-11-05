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

theorem FCA_chap_D_6_3_1
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let delta_set := {y | DifferentiableAt ℝ f y}
  let lim_set := fun x =>
    {s | ∃ (yk : ℕ → E),
      (∀ k, yk k ∈ delta_set) ∧
      (Filter.Tendsto yk Filter.atTop (𝓝 x)) ∧
      (Filter.Tendsto (fun k => gradient f (yk k))
        Filter.atTop (𝓝 s))}
  ∀ (x : E),
  directionalSubdifferential (liftRealtoEReal f) x =
    convexHull ℝ (lim_set x) := by
  sorry
