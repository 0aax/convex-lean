import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

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

theorem FCA_chap_D_4_4_2
  {J : Type*}
  [TopologicalSpace J]
  [CompactSpace J]
  [Nonempty J]
  [FirstCountableTopology J]
  (f : J → E → ℝ)
  (x : E)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ j, (f j z : EReal) < ⊤)
  (hf_usc : ∀ z j', UpperSemicontinuousAt (fun (j : J) => f j z) j') :
  let F : E → EReal := fun z => ⨆ j, (f j z : EReal)
  let active := {j | f j x = F x}
  convexHull ℝ (⋃ j ∈ active, directionalSubdifferential (liftRealtoEReal (f j)) x) =
    directionalSubdifferential F x := by
  sorry
