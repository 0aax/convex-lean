import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

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

theorem FCA_chap_D_4_4_4
  {J : Type*}
  [TopologicalSpace J]
  [CompactSpace J]
  [Nonempty J]
  [FirstCountableTopology J]
  (f : J → (E → ℝ))
  (x : E)
  (hf_convex : ∀ (i : J), ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ (j : J), (f j z : EReal) < ⊤)
  (hf_usc : ∀ z, ∀ j', UpperSemicontinuousAt (fun (j : J) => f j z) j')
  (hf_differentiable : ∀ (j : J), Differentiable ℝ (f j)) :
  let F_fun : E → EReal := fun z => ⨆ (j : J), (f j z)
  let Jx := {j | f j x = F_fun x}
  directionalSubdifferential F_fun x = convexHull ℝ (⋃ j ∈ Jx, {gradient (f j) x}) := by
  sorry
