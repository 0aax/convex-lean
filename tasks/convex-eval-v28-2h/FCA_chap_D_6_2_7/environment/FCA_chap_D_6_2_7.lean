import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

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

theorem FCA_chap_D_6_2_7
  (fk : ℕ → (E → ℝ))
  (xk : ℕ → E)
  (f : E → ℝ)
  (x : E)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
  (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v)))
  (hx_limit : Filter.Tendsto xk Filter.atTop (𝓝 x)) :
  let subdiff_neighborhood := fun (eps : ℝ) =>
                              {v | ∃ w d, (‖d‖ ≤ eps) ∧
                              (w ∈ directionalSubdifferential (liftRealtoEReal f) x) ∧ (v = w + d)}
  ∀ eps > 0, ∃ (K : ℕ), ∀ k ≥ K,
  directionalSubdifferential (liftRealtoEReal (fk k)) (xk k) ⊆ subdiff_neighborhood eps := by
  sorry
