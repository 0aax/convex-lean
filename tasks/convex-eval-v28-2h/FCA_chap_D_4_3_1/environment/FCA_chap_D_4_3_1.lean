import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

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

theorem FCA_chap_D_4_3_1
    (f : ι → E → ℝ)
    (g : EuclideanSpace ℝ ι → ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_increasing : ∀ y z : EuclideanSpace ℝ ι, (∀ i, y i ≥ z i) → g y ≥ g z) :
    let F_fun : E → EuclideanSpace ℝ ι := fun x => (WithLp.equiv 2 _).symm (fun i => f i x)
    ∀ (x : E),
      directionalSubdifferential (liftRealtoEReal (g ∘ F_fun)) x =
      {v | ∃ ρ ∈ directionalSubdifferential (liftRealtoEReal g) (F_fun x),
          ∃ s : ι → E,
            (∀ i, s i ∈ directionalSubdifferential (liftRealtoEReal (f i)) x) ∧
            v = ∑ i, (ρ i) • s i} := by
  sorry
