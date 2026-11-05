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

theorem FCA_chap_D_4_5_1 (g : F → ℝ)
    (A : F →ₗ[ℝ] E)
    (x : E)
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_bounded : BddBelow (Set.image g {y | A y = x}))
    (hA_surjective : Function.Surjective A) :
    let Ag := fun x => sInf (Set.image g {y | A y = x})
    let Yx := {y | (A y = x) ∧ (g y = Ag x)}
    (Set.Nonempty Yx) → ∀ y ∈ Yx,
    (directionalSubdifferential (liftRealtoEReal Ag) x =
    {s | A.adjoint s ∈ directionalSubdifferential (liftRealtoEReal g) y}) ∧
    (directionalSubdifferential (liftRealtoEReal Ag) x =
    Set.preimage A.adjoint (directionalSubdifferential (liftRealtoEReal g) y)) := by
  sorry
