import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsNormalToProd {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set (E × ℝ)) (x : E × ℝ) (s : E × ℝ) : Prop :=
  ∀ y ∈ C, inner ℝ s.1 (y.1 - x.1) + s.2 * (y.2 - x.2) ≤ 0

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

theorem FCA_chap_D_1_3_1
  (f : E → ℝ)
  (x s : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := directionalDeriv (liftRealtoEReal f) x
  let f'_epi := epigraph (fun d => f' d : E → EReal)
  let epi_f := epigraph (liftRealtoEReal f)
  let s' : E × ℝ := (s, -1)
  let x' : E × ℝ := (x, f x)
  (s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔ IsNormalToProd epi_f x' s') ∧
  (posTangentConeAt epi_f x' = f'_epi) := by
  sorry
