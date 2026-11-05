import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

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

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

theorem FCA_chap_D_ex12
  (f : EuclideanSpace ℝ (Fin 1) → ℝ)
  (g : EuclideanSpace ℝ (Fin 1) → ℝ)
  (h_convex : (InConvRn (liftRealtoEReal f)) ∧ (InConvRn (liftRealtoEReal g)))
  (h_pos : ∀ x, (f x > 0) ∧ (g x > 0))
  (hf_increasing : ∀ x y, (x 0 < y 0) → (f x < f y))
  (hg_increasing : ∀ x y, (x 0 < y 0) → (g x < g y)) :
  let fg := fun x => (f x) * (g x)
  (InConvRn (liftRealtoEReal fg)) ∧ (∀ x y, (x 0 < y 0) → (fg x < fg y)) ∧
  (∀ x, directionalSubdifferential (liftRealtoEReal fg) x =
  setAdd ({v : EuclideanSpace ℝ (Fin 1) | ∃ y ∈ directionalSubdifferential (liftRealtoEReal g) x, v 0 = ((f x) * (y 0))})
          ({v : EuclideanSpace ℝ (Fin 1) | ∃ y ∈ directionalSubdifferential (liftRealtoEReal f) x, v 0 = ((g x) * (y 0))})) := by
  sorry
