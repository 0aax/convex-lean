import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

theorem FCA_chap_B_2_1_1
  {m : ℕ}
  (f : Fin m → (E → EReal))
  (t : Fin m → ℝ)
  (ht_positive : ∀ i, (t i) > 0)
  (hf_common_finite : ∃ x₀, ∀ i, (f i) x₀ < ⊤)
  (f_ne_bot : ∀ x₁ x₂, ⊥ < f x₁ x₂) :
  let g := fun x => ∑ i, (t i) * ((f i) x)
  ((∀ i, InConvRn ((f i))) → InConvRn g) ∧
  ((∀ i, InClosedConvRn ((f i))) → InClosedConvRn g) := by
  sorry
