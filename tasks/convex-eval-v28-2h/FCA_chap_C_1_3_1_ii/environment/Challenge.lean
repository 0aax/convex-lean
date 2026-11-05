import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

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

def IsERealPosHomogeneous {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∀ (x : E), ∀ (t : ℝ),
  t > 0 → f (t • x) = t * (f x)

def IsSublinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (σ : E → EReal) : Prop :=
  (InConvRn σ) ∧ IsERealPosHomogeneous σ

theorem FCA_chap_C_1_3_1_ii
  {ι : Type*}
  (σ : ι → (E → EReal))
  (J : Set ι)
  (hJ : J.Nonempty)
  (hσ_sublinear : ∀ j ∈ J, IsSublinear ((σ j))) :
  let σ' := fun x => sSup (⋃ j ∈ J, {(σ j) x})
  (∃ x, σ' x ≠ ⊤) →
  (IsSublinear σ') ∧
  ((∀ j ∈ J, LowerSemicontinuous (σ j)) → (LowerSemicontinuous σ')) := by
  sorry
