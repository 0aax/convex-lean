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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

theorem FCA_chap_B_3_1_4
  (fk : ℕ → E → ℝ)
  (f : E → ℝ)
  (hfk_convex : ∀ k, InConvRn (liftRealtoEReal (fk k)))
  (hfk_pointwise : ∀ x, Filter.Tendsto (fun k ↦ fk k x) Filter.atTop (𝓝 (f x))) :
  InConvRn (liftRealtoEReal f) ∧
  ∀ (S : Set E), IsCompact S → TendstoUniformlyOn fk f Filter.atTop S := by
  sorry
