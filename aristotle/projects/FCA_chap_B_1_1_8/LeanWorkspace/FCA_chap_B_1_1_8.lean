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

def probSimplex (k : ℕ) : Set (Fin k → ℝ) :=
  {v : Fin k → ℝ | (∀ i, 0 ≤ v i) ∧ (∑ i, v i = 1)}

theorem FCA_chap_B_1_1_8
  {n : ℕ}
  (k : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hC_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ (x : Fin k → EuclideanSpace ℝ (Fin n)), ∀ (α : EuclideanSpace ℝ (Fin k)),
  α.ofLp ∈ probSimplex k → (f (∑ i, (α i) • (x i))) ≤ ∑ i, ((α i) * (f (x i))) := by
  sorry
