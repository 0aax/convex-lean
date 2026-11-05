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

noncomputable def marginalFun {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → EReal)
  (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  let g_concat : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → EReal := fun a b
  => g ((WithLp.equiv 2 _).symm (Fin.append (α := ℝ) a.ofLp b.ofLp))
  sInf (Set.range (g_concat x))

theorem FCA_chap_B_2_4_5
  {n m : ℕ}
  (g : EuclideanSpace ℝ (Fin (n + m)) → EReal)
  (hg_convex : InConvRn g)
  (hg_bounded : ∀ (x : EuclideanSpace ℝ (Fin n)), marginalFun g x > ⊥) :
  InConvRn (marginalFun g) := by
  sorry
