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

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def valueFun {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → EReal)
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → EReal))
  (x : EuclideanSpace ℝ (Fin n)) : EReal :=
  sInf (Set.image phi {u | ∀ j, (c j) u ≤ x j})

set_option maxHeartbeats 800000 in
theorem FCA_chap_B_2_4_3
  {p n : ℕ}
  (phi : EuclideanSpace ℝ (Fin p) → EReal)
  (c : (Fin n) → (EuclideanSpace ℝ (Fin p) → EReal))
  (h_phi_convex : InConvRn phi)
  (hc_convex : ∀ j, InConvRn (c j))
  (h_nonempty_dom : Set.Nonempty (effDom phi ∩ (⋂ j, effDom (c j))))
  (h_noninf_val : ∀ x, (valueFun phi c x) > ⊥) :
  InConvRn (valueFun phi c) := by
  sorry
