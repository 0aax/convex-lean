import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_2_2_4
  [FiniteDimensional ℝ E]
  (S : Set E)
  (x : E)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S)
  (hx : x ∈ S) :
  let σS := supportFunction S
  let Sinfty := asymptoticConeAt S x
  (polarCone (closure (effDom σS)) = Sinfty) ∧
  (closure (effDom σS) = polarCone Sinfty) := by
  sorry
