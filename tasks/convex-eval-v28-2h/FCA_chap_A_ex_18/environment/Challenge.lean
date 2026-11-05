import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def asymptoticConeAt {E : Type*} [AddCommGroup E] [Module ℝ E]
  (C : Set E)
  (x : E) : Set E :=
  {d | ∀ (t : ℝ), t > 0 → x + t • d ∈ C}

theorem FCA_chap_A_ex_18 :
  (∀ (C : Set E) (A : E →L[ℝ] F),
    C.Nonempty → IsClosed C → Convex ℝ C →
    (∀ x₀ ∈ C, asymptoticConeAt C x₀ ∩ (LinearMap.ker A.toLinearMap : Set _) = {0}) →
    IsClosed (A '' C)) ∧
  (∀ (C : Set E) (V : Submodule ℝ E) [CompleteSpace V],
    C.Nonempty → IsClosed C → Convex ℝ C →
    (∀ x₀ ∈ C, asymptoticConeAt C x₀ ∩ (V.orthogonal : Set _) = {0}) →
    IsClosed ((fun x ↦ (V.orthogonalProjection x : E)) '' C)) := by
  sorry
