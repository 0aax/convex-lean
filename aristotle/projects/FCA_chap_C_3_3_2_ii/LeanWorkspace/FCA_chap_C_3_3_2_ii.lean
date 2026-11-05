import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_3_2_ii {ι : Type*}
  (S : ι → Set E)
  (J : Set ι)
  (hJ_nonempty : Set.Nonempty J)
  (hS_nonempty : ∀ j ∈ J, Set.Nonempty (S j))
  (hS_closed : ∀ j ∈ J, IsClosed (S j))
  (hS_convex : ∀ j ∈ J, Convex ℝ (S j)) :
  let σ := fun j => supportFunction (S j)
  let σ_sup := fun x => sSup (Set.image (fun j => σ j x) J)
  let S' := closure (convexHull ℝ (⋃ j ∈ J, S j))
  ∀ x, σ_sup x = supportFunction S' x := by
  sorry
