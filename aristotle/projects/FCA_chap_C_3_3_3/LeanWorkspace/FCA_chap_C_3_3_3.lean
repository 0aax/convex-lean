import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_3_3
  (A : E →ₗ[ℝ] F)
  (S : Set E)
  (hS_nonempty : Set.Nonempty S) :
  let A_adj := A.adjoint
  let cl_AS := closure (Set.image A S)
  let σ_clAS := supportFunction cl_AS
  let σ_S_Aadj := fun y => supportFunction S (A_adj y)
  ∀ (y : F), σ_clAS y = σ_S_Aadj y := by
  sorry
