import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

noncomputable def imageFun {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (A : F →ₗ[ℝ] E)
  (g : F → EReal)
  (x : E) : EReal :=
  sInf (Set.image g {y : F | A y = x})

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_C_3_3_4
  (A : F →ₗ[ℝ] E)
  (S : Set F)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S) :
  let A_star := A.adjoint
  let σ := supportFunction S
  let A_adj_inv_S :=
    {p : E |
      ∃ d ∈ S, A_star p = d}
  let σ_adj_inv := supportFunction A_adj_inv_S
  A_adj_inv_S.Nonempty →
  (∀ (d : E),
    imageFun A σ d > ⊥) →
  (∀ (x : E),
    (σ_adj_inv x) =
    lscHull (imageFun A σ) x) := by
  sorry
