import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def singularValues {n : ℕ}
    (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
    Fin n → ℝ :=
  let T := ((ContinuousLinearMap.adjoint A).comp A)
  let h_sym : T.toLinearMap.IsSymmetric :=
    (ContinuousLinearMap.isPositive_adjoint_comp_self A).toLinearMap.isSymmetric
  fun i => Real.sqrt (h_sym.eigenvalues finrank_euclideanSpace_fin i)

theorem Duchi_Q2_3 {n : ℕ}
  (X Y : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
  (hX : X.toLinearMap.IsSymmetric) (hY : Y.toLinearMap.IsSymmetric) :
  let lamX : Fin n → ℝ := hX.eigenvalues finrank_euclideanSpace_fin
  let lamY : Fin n → ℝ := hY.eigenvalues finrank_euclideanSpace_fin
  (LinearMap.trace ℝ _ (X.toLinearMap.comp Y.toLinearMap) ≤ ∑ (i : Fin n), lamX i * lamY i) ∧
  (LinearMap.trace ℝ _ (X.toLinearMap.comp Y.toLinearMap) = ∑ (i : Fin n), lamX i * lamY i ↔
    ∃ U : OrthonormalBasis (Fin n) ℝ (EuclideanSpace ℝ (Fin n)),
      ∀ i, X (U i) = lamX i • U i ∧ Y (U i) = lamY i • U i) ∧
  (∀ (A B : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    abs (LinearMap.trace ℝ _ ((ContinuousLinearMap.adjoint A).toLinearMap.comp B.toLinearMap)) ≤
      ∑ (i : Fin n), singularValues A i * singularValues B i) := by
  sorry
