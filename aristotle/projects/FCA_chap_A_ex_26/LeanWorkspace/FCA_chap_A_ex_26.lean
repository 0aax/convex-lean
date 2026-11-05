import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


noncomputable def onesVec (n : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ i : Fin n, EuclideanSpace.single i 1

def doublyStochasticSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A | A (onesVec n) = onesVec n ∧
    ∀ j : Fin n, ∑ i : Fin n, (A (EuclideanSpace.single j 1)) i = 1}

def birkhoffPolytope (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A ∈ doublyStochasticSet n |
    ∀ i j : Fin n, (A (EuclideanSpace.single j 1)) i ≥ 0}

theorem FCA_chap_A_ex_26 :
  (∀ {n m : ℕ} (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin m))
    (b : EuclideanSpace ℝ (Fin m)),
    let P := {x : EuclideanSpace ℝ (Fin n) | A x = b ∧ ∀ i, x i ≥ 0}
    ∀ x ∈ P, x ≠ 0 →
      (x ∈ Set.extremePoints ℝ P ↔
        LinearIndependent ℝ (fun i : {i : Fin n // x i > 0} =>
          A (EuclideanSpace.single i.val 1)))) ∧
  (∀ {n : ℕ},
    IsCompact (birkhoffPolytope n) ∧ Convex ℝ (birkhoffPolytope n) ∧
    Set.extremePoints ℝ (birkhoffPolytope n) =
      {A | ∃ σ : Equiv.Perm (Fin n),
        ∀ j, A (EuclideanSpace.single j 1) = EuclideanSpace.single (σ j) 1}) := by
  sorry
