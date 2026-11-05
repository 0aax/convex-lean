import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def corrSet (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A | A.IsPositive ∧
    ∀ i : Fin n, inner ℝ (A (EuclideanSpace.single i (1:ℝ))) (EuclideanSpace.single i (1:ℝ)) = 1}

def corrFV (n : ℕ) (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))) :
    Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :=
  {A ∈ corrSet n | V ≤ LinearMap.ker A.toLinearMap}

def IsExposedFaceOf {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (C F : Set X) : Prop :=
  ∃ (phi : X →L[ℝ] ℝ),
    F = {x ∈ C | ∀ y ∈ C, phi y ≤ phi x}

def IsFaceOf {E : Type*} [AddCommGroup E] [Module ℝ E]
  (F K : Set E) : Prop :=
  Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ K F

theorem FCA_chap_A_ex_5 {n : ℕ} :
  (∀ (V : Submodule ℝ (EuclideanSpace ℝ (Fin n))),
    Set.Nonempty (corrFV n V) →
    IsFaceOf (corrFV n V) (corrSet n)) ∧
  (∀ (F : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
    IsFaceOf F (corrSet n) →
    F = corrFV n (⨅ (A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))
      (_ : A ∈ F), LinearMap.ker A.toLinearMap)) ∧
  (∀ (M₀ : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)),
    M₀ ∈ corrSet n →
    IsFaceOf (corrFV n (LinearMap.ker M₀.toLinearMap)) (corrSet n) ∧
    M₀ ∈ corrFV n (LinearMap.ker M₀.toLinearMap) ∧
    (∀ F, IsFaceOf F (corrSet n) → M₀ ∈ F → corrFV n (LinearMap.ker M₀.toLinearMap) ⊆ F)) ∧
  (∀ (F : Set (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n))),
    IsFaceOf F (corrSet n) →
    IsExposedFaceOf (corrSet n) F) := by
  sorry
