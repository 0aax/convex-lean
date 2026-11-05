import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsAcuteCone {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) : Prop :=
  ∀ x ∈ K, ∀ x' ∈ K, (0 : ℝ) ≤ inner ℝ x x'

def coneKp {n : ℕ} (p : ℝ) (hn : n ≥ 2) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | x ⟨n - 1, by omega⟩ ≥
    (∑ k : Fin (n - 1), |x ⟨k.val, by omega⟩| ^ p) ^ (1 / p)}

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem FCA_chap_A_ex_23 :
  (∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))),
    IsAcuteCone K ↔ K ⊆ {x | -x ∈ polarCone K}) ∧
  (∀ {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp : 1 < p),
    let q := p / (p - 1)
    polarCone (coneKp p hn) =
      {x : EuclideanSpace ℝ (Fin n) | -x ∈ coneKp q hn}) ∧
  (∀ {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp : 1 ≤ p),
    (n ≥ 3 → (IsAcuteCone (coneKp p hn) ↔ p ≤ 2)) ∧
    (n = 2 → IsAcuteCone (coneKp p hn))) := by
  sorry
