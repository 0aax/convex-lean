import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def setLiminf {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∀ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def setLimsup {X : Type*} [TopologicalSpace X] (A : ℕ → Set X) : Set X :=
  {u | ∀ V ∈ 𝓝 u, ∃ᶠ n in Filter.atTop, ∃ v ∈ A n, v ∈ V}

def graph {E : Type*} (T : E → Set E) : Set (E × E) :=
  {p | p.2 ∈ T p.1}

def graphSetLiminf {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLiminf (fun n => graph (Tseq n))

def graphSetLimsup {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) : Set (E × E) :=
  setLimsup (fun n => graph (Tseq n))

def GraphicallyConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  graphSetLimsup Tseq = graph T ∧
  graphSetLiminf Tseq = graph T

def idMap {E : Type*} (x : E) : Set E := {x}

def IsMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  ∀ (x₀ x₁ v₀ v₁ : E), v₀ ∈ T x₀ → v₁ ∈ T x₁ →
  0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

def IsMaximalMonotone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (T : E → Set E) : Prop :=
  IsMonotone T ∧
  ∀ (x_hat v_hat : E),
    v_hat ∉ T x_hat →
    ∃ (x_tilde v_tilde : E),
      v_tilde ∈ T x_tilde ∧
      inner ℝ (v_hat - v_tilde) (x_hat - x_tilde) < 0

def pLiminf {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLiminf (fun n => Tseq n x)

def pLimsup {E : Type*} [NormedAddCommGroup E] (Tseq : ℕ → E → Set E) : E → Set E :=
  fun x => setLimsup (fun n => Tseq n x)

def PointwiseMapConverges {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E) (T : E → Set E) : Prop :=
  pLimsup Tseq = T ∧ pLiminf Tseq = T

def εEnlarge {E : Type*} [NormedAddCommGroup E] (A : Set E) (ε : ℝ) : Set E :=
  {y | ∃ z ∈ A, dist y z < ε}

def UniformlyConvergesOn {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E)
  (X : Set E) : Prop :=
  ∀ ε > (0 : ℝ), ∀ ρ > (0 : ℝ),
    ∃ N : ℕ,
      ∀ n ≥ N, ∀ x ∈ X,
        (Tseq n x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (T x) ε ∧
        (T x ∩ Metric.ball 0 ρ) ⊆ εEnlarge (Tseq n x) ε

def UniformlyConvergesOnBounded {E : Type*} [NormedAddCommGroup E]
  (Tseq : ℕ → E → Set E)
  (T : E → Set E) : Prop :=
  ∀ R > (0 : ℝ),
    UniformlyConvergesOn Tseq T {x | ‖x‖ ≤ R}

def addMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u + v}

def invMap {E : Type*}
  (T : E → Set E) : E → Set E :=
  fun y => {x | y ∈ T x}

def smulMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (T : E → Set E) : E → Set E :=
  fun x => {v | ∃ w ∈ T x, v = a • w}

theorem RW_chap_12_32
  (Tseq : ℕ → (E → Set E))
  (T : E → Set E) :
  let resolvent : ℝ → (E → Set E) → (E → Set E) :=
    fun l S => invMap (addMap idMap (smulMap l S))
  ((GraphicallyConverges Tseq T ∧ ∀ i, IsMonotone (Tseq i)) →
    IsMonotone T) ∧
  ((GraphicallyConverges Tseq T ∧ (∀ i, IsMaximalMonotone (Tseq i)) ∧ (graph T).Nonempty) →
    IsMaximalMonotone T) ∧
  (∀ lam : ℝ, 0 < lam →
    (IsMaximalMonotone T ∧ ∀ i, IsMaximalMonotone (Tseq i)) →
      (GraphicallyConverges Tseq T ↔
        PointwiseMapConverges
          (fun i => resolvent lam (Tseq i))
          (resolvent lam T))) ∧
  (∀ (lamseq : ℕ → ℝ) (lam : ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝 lam) →
    0 < lam →
    ((GraphicallyConverges Tseq T) ∧
      IsMaximalMonotone T ∧
      (∀ i, IsMaximalMonotone (Tseq i)) ∧
      (∀ i, 0 < lamseq i)) →
    UniformlyConvergesOnBounded
      (fun i => resolvent (lamseq i) (Tseq i))
      (resolvent lam T)) := by
  sorry
