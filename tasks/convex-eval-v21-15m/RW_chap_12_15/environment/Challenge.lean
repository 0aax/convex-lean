import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def graph {E : Type*} (T : E → Set E) : Set (E × E) :=
  {p | p.2 ∈ T p.1}

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

def IsNonexpansive {E : Type*} [NormedAddCommGroup E]
  (S : E → Set E) : Prop :=
  ∀ (z₀ z₁ w₀ w₁ : E), w₀ ∈ S z₀ → w₁ ∈ S z₁ →
    ‖w₁ - w₀‖ ≤ ‖z₁ - z₀‖

def IsSingleValued {E : Type*}
  (S : E → Set E) : Prop :=
  ∀ z, ∃! x, x ∈ S z

def addMap {E : Type*} [NormedAddCommGroup E]
  (S T : E → Set E) : E → Set E :=
  fun x => {z | ∃ u ∈ S x, ∃ v ∈ T x, z = u + v}

def invMap {E : Type*}
  (T : E → Set E) : E → Set E :=
  fun y => {x | y ∈ T x}

theorem RW_chap_12_15
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let P := invMap (addMap idMap T)
  let Q := invMap (addMap idMap (invMap T))
  let Pfun : IsSingleValued P → E → E :=
    fun hP z => Classical.choose (hP z)
  let Qfun : IsSingleValued Q → E → E :=
    fun hQ z => Classical.choose (hQ z)
  IsSingleValued P ∧
  IsSingleValued Q ∧
  IsMaximalMonotone P ∧
  IsMaximalMonotone Q ∧
  IsNonexpansive P ∧
  IsNonexpansive Q ∧
  (∀ hP : IsSingleValued P, ∀ hQ : IsSingleValued Q,
    ∀ z x v,
      (Pfun hP z, Qfun hQ z) = (x, v) ↔
      z = x + v ∧ v ∈ T x) ∧
  (∀ hP : IsSingleValued P, ∀ hQ : IsSingleValued Q,
    let g : E → E × E := fun z => (Pfun hP z, Qfun hQ z)
    Function.Injective g ∧
    Set.range g = graph T) := by
  sorry
