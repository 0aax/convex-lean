import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsRegularNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  x_bar ∈ C ∧
  ∃ (r : E → ℝ),
    r =o[𝓝 x_bar] (fun x => ‖x - x_bar‖) ∧
    ∃ V ∈ 𝓝 x_bar, ∀ x ∈ V, x ∈ C →
      inner ℝ v (x - x_bar) ≤ r x

def regularNormalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsRegularNormalAt C x_bar v}

def IsNormalAt {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar v : E) : Prop :=
  ∃ (x : ℕ → E), ∃ (vseq : ℕ → E),
    Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
    Filter.Tendsto vseq Filter.atTop (𝓝 v) ∧
    (∀ n, vseq n ∈ regularNormalCone C (x n))

def normalCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E)
  (x_bar : E) : Set E :=
  {v | IsNormalAt C x_bar v}

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

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

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

def smulMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (T : E → Set E) : E → Set E :=
  fun x => {v | ∃ w ∈ T x, v = a • w}

theorem RW_chap_12_20
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C) :
  IsMonotone (projectionMapping C) ∧
  List.TFAE [
    Convex ℝ C,
    IsSingleValued (projectionMapping C),
    IsNonexpansive (projectionMapping C),
    IsMaximalMonotone (projectionMapping C),
    ∃ rho : ℝ, IsMonotone (addMap (normalCone C) (smulMap rho idMap))
  ] := by
  sorry
