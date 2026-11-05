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

def projectionMapping {E : Type*} [NormedAddCommGroup E] (C : Set E) (x : E) : Set E :=
  {w : E | w ∈ C ∧ ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}

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

def horizonCone {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  (C : Set E) : Set E :=
  {x : E | ∃ (xseq : ℕ → E) (l : ℕ → ℝ),
    (∀ i, xseq i ∈ C) ∧
    (Filter.Tendsto l Filter.atTop (𝓝[>] 0)) ∧
    (Filter.Tendsto
      (fun i => (l i) • (xseq i))
      Filter.atTop
      (𝓝 x))}

def invMap {E : Type*}
  (T : E → Set E) : E → Set E :=
  fun y => {x | y ∈ T x}

def smulMap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a : ℝ) (T : E → Set E) : E → Set E :=
  fun x => {v | ∃ w ∈ T x, v = a • w}

theorem RW_chap_12_37
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let domT : Set E := {x | (T x).Nonempty}
  let D : Set E := closure domT
  Convex ℝ D ∧
  (∀ x, x ∈ domT → horizonCone (T x) = normalCone D x) ∧
  (∀ (lamseq : ℕ → ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝[>] (0 : ℝ)) →
    GraphicallyConverges
      (fun n => smulMap (lamseq n) T)
      (normalCone D)) ∧
  (invMap (addMap idMap (normalCone D)) = projectionMapping D) ∧
  (∀ (lamseq : ℕ → ℝ),
    Filter.Tendsto lamseq Filter.atTop (𝓝[>] (0 : ℝ)) →
    UniformlyConvergesOnBounded
      (fun n => invMap (addMap idMap (smulMap (lamseq n) T)))
      (invMap (addMap idMap (normalCone D)))) := by
  sorry
