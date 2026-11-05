import Mathlib

/-!
Monotonicity of set-valued operators on a real Hilbert space, as in
Bauschke--Combettes, Definitions 20.1 and 22.1, and Rockafellar--Wets,
Definitions 12.1 and 12.53. These include the single-valued notions of
Hiriart-Urruty--Lemaréchal, Fundamentals of Convex Analysis, Definition B.4.1.3.

A mapping `F` defined on `C` is represented by `fun x => {v | x ∈ C ∧ v = F x}`:
its value is `{F x}` on `C` and is empty outside `C`.
-/

/-- Monotonicity, expressed by an inequality between any two points of the graph. -/
def IsMonotoneOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁,
    0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- Strict monotonicity: the graph inequality is strict at distinct input points. -/
def IsStrictlyMonotoneOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁,
    x₀ ≠ x₁ → 0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- The strong monotonicity inequality with modulus `c`.
As with `StrongConvexOn`, positivity of the modulus is supplied by the caller. -/
def IsStronglyMonotoneOperator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (T : E → Set E) (c : ℝ) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁,
    c * ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)
