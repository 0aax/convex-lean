import Mathlib

/-!
Monotonicity of set-valued operators, shared by the single-valued notions in
Hiriart-Urruty--Lemaréchal, *Fundamentals of Convex Analysis*, B.4.1.3, and the
set-valued notions in Rockafellar--Wets, *Variational Analysis*, Definitions 12.1
and 12.53, and Bauschke--Combettes, *Convex Analysis and Monotone Operator Theory
in Hilbert Spaces*, Definitions 20.1 and 22.1.

A mapping `F` defined on `C` is represented by `fun x => {v | x ∈ C ∧ v = F x}`:
its value is the singleton `{F x}` on `C` and the empty set outside `C`.
-/

section MonotoneOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Monotonicity of a set-valued operator, expressed on pairs of graph elements. -/
def IsMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ →
    0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- Strict monotonicity requires a strict inequality for distinct input points. -/
def IsStrictlyMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → x₀ ≠ x₁ →
    0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- The strong monotonicity inequality with modulus `c`. Positivity of the modulus
is imposed at use sites; modulus zero gives ordinary monotonicity. -/
def IsStronglyMonotoneOperator (T : E → Set E) (c : ℝ) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ →
    c * ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

end MonotoneOperators
