import Mathlib

/-!
# Shared definitions of the formalization project

Definitions used by more than one result live here.  Each concept has one definition, stated
in the generality the corpus requires.
-/

open scoped InnerProductSpace

noncomputable section

/-! ## Monotone multifunctions (operators)

A multifunction (set-valued mapping, operator) is `T : E → Set E`; its graph is
`{(x, v) | v ∈ T x}` and its domain is `{x | (T x).Nonempty}`.  Monotonicity properties are
stated on the graph, as in Rockafellar–Wets (Def. 12.1, Prop. 12.54 / 12.53 for the strong
version) and Bauschke–Combettes (Defs. 20.1 and 22.1).  A single-valued mapping `F : C → E`
on a set `C`, as in Hiriart-Urruty & Lemaréchal (FCA Def. B.4.1.3, CAMA Def. IV.4.1.3), is
the multifunction `toMultifunOn F C` with values `{F x}` on `C` and `∅` outside `C`, and the
graph conditions below are then exactly their conditions "for all `x, x' ∈ C`". -/

section Monotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A single-valued mapping `F`, considered on the set `C` only, viewed as a multifunction:
its value at `x` is `{F x}` when `x ∈ C` and `∅` otherwise. -/
def toMultifunOn (F : E → E) (C : Set E) : E → Set E :=
  fun x => {v | x ∈ C ∧ v = F x}

/-- The multifunction `T` is monotone: `⟪v₁ - v₀, x₁ - x₀⟫ ≥ 0` whenever `v₀ ∈ T x₀` and
`v₁ ∈ T x₁`. -/
def IsMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, 0 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- The multifunction `T` is strictly monotone: `⟪v₁ - v₀, x₁ - x₀⟫ > 0` whenever
`v₀ ∈ T x₀`, `v₁ ∈ T x₁` and `x₀ ≠ x₁`. -/
def IsStrictlyMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, x₀ ≠ x₁ → ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, 0 < ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- The multifunction `T` is strongly monotone with modulus (constant) `c`:
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ c ‖x₁ - x₀‖ ^ 2` whenever `v₀ ∈ T x₀` and `v₁ ∈ T x₁`.  The sources
take `c > 0`; this is a hypothesis of the results using it. -/
def IsStronglyMonotoneOperator (T : E → Set E) (c : ℝ) : Prop :=
  ∀ ⦃x₀ x₁ : E⦄, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, c * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

end Monotone

end
