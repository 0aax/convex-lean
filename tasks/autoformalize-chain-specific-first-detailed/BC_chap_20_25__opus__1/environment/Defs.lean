import Mathlib

/-!
# Shared definitions of the formalization project
-/

open scoped InnerProductSpace

section MonotoneOperator

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A multifunction `T : E → Set E` is *monotone* when `⟪v₁ - v₀, x₁ - x₀⟫ ≥ 0` for all pairs
`(x₀, v₀)`, `(x₁, v₁)` of its graph (Bauschke–Combettes Def. 20.1, Rockafellar–Wets Def. 12.1).
A single-valued map `F` that is monotone on a set `C` (Hiriart-Urruty–Lemaréchal Def. B.4.1.3) is
the multifunction `fun x => {v | x ∈ C ∧ v = F x}`, whose values are `∅` outside `C`. -/
def IsMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → 0 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- A multifunction `T : E → Set E` is *strictly monotone* when `⟪v₁ - v₀, x₁ - x₀⟫ > 0` for all
pairs `(x₀, v₀)`, `(x₁, v₁)` of its graph with `x₀ ≠ x₁` (Bauschke–Combettes Def. 22.1,
Rockafellar–Wets Def. 12.1, Hiriart-Urruty–Lemaréchal Def. B.4.1.3). -/
def IsStrictlyMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → x₀ ≠ x₁ → 0 < ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

/-- A multifunction `T : E → Set E` is *strongly monotone with modulus (constant) `c`* when
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ c ‖x₁ - x₀‖²` for all pairs `(x₀, v₀)`, `(x₁, v₁)` of its graph, i.e. when
`T - c • id` is monotone (Bauschke–Combettes Def. 22.1, Rockafellar–Wets §12, before Prop. 12.54,
Hiriart-Urruty–Lemaréchal Def. B.4.1.3). The sources require `c > 0`; results state this as a
hypothesis, as for Mathlib's `StrongConvexOn`. -/
def IsStronglyMonotoneOperator (T : E → Set E) (c : ℝ) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → c * ‖x₁ - x₀‖ ^ 2 ≤ ⟪v₁ - v₀, x₁ - x₀⟫_ℝ

end MonotoneOperator
