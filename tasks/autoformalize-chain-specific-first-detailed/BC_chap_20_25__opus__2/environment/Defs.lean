import Mathlib

/-!
# Shared definitions of the formalization project
-/

section MonotoneOperators

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A multifunction `T : E ⇉ E`, encoded as `T : E → Set E`, is *monotone* when
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ 0` whenever `v₀ ∈ T x₀` and `v₁ ∈ T x₁`
(Rockafellar–Wets, Def. 12.1; Bauschke–Combettes, Def. 20.1).

A single-valued mapping `F` defined on a set `C` (Hiriart-Urruty–Lemaréchal, Def. B.4.1.3)
is the multifunction `fun x => {v | x ∈ C ∧ v = F x}`, with value `{F x}` on `C` and `∅`
outside `C`; it is monotone on `C` iff this multifunction is monotone. -/
def IsMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → 0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- A multifunction `T : E ⇉ E` is *strictly monotone* when `⟪v₁ - v₀, x₁ - x₀⟫ > 0`
whenever `v₀ ∈ T x₀`, `v₁ ∈ T x₁` and `x₀ ≠ x₁`
(Rockafellar–Wets, Def. 12.1; Bauschke–Combettes, Def. 22.1(ii);
Hiriart-Urruty–Lemaréchal, Def. B.4.1.3). -/
def IsStrictlyMonotoneOperator (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ → x₀ ≠ x₁ → 0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- A multifunction `T : E ⇉ E` is *strongly monotone with modulus (constant) `c`* when
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ c ‖x₁ - x₀‖²` whenever `v₀ ∈ T x₀` and `v₁ ∈ T x₁`, i.e. `T - c Id` is
monotone (Rockafellar–Wets, Def. 12.53; Bauschke–Combettes, Def. 22.1(iv);
Hiriart-Urruty–Lemaréchal, Def. B.4.1.3). As for Mathlib's `StrongConvexOn`, the sources'
requirement `c > 0` is not part of the definition and is assumed where the sources assume it. -/
def IsStronglyMonotoneOperator (c : ℝ) (T : E → Set E) : Prop :=
  ∀ ⦃x₀ x₁ v₀ v₁ : E⦄, v₀ ∈ T x₀ → v₁ ∈ T x₁ →
    c * ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

end MonotoneOperators
