import Mathlib

/-!
# Project-wide definitions

Definitions shared by the formalizations in this project.

Mathlib already provides the convexity notions `ConvexOn`, `StrictConvexOn` and `StrongConvexOn`
(the latter with the convention of Hiriart-Urruty–Lemaréchal, Definition B.1.1.1:
`f (α x + (1 - α) x') ≤ α f x + (1 - α) f x' - ½ c α (1 - α) ‖x - x'‖²`), as well as the
gradient `∇ f` (`gradient f`) of a real-valued function on a real Hilbert space.

Here we add the monotonicity notions for (single-valued) mappings on a subset of a real
inner product space, following Hiriart-Urruty–Lemaréchal, *Fundamentals of Convex Analysis*,
Definition B.4.1.3 (compare Bauschke–Combettes, Definitions 20.1 and 22.1, and
Rockafellar–Wets, Definition 12.1, for the set-valued versions).
-/

open scoped InnerProductSpace

section MonotoneMaps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A mapping `F` is *monotone* on the set `s` (Hiriart-Urruty–Lemaréchal, Definition B.4.1.3):
`⟪F x - F x', x - x'⟫ ≥ 0` for all `x, x'` in `s`. The values of `F` outside `s` are irrelevant,
so this is the usual way of speaking about a mapping `F : s → E`. -/
def MonotoneMapOn (s : Set E) (F : E → E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → 0 ≤ ⟪F x - F y, x - y⟫_ℝ

/-- A mapping `F` is *strictly monotone* on the set `s` (Hiriart-Urruty–Lemaréchal,
Definition B.4.1.3): `⟪F x - F x', x - x'⟫ > 0` whenever `x ≠ x'` in `s`. -/
def StrictMonotoneMapOn (s : Set E) (F : E → E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → x ≠ y → 0 < ⟪F x - F y, x - y⟫_ℝ

/-- A mapping `F` is *strongly monotone with modulus `c`* on the set `s` (Hiriart-Urruty–Lemaréchal,
Definition B.4.1.3): `⟪F x - F x', x - x'⟫ ≥ c ‖x - x'‖²` for all `x, x'` in `s`.
Note the coefficient `c` (and not `½ c`, as in strong convexity).
As for Mathlib's `StrongConvexOn`, positivity of the modulus `c` is not built into the
definition (the book takes `c > 0`; for `c = 0` this is plain monotonicity). -/
def StrongMonotoneMapOn (s : Set E) (c : ℝ) (F : E → E) : Prop :=
  ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → c * ‖x - y‖ ^ 2 ≤ ⟪F x - F y, x - y⟫_ℝ

end MonotoneMaps
