import Mathlib

/-!
# Shared definitions for the formalization project

Notions used by the formalized results that are not (yet) available in Mathlib.

## Monotone maps (Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Def. B.4.1.3)

For a map `F : E → E` on a real inner product space `E` and a set `C ⊆ E`:

* `IsMonotoneOn F C`             : `⟪F x - F y, x - y⟫ ≥ 0` for all `x, y ∈ C`;
* `IsStrictlyMonotoneOn F C`     : `⟪F x - F y, x - y⟫ > 0` for all `x ≠ y` in `C`;
* `IsStronglyMonotoneOn F C c`   : `⟪F x - F y, x - y⟫ ≥ c * ‖x - y‖ ^ 2` for all `x, y ∈ C`
  (strongly monotone with modulus `c`).

These are the single-valued versions of the usual notions for monotone operators on a
Hilbert space; the book states them for `ℝⁿ`.
-/

section MonotoneMaps

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A map `F : E → E` on a real inner product space is **monotone on `C`**
(HUL, Def. B.4.1.3): `⟪F x - F y, x - y⟫ ≥ 0` for all `x, y ∈ C`. -/
def IsMonotoneOn (F : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (F x - F y) (x - y)

/-- A map `F : E → E` on a real inner product space is **strictly monotone on `C`**
(HUL, Def. B.4.1.3): `⟪F x - F y, x - y⟫ > 0` whenever `x ≠ y` in `C`. -/
def IsStrictlyMonotoneOn (F : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 0 < inner ℝ (F x - F y) (x - y)

/-- A map `F : E → E` on a real inner product space is **strongly monotone on `C` with
modulus `c`** (HUL, Def. B.4.1.3): `⟪F x - F y, x - y⟫ ≥ c * ‖x - y‖ ^ 2` for all `x, y ∈ C`.
(Note the coefficient is `c`, not `c / 2`, in contrast with `StrongConvexOn`.) -/
def IsStronglyMonotoneOn (F : E → E) (C : Set E) (c : ℝ) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, c * ‖x - y‖ ^ 2 ≤ inner ℝ (F x - F y) (x - y)

end MonotoneMaps
