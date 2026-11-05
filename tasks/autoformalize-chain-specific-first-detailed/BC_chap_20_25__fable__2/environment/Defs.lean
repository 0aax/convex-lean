import Mathlib

/-!
# Shared definitions of the formalization project

One definition per concept, shared by every source in the corpus that uses the concept.
-/

noncomputable section

/-! ### Multifunctions (set-valued mappings) -/

section Multifunctions

variable {E F : Type*}

/-- A single-valued map `g : E → F` considered only on a set `C`, viewed as a multifunction
`E → Set F`: its value at `x` is `{g x}` when `x ∈ C` and `∅` otherwise.
This places a map "on `C`" (e.g. Hiriart-Urruty & Lemaréchal, Fundamentals, Def. B.4.1.3)
in the graph-based framework of set-valued mappings used by Rockafellar–Wets (Def. 12.1)
and Bauschke–Combettes (Def. 20.1): restricting a multifunction to a set means making its
values `∅` outside the set. -/
def Function.toMultifunOn (g : E → F) (C : Set E) : E → Set F :=
  fun x => {v | x ∈ C ∧ v = g x}

end Multifunctions

/-! ### Monotone multifunctions -/

section Monotone

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- A multifunction `T : E → Set E` is *monotone* when `⟪v₁ - v₀, x₁ - x₀⟫ ≥ 0` whenever
`v₀ ∈ T x₀` and `v₁ ∈ T x₁` (Rockafellar–Wets Def. 12.1; Bauschke–Combettes Def. 20.1).
A single-valued map `F` on a set `C` is monotone on `C` in the sense of
Hiriart-Urruty & Lemaréchal (Fundamentals, Def. B.4.1.3) when `F.toMultifunOn C` is. -/
def IsMonotoneMultifun (T : E → Set E) : Prop :=
  ∀ x₀ x₁ : E, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, 0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- A multifunction `T : E → Set E` is *strictly monotone* when `⟪v₁ - v₀, x₁ - x₀⟫ > 0`
whenever `x₀ ≠ x₁`, `v₀ ∈ T x₀` and `v₁ ∈ T x₁` (Rockafellar–Wets Def. 12.1;
Bauschke–Combettes Def. 22.1; Hiriart-Urruty & Lemaréchal Def. B.4.1.3 via `toMultifunOn`). -/
def IsStrictlyMonotoneMultifun (T : E → Set E) : Prop :=
  ∀ x₀ x₁ : E, x₀ ≠ x₁ → ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, 0 < inner ℝ (v₁ - v₀) (x₁ - x₀)

/-- A multifunction `T : E → Set E` is *strongly monotone with modulus (constant) `c`* when
`⟪v₁ - v₀, x₁ - x₀⟫ ≥ c * ‖x₁ - x₀‖ ^ 2` whenever `v₀ ∈ T x₀` and `v₁ ∈ T x₁`
(Rockafellar–Wets 12.53; Bauschke–Combettes Def. 22.1; Hiriart-Urruty & Lemaréchal
Def. B.4.1.3 via `toMultifunOn`). The sources take `c > 0`; that is a hypothesis of the
results using the notion, not part of the definition. Note the coefficient is `c`, not `c/2`. -/
def IsStronglyMonotoneMultifun (T : E → Set E) (c : ℝ) : Prop :=
  ∀ x₀ x₁ : E, ∀ v₀ ∈ T x₀, ∀ v₁ ∈ T x₁, c * ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀)

end Monotone

end
