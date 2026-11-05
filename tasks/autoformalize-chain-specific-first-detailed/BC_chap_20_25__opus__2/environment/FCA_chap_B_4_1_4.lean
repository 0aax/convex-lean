import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Theorem B.4.1.4

Source (Chap. B, §4.1, PDF p. 122 / book p. 112):
"Let `f` be a function differentiable on an open set `Ω ⊂ ℝⁿ`, and let `C` be a convex subset
of `Ω`. Then, `f` is convex [resp. strictly convex, resp. strongly convex with modulus `c`] on `C`
if and only if its gradient `∇f` is monotone [resp. strictly monotone, resp. strongly monotone
with modulus `c`] on `C`."

Hypotheses, including the standing ones:
* the space is `ℝⁿ` with a scalar product; here an abstract finite-dimensional real
  inner-product space `E`;
* (standing assumption of §B.4) `C` is nonempty and convex, and `f` is finite on `C`;
  `f` is real-valued (§B.4.1: `f` is differentiable on `Ω`, hence finite there);
* `Ω` is open, `f` is differentiable on `Ω`, and `C ⊆ Ω`;
* the modulus `c` is positive: (1.1.2) and Def. B.4.1.3 both ask for `c > 0`.

Definitions used:
* convex, strictly convex, strongly convex with modulus `c` on `C` (Def. B.1.1.1 and (1.1.2)):
  `f (α x + (1-α) x') ≤ α f x + (1-α) f x' [- ½ c α (1-α) ‖x - x'‖²]`, strict for `x ≠ x'` in
  the strict case. These are Mathlib's `ConvexOn ℝ C f`, `StrictConvexOn ℝ C f` and
  `StrongConvexOn C c f`; the last one uses the same `c/2` convention as (1.1.2).
* monotone, strictly monotone, strongly monotone with modulus `c` on `C` (Def. B.4.1.3), for
  `F : C → ℝⁿ`: `⟪F x - F x', x - x'⟫ ≥ 0` [resp. `> 0` whenever `x ≠ x'`, resp.
  `≥ c ‖x - x'‖²`] for all `x, x' ∈ C`. This is the set-valued notion of `Defs.lean`
  (`IsMonotoneOperator`, `IsStrictlyMonotoneOperator`, `IsStronglyMonotoneOperator`)
  applied to the multifunction `x ↦ {∇f x}` for `x ∈ C`, `x ↦ ∅` for `x ∉ C`.

Conclusion: the three equivalences
convex ⟺ `∇f` monotone, strictly convex ⟺ `∇f` strictly monotone, and, for every `c > 0`,
strongly convex with modulus `c` ⟺ `∇f` strongly monotone with modulus `c`, all on `C`.

`gradient f x` is only evaluated at `x ∈ C ⊆ Ω`, where `f` is differentiable because `Ω` is
open, so it is the true gradient there.
-/

theorem FCA_chap_B_4_1_4
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → ℝ) (Ω C : Set E)
    -- `f` is differentiable on the open set `Ω`
    (hΩ_open : IsOpen Ω) (hf_diff : DifferentiableOn ℝ f Ω)
    -- `C` is a nonempty convex subset of `Ω`
    (hC_nonempty : C.Nonempty) (hC_convex : Convex ℝ C) (hC_sub : C ⊆ Ω) :
    (ConvexOn ℝ C f ↔
      IsMonotoneOperator (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
    (StrictConvexOn ℝ C f ↔
      IsStrictlyMonotoneOperator (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
    (∀ c : ℝ, 0 < c →
      (StrongConvexOn C c f ↔
        IsStronglyMonotoneOperator c (fun x => {v | x ∈ C ∧ v = gradient f x}))) := by
  sorry
