import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_ii`, so the main result is `FCA_chap_E_1_3_1_ii.FCA_chap_E_1_3_1_ii`.
-/

namespace FCA_chap_E_1_3_1_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_1_ii
  (f : E → EReal) (t : ℝ)
  (hf_nondegenerate : IsNondegenerate f) (ht_pos : t > 0) :
  let f' := f
  let g := fun x => t * f' x
  ∀ s, conjugate g s = t * conjugate f' (t⁻¹ • s) := by
  intro f' g s
  have ht0 : t ≠ 0 := ne_of_gt ht_pos
  have hinv : ∀ x : EReal, ((t⁻¹ : ℝ) : EReal) * ((t : EReal) * x) = x := by
    intro x
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht0, EReal.coe_one, one_mul]
  have hinv' : ∀ x : EReal, (t : EReal) * (((t⁻¹ : ℝ) : EReal) * x) = x := by
    intro x
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht0, EReal.coe_one, one_mul]
  have ht_nn : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast ht_pos.le
  have htinv_nn : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.mpr ht_pos).le
  let e : EReal ≃ EReal :=
    { toFun := fun x => (t : EReal) * x
      invFun := fun x => ((t⁻¹ : ℝ) : EReal) * x
      left_inv := hinv
      right_inv := hinv' }
  let Φ : EReal ≃o EReal :=
    e.toOrderIso (fun a b h => mul_le_mul_of_nonneg_left h ht_nn)
      (fun a b h => mul_le_mul_of_nonneg_left h htinv_nn)
  have hΦ : ∀ x, Φ x = (t : EReal) * x := fun x => rfl
  have hpt : ∀ x, ((inner ℝ s x : ℝ) : EReal) - g x
      = Φ (((inner ℝ (t⁻¹ • s) x : ℝ) : EReal) - f' x) := by
    intro x
    rw [hΦ]
    show ((inner ℝ s x : ℝ) : EReal) - (t : EReal) * f x
      = (t : EReal) * (((inner ℝ (t⁻¹ • s) x : ℝ) : EReal) - f x)
    rw [real_inner_smul_left]
    induction f x using EReal.rec with
    | bot =>
      rw [EReal.coe_mul_bot_of_pos ht_pos, EReal.coe_sub_bot, EReal.coe_sub_bot,
        EReal.coe_mul_top_of_pos ht_pos]
    | top =>
      rw [EReal.coe_mul_top_of_pos ht_pos, EReal.sub_top, EReal.sub_top,
        EReal.coe_mul_bot_of_pos ht_pos]
    | coe r =>
      rw [← EReal.coe_mul, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul]
      congr 1
      field_simp
  unfold conjugate
  have hfun : (fun x => ((inner ℝ s x : ℝ) : EReal) - g x)
      = Φ ∘ (fun x => ((inner ℝ (t⁻¹ • s) x : ℝ) : EReal) - f' x) := funext hpt
  rw [hfun, Set.image_comp, ← hΦ, OrderIso.map_sSup, sSup_image]

end FCA_chap_E_1_3_1_ii
