import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex6`, so the main result is `FCA_chap_E_ex6.FCA_chap_E_ex6`.
-/

namespace FCA_chap_E_ex6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex6 (p : ℝ)
  (fp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (gp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp : ℝ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp_pos : p > 0)
  (h_eq : ∀ r > 0, ∀ (x : EuclideanSpace ℝ (Fin 1)),
            (x 0 ≥ 0) →
            ((fp r x = gp r x) ∧ (gp r x = hp r x) ∧
            ((fp r x) = (((r + 1)⁻¹ * (x 0) ^ (r + 1) : ℝ) : EReal))))
  (h_ow : ∀ r > 0, ∀ (x : EuclideanSpace ℝ (Fin 1)),
            (x 0 < 0) →
            ((fp r x = ⊤) ∧ (gp r x = 0) ∧
            ((hp r x) = (((r + 1)⁻¹ * (-1 * (x 0)) ^ (r + 1) : ℝ) : EReal))))
  (fp_ne_bot : ∀ x₁ x₂, ⊥ < fp x₁ x₂) (gp_ne_bot : ∀ x₁ x₂, ⊥ < gp x₁ x₂) (hp_ne_bot : ∀ x₁ x₂, ⊥ < hp x₁ x₂) :
  let fp_conj := conjugate (fp p)
  let gp_conj := conjugate (gp p)
  let hp_conj := conjugate (hp p)
  (∀ x, fp_conj x = gp (p⁻¹) x) ∧
  (∀ x, gp_conj x = fp (p⁻¹) x) ∧
  (∀ x, hp_conj x = hp (p⁻¹) x) := by
  intro fp_conj gp_conj hp_conj
  have hq : p⁻¹ > 0 := inv_pos.mpr hp_pos
  have young_aux : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * b ≤ (p + 1)⁻¹ * a ^ (p + 1) + (p⁻¹ + 1)⁻¹ * b ^ (p⁻¹ + 1) := by
    intro a b ha hb
    have hpq : (p + 1).HolderConjugate (p⁻¹ + 1) := by
      rw [Real.holderConjugate_iff]
      refine ⟨by linarith, ?_⟩
      field_simp
      ring
    have := Real.young_inequality_of_nonneg ha hb hpq
    rw [div_eq_inv_mul, div_eq_inv_mul] at this
    exact this
  have conj_eq : ∀ (f : EuclideanSpace ℝ (Fin 1) → EReal) (v : EuclideanSpace ℝ (Fin 1))
      (c : EReal), (∀ x, ((inner ℝ v x : ℝ) : EReal) - f x ≤ c) →
      ∀ x₀, ((inner ℝ v x₀ : ℝ) : EReal) - f x₀ = c → conjugate f v = c := by
    intro f v c hub x₀ hx₀
    unfold conjugate
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      exact hub x
    · exact le_sSup ⟨x₀, Set.mem_univ _, hx₀⟩
  have conj_top : ∀ (f : EuclideanSpace ℝ (Fin 1) → EReal) (v : EuclideanSpace ℝ (Fin 1)),
      (∀ M : ℝ, ∃ x, (M : EReal) < ((inner ℝ v x : ℝ) : EReal) - f x) →
      conjugate f v = ⊤ := by
    intro f v h
    unfold conjugate
    rw [EReal.eq_top_iff_forall_lt]
    intro M
    obtain ⟨x, hx⟩ := h M
    exact lt_of_lt_of_le hx (le_sSup ⟨x, Set.mem_univ _, rfl⟩)
  have hinner : ∀ v x : EuclideanSpace ℝ (Fin 1), inner ℝ v x = v 0 * x 0 := by
    intro v x
    simp [PiLp.inner_apply, mul_comm]
  have hsingle : ∀ t : ℝ, (EuclideanSpace.single (0 : Fin 1) t) 0 = t := by
    intro t
    simp
  -- values of fp, gp, hp at nonnegative points
  have hf_nn : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 ≥ 0 →
      fp r x = (((r + 1)⁻¹ * (x 0) ^ (r + 1) : ℝ) : EReal) := fun r hr x hx =>
    (h_eq r hr x hx).2.2
  have hg_nn : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 ≥ 0 →
      gp r x = (((r + 1)⁻¹ * (x 0) ^ (r + 1) : ℝ) : EReal) := fun r hr x hx => by
    rw [← (h_eq r hr x hx).1, (h_eq r hr x hx).2.2]
  have hh_nn : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 ≥ 0 →
      hp r x = (((r + 1)⁻¹ * (x 0) ^ (r + 1) : ℝ) : EReal) := fun r hr x hx => by
    rw [← (h_eq r hr x hx).2.1, hg_nn r hr x hx]
  have hf_neg : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 < 0 → fp r x = ⊤ :=
    fun r hr x hx => (h_ow r hr x hx).1
  have hg_neg : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 < 0 → gp r x = 0 :=
    fun r hr x hx => (h_ow r hr x hx).2.1
  have hh_neg : ∀ r > 0, ∀ x : EuclideanSpace ℝ (Fin 1), x 0 < 0 →
      hp r x = (((r + 1)⁻¹ * (-(x 0)) ^ (r + 1) : ℝ) : EReal) := fun r hr x hx => by
    rw [(h_ow r hr x hx).2.2, neg_one_mul]
  -- Young's inequality and its equality case, specialized
  have young : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      a * b - (p + 1)⁻¹ * a ^ (p + 1) ≤ (p⁻¹ + 1)⁻¹ * b ^ (p⁻¹ + 1) := by
    intro a b ha hb
    have := young_aux a b ha hb
    linarith
  have young_eq : ∀ s : ℝ, 0 ≤ s →
      s * s ^ p⁻¹ - (p + 1)⁻¹ * (s ^ p⁻¹) ^ (p + 1) = (p⁻¹ + 1)⁻¹ * s ^ (p⁻¹ + 1) := by
    intro s hs
    rw [← Real.rpow_mul hs]
    have h1 : p⁻¹ * (p + 1) = 1 + p⁻¹ := by field_simp
    have hpos : (0 : ℝ) < 1 + p⁻¹ := by positivity
    rw [h1, add_comm p⁻¹ 1, Real.rpow_one_add' hs hpos.ne']
    field_simp
    ring
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · -- conjugate of fp p is gp p⁻¹
    rcases le_or_gt 0 (v 0) with hv | hv
    · rw [hg_nn p⁻¹ hq v hv]
      refine conj_eq _ _ _ (fun x => ?_) (EuclideanSpace.single 0 ((v 0) ^ p⁻¹)) ?_
      · rcases le_or_gt 0 (x 0) with hx | hx
        · rw [hf_nn p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have := young (x 0) (v 0) hx hv
          linarith [mul_comm (v 0) (x 0)]
        · rw [hf_neg p hp_pos x hx]
          simp
      · have h0 : (EuclideanSpace.single (0 : Fin 1) ((v 0) ^ p⁻¹)) 0 ≥ 0 := by
          rw [hsingle]; exact Real.rpow_nonneg hv _
        rw [hf_nn p hp_pos _ h0, hinner, hsingle, ← EReal.coe_sub, young_eq (v 0) hv]
    · rw [hg_neg p⁻¹ hq v hv]
      refine conj_eq _ _ _ (fun x => ?_) 0 ?_
      · rcases le_or_gt 0 (x 0) with hx | hx
        · rw [hf_nn p hp_pos x hx, hinner, ← EReal.coe_sub, ← EReal.coe_zero,
            EReal.coe_le_coe_iff]
          have h1 : v 0 * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv.le hx
          have h2 : 0 ≤ (p + 1)⁻¹ * x 0 ^ (p + 1) := by
            have := Real.rpow_nonneg hx (p + 1)
            positivity
          linarith
        · rw [hf_neg p hp_pos x hx]
          simp
      · have h0 : (0 : EuclideanSpace ℝ (Fin 1)) 0 ≥ 0 := by simp
        rw [hf_nn p hp_pos _ h0, hinner]
        simp [Real.zero_rpow (by linarith : p + 1 ≠ 0)]
  · -- conjugate of gp p is fp p⁻¹
    rcases le_or_gt 0 (v 0) with hv | hv
    · rw [hf_nn p⁻¹ hq v hv]
      refine conj_eq _ _ _ (fun x => ?_) (EuclideanSpace.single 0 ((v 0) ^ p⁻¹)) ?_
      · rcases le_or_gt 0 (x 0) with hx | hx
        · rw [hg_nn p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have := young (x 0) (v 0) hx hv
          linarith [mul_comm (v 0) (x 0)]
        · rw [hg_neg p hp_pos x hx, hinner, ← EReal.coe_zero, ← EReal.coe_sub,
            EReal.coe_le_coe_iff]
          have h1 : v 0 * x 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv hx.le
          have h2 : 0 ≤ (p⁻¹ + 1)⁻¹ * v 0 ^ (p⁻¹ + 1) := by
            have := Real.rpow_nonneg hv (p⁻¹ + 1)
            positivity
          linarith
      · have h0 : (EuclideanSpace.single (0 : Fin 1) ((v 0) ^ p⁻¹)) 0 ≥ 0 := by
          rw [hsingle]; exact Real.rpow_nonneg hv _
        rw [hg_nn p hp_pos _ h0, hinner, hsingle, ← EReal.coe_sub, young_eq (v 0) hv]
    · rw [hf_neg p⁻¹ hq v hv]
      refine conj_top _ _ (fun M => ⟨EuclideanSpace.single 0 ((|M| + 1) / v 0), ?_⟩)
      have h0 : (EuclideanSpace.single (0 : Fin 1) ((|M| + 1) / v 0)) 0 < 0 := by
        rw [hsingle]
        exact div_neg_of_pos_of_neg (by positivity) hv
      rw [hg_neg p hp_pos _ h0, hinner, hsingle, ← EReal.coe_zero, ← EReal.coe_sub,
        EReal.coe_lt_coe_iff]
      have h1 : v 0 * ((|M| + 1) / v 0) = |M| + 1 := by
        have := hv.ne
        field_simp
      rw [h1]
      linarith [le_abs_self M]
  · -- conjugate of hp p is hp p⁻¹
    rcases le_or_gt 0 (v 0) with hv | hv
    · rw [hh_nn p⁻¹ hq v hv]
      refine conj_eq _ _ _ (fun x => ?_) (EuclideanSpace.single 0 ((v 0) ^ p⁻¹)) ?_
      · rcases le_or_gt 0 (x 0) with hx | hx
        · rw [hh_nn p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have := young (x 0) (v 0) hx hv
          linarith [mul_comm (v 0) (x 0)]
        · rw [hh_neg p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have h1 : v 0 * x 0 ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hv hx.le
          have h2 : 0 ≤ (p⁻¹ + 1)⁻¹ * v 0 ^ (p⁻¹ + 1) := by
            have := Real.rpow_nonneg hv (p⁻¹ + 1)
            positivity
          have h3 : 0 ≤ (p + 1)⁻¹ * (-x 0) ^ (p + 1) := by
            have := Real.rpow_nonneg (by linarith : (0 : ℝ) ≤ -x 0) (p + 1)
            positivity
          linarith
      · have h0 : (EuclideanSpace.single (0 : Fin 1) ((v 0) ^ p⁻¹)) 0 ≥ 0 := by
          rw [hsingle]; exact Real.rpow_nonneg hv _
        rw [hh_nn p hp_pos _ h0, hinner, hsingle, ← EReal.coe_sub, young_eq (v 0) hv]
    · have hv' : 0 ≤ -v 0 := by linarith
      rw [hh_neg p⁻¹ hq v hv]
      refine conj_eq _ _ _ (fun x => ?_)
        (EuclideanSpace.single 0 (-((-v 0) ^ p⁻¹))) ?_
      · rcases le_or_gt 0 (x 0) with hx | hx
        · rw [hh_nn p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have h1 : v 0 * x 0 ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hv.le hx
          have h2 : 0 ≤ (p⁻¹ + 1)⁻¹ * (-v 0) ^ (p⁻¹ + 1) := by
            have := Real.rpow_nonneg hv' (p⁻¹ + 1)
            positivity
          have h3 : 0 ≤ (p + 1)⁻¹ * x 0 ^ (p + 1) := by
            have := Real.rpow_nonneg hx (p + 1)
            positivity
          linarith
        · rw [hh_neg p hp_pos x hx, hinner, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have := young (-x 0) (-v 0) (by linarith) hv'
          have h1 : v 0 * x 0 = -x 0 * -v 0 := by ring
          linarith
      · have h0 : (EuclideanSpace.single (0 : Fin 1) (-((-v 0) ^ p⁻¹))) 0 < 0 := by
          rw [hsingle, neg_lt_zero]
          exact Real.rpow_pos_of_pos (by linarith) _
        rw [hh_neg p hp_pos _ h0, hinner, hsingle, neg_neg, ← EReal.coe_sub,
          ← young_eq (-v 0) hv']
        congr 2
        ring

end FCA_chap_E_ex6
