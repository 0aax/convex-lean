import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_2_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_2_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_2_6`, so the main result is `FCA_chap_C_1_2_6.FCA_chap_C_1_2_6`.
-/

namespace FCA_chap_C_1_2_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_2_6
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let g : E → EReal := fun x => gaugeFun C x
  (IsCompact C) ↔ (∀ x, x ≠ 0 → g x > 0) := by
  intro g
  show IsCompact C ↔ ∀ x, x ≠ 0 → gaugeFun C x > 0
  constructor
  · intro hK x hx
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hK.isBounded
    have hR'pos : (0 : ℝ) < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hbound : ∀ y ∈ C, ‖y‖ ≤ max R 1 := fun y hy => (hR y hy).trans (le_max_left _ _)
    have hxpos : 0 < ‖x‖ / max R 1 := div_pos (norm_pos_iff.mpr hx) hR'pos
    have hle : ((‖x‖ / max R 1 : ℝ) : EReal) ≤ gaugeFun C x := by
      unfold gaugeFun
      apply le_sInf
      rintro l ⟨l', rfl, hl', y, hy, rfl⟩
      apply EReal.coe_le_coe_iff.mpr
      rw [div_le_iff₀ hR'pos, norm_smul, Real.norm_eq_abs, abs_of_pos hl']
      exact mul_le_mul_of_nonneg_left (hbound y hy) hl'.le
    exact lt_of_lt_of_le (EReal.coe_pos.mpr hxpos) hle
  · intro hg
    refine Metric.isCompact_of_isClosed_isBounded hC_closed ?_
    by_contra hunb
    have hex : ∀ r : ℝ, ∃ x ∈ C, r < ‖x‖ := by
      intro r
      by_contra h
      push_neg at h
      exact hunb (isBounded_iff_forall_norm_le.mpr ⟨r, h⟩)
    let t : ℕ → Set E := fun n => Metric.sphere (0:E) 1 ∩ {d | (n : ℝ) • d ∈ C}
    have htd : ∀ i, t (i + 1) ⊆ t i := by
      rintro i d ⟨hd1, hd2⟩
      refine ⟨hd1, ?_⟩
      simp only [Set.mem_setOf_eq] at hd2 ⊢
      have hi : (0:ℝ) < (i:ℝ) + 1 := by positivity
      have : (i : ℝ) • d = ((i : ℝ) / ((i:ℝ) + 1)) • (((i + 1 : ℕ) : ℝ) • d) := by
        rw [smul_smul]; push_cast; congr 1; field_simp
      rw [this]
      apply hC_convex.smul_mem_of_zero_mem hC_origin hd2
      constructor
      · positivity
      · rw [div_le_one hi]; linarith
    have htn : ∀ i, (t i).Nonempty := by
      intro i
      obtain ⟨x, hxC, hx⟩ := hex i
      have hxpos : 0 < ‖x‖ := lt_of_le_of_lt (Nat.cast_nonneg i) hx
      refine ⟨‖x‖⁻¹ • x, ?_, ?_⟩
      · simp [norm_smul, hxpos.ne']
      · simp only [Set.mem_setOf_eq, smul_smul]
        apply hC_convex.smul_mem_of_zero_mem hC_origin hxC
        constructor
        · positivity
        · rw [← div_eq_mul_inv, div_le_one hxpos]; exact hx.le
    have ht0 : IsCompact (t 0) := by
      have : t 0 = Metric.sphere (0:E) 1 := by
        ext d; simp [t, hC_origin]
      rw [this]; exact isCompact_sphere 0 1
    have htcl : ∀ i, IsClosed (t i) := by
      intro i
      exact Metric.isClosed_sphere.inter (hC_closed.preimage (continuous_const_smul _))
    obtain ⟨d, hd⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed t htd htn ht0 htcl
    rw [Set.mem_iInter] at hd
    have hd1 : ‖d‖ = 1 := by simpa using (hd 0).1
    have hdne : d ≠ 0 := by intro h; rw [h, norm_zero] at hd1; exact zero_ne_one hd1
    have hdC : ∀ n : ℕ, (n : ℝ) • d ∈ C := fun n => (hd n).2
    have hgd := hg d hdne
    have hle0 : gaugeFun C d ≤ 0 := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨r, hr0, hrg⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hr0' : (0:ℝ) < r := by exact_mod_cast hr0
      have hler : gaugeFun C d ≤ r := by
        unfold gaugeFun
        apply sInf_le
        refine ⟨r, rfl, hr0', r⁻¹ • d, ?_, ?_⟩
        · obtain ⟨n, hn⟩ := exists_nat_ge r⁻¹
          have hnpos : (0:ℝ) < n := lt_of_lt_of_le (inv_pos.mpr hr0') hn
          have : r⁻¹ • d = (r⁻¹ / n) • ((n:ℝ) • d) := by
            rw [smul_smul]; congr 1; field_simp
          rw [this]
          apply hC_convex.smul_mem_of_zero_mem hC_origin (hdC n)
          constructor
          · positivity
          · rw [div_le_one hnpos]; exact hn
        · rw [smul_smul, mul_inv_cancel₀ hr0'.ne', one_smul]
      exact absurd (lt_of_le_of_lt hler hrg) (lt_irrefl _)
    exact absurd (lt_of_le_of_lt hle0 hgd) (lt_irrefl _)

end FCA_chap_C_1_2_6
