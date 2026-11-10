import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_1_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_1_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_1_6`, so the main result is `FCA_chap_B_1_1_6.FCA_chap_B_1_1_6`.
-/

namespace FCA_chap_B_1_1_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_1_1_6
  (f : E → EReal)
  (hf_nonemptyDomain : ∃ x, f x < ⊤)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  List.TFAE [
    (∀ (x y : E), ∀ (t : ℝ), 0 ≤ t ∧ t ≤ 1 →
      f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y),
    Convex ℝ (epigraph f),
    Convex ℝ (strictEpigraph f)
  ] := by
  -- `1 - ↑t` in `EReal` is the coercion of the real number `1 - t`
  have hsub : ∀ t : ℝ, (1 : EReal) - (t : EReal) = ((1 - t : ℝ) : EReal) := fun t => by
    rw [EReal.coe_sub, EReal.coe_one]
  -- a function value which is not `⊤` is a real number
  have hreal : ∀ z, f z ≠ ⊤ → f z = ((f z).toReal : EReal) := fun z hz =>
    (EReal.coe_toReal hz (f_ne_bot z).ne').symm
  tfae_have 1 → 2 := by
    intro h p hp q hq a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
    obtain rfl : b = 1 - a := by linarith
    have h1 := h p.1 q.1 a ⟨ha, by linarith⟩
    rw [hsub] at h1
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    calc f (a • p.1 + (1 - a) • q.1)
        ≤ (a : EReal) * f p.1 + ((1 - a : ℝ) : EReal) * f q.1 := h1
      _ ≤ (a : EReal) * (p.2 : EReal) + ((1 - a : ℝ) : EReal) * (q.2 : EReal) := by
        apply _root_.add_le_add
        · exact mul_le_mul_of_nonneg_left hp (EReal.coe_nonneg.mpr ha)
        · exact mul_le_mul_of_nonneg_left hq (EReal.coe_nonneg.mpr hb)
      _ = ((a * p.2 + (1 - a) * q.2 : ℝ) : EReal) := by
        rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]
  tfae_have 2 → 3 := by
    intro h p hp q hq a b ha hb hab
    simp only [strictEpigraph, Set.mem_setOf_eq] at hp hq ⊢
    have hpx : f p.1 = ((f p.1).toReal : EReal) := hreal _ (hp.trans (EReal.coe_lt_top _)).ne
    have hqx : f q.1 = ((f q.1).toReal : EReal) := hreal _ (hq.trans (EReal.coe_lt_top _)).ne
    have hmem := h (x := (p.1, (f p.1).toReal))
      (by simp only [epigraph, Set.mem_setOf_eq]; exact hpx.le)
      (y := (q.1, (f q.1).toReal))
      (by simp only [epigraph, Set.mem_setOf_eq]; exact hqx.le) ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
      Prod.smul_snd, smul_eq_mul] at hmem
    simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    refine lt_of_le_of_lt hmem ?_
    rw [hpx, EReal.coe_lt_coe_iff] at hp
    rw [hqx, EReal.coe_lt_coe_iff] at hq
    rw [EReal.coe_lt_coe_iff]
    rcases ha.lt_or_eq with ha' | ha'
    · have := mul_lt_mul_of_pos_left hp ha'
      have := mul_le_mul_of_nonneg_left hq.le hb
      linarith
    · subst ha'
      obtain rfl : b = 1 := by linarith
      linarith
  tfae_have 3 → 1 := by
    intro h x y t ⟨ht0, ht1⟩
    rw [hsub]
    rcases ht0.lt_or_eq with ht0' | rfl
    swap
    · simp
    rcases ht1.lt_or_eq with ht1' | rfl
    swap
    · simp
    have hpos : 0 < 1 - t := by linarith
    by_cases hxt : f x = ⊤
    · rw [hxt, EReal.coe_mul_top_of_pos ht0', EReal.top_add_of_ne_bot]
      · exact le_top
      · rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (f_ne_bot y).ne', Or.inl (EReal.coe_ne_top _),
          Or.inl (EReal.coe_nonneg.mpr hpos.le)⟩
    by_cases hyt : f y = ⊤
    · rw [hyt, EReal.coe_mul_top_of_pos hpos, EReal.add_top_of_ne_bot]
      · exact le_top
      · rw [EReal.mul_ne_bot]
        refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr (f_ne_bot x).ne', Or.inl (EReal.coe_ne_top _),
          Or.inl (EReal.coe_nonneg.mpr ht0'.le)⟩
    rw [hreal x hxt, hreal y hyt]
    set u := (f x).toReal with hu
    set v := (f y).toReal with hv
    rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    apply le_of_forall_gt_imp_ge_of_dense
    intro c hc
    induction c using EReal.rec with
    | bot => exact absurd hc (not_lt_bot)
    | top => exact le_top
    | coe c =>
      rw [EReal.coe_lt_coe_iff] at hc
      set δ := c - (t * u + (1 - t) * v) with hδ
      have hδpos : 0 < δ := by rw [hδ]; linarith
      have hmem := h (x := (x, u + δ))
        (by
          simp only [strictEpigraph, Set.mem_setOf_eq]
          rw [hreal x hxt, EReal.coe_lt_coe_iff]
          linarith)
        (y := (y, v + δ))
        (by
          simp only [strictEpigraph, Set.mem_setOf_eq]
          rw [hreal y hyt, EReal.coe_lt_coe_iff]
          linarith)
        ht0'.le hpos.le (by ring)
      simp only [strictEpigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
        Prod.smul_snd, smul_eq_mul] at hmem
      refine hmem.le.trans (le_of_eq ?_)
      congr 1
      rw [hδ]
      ring
  tfae_finish

end FCA_chap_B_1_1_6
