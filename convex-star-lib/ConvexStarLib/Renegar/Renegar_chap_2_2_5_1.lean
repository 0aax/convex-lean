import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_5_1`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_5_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_5_1`, so the main result is `Renegar_chap_2_2_5_1.Renegar_chap_2_2_5_1`.
-/

namespace Renegar_chap_2_2_5_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem Renegar_chap_2_2_5_1 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (hf_1 : ∀ x ∈ Df, localBall f x x 1 ⊆ Df ∧
    (∀ y ∈ localBall f x x 1, ∀ v ≠ 0,
      (localNorm f x v)⁻¹ * (localNorm f y v) ≤
      (1 - (localNorm f x (y - x)))⁻¹)) :
  ∀ x ∈ Df, localBall f x x 1 ⊆ Df ∧
    (∀ y ∈ localBall f x x 1, ∀ v ≠ 0,
    1 - (localNorm f x (y - x)) ≤ (localNorm f x v)⁻¹ * (localNorm f y v)) := by
  -- homogeneity of the local norm
  have hscale : ∀ z : E, ∀ c : ℝ, ∀ w : E, localNorm f z (c • w) = |c| * localNorm f z w := by
    intro z c w
    simp only [localNorm, localInnerProd, map_smul, real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg c), Real.sqrt_mul_self_eq_abs]
  have hnonneg : ∀ z w : E, 0 ≤ localNorm f z w := fun z w => Real.sqrt_nonneg _
  have hpos : ∀ z ∈ Df, ∀ w ≠ 0, 0 < localNorm f z w := by
    intro z hz w hw
    exact Real.sqrt_pos.mpr (h_Df_pd z hz w hw)
  have hzero : ∀ z : E, localNorm f z 0 = 0 := by
    intro z
    simp [localNorm, localInnerProd]
  intro x hx
  refine ⟨(hf_1 x hx).1, ?_⟩
  intro y hy v hv
  have hAx : 0 < localNorm f x v := hpos x hx v hv
  by_cases hyx : y = x
  · subst hyx
    rw [sub_self, hzero, sub_zero, inv_mul_cancel₀ hAx.ne']
  set d := y - x with hd_def
  have hd : d ≠ 0 := sub_ne_zero.mpr hyx
  set r := localNorm f x d with hr_def
  have hr0 : 0 < r := hpos x hx d hd
  have hr1 : r < 1 := hy
  -- points on the segment from `x` to `y`
  set p : ℝ → E := fun t => x + t • d with hp_def
  have hp_norm : ∀ t, localNorm f x (p t - x) = |t| * r := by
    intro t
    simp only [hp_def, add_sub_cancel_left]
    exact hscale x t d
  have hp_mem : ∀ t, 0 ≤ t → t ≤ 1 → p t ∈ localBall f x x 1 := by
    intro t ht0 ht1
    show localNorm f x (p t - x) < 1
    rw [hp_norm, abs_of_nonneg ht0]
    have := mul_le_mul_of_nonneg_right ht1 hr0.le
    linarith
  have hp_Df : ∀ t, 0 ≤ t → t ≤ 1 → p t ∈ Df :=
    fun t ht0 ht1 => (hf_1 x hx).1 (hp_mem t ht0 ht1)
  -- the upper bound at `x`, applied to the direction `d`
  have hd_bound : ∀ t, 0 ≤ t → t ≤ 1 → localNorm f (p t) d * (1 - t * r) ≤ r := by
    intro t ht0 ht1
    have h := (hf_1 x hx).2 (p t) (hp_mem t ht0 ht1) d hd
    rw [hp_norm, abs_of_nonneg ht0] at h
    have h1 : 0 < 1 - t * r := by
      have := mul_le_mul_of_nonneg_right ht1 hr0.le
      linarith
    rw [inv_mul_le_iff₀ hr0] at h
    calc localNorm f (p t) d * (1 - t * r) ≤ r * (1 - t * r)⁻¹ * (1 - t * r) := by gcongr
      _ = r := by rw [mul_assoc, inv_mul_cancel₀ h1.ne', mul_one]
  have hp0 : p 0 = x := by simp [hp_def]
  have hp1 : p 1 = y := by simp [hp_def, hd_def]
  have hp_sub : ∀ s t : ℝ, p s - p t = (s - t) • d := by
    intro s t
    simp only [hp_def]
    rw [sub_smul]
    abel
  -- the key discrete estimate, obtained by subdividing the segment into `N` pieces
  have key : ∀ N : ℕ, 0 < N → ((N:ℝ) + 1) * r < N →
      localNorm f x v * (N - (N + 1) * r) ≤ localNorm f y v * (N - r) := by
    intro N hN hNr
    have hNpos : (0:ℝ) < N := by exact_mod_cast hN
    set a : ℕ → ℝ := fun k => localNorm f (p ((k:ℝ) / N)) v / (N - ((k:ℝ) + 1) * r)
      with ha_def
    have hstep : ∀ k : ℕ, k < N → a k ≤ a (k + 1) := by
      intro k hk
      have hkN : (k:ℝ) + 1 ≤ N := by exact_mod_cast hk
      have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
      set s : ℝ := (k:ℝ) / N with hs_def
      set t : ℝ := ((k:ℝ) + 1) / N with ht_def
      have hs0 : 0 ≤ s := by positivity
      have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hNpos]; linarith
      have ht0 : 0 ≤ t := by positivity
      have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hNpos]; linarith
      have hptDf := hp_Df t ht0 ht1
      have hkr : ((k:ℝ) + 1) * r ≤ N * r := mul_le_mul_of_nonneg_right hkN hr0.le
      have hM1 : 0 < (N:ℝ) - ((k:ℝ) + 1) * r := by linarith
      have hM2 : 0 < (N:ℝ) - ((k:ℝ) + 1 + 1) * r := by linarith
      -- distance from `p t` to `p s` in the local norm at `p t`
      have hdist : localNorm f (p t) (p s - p t) = localNorm f (p t) d / N := by
        rw [hp_sub, hscale]
        have : s - t = -(1 / (N:ℝ)) := by
          rw [hs_def, ht_def]; field_simp; ring
        rw [this, abs_neg, abs_of_pos (by positivity)]
        ring
      have htr : t * r * N = ((k:ℝ) + 1) * r := by
        rw [ht_def]; field_simp
      have hσ : localNorm f (p t) (p s - p t) * ((N:ℝ) - ((k:ℝ) + 1) * r) ≤ r := by
        rw [hdist]
        have : localNorm f (p t) d / N * ((N:ℝ) - ((k:ℝ) + 1) * r)
            = localNorm f (p t) d * (1 - t * r) := by
          rw [← htr]; field_simp
        rw [this]; exact hd_bound t ht0 ht1
      have hσ0 := hnonneg (p t) (p s - p t)
      have hσ1 : localNorm f (p t) (p s - p t) < 1 := by
        by_contra hcon
        push_neg at hcon
        have := mul_le_mul_of_nonneg_right hcon hM1.le
        linarith
      have h := (hf_1 (p t) hptDf).2 (p s) hσ1 v hv
      have hb := hpos (p t) hptDf v hv
      have ha0 := hnonneg (p s) v
      rw [inv_mul_le_iff₀ hb] at h
      have h1σ : 0 < 1 - localNorm f (p t) (p s - p t) := by linarith
      have h' : localNorm f (p s) v * (1 - localNorm f (p t) (p s - p t)) ≤
          localNorm f (p t) v := by
        calc localNorm f (p s) v * (1 - localNorm f (p t) (p s - p t))
            ≤ localNorm f (p t) v * (1 - localNorm f (p t) (p s - p t))⁻¹ *
                (1 - localNorm f (p t) (p s - p t)) := by gcongr
          _ = localNorm f (p t) v := by rw [mul_assoc, inv_mul_cancel₀ h1σ.ne', mul_one]
      show localNorm f (p ((k:ℝ) / N)) v / (N - ((k:ℝ) + 1) * r) ≤
        localNorm f (p (((k + 1 : ℕ) : ℝ) / N)) v / (N - (((k + 1 : ℕ) : ℝ) + 1) * r)
      rw [Nat.cast_succ, ← hs_def, ← ht_def, div_le_div_iff₀ hM1 hM2]
      have e1 := mul_le_mul_of_nonneg_left hσ ha0
      have e2 := mul_le_mul_of_nonneg_left h' hM1.le
      linarith
    have hmono : ∀ k : ℕ, k ≤ N → a 0 ≤ a k := by
      intro k
      induction k with
      | zero => intro _; exact le_refl _
      | succ k ih =>
        intro hk
        exact le_trans (ih (Nat.le_of_succ_le hk)) (hstep k (Nat.lt_of_succ_le hk))
    have h0N := hmono N le_rfl
    simp only [ha_def, Nat.cast_zero, zero_div, zero_add, one_mul] at h0N
    rw [div_self hNpos.ne', hp0, hp1] at h0N
    have hM : 0 < (N:ℝ) - r := by
      have := mul_nonneg hNpos.le hr0.le
      linarith
    rw [div_le_div_iff₀ hM (by linarith)] at h0N
    linarith
  -- pass to the limit `N → ∞`
  have hAy : 0 < localNorm f y v := hpos y ((hf_1 x hx).1 hy) v hv
  rw [le_inv_mul_iff₀ hAx]
  by_contra hcon
  push_neg at hcon
  have h1r : 0 < 1 - r := by linarith
  have hgap : 0 < localNorm f x v * (1 - r) - localNorm f y v := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt
    (localNorm f x v / (localNorm f x v * (1 - r) - localNorm f y v) + 1 / (1 - r))
  have hA : 0 < localNorm f x v / (localNorm f x v * (1 - r) - localNorm f y v) := by
    positivity
  have hB : 1 < 1 / (1 - r) := by rw [lt_div_iff₀ h1r]; linarith
  have hNnat : 0 < N := by exact_mod_cast (show (0:ℝ) < N by linarith)
  have hNr : ((N:ℝ) + 1) * r < N := by
    have : 1 / (1 - r) < N := by linarith
    rw [div_lt_iff₀ h1r] at this
    linarith
  have hk := key N hNnat hNr
  have hlt : localNorm f x v / (localNorm f x v * (1 - r) - localNorm f y v) < N := by linarith
  rw [div_lt_iff₀ hgap] at hlt
  have e1 := mul_pos hAx h1r
  have e2 := mul_pos hAy hr0
  linarith

end Renegar_chap_2_2_5_1
