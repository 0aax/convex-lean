import ConvexStarLib.Defs

/-!
# `Duchi_Q5_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q5_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q5_1`, so the main result is `Duchi_Q5_1.Duchi_Q5_1`.
-/

namespace Duchi_Q5_1

namespace PLAux

open MeasureTheory Set
open scoped ENNReal

/-- Prékopa–Leindler property, ENNReal-valued, measurable functions. -/
def PLProp (X : Type*) [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    (μ : Measure X) (t : ℝ) : Prop :=
  ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) →
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ x, g x ∂μ) ^ (1 - t) ≤ ∫⁻ x, h x ∂μ

theorem bm_aux_le_iSup_Iic {A : Set ℝ} (hA : MeasurableSet A) :
    volume A ≤ ⨆ a : A, volume (A ∩ Iic (a : ℝ)) := by
  rw [hA.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K hKA => iSup_le fun hK => ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hmem : sSup K ∈ K := hK.sSup_mem hne
    refine le_trans ?_ (le_iSup (fun a : A => volume (A ∩ Iic (a : ℝ))) ⟨sSup K, hKA hmem⟩)
    exact measure_mono fun x hx => ⟨hKA hx, le_csSup hK.bddAbove hx⟩

theorem bm_aux_le_iSup_Ici {B : Set ℝ} (hB : MeasurableSet B) :
    volume B ≤ ⨆ b : B, volume (B ∩ Ici (b : ℝ)) := by
  rw [hB.measure_eq_iSup_isCompact]
  refine iSup₂_le fun K hKB => iSup_le fun hK => ?_
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simp
  · have hmem : sInf K ∈ K := hK.sInf_mem hne
    refine le_trans ?_ (le_iSup (fun b : B => volume (B ∩ Ici (b : ℝ))) ⟨sInf K, hKB hmem⟩)
    exact measure_mono fun x hx => ⟨hKB hx, csInf_le hK.bddBelow hx⟩

theorem bm_aux_pair {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A B C : Set ℝ}
    (hC : ∀ a ∈ A, ∀ b ∈ B, t * a + (1 - t) * b ∈ C) {a0 b0 : ℝ} (ha0 : a0 ∈ A) (hb0 : b0 ∈ B) :
    ENNReal.ofReal t * volume (A ∩ Iic a0) + ENNReal.ofReal (1 - t) * volume (B ∩ Ici b0)
      ≤ volume C := by
  set p := t * a0 + (1 - t) * b0 with hp
  have h1 : ENNReal.ofReal t * volume (A ∩ Iic a0) ≤ volume (C ∩ Iic p) := by
    have := Measure.addHaar_image_homothety (volume : Measure ℝ) b0 t (A ∩ Iic a0)
    rw [Module.finrank_self, pow_one, abs_of_pos ht0] at this
    rw [← this]
    apply measure_mono
    rintro z ⟨x, ⟨hxA, hxa⟩, rfl⟩
    have hz : AffineMap.homothety b0 t x = t * x + (1 - t) * b0 := by
      simp [AffineMap.homothety_apply]; ring
    rw [hz]
    refine ⟨hC x hxA b0 hb0, ?_⟩
    simp only [mem_Iic] at hxa ⊢
    nlinarith
  have h2 : ENNReal.ofReal (1 - t) * volume (B ∩ Ici b0) ≤ volume (C \ Iic p) := by
    have := Measure.addHaar_image_homothety (volume : Measure ℝ) a0 (1 - t) (B ∩ Ici b0)
    rw [Module.finrank_self, pow_one, abs_of_pos (by linarith)] at this
    rw [← this]
    calc volume (AffineMap.homothety a0 (1 - t) '' (B ∩ Ici b0))
        ≤ volume ((C \ Iic p) ∪ {p}) := by
          apply measure_mono
          rintro z ⟨y, ⟨hyB, hyb⟩, rfl⟩
          have hz : AffineMap.homothety a0 (1 - t) y = t * a0 + (1 - t) * y := by
            simp [AffineMap.homothety_apply]; ring
          rw [hz]
          simp only [mem_Ici] at hyb
          rcases eq_or_lt_of_le hyb with h | h
          · right; simp [hp, h]
          · left
            refine ⟨hC a0 ha0 y hyB, ?_⟩
            simp only [mem_Iic, not_le]
            nlinarith
      _ ≤ volume (C \ Iic p) + volume ({p} : Set ℝ) := measure_union_le _ _
      _ = volume (C \ Iic p) := by simp
  calc ENNReal.ofReal t * volume (A ∩ Iic a0) + ENNReal.ofReal (1 - t) * volume (B ∩ Ici b0)
      ≤ volume (C ∩ Iic p) + volume (C \ Iic p) := add_le_add h1 h2
    _ = volume C := measure_inter_add_diff C measurableSet_Iic

/-- 1D Brunn–Minkowski. -/
theorem bm_1d {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hA' : A.Nonempty) (hB' : B.Nonempty)
    (hC : ∀ a ∈ A, ∀ b ∈ B, t * a + (1 - t) * b ∈ C) :
    ENNReal.ofReal t * volume A + ENNReal.ofReal (1 - t) * volume B ≤ volume C := by
  haveI : Nonempty A := hA'.to_subtype
  haveI : Nonempty B := hB'.to_subtype
  calc ENNReal.ofReal t * volume A + ENNReal.ofReal (1 - t) * volume B
      ≤ ENNReal.ofReal t * (⨆ a : A, volume (A ∩ Iic (a : ℝ)))
        + ENNReal.ofReal (1 - t) * (⨆ b : B, volume (B ∩ Ici (b : ℝ))) := by
        gcongr
        · exact bm_aux_le_iSup_Iic hA
        · exact bm_aux_le_iSup_Ici hB
    _ ≤ volume C := by
        rw [ENNReal.mul_iSup, ENNReal.mul_iSup]
        exact ENNReal.iSup_add_iSup_le fun a b => bm_aux_pair ht0 ht1 hC a.2 b.2

theorem lc_aux_vol (a : ℝ≥0∞) :
    volume ({r : ℝ | ENNReal.ofReal r < a} ∩ Ioi (0:ℝ)) = a := by
  rcases eq_or_ne a ∞ with rfl | ha
  · simp
  · have : {r : ℝ | ENNReal.ofReal r < a} ∩ Ioi (0:ℝ) = Ioo 0 a.toReal := by
      ext r
      simp only [mem_inter_iff, mem_setOf_eq, mem_Ioi, mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le ha).1 h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h1.le ha).2 h2, h1⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

/-- Layer cake for ENNReal-valued functions. -/
theorem layercake {α : Type*} [MeasurableSpace α] (μ : Measure α) [SFinite μ]
    (f : α → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x ∂μ = ∫⁻ r in Ioi (0:ℝ), μ {x | ENNReal.ofReal r < f x} := by
  set g : α → ℝ → ℝ≥0∞ := fun x r => {p : α × ℝ | ENNReal.ofReal p.2 < f p.1}.indicator 1 (x, r)
    with hg_def
  have hS : MeasurableSet {p : α × ℝ | ENNReal.ofReal p.2 < f p.1} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_snd) (hf.comp measurable_fst)
  have hg : Measurable (Function.uncurry g) := by
    have : Function.uncurry g = {p : α × ℝ | ENNReal.ofReal p.2 < f p.1}.indicator 1 := by
      ext ⟨x, r⟩; rfl
    rw [this]
    exact measurable_one.indicator hS
  have h1 : ∀ x, ∫⁻ r in Ioi (0:ℝ), g x r = f x := by
    intro x
    have : (fun r => g x r) = {r : ℝ | ENNReal.ofReal r < f x}.indicator 1 := by
      ext r
      simp only [hg_def, indicator_apply, mem_setOf_eq, Pi.one_apply]
    rw [this, lintegral_indicator_one
      (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      Measure.restrict_apply (measurableSet_lt ENNReal.measurable_ofReal measurable_const),
      lc_aux_vol]
  have h2 : ∀ r, ∫⁻ x, g x r ∂μ = μ {x | ENNReal.ofReal r < f x} := by
    intro r
    have : (fun x => g x r) = {x : α | ENNReal.ofReal r < f x}.indicator 1 := by
      ext x
      simp only [hg_def, indicator_apply, mem_setOf_eq, Pi.one_apply]
    rw [this, lintegral_indicator_one (measurableSet_lt measurable_const hf)]
  calc ∫⁻ x, f x ∂μ = ∫⁻ x, (∫⁻ r in Ioi (0:ℝ), g x r) ∂μ := by simp_rw [h1]
    _ = ∫⁻ r in Ioi (0:ℝ), ∫⁻ x, g x r ∂μ := lintegral_lintegral_swap hg.aemeasurable
    _ = _ := by simp_rw [h2]

/-- min ≤ weighted geometric mean -/
theorem min_le_gm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a b : ℝ≥0∞) :
    min a b ≤ a ^ t * b ^ (1 - t) := by
  calc min a b = (min a b) ^ (t + (1 - t)) := by rw [add_sub_cancel, ENNReal.rpow_one]
    _ = (min a b) ^ t * (min a b) ^ (1 - t) :=
        ENNReal.rpow_add_of_nonneg t (1 - t) ht0.le (by linarith)
    _ ≤ a ^ t * b ^ (1 - t) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left a b) ht0.le)
          (ENNReal.rpow_le_rpow (min_le_right a b) (by linarith))

/-- weighted AM-GM in ENNReal -/
theorem amgm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (a b : ℝ≥0∞) :
    a ^ t * b ^ (1 - t) ≤ ENNReal.ofReal t * a + ENNReal.ofReal (1 - t) * b := by
  have ht1' : 0 < 1 - t := by linarith
  rcases eq_or_ne a ⊤ with rfl | ha
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ht0).ne', top_add]
    exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 ht1').ne', add_top]
    exact le_top
  lift a to NNReal using ha
  lift b to NNReal using hb
  have key := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal t)
    (Real.toNNReal (1 - t)) a b (by rw [← Real.toNNReal_add ht0.le ht1'.le]; simp)
  rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ ht1'.le] at key
  rw [← ENNReal.coe_rpow_of_nonneg _ ht0.le, ← ENNReal.coe_rpow_of_nonneg _ ht1'.le,
    ENNReal.ofReal, ENNReal.ofReal, ← ENNReal.coe_mul, ← ENNReal.coe_mul, ← ENNReal.coe_mul,
    ← ENNReal.coe_add, ENNReal.coe_le_coe]
  exact key

/-- Linear 1D PL with equal sups. -/
theorem pl_linear_1d {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfg : ⨆ x, f x = ⨆ x, g x)
    (hyp : ∀ x y, min (f x) (g y) ≤ h (t * x + (1 - t) * y)) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  have key : ∀ r : ℝ, ENNReal.ofReal t * volume {x | ENNReal.ofReal r < f x}
      + ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal r < g x}
      ≤ volume {x | ENNReal.ofReal r < h x} := by
    intro r
    by_cases hfne : {x | ENNReal.ofReal r < f x}.Nonempty
    · by_cases hgne : {x | ENNReal.ofReal r < g x}.Nonempty
      · apply bm_1d ht0 ht1 (measurableSet_lt measurable_const hf)
          (measurableSet_lt measurable_const hg) hfne hgne
        intro a ha b hb
        simp only [mem_setOf_eq] at ha hb ⊢
        exact lt_of_lt_of_le (lt_min ha hb) (hyp a b)
      · exfalso
        obtain ⟨x, hx⟩ := hfne
        apply hgne
        have : ENNReal.ofReal r < ⨆ y, g y := hfg ▸ lt_of_lt_of_le hx (le_iSup f x)
        obtain ⟨y, hy⟩ := lt_iSup_iff.mp this
        exact ⟨y, hy⟩
    · have hf0 : {x | ENNReal.ofReal r < f x} = ∅ := not_nonempty_iff_eq_empty.mp hfne
      have hg0 : {x | ENNReal.ofReal r < g x} = ∅ := by
        rw [← not_nonempty_iff_eq_empty]
        rintro ⟨y, hy⟩
        apply hfne
        have : ENNReal.ofReal r < ⨆ x, f x := hfg.symm ▸ lt_of_lt_of_le hy (le_iSup g y)
        obtain ⟨x, hx⟩ := lt_iSup_iff.mp this
        exact ⟨x, hx⟩
      simp [hf0, hg0]
  rw [show ∫⁻ x, f x = ∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < f x} from
      layercake volume f hf,
    show ∫⁻ x, g x = ∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < g x} from
      layercake volume g hg,
    show ∫⁻ x, h x = ∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < h x} from
      layercake volume h hh]
  calc ENNReal.ofReal t * (∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < f x})
        + ENNReal.ofReal (1 - t) * (∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < g x})
      ≤ (∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal t * volume {x | ENNReal.ofReal r < f x})
        + ∫⁻ r in Ioi (0:ℝ), ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal r < g x} :=
        add_le_add (lintegral_const_mul_le _ _) (lintegral_const_mul_le _ _)
    _ ≤ ∫⁻ r in Ioi (0:ℝ), (ENNReal.ofReal t * volume {x | ENNReal.ofReal r < f x}
        + ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal r < g x}) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ r in Ioi (0:ℝ), volume {x | ENNReal.ofReal r < h x} :=
        lintegral_mono (fun r => key r)

/-- 1D PL for bounded functions. -/
theorem pl_1d_bdd {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hfb : ⨆ x, f x ≠ ∞) (hgb : ⨆ x, g x ≠ ∞)
    (hyp : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ x, g x) ^ (1 - t) ≤ ∫⁻ x, h x := by
  have ht1' : 0 < 1 - t := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ⨆ x, f x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ⨆ x, g x := ⟨_, rfl⟩
  rw [← ha] at hfb
  rw [← hb] at hgb
  by_cases ha0 : a = 0
  · have hf0 : ∀ x, f x = 0 := fun x =>
      le_antisymm (by rw [← ha0, ha]; exact le_iSup f x) (zero_le _)
    have hI : ∫⁻ x, f x = 0 := by simp [hf0]
    rw [hI, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le _
  by_cases hb0 : b = 0
  · have hg0 : ∀ x, g x = 0 := fun x =>
      le_antisymm (by rw [← hb0, hb]; exact le_iSup g x) (zero_le _)
    have hI : ∫⁻ x, g x = 0 := by simp [hg0]
    rw [hI, ENNReal.zero_rpow_of_pos ht1', mul_zero]
    exact zero_le _
  have hat0 : a ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hfb).ne'
  have hattop : a ^ t ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ht0.le hfb
  have hbt0 : b ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hgb).ne'
  have hbttop : b ^ (1 - t) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ht1'.le hgb
  obtain ⟨c, hc⟩ : ∃ c, c = a ^ t * b ^ (1 - t) := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hc ▸ mul_ne_zero hat0 hbt0
  have hctop : c ≠ ∞ := hc ▸ ENNReal.mul_ne_top hattop hbttop
  have hcinv : c⁻¹ = (a ^ t)⁻¹ * (b ^ (1 - t))⁻¹ := by
    rw [hc]; exact ENNReal.mul_inv (Or.inl hat0) (Or.inl hattop)
  -- scaling identity
  have hscale : ∀ u v : ℝ≥0∞,
      (a⁻¹ * u) ^ t * (b⁻¹ * v) ^ (1 - t) = c⁻¹ * (u ^ t * v ^ (1 - t)) := by
    intro u v
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ ht1'.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hcinv]
    ring
  have key := pl_linear_1d ht0 ht1 (fun x => a⁻¹ * f x) (fun x => b⁻¹ * g x)
    (fun x => c⁻¹ * h x) (hf.const_mul _) (hg.const_mul _) (hh.const_mul _) (by
      rw [← ENNReal.mul_iSup, ← ENNReal.mul_iSup, ← ha, ← hb, ENNReal.inv_mul_cancel ha0 hfb,
        ENNReal.inv_mul_cancel hb0 hgb]) (by
      intro x y
      refine (min_le_gm ht0 ht1 _ _).trans ?_
      rw [hscale]
      dsimp only
      gcongr
      exact hyp x y)
  beta_reduce at key
  have h2 := (amgm ht0 ht1 (∫⁻ x, a⁻¹ * f x) (∫⁻ x, b⁻¹ * g x)).trans key
  rw [lintegral_const_mul _ hf, lintegral_const_mul _ hg, lintegral_const_mul _ hh,
    hscale] at h2
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 hctop)
    (ENNReal.inv_ne_top.2 hc0)).1 h2

theorem trunc_aux_iSup_min (a : ℝ≥0∞) : ⨆ N : ℕ, min a (N : ℝ≥0∞) = a := by
  refine le_antisymm (iSup_le fun N => min_le_left _ _) ?_
  rcases eq_or_ne a ∞ with rfl | ha
  · simp [ENNReal.iSup_natCast]
  · obtain ⟨N, hN⟩ := ENNReal.exists_nat_gt ha
    exact le_iSup_of_le N (le_min le_rfl hN.le)

theorem trunc_aux_iSup_rpow {s : ℝ} (hs : 0 < s) (u : ℕ → ℝ≥0∞) :
    (⨆ N, u N) ^ s = ⨆ N, u N ^ s :=
  Monotone.map_iSup_of_continuousAt (f := fun a : ℝ≥0∞ => a ^ s)
    ENNReal.continuous_rpow_const.continuousAt (ENNReal.monotone_rpow_of_nonneg hs.le)
    (by simp [ENNReal.zero_rpow_of_pos hs])

theorem trunc_aux_lintegral_iSup_min {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ⨆ N : ℕ, ∫⁻ x, min (f x) (N : ℝ≥0∞) := by
  rw [← lintegral_iSup (fun N => hf.min measurable_const)
    (fun N M hNM x => min_le_min_left _ (by exact_mod_cast hNM))]
  exact lintegral_congr fun x => (trunc_aux_iSup_min (f x)).symm

/-- 1D PL. -/
theorem pl_1d {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) : PLProp ℝ volume t := by
  intro f g h hf hg hh hyp
  have hbdd : ∀ N M : ℕ, (∫⁻ x, min (f x) (N : ℝ≥0∞)) ^ t *
      (∫⁻ x, min (g x) (M : ℝ≥0∞)) ^ (1 - t) ≤ ∫⁻ x, h x := by
    intro N M
    calc (∫⁻ x, min (f x) (N : ℝ≥0∞)) ^ t * (∫⁻ x, min (g x) (M : ℝ≥0∞)) ^ (1 - t)
        ≤ (∫⁻ x, min (f x) ((max N M : ℕ) : ℝ≥0∞)) ^ t *
            (∫⁻ x, min (g x) ((max N M : ℕ) : ℝ≥0∞)) ^ (1 - t) := by
          apply mul_le_mul'
          · apply ENNReal.rpow_le_rpow _ ht0.le
            apply lintegral_mono
            intro x
            exact min_le_min_left _ (by exact_mod_cast le_max_left N M)
          · apply ENNReal.rpow_le_rpow _ (by linarith)
            apply lintegral_mono
            intro x
            exact min_le_min_left _ (by exact_mod_cast le_max_right N M)
      _ ≤ ∫⁻ x, h x := by
          apply pl_1d_bdd ht0 ht1 _ _ h (hf.min measurable_const) (hg.min measurable_const) hh
          · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
              (iSup_le fun x => min_le_right _ _)
          · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top _)
              (iSup_le fun x => min_le_right _ _)
          · intro x y
            calc min (f x) ((max N M : ℕ) : ℝ≥0∞) ^ t * min (g y) ((max N M : ℕ) : ℝ≥0∞) ^ (1 - t)
                ≤ f x ^ t * g y ^ (1 - t) :=
                  mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ht0.le)
                    (ENNReal.rpow_le_rpow (min_le_left _ _) (by linarith))
              _ ≤ h (t • x + (1 - t) • y) := hyp x y
              _ = h (t * x + (1 - t) * y) := by simp only [smul_eq_mul]
  rw [trunc_aux_lintegral_iSup_min hf, trunc_aux_lintegral_iSup_min hg,
    trunc_aux_iSup_rpow ht0, trunc_aux_iSup_rpow (by linarith : (0:ℝ) < 1 - t), ENNReal.iSup_mul]
  refine iSup_le fun N => ?_
  rw [ENNReal.mul_iSup]
  exact iSup_le fun M => hbdd N M

theorem pl_prod {t : ℝ} {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] (μ : Measure X) (ν : Measure Y)
    [SFinite μ] [SFinite ν] (hX : PLProp X μ t) (hY : PLProp Y ν t) :
    PLProp (X × Y) (μ.prod ν) t := by
  intro f g h hf hg hh hyp
  rw [lintegral_prod f hf.aemeasurable, lintegral_prod g hg.aemeasurable,
    lintegral_prod h hh.aemeasurable]
  refine hX (fun x => ∫⁻ y, f (x, y) ∂ν) (fun x => ∫⁻ y, g (x, y) ∂ν)
    (fun x => ∫⁻ y, h (x, y) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' ?_
  intro x1 x2
  refine hY (fun y => f (x1, y)) (fun y => g (x2, y)) (fun y => h (t • x1 + (1 - t) • x2, y))
    (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
    (hh.comp measurable_prodMk_left) ?_
  intro y1 y2
  have := hyp (x1, y1) (x2, y2)
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

theorem pl_transfer {t : ℝ} {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X → Y) (he : MeasurePreserving e μ ν)
    (hlin : ∀ x y, e (t • x + (1 - t) • y) = t • e x + (1 - t) • e y)
    (hX : PLProp X μ t) : PLProp Y ν t := by
  intro f g h hf hg hh hyp
  rw [← he.lintegral_comp hf, ← he.lintegral_comp hg, ← he.lintegral_comp hh]
  refine hX (fun x => f (e x)) (fun x => g (e x)) (fun x => h (e x))
    (hf.comp he.measurable) (hg.comp he.measurable) (hh.comp he.measurable) ?_
  intro x y
  dsimp only
  rw [hlin]
  exact hyp (e x) (e y)

theorem pl_pi {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    PLProp (Fin n → ℝ) volume t := by
  induction n with
  | zero =>
    intro f g h hf hg hh hyp
    rw [Measure.volume_pi_eq_dirac (isEmptyElim : ∀ a : Fin 0, ℝ), lintegral_dirac' _ hf,
      lintegral_dirac' _ hg, lintegral_dirac' _ hh]
    have := hyp (isEmptyElim : ∀ a : Fin 0, ℝ) (isEmptyElim : ∀ a : Fin 0, ℝ)
    rwa [Subsingleton.elim (t • (isEmptyElim : ∀ a : Fin 0, ℝ) + (1 - t) • isEmptyElim)
      (isEmptyElim : ∀ a : Fin 0, ℝ)] at this
  | succ n ih =>
    have he : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) volume :=
      (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) 0).symm
    refine pl_transfer _ he ?_ (pl_prod volume volume (pl_1d ht0 ht1) ih)
    intro x y
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp
    · simp

theorem pl_euclid {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (n : ℕ) :
    PLProp (EuclideanSpace ℝ (Fin n)) volume t := by
  refine pl_transfer (WithLp.toLp 2) (PiLp.volume_preserving_toLp (Fin n)) ?_ (pl_pi ht0 ht1 n)
  intro x y
  simp [WithLp.toLp_add, WithLp.toLp_smul]

/-- PL for nonmeasurable f, g and AEMeasurable h. -/
theorem pl_ae {t : ℝ} {X : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    {μ : Measure X} (hX : PLProp X μ t) (ht0 : 0 < t) (ht1 : t < 1) (f g h : X → ℝ≥0∞)
    (hh : AEMeasurable h μ)
    (hyp : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ x, g x ∂μ) ^ (1 - t) ≤ ∫⁻ x, h x ∂μ := by
  classical
  obtain ⟨f', hf'm, hf'le, hf'eq⟩ := exists_measurable_le_lintegral_eq μ f
  obtain ⟨g', hg'm, hg'le, hg'eq⟩ := exists_measurable_le_lintegral_eq μ g
  have hnull : μ {x | h x ≠ hh.mk h x} = 0 := ae_iff.mp hh.ae_eq_mk
  set N := toMeasurable μ {x | h x ≠ hh.mk h x} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable μ _
  have hN0 : μ N = 0 := by rw [hN, measure_toMeasurable]; exact hnull
  have hnotN : ∀ x, x ∉ N → h x = hh.mk h x := by
    intro x hx
    by_contra hne
    exact hx (subset_toMeasurable μ _ hne)
  set h' : X → ℝ≥0∞ := N.piecewise (fun _ => ∞) (hh.mk h)
  have hh'm : Measurable h' := Measurable.piecewise hNm measurable_const hh.measurable_mk
  have hle : ∀ x, h x ≤ h' x := by
    intro x
    by_cases hx : x ∈ N
    · simp [h', hx]
    · simp [h', hx, hnotN x hx]
  have hae : h' =ᵐ[μ] h := by
    have hc : Nᶜ ∈ ae μ := compl_mem_ae_iff.mpr hN0
    filter_upwards [hc] with x hx
    have hx' : x ∉ N := hx
    simp [h', hx', hnotN x hx']
  rw [hf'eq, hg'eq, ← lintegral_congr_ae hae]
  apply hX f' g' h' hf'm hg'm hh'm
  intro x y
  calc f' x ^ t * g' y ^ (1 - t) ≤ f x ^ t * g y ^ (1 - t) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (hf'le x) ht0.le)
          (ENNReal.rpow_le_rpow (hg'le y) (by linarith))
    _ ≤ h (t • x + (1 - t) • y) := hyp x y
    _ ≤ h' (t • x + (1 - t) • y) := hle _

end PLAux

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem Duchi_Q5_1 {n : ℕ}
  (f g m : EuclideanSpace ℝ (Fin n) → ℝ)
  (t : ℝ)
  (ht : t ∈ Set.Ioo 0 1)
  (hf_nn : ∀ x, 0 ≤ f x)
  (hg_nn : ∀ x, 0 ≤ g x)
  (hm_nn : ∀ x, 0 ≤ m x)
  (hf_int : MeasureTheory.Integrable f)
  (hg_int : MeasureTheory.Integrable g)
  (hm_int : MeasureTheory.Integrable m)
  (h_supermult : ∀ x y : EuclideanSpace ℝ (Fin n),
    m (t • x + (1 - t) • y) ≥ (Real.rpow (f x) t) * (Real.rpow (g y) (1 - t))) :
  ∫ x, m x ≥ (Real.rpow (∫ x, f x) t) * (Real.rpow (∫ x, g x) (1 - t)) := by
  obtain ⟨ht0, ht1⟩ := ht
  have ht1' : (0 : ℝ) ≤ 1 - t := by linarith
  have key := PLAux.pl_ae (PLAux.pl_euclid ht0 ht1 n) ht0 ht1
    (fun x => ENNReal.ofReal (f x)) (fun x => ENNReal.ofReal (g x))
    (fun x => ENNReal.ofReal (m x)) hm_int.aemeasurable.ennreal_ofReal
    (by
      intro x y
      dsimp only
      rw [ENNReal.ofReal_rpow_of_nonneg (hf_nn x) ht0.le,
        ENNReal.ofReal_rpow_of_nonneg (hg_nn y) ht1',
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (hf_nn x) t)]
      exact ENNReal.ofReal_le_ofReal (h_supermult x y))
  have hf_eq : ∫ x, f x = (∫⁻ x, ENNReal.ofReal (f x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hf_nn)
      hf_int.aestronglyMeasurable
  have hg_eq : ∫ x, g x = (∫⁻ x, ENNReal.ofReal (g x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg_nn)
      hg_int.aestronglyMeasurable
  have hm_eq : ∫ x, m x = (∫⁻ x, ENNReal.ofReal (m x)).toReal :=
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hm_nn)
      hm_int.aestronglyMeasurable
  have hm_fin : ∫⁻ x, ENNReal.ofReal (m x) ≠ ∞ := hm_int.lintegral_lt_top.ne
  show Real.rpow (∫ x, f x) t * Real.rpow (∫ x, g x) (1 - t) ≤ ∫ x, m x
  rw [Real.rpow_eq_pow, Real.rpow_eq_pow, hf_eq, hg_eq, hm_eq, ENNReal.toReal_rpow,
    ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hm_fin key

end Duchi_Q5_1
