import ConvexStarLib.Defs

/-!
# `grunbaum`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/grunbaum` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace grunbaum`, so the main result is `grunbaum.grunbaum`.
-/

namespace grunbaum

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Compact case of 1-dimensional Brunn–Minkowski. -/
lemma bm1_compact (A B C : Set ℝ) (hA : IsCompact A) (hB : IsCompact B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hC : ∀ x ∈ A, ∀ y ∈ B, θ * x + (1 - θ) * y ∈ C) :
    ENNReal.ofReal θ * volume A + ENNReal.ofReal (1 - θ) * volume B ≤ volume C := by
  have haA : sSup A ∈ A := hA.sSup_mem hAne
  have hbB : sInf B ∈ B := hB.sInf_mem hBne
  have hxa : ∀ x ∈ A, x ≤ sSup A := fun x hx => le_csSup hA.bddAbove hx
  have hyb : ∀ y ∈ B, sInf B ≤ y := fun y hy => csInf_le hB.bddBelow hy
  set a := sSup A with ha_def
  set b := sInf B with hb_def
  set c := θ * a + (1 - θ) * b with hc_def
  have hhom : ∀ (p r x : ℝ), AffineMap.homothety p r x = r * x + (1 - r) * p := by
    intro p r x; simp [AffineMap.homothety_apply]; ring
  set S1 := (AffineMap.homothety b θ) '' A with hS1_def
  set S2 := (AffineMap.homothety a (1 - θ)) '' B with hS2_def
  have hS1 : ∀ z ∈ S1, z ∈ C ∧ z ≤ c := by
    rintro z ⟨x, hx, rfl⟩
    rw [hhom]
    exact ⟨hC x hx b hbB, by nlinarith [hxa x hx]⟩
  have hS2 : ∀ z ∈ S2, z ∈ C ∧ c ≤ z := by
    rintro z ⟨y, hy, rfl⟩
    rw [hhom]
    refine ⟨?_, by nlinarith [hyb y hy]⟩
    have := hC a haA y hy
    convert this using 1; ring
  have vS1 : volume S1 = ENNReal.ofReal θ * volume A := by
    rw [hS1_def, MeasureTheory.Measure.addHaar_image_homothety]; simp [abs_of_pos hθ0]
  have vS2 : volume S2 = ENNReal.ofReal (1 - θ) * volume B := by
    rw [hS2_def, MeasureTheory.Measure.addHaar_image_homothety]
    simp [abs_of_pos (sub_pos.mpr hθ1)]
  have hS2m : MeasurableSet S2 := (hB.image (AffineMap.homothety_continuous _ _)).measurableSet
  have hdisj : Disjoint (S1 \ {c}) S2 := by
    rw [Set.disjoint_left]
    rintro z ⟨hz1, hzc⟩ hz2
    exact hzc (le_antisymm (hS1 z hz1).2 (hS2 z hz2).2)
  calc ENNReal.ofReal θ * volume A + ENNReal.ofReal (1 - θ) * volume B
      = volume (S1 \ {c}) + volume S2 := by
        rw [measure_diff_null Real.volume_singleton, vS1, vS2]
    _ = volume ((S1 \ {c}) ∪ S2) := (measure_union hdisj hS2m).symm
    _ ≤ volume C := measure_mono (Set.union_subset (fun z hz => (hS1 z hz.1).1)
        (fun z hz => (hS2 z hz).1))


/-- 1-dimensional Brunn–Minkowski for measurable sets. -/
lemma grun_bm1 (A B C : Set ℝ) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hC : ∀ x ∈ A, ∀ y ∈ B, θ * x + (1 - θ) * y ∈ C) :
    ENNReal.ofReal θ * volume A + ENNReal.ofReal (1 - θ) * volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  have key : ∀ K1 : Set ℝ, K1 ⊆ A ∧ IsCompact K1 → ∀ K2 : Set ℝ, K2 ⊆ B ∧ IsCompact K2 →
      ENNReal.ofReal θ * volume K1 + ENNReal.ofReal (1 - θ) * volume K2 ≤ volume C := by
    rintro K1 ⟨hK1A, hK1⟩ K2 ⟨hK2B, hK2⟩
    have hsub1 : insert a0 K1 ⊆ A := Set.insert_subset ha0 hK1A
    have hsub2 : insert b0 K2 ⊆ B := Set.insert_subset hb0 hK2B
    calc ENNReal.ofReal θ * volume K1 + ENNReal.ofReal (1 - θ) * volume K2
        ≤ ENNReal.ofReal θ * volume (insert a0 K1)
            + ENNReal.ofReal (1 - θ) * volume (insert b0 K2) := by
          gcongr <;> exact Set.subset_insert _ _
      _ ≤ volume C := bm1_compact _ _ C (hK1.insert a0) (hK2.insert b0)
          ⟨a0, Set.mem_insert _ _⟩ ⟨b0, Set.mem_insert _ _⟩ θ hθ0 hθ1
          (fun x hx y hy => hC x (hsub1 hx) y (hsub2 hy))
  have hvA : volume A = ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K := by
    rw [hA.measure_eq_iSup_isCompact volume]; simp only [iSup_and]
  have hvB : volume B = ⨆ K, ⨆ (_ : K ⊆ B ∧ IsCompact K), volume K := by
    rw [hB.measure_eq_iSup_isCompact volume]; simp only [iSup_and]
  rw [hvA, hvB]
  simp only [ENNReal.mul_iSup]
  exact ENNReal.biSup_add_biSup_le' ⟨∅, Set.empty_subset _, isCompact_empty⟩
    ⟨∅, Set.empty_subset _, isCompact_empty⟩ key






lemma pl1_vol_level (a : ℝ≥0∞) : volume ({t : ℝ | ENNReal.ofReal t < a} ∩ Set.Ioi 0) = a := by
  rcases eq_or_ne a ∞ with rfl | ha
  · have : {t : ℝ | ENNReal.ofReal t < ∞} ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext t; simp
    rw [this, Real.volume_Ioi]
  · have : {t : ℝ | ENNReal.ofReal t < a} ∩ Set.Ioi 0 = Set.Ioo 0 a.toReal := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_Ioi, Set.mem_Ioo]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h2, (ENNReal.ofReal_lt_iff_lt_toReal h2.le ha).mp h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨(ENNReal.ofReal_lt_iff_lt_toReal h1.le ha).mpr h2, h1⟩
    rw [this, Real.volume_Ioo, sub_zero, ENNReal.ofReal_toReal ha]

lemma pl1_layercake (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ t in Set.Ioi (0:ℝ), volume {x | ENNReal.ofReal t < f x} := by
  have hS : MeasurableSet {p : ℝ × ℝ | ENNReal.ofReal p.1 < f p.2} :=
    measurableSet_lt (ENNReal.measurable_ofReal.comp measurable_fst) (hf.comp measurable_snd)
  calc ∫⁻ x, f x = ∫⁻ x, (volume.restrict (Set.Ioi (0:ℝ)))
          ((fun t => (t, x)) ⁻¹' {p : ℝ × ℝ | ENNReal.ofReal p.1 < f p.2}) := by
        congr 1; funext x
        rw [Measure.restrict_apply' measurableSet_Ioi]
        exact (pl1_vol_level (f x)).symm
    _ = ((volume.restrict (Set.Ioi (0:ℝ))).prod volume)
          {p : ℝ × ℝ | ENNReal.ofReal p.1 < f p.2} := (Measure.prod_apply_symm hS).symm
    _ = ∫⁻ t in Set.Ioi (0:ℝ), volume {x | ENNReal.ofReal t < f x} := Measure.prod_apply hS

lemma pl1_layercake_le_one (f : ℝ → ℝ≥0∞) (hf : Measurable f) (h1 : ∀ x, f x ≤ 1) :
    ∫⁻ x, f x ≤ ∫⁻ t in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal t < f x} := by
  rw [pl1_layercake f hf, ← Set.Ioo_union_Ici_eq_Ioi (zero_lt_one' ℝ)]
  refine (lintegral_union_le _ _ _).trans ?_
  have : ∫⁻ t in Set.Ici (1:ℝ), volume {x | ENNReal.ofReal t < f x} = 0 := by
    apply setLIntegral_eq_zero measurableSet_Ici
    intro t ht
    have : {x | ENNReal.ofReal t < f x} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact (h1 x).trans (ENNReal.one_le_ofReal.mpr ht)
    simp [this]
  rw [this, add_zero]

lemma pl1_key (F G H : ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (hF1 : ∀ x, F x ≤ 1) (hG1 : ∀ x, G x ≤ 1)
    (hFs : ∀ r : ℝ≥0∞, r < 1 → ∃ x, r < F x) (hGs : ∀ r : ℝ≥0∞, r < 1 → ∃ x, r < G x)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hle : ∀ x y, F x ^ θ * G y ^ (1 - θ) ≤ H (θ * x + (1 - θ) * y)) :
    ENNReal.ofReal θ * (∫⁻ x, F x) + ENNReal.ofReal (1 - θ) * (∫⁻ x, G x) ≤ ∫⁻ x, H x := by
  have hbm : ∀ t ∈ Set.Ioo (0:ℝ) 1,
      ENNReal.ofReal θ * volume {x | ENNReal.ofReal t < F x}
        + ENNReal.ofReal (1 - θ) * volume {x | ENNReal.ofReal t < G x}
        ≤ volume {x | ENNReal.ofReal t < H x} := by
    intro t ht
    apply grun_bm1 _ _ _ (measurableSet_lt measurable_const hF)
      (measurableSet_lt measurable_const hG) (hFs _ (ENNReal.ofReal_lt_one.mpr ht.2))
      (hGs _ (ENNReal.ofReal_lt_one.mpr ht.2)) θ hθ0 hθ1
    intro x hx y hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    have ht0 : ENNReal.ofReal t ≠ 0 := by simpa using ht.1
    calc ENNReal.ofReal t = ENNReal.ofReal t ^ θ * ENNReal.ofReal t ^ (1 - θ) := by
          rw [← ENNReal.rpow_add _ _ ht0 ENNReal.ofReal_ne_top]; simp
      _ < F x ^ θ * G y ^ (1 - θ) :=
          ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx hθ0) (ENNReal.rpow_lt_rpow hy (by linarith))
      _ ≤ H (θ * x + (1 - θ) * y) := hle x y
  have hlcF := pl1_layercake_le_one F hF hF1
  have hlcG := pl1_layercake_le_one G hG hG1
  have hlcH : ∫⁻ t in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal t < H x} ≤ ∫⁻ x, H x := by
    rw [pl1_layercake H hH]
    exact lintegral_mono_set Set.Ioo_subset_Ioi_self
  calc ENNReal.ofReal θ * (∫⁻ x, F x) + ENNReal.ofReal (1 - θ) * (∫⁻ x, G x)
      ≤ ENNReal.ofReal θ * (∫⁻ t in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal t < F x})
        + ENNReal.ofReal (1 - θ) * (∫⁻ t in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal t < G x}) := by
        gcongr
    _ = (∫⁻ t in Set.Ioo (0:ℝ) 1, ENNReal.ofReal θ * volume {x | ENNReal.ofReal t < F x})
        + (∫⁻ t in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (1 - θ) * volume {x | ENNReal.ofReal t < G x}) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ t in Set.Ioo (0:ℝ) 1, (ENNReal.ofReal θ * volume {x | ENNReal.ofReal t < F x}
        + ENNReal.ofReal (1 - θ) * volume {x | ENNReal.ofReal t < G x}) := le_lintegral_add _ _
    _ ≤ ∫⁻ t in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal t < H x} :=
        setLIntegral_mono' measurableSet_Ioo hbm
    _ ≤ ∫⁻ x, H x := hlcH

lemma pl1_amgm (a b : ℝ≥0∞) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    a ^ θ * b ^ (1 - θ) ≤ ENNReal.ofReal θ * a + ENNReal.ofReal (1 - θ) * b := by
  have h1θ : 0 < 1 - θ := by linarith
  rcases eq_or_ne a ∞ with rfl | ha
  · have : ENNReal.ofReal θ * ∞ = ∞ := ENNReal.mul_top (by simpa using hθ0)
    rw [this, top_add]; exact le_top
  rcases eq_or_ne b ∞ with rfl | hb
  · have : ENNReal.ofReal (1 - θ) * ∞ = ∞ := ENNReal.mul_top (by simpa using h1θ)
    rw [this, add_top]; exact le_top
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hθ0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg h1θ.le,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg ENNReal.toReal_nonneg _),
    ← ENNReal.ofReal_mul hθ0.le, ← ENNReal.ofReal_mul h1θ.le,
    ← ENNReal.ofReal_add (mul_nonneg hθ0.le ENNReal.toReal_nonneg)
      (mul_nonneg h1θ.le ENNReal.toReal_nonneg)]
  apply ENNReal.ofReal_le_ofReal
  exact Real.geom_mean_le_arith_mean2_weighted hθ0.le h1θ.le ENNReal.toReal_nonneg
    ENNReal.toReal_nonneg (by ring)

lemma pl1_alg (a b c d : ℝ≥0∞) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hc0 : c ≠ 0) (hct : c ≠ ∞) :
    (a / c) ^ θ * (b / d) ^ (1 - θ) = (a ^ θ * b ^ (1 - θ)) / (c ^ θ * d ^ (1 - θ)) := by
  have h1θ : 0 < 1 - θ := by linarith
  have hc1 : c ^ θ ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hct).ne'
  have hc2 : c ^ θ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hθ0.le hct
  rw [ENNReal.div_rpow_of_nonneg _ _ hθ0.le, ENNReal.div_rpow_of_nonneg _ _ h1θ.le,
    div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, ENNReal.mul_inv (Or.inl hc1) (Or.inl hc2)]
  ring


/-- 1-dimensional Prékopa–Leindler for bounded measurable functions. -/
lemma grun_pl1 (F G H : ℝ → ℝ≥0∞) (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (MF MG : ℝ≥0∞) (hMF : MF ≠ ∞) (hMG : MG ≠ ∞) (hFb : ∀ x, F x ≤ MF) (hGb : ∀ x, G x ≤ MG)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hle : ∀ x y, F x ^ θ * G y ^ (1 - θ) ≤ H (θ * x + (1 - θ) * y)) :
    (∫⁻ x, F x) ^ θ * (∫⁻ x, G x) ^ (1 - θ) ≤ ∫⁻ x, H x := by
  have h1θ : 0 < 1 - θ := by linarith
  set sF := ⨆ x, F x with hsF
  set sG := ⨆ x, G x with hsG
  have hFle : ∀ x, F x ≤ sF := fun x => le_iSup F x
  have hGle : ∀ x, G x ≤ sG := fun x => le_iSup G x
  have hsFtop : sF ≠ ∞ := ne_top_of_le_ne_top hMF (iSup_le hFb)
  have hsGtop : sG ≠ ∞ := ne_top_of_le_ne_top hMG (iSup_le hGb)
  rcases eq_or_ne sF 0 with hsF0 | hsF0
  · have h0 : ∀ x, F x = 0 := fun x => le_antisymm ((hFle x).trans hsF0.le) (zero_le _)
    simp [h0, ENNReal.zero_rpow_of_pos hθ0]
  rcases eq_or_ne sG 0 with hsG0 | hsG0
  · have h0 : ∀ x, G x = 0 := fun x => le_antisymm ((hGle x).trans hsG0.le) (zero_le _)
    simp [h0, ENNReal.zero_rpow_of_pos h1θ]
  set S := sF ^ θ * sG ^ (1 - θ) with hS
  have hS0 : S ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hsF0) hsFtop).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hsG0) hsGtop).ne'
  have hStop : S ≠ ∞ := ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hθ0.le hsFtop)
    (ENNReal.rpow_ne_top_of_nonneg h1θ.le hsGtop)
  have key := pl1_key (fun x => F x / sF) (fun x => G x / sG) (fun x => H x / S)
    (hF.div_const _) (hG.div_const _) (hH.div_const _)
    (fun x => ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hFle x))
    (fun x => ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hGle x))
    (fun r hr => by
      have : r * sF < sF := by
        calc r * sF < 1 * sF := ENNReal.mul_lt_mul_left hsF0 hsFtop hr
          _ = sF := one_mul _
      obtain ⟨x, hx⟩ := lt_iSup_iff.mp this
      exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl hsF0) (Or.inl hsFtop)).mpr hx⟩)
    (fun r hr => by
      have : r * sG < sG := by
        calc r * sG < 1 * sG := ENNReal.mul_lt_mul_left hsG0 hsGtop hr
          _ = sG := one_mul _
      obtain ⟨x, hx⟩ := lt_iSup_iff.mp this
      exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl hsG0) (Or.inl hsGtop)).mpr hx⟩)
    θ hθ0 hθ1
    (fun x y => by
      simp only
      rw [pl1_alg _ _ _ _ θ hθ0 hθ1 hsF0 hsFtop]
      exact ENNReal.div_le_div_right (hle x y) _)
  have hintF : ∫⁻ x, F x / sF = (∫⁻ x, F x) / sF := by
    simp_rw [div_eq_mul_inv]; exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hsF0)
  have hintG : ∫⁻ x, G x / sG = (∫⁻ x, G x) / sG := by
    simp_rw [div_eq_mul_inv]; exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hsG0)
  have hintH : ∫⁻ x, H x / S = (∫⁻ x, H x) / S := by
    simp_rw [div_eq_mul_inv]; exact lintegral_mul_const' _ _ (ENNReal.inv_ne_top.mpr hS0)
  simp only at key
  rw [hintF, hintG, hintH] at key
  have h2 := (pl1_amgm ((∫⁻ x, F x) / sF) ((∫⁻ x, G x) / sG) θ hθ0 hθ1).trans key
  rw [pl1_alg _ _ _ _ θ hθ0 hθ1 hsF0 hsFtop] at h2
  calc (∫⁻ x, F x) ^ θ * (∫⁻ x, G x) ^ (1 - θ)
      = ((∫⁻ x, F x) ^ θ * (∫⁻ x, G x) ^ (1 - θ)) / S * S :=
        (ENNReal.div_mul_cancel hS0 hStop).symm
    _ ≤ (∫⁻ x, H x) / S * S := by gcongr
    _ = ∫⁻ x, H x := ENNReal.div_mul_cancel hS0 hStop





lemma bm_symm_apply (m : ℕ) (s : ℝ) (y : Fin m → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm (s, y) = Fin.cons s y := by
  simp only [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv_zero]
  rfl

lemma bm_apply_snd (m : ℕ) (x : Fin (m+1) → ℝ) :
    ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0) x).2 = Fin.tail x := by
  simp

lemma bm_cont_symm (m : ℕ) :
    Continuous (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm := by
  have : ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm =
      fun p : ℝ × (Fin m → ℝ) => (Fin.cons p.1 p.2 : Fin (m+1) → ℝ) := by
    funext p; exact bm_symm_apply m p.1 p.2
  rw [this]
  exact Continuous.finCons (A := fun _ => ℝ) continuous_fst continuous_snd

lemma bm_cont_snd (m : ℕ) :
    Continuous (fun x => ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0) x).2) := by
  simp only [bm_apply_snd]
  exact continuous_pi fun j => continuous_apply _

lemma bm_comb (m : ℕ) (θ s t : ℝ) (y z : Fin m → ℝ) :
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm
        (θ * s + (1 - θ) * t, θ • y + (1 - θ) • z) =
      θ • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm (s, y) +
        (1 - θ) • (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm (t, z) := by
  simp only [bm_symm_apply]
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

lemma bm_vol (m : ℕ) (X : Set (Fin (m+1) → ℝ)) (hX : MeasurableSet X) :
    volume X = ∫⁻ s, volume (Prod.mk s ⁻¹'
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm ⁻¹' X)) := by
  have he := volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
  rw [← (MeasurePreserving.symm _ he).measure_preimage_equiv X]
  exact Measure.prod_apply (hX.preimage (MeasurableEquiv.measurable _))

lemma bm_slice_sub (m : ℕ) (A : Set (Fin (m+1) → ℝ)) (s : ℝ) :
    Prod.mk s ⁻¹' ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm ⁻¹' A) ⊆
      (fun x => ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0) x).2) '' A := by
  intro y hy
  exact ⟨_, hy, by simp⟩

lemma bm_slice_compact (m : ℕ) (A : Set (Fin (m+1) → ℝ)) (hA : IsCompact A) (s : ℝ) :
    IsCompact (Prod.mk s ⁻¹'
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm ⁻¹' A)) := by
  refine (hA.image (bm_cont_snd m)).of_isClosed_subset ?_ (bm_slice_sub m A s)
  exact hA.isClosed.preimage ((bm_cont_symm m).comp (Continuous.prodMk_right s))

lemma bm_slice_bdd (m : ℕ) (A : Set (Fin (m+1) → ℝ)) (hA : IsCompact A) :
    ∃ M : ℝ≥0∞, M ≠ ∞ ∧ ∀ s, volume (Prod.mk s ⁻¹'
      ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0).symm ⁻¹' A)) ≤ M :=
  ⟨_, (hA.image (bm_cont_snd m)).measure_lt_top.ne, fun s => measure_mono (bm_slice_sub m A s)⟩


/-- Multiplicative Brunn–Minkowski in `Fin m → ℝ` for compact sets. -/
lemma grun_bm (m : ℕ) (A B C : Set (Fin m → ℝ)) (hA : IsCompact A) (hB : IsCompact B)
    (hC : MeasurableSet C) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hsub : ∀ x ∈ A, ∀ y ∈ B, θ • x + (1 - θ) • y ∈ C) :
    volume A ^ θ * volume B ^ (1 - θ) ≤ volume C := by
  induction m with
  | zero =>
    rcases A.eq_empty_or_nonempty with hAe | ⟨a, ha⟩
    · subst hAe; simp [ENNReal.zero_rpow_of_pos hθ0]
    rcases B.eq_empty_or_nonempty with hBe | ⟨b, hb⟩
    · subst hBe; simp [ENNReal.zero_rpow_of_pos (sub_pos.2 hθ1)]
    have hc := hsub a ha b hb
    have hAC : A ⊆ C := fun x _ => by
      have : x = θ • a + (1 - θ) • b := Subsingleton.elim _ _
      rw [this]; exact hc
    have hBC : B ⊆ C := fun x _ => by
      have : x = θ • a + (1 - θ) • b := Subsingleton.elim _ _
      rw [this]; exact hc
    calc volume A ^ θ * volume B ^ (1 - θ) ≤ volume C ^ θ * volume C ^ (1 - θ) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (measure_mono hAC) hθ0.le)
            (ENNReal.rpow_le_rpow (measure_mono hBC) (sub_pos.2 hθ1).le)
      _ = volume C := by
          rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (sub_pos.2 hθ1).le]; simp
  | succ m ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0 with he_def
    have hAm : MeasurableSet (e.symm ⁻¹' A) :=
      hA.isClosed.measurableSet.preimage e.symm.measurable
    have hBm : MeasurableSet (e.symm ⁻¹' B) :=
      hB.isClosed.measurableSet.preimage e.symm.measurable
    have hCm : MeasurableSet (e.symm ⁻¹' C) := hC.preimage e.symm.measurable
    obtain ⟨MF, hMF, hFb⟩ := bm_slice_bdd m A hA
    obtain ⟨MG, hMG, hGb⟩ := bm_slice_bdd m B hB
    rw [bm_vol m A hA.isClosed.measurableSet, bm_vol m B hB.isClosed.measurableSet,
      bm_vol m C hC]
    refine grun_pl1 _ _ _ (measurable_measure_prodMk_left hAm)
      (measurable_measure_prodMk_left hBm) (measurable_measure_prodMk_left hCm)
      MF MG hMF hMG hFb hGb θ hθ0 hθ1 ?_
    intro s t
    apply ih _ _ _ (bm_slice_compact m A hA s) (bm_slice_compact m B hB t)
      (measurable_prodMk_left hCm)
    intro y hy z hz
    show e.symm (θ * s + (1 - θ) * t, θ • y + (1 - θ) • z) ∈ C
    rw [bm_comb]
    exact hsub _ hy _ hz


/-- Upper half comparison with the exponential `g 0 * exp (-β t)`. -/
lemma grun_1d_upper (g : ℝ → ℝ)
    (a b : ℝ) (hg_supp : ∀ t, t ∉ Set.Icc a b → g t = 0)
    (hg_lc : ∀ s t θ : ℝ, 0 < θ → θ < 1 → g s ^ θ * g t ^ (1 - θ) ≤ g (θ * s + (1 - θ) * t))
    (β : ℝ) (hg0 : 0 < g 0) (hβ : 0 < β)
    (hP : ∫ t in Set.Ioi 0, g t = g 0 / β) :
    ∫ t in Set.Ioi 0, t * g t ≤ g 0 / β ^ 2 := by
  -- exponential integrals
  have I1 : ∫ t in Set.Ioi 0, g 0 * Real.exp (-(β * t)) = g 0 / β := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 1) one_pos hβ
    simp only [sub_self, Real.rpow_zero, one_mul, Real.rpow_one, Real.Gamma_one,
      mul_one] at h
    rw [MeasureTheory.integral_const_mul, h]
    field_simp
  have I2 : ∫ t in Set.Ioi 0, t * (g 0 * Real.exp (-(β * t))) = g 0 / β ^ 2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) two_pos hβ
    have h21 : (2:ℝ) - 1 = 1 := by norm_num
    simp only [h21, Real.rpow_one, Real.Gamma_two, mul_one, Real.rpow_two] at h
    have hfun : (fun t : ℝ => t * (g 0 * Real.exp (-(β * t))))
        = fun t => g 0 * (t * Real.exp (-(β * t))) := by
      funext t; ring
    rw [hfun, MeasureTheory.integral_const_mul, h]
    field_simp
  have he_int : MeasureTheory.IntegrableOn (fun t => g 0 * Real.exp (-(β * t))) (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [I1]; positivity
  have hte_int : MeasureTheory.IntegrableOn
      (fun t => t * (g 0 * Real.exp (-(β * t)))) (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [I2]; positivity
  have hg_int : MeasureTheory.IntegrableOn g (Set.Ioi 0) := by
    apply MeasureTheory.Integrable.of_integral_ne_zero
    rw [hP]; positivity
  by_cases htg_int : MeasureTheory.IntegrableOn (fun t => t * g t) (Set.Ioi 0)
  swap
  · rw [MeasureTheory.integral_undef htg_int]; positivity
  -- crossing set
  set T : Set ℝ := {t | 0 < t ∧ g 0 * Real.exp (-(β * t)) ≤ g t} with hT
  have hTb : ∀ t ∈ T, t ≤ b := by
    intro t ht
    by_contra hcon
    push_neg at hcon
    have h0 : g t = 0 := hg_supp t (fun hmem => by linarith [hmem.2])
    have hpos : 0 < g 0 * Real.exp (-(β * t)) := by positivity
    linarith [ht.2]
  have hTdown : ∀ s t, 0 < s → s < t → t ∈ T → s ∈ T := by
    intro s t hs hst ht
    obtain ⟨htpos, hle⟩ := ht
    refine ⟨hs, ?_⟩
    have htne : t ≠ 0 := htpos.ne'
    have hθ0 : 0 < s / t := div_pos hs htpos
    have hθ1 : s / t < 1 := (div_lt_one htpos).mpr hst
    have hlc := hg_lc t 0 (s / t) hθ0 hθ1
    have hcomb : s / t * t + (1 - s / t) * 0 = s := by
      rw [mul_zero, add_zero, div_mul_cancel₀ s htne]
    rw [hcomb] at hlc
    have hc : 0 < g 0 := hg0
    have he_pos : 0 < g 0 * Real.exp (-(β * t)) := by positivity
    have h1 : (g 0 * Real.exp (-(β * t))) ^ (s / t) ≤ g t ^ (s / t) :=
      Real.rpow_le_rpow he_pos.le hle hθ0.le
    have hc1 : g 0 ^ (s / t) * g 0 ^ (1 - s / t) = g 0 := by
      rw [← Real.rpow_add hc]; simp
    have hc2 : -(β * t) * (s / t) = -(β * s) := by
      field_simp
    have h2 : (g 0 * Real.exp (-(β * t))) ^ (s / t) * g 0 ^ (1 - s / t)
        = g 0 * Real.exp (-(β * s)) := by
      rw [Real.mul_rpow hc.le (Real.exp_pos _).le, ← Real.exp_mul]
      calc g 0 ^ (s / t) * Real.exp (-(β * t) * (s / t)) * g 0 ^ (1 - s / t)
          = (g 0 ^ (s / t) * g 0 ^ (1 - s / t)) * Real.exp (-(β * t) * (s / t)) := by ring
        _ = g 0 * Real.exp (-(β * s)) := by rw [hc1, hc2]
    calc g 0 * Real.exp (-(β * s))
        = (g 0 * Real.exp (-(β * t))) ^ (s / t) * g 0 ^ (1 - s / t) := h2.symm
      _ ≤ g t ^ (s / t) * g 0 ^ (1 - s / t) :=
          mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hc.le _)
      _ ≤ g s := hlc
  set S : Set ℝ := insert 0 T with hS
  have hSne : S.Nonempty := ⟨0, Set.mem_insert 0 T⟩
  have hSbdd : BddAbove S := by
    refine ⟨max b 0, fun x hx => ?_⟩
    rcases hx with rfl | hx
    · exact le_max_right _ _
    · exact le_trans (hTb x hx) (le_max_left _ _)
  set t1 := sSup S with ht1
  have hcross : ∀ t ∈ Set.Ioi (0:ℝ), (t - t1) * (g t - g 0 * Real.exp (-(β * t))) ≤ 0 := by
    intro t ht
    have ht0 : 0 < t := ht
    rcases lt_trichotomy t t1 with h | h | h
    · obtain ⟨t', ht'S, htt'⟩ := exists_lt_of_lt_csSup hSne h
      have ht'T : t' ∈ T := by
        rcases ht'S with h0 | h'
        · exfalso; rw [h0] at htt'; linarith
        · exact h'
      have := (hTdown t t' ht0 htt' ht'T).2
      nlinarith
    · rw [h]; simp
    · have hnot : t ∉ T := fun hmem => by
        have := le_csSup hSbdd (Set.mem_insert_of_mem 0 hmem)
        linarith
      have hlt : g t < g 0 * Real.exp (-(β * t)) := by
        by_contra hcon
        push_neg at hcon
        exact hnot ⟨ht0, hcon⟩
      nlinarith
  have hneg : ∫ t in Set.Ioi 0, (t - t1) * (g t - g 0 * Real.exp (-(β * t))) ≤ 0 :=
    MeasureTheory.setIntegral_nonpos measurableSet_Ioi hcross
  have key : ∫ t in Set.Ioi 0, (t - t1) * (g t - g 0 * Real.exp (-(β * t)))
      = ((∫ t in Set.Ioi 0, t * g t) - t1 * ∫ t in Set.Ioi 0, g t)
        - ((∫ t in Set.Ioi 0, t * (g 0 * Real.exp (-(β * t))))
          - t1 * ∫ t in Set.Ioi 0, g 0 * Real.exp (-(β * t))) := by
    have e1 : ∫ t in Set.Ioi 0, (t - t1) * (g t - g 0 * Real.exp (-(β * t))) =
        ∫ t in Set.Ioi 0, ((t * g t - t1 * g t) - (t * (g 0 * Real.exp (-(β * t)))
          - t1 * (g 0 * Real.exp (-(β * t))))) := by
      congr 1; funext t; ring
    have hA : MeasureTheory.IntegrableOn (fun t => t * g t - t1 * g t) (Set.Ioi 0) :=
      MeasureTheory.Integrable.sub htg_int (MeasureTheory.Integrable.const_mul hg_int t1)
    have hB : MeasureTheory.IntegrableOn (fun t => t * (g 0 * Real.exp (-(β * t)))
        - t1 * (g 0 * Real.exp (-(β * t)))) (Set.Ioi 0) :=
      MeasureTheory.Integrable.sub hte_int (MeasureTheory.Integrable.const_mul he_int t1)
    have hC : MeasureTheory.IntegrableOn (fun t => t1 * g t) (Set.Ioi 0) :=
      MeasureTheory.Integrable.const_mul hg_int t1
    have hD : MeasureTheory.IntegrableOn (fun t => t1 * (g 0 * Real.exp (-(β * t))))
        (Set.Ioi 0) :=
      MeasureTheory.Integrable.const_mul he_int t1
    rw [e1, MeasureTheory.integral_sub hA hB, MeasureTheory.integral_sub htg_int hC,
      MeasureTheory.integral_sub hte_int hD,
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [key, I1, I2, hP] at hneg
  linarith


/-- On the negative half-line `g` is dominated by the exponential `g 0 * exp (-β t)`. -/
lemma grun_1d_dom (g : ℝ → ℝ) (hg_nn : ∀ t, 0 ≤ g t) (hg_meas : Measurable g)
    (hg_lc : ∀ s t θ : ℝ, 0 < θ → θ < 1 → g s ^ θ * g t ^ (1 - θ) ≤ g (θ * s + (1 - θ) * t))
    (β : ℝ) (hg0 : 0 < g 0) (hβ : 0 < β)
    (hP : ∫ t in Set.Ioi 0, g t = g 0 / β) :
    ∀ t < 0, g t ≤ g 0 * Real.exp (-(β * t)) := by
  intro t0 ht0
  by_contra hcon
  push_neg at hcon
  have he_pos : ∀ t, 0 < g 0 * Real.exp (-(β * t)) := fun t => mul_pos hg0 (Real.exp_pos _)
  have hkey : ∀ θ s u : ℝ, (g 0 * Real.exp (-(β * s))) ^ θ * (g 0 * Real.exp (-(β * u))) ^ (1 - θ)
      = g 0 * Real.exp (-(β * (θ * s + (1 - θ) * u))) := by
    intro θ s u
    rw [Real.mul_rpow hg0.le (Real.exp_pos _).le, Real.mul_rpow hg0.le (Real.exp_pos _).le,
      ← Real.exp_mul, ← Real.exp_mul]
    have : g 0 ^ θ * Real.exp (-(β * s) * θ) * (g 0 ^ (1 - θ) * Real.exp (-(β * u) * (1 - θ)))
        = (g 0 ^ θ * g 0 ^ (1 - θ)) * (Real.exp (-(β * s) * θ) * Real.exp (-(β * u) * (1 - θ))) := by
      ring
    rw [this, ← Real.rpow_add hg0, ← Real.exp_add]
    congr 1
    · simp
    · congr 1; ring
  have hclaim : ∀ u > 0, g u < g 0 * Real.exp (-(β * u)) := by
    intro u hu
    by_contra hge
    push_neg at hge
    have hut : 0 < u - t0 := by linarith
    have hθ0 : 0 < u / (u - t0) := div_pos hu hut
    have hθ1 : u / (u - t0) < 1 := by rw [div_lt_one hut]; linarith
    have hcomb : u / (u - t0) * t0 + (1 - u / (u - t0)) * u = 0 := by
      field_simp; ring
    have h1 := hg_lc t0 u (u / (u - t0)) hθ0 hθ1
    rw [hcomb] at h1
    have h2 : (g 0 * Real.exp (-(β * t0))) ^ (u / (u - t0)) < g t0 ^ (u / (u - t0)) :=
      Real.rpow_lt_rpow (he_pos t0).le hcon hθ0
    have h3 : (g 0 * Real.exp (-(β * u))) ^ (1 - u / (u - t0)) ≤ g u ^ (1 - u / (u - t0)) :=
      Real.rpow_le_rpow (he_pos u).le hge (by linarith)
    have h4 : 0 < (g 0 * Real.exp (-(β * u))) ^ (1 - u / (u - t0)) :=
      Real.rpow_pos_of_pos (he_pos u) _
    have h5 : (g 0 * Real.exp (-(β * t0))) ^ (u / (u - t0))
          * (g 0 * Real.exp (-(β * u))) ^ (1 - u / (u - t0))
        < g t0 ^ (u / (u - t0)) * g u ^ (1 - u / (u - t0)) := by
      calc _ < g t0 ^ (u / (u - t0)) * (g 0 * Real.exp (-(β * u))) ^ (1 - u / (u - t0)) := by
            exact mul_lt_mul_of_pos_right h2 h4
        _ ≤ g t0 ^ (u / (u - t0)) * g u ^ (1 - u / (u - t0)) := by
            exact mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg (hg_nn t0) _)
    rw [hkey, hcomb] at h5
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one] at h5
    linarith
  -- integrals
  have hint_e : IntegrableOn (fun t => g 0 * Real.exp (-(β * t))) (Set.Ioi 0) := by
    have := (integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0).const_mul (g 0)
    simpa [neg_mul] using this
  have hval_e : ∫ t in Set.Ioi 0, g 0 * Real.exp (-(β * t)) = g 0 / β := by
    rw [integral_const_mul]
    have := integral_exp_mul_Ioi (a := -β) (by linarith) 0
    simp only [neg_mul] at this
    rw [this]
    simp
    field_simp
  have hint_g : IntegrableOn g (Set.Ioi 0) := by
    refine Integrable.mono' hint_e hg_meas.aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
    intro x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn x)]
    exact (hclaim x hx).le
  have hlt : ∫ t in Set.Ioi 0, g t < ∫ t in Set.Ioi 0, g 0 * Real.exp (-(β * t)) := by
    rw [← sub_pos, ← integral_sub hint_e hint_g, setIntegral_pos_iff_support_of_nonneg_ae]
    · have hsupp : (Function.support fun t => g 0 * Real.exp (-(β * t)) - g t) ∩ Set.Ioi 0
          = Set.Ioi 0 := by
        ext x
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨(sub_pos.2 (hclaim x h)).ne', h⟩
      rw [hsupp, Real.volume_Ioi]
      exact ENNReal.zero_lt_top
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall ?_)
      intro x hx
      exact sub_nonneg.2 (hclaim x hx).le
    · exact hint_e.sub hint_g
  rw [hP, hval_e] at hlt
  exact lt_irrefl _ hlt


/-- Bathtub estimate for the first moment on the negative half-line. -/
lemma grun_1d_bathtub (g : ℝ → ℝ) (hg_nn : ∀ t, 0 ≤ g t) (hg_meas : Measurable g)
    (a b M : ℝ) (hg_supp : ∀ t, t ∉ Set.Icc a b → g t = 0) (hg_bdd : ∀ t, g t ≤ M)
    (c β : ℝ) (hc : 0 < c) (hβ : 0 < β)
    (hdom : ∀ t < 0, g t ≤ c * Real.exp (-(β * t))) :
    c / β ^ 2 * ((1 + β / c * ∫ t in Set.Iio 0, g t) * Real.log (1 + β / c * ∫ t in Set.Iio 0, g t)
      - β / c * ∫ t in Set.Iio 0, g t) ≤ ∫ t in Set.Iio 0, (-t) * g t := by
  have hc0 : c ≠ 0 := hc.ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  set Q := ∫ t in Set.Iio 0, g t with hQ_def
  have hQ_nn : 0 ≤ Q := setIntegral_nonneg measurableSet_Iio (fun t _ => hg_nn t)
  set x := β / c * Q with hx_def
  have hx_nn : 0 ≤ x := mul_nonneg (div_nonneg hβ.le hc.le) hQ_nn
  set s0 := Real.log (1 + x) / β with hs0_def
  have hs0_nn : 0 ≤ s0 := div_nonneg (Real.log_nonneg (by linarith)) hβ.le
  have hlog : Real.log (1 + x) = β * s0 := by rw [hs0_def]; field_simp
  have hexp : Real.exp (β * s0) = 1 + x := by
    rw [← hlog]; exact Real.exp_log (by linarith)
  -- integrability of g
  have hsupp : Function.support g ⊆ Set.Icc a b := by
    intro t ht
    by_contra h
    exact ht (hg_supp t h)
  have hg_int : Integrable g := by
    rw [← integrableOn_iff_integrable_of_support_subset hsupp]
    refine Measure.integrableOn_of_bounded (M := M) measure_Icc_lt_top.ne
      hg_meas.aestronglyMeasurable ?_
    refine ae_of_all _ (fun t => ?_)
    rw [Real.norm_of_nonneg (hg_nn t)]
    exact hg_bdd t
  have htg_int : Integrable (fun t => (-t) * g t) := by
    have hsupp' : Function.support (fun t => (-t) * g t) ⊆ Set.Icc a b := by
      intro t ht
      by_contra h
      apply ht
      simp [hg_supp t h]
    rw [← integrableOn_iff_integrable_of_support_subset hsupp']
    exact IntegrableOn.continuousOn_mul (continuous_neg.continuousOn) hg_int.integrableOn
      isCompact_Icc
  set F : ℝ → ℝ := fun t => (-t - s0) * (c * Real.exp (-(β * t))) with hF_def
  have hF_cont : Continuous F := by
    rw [hF_def]; fun_prop
  have hF_int : Integrable (Set.indicator (Set.Ioo (-s0) 0) F) :=
    ((hF_cont.integrableOn_Icc (a := -s0) (b := 0)).mono_set Set.Ioo_subset_Icc_self).integrable_indicator
      measurableSet_Ioo
  -- pointwise
  have hpt : ∀ t ∈ Set.Iio (0:ℝ), s0 * g t + Set.indicator (Set.Ioo (-s0) 0) F t ≤ (-t) * g t := by
    intro t ht
    rw [Set.mem_Iio] at ht
    by_cases h : -s0 < t
    · rw [Set.indicator_of_mem (Set.mem_Ioo.2 ⟨h, ht⟩)]
      have h1 : (-t - s0) * (c * Real.exp (-(β * t))) ≤ (-t - s0) * g t :=
        mul_le_mul_of_nonpos_left (hdom t ht) (by linarith)
      simp only [hF_def]
      linarith
    · rw [Set.indicator_of_notMem (fun hm => h (Set.mem_Ioo.1 hm).1)]
      have h1 : s0 * g t ≤ (-t) * g t := mul_le_mul_of_nonneg_right (by linarith) (hg_nn t)
      linarith
  have hmono : ∫ t in Set.Iio 0, (s0 * g t + Set.indicator (Set.Ioo (-s0) 0) F t)
      ≤ ∫ t in Set.Iio 0, (-t) * g t :=
    setIntegral_mono_on ((hg_int.const_mul s0).add hF_int).integrableOn htg_int.integrableOn
      measurableSet_Iio hpt
  have hsplit : ∫ t in Set.Iio 0, (s0 * g t + Set.indicator (Set.Ioo (-s0) 0) F t)
      = s0 * Q + ∫ t in (-s0)..0, F t := by
    rw [integral_add (hg_int.const_mul s0).integrableOn hF_int.integrableOn, integral_const_mul]
    congr 1
    rw [setIntegral_indicator measurableSet_Ioo, Set.inter_eq_right.2 Set.Ioo_subset_Iio_self,
      intervalIntegral.integral_of_le (by linarith), integral_Ioc_eq_integral_Ioo]
  have hFTC : ∫ t in (-s0)..0, F t = c * s0 / β - c * x / β ^ 2 := by
    have hderiv : ∀ t ∈ Set.uIcc (-s0) 0,
        HasDerivAt (fun t => c * ((t + s0) / β + 1 / β ^ 2) * Real.exp (-(β * t))) (F t) t := by
      intro t _
      have h1 : HasDerivAt (fun t => -(β * t)) (-β) t := by
        simpa using ((hasDerivAt_id t).const_mul β).neg
      have h3 : HasDerivAt (fun t => c * ((t + s0) / β + 1 / β ^ 2)) (c * (1 / β)) t := by
        have := (((hasDerivAt_id t).add_const s0).div_const β).add_const (1 / β ^ 2)
        simpa using this.const_mul c
      convert h3.mul h1.exp using 1
      simp only [hF_def]
      field_simp
      ring
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hF_cont.intervalIntegrable _ _)]
    simp only [mul_zero, neg_zero, Real.exp_zero, zero_add, mul_one]
    rw [show -(β * -s0) = β * s0 by ring, hexp]
    field_simp
    ring
  have hQx : Q = c * x / β := by rw [hx_def]; field_simp
  calc c / β ^ 2 * ((1 + x) * Real.log (1 + x) - x) = s0 * Q + (c * s0 / β - c * x / β ^ 2) := by
        rw [hlog, hQx]; field_simp; ring
    _ = ∫ t in Set.Iio 0, (s0 * g t + Set.indicator (Set.Ioo (-s0) 0) F t) := by rw [hsplit, hFTC]
    _ ≤ _ := hmono









/-- Grünbaum's inequality for a log-concave density on `ℝ` with mean zero. -/
lemma grun_1d (g : ℝ → ℝ) (hg_nn : ∀ t, 0 ≤ g t) (hg_meas : Measurable g)
    (a b M : ℝ) (hg_supp : ∀ t, t ∉ Set.Icc a b → g t = 0) (hg_bdd : ∀ t, g t ≤ M)
    (hg_lc : ∀ s t θ : ℝ, 0 < θ → θ < 1 → g s ^ θ * g t ^ (1 - θ) ≤ g (θ * s + (1 - θ) * t))
    (hmean : ∫ t, t * g t = 0) :
    Real.exp (-1) * ∫ t, g t ≤ ∫ t in Set.Ici 0, g t := by
  -- integrability
  have hgi : Integrable g := by
    have h1 : IntegrableOn g (Set.Icc a b) := by
      refine Measure.integrableOn_of_bounded (M := M) measure_Icc_lt_top.ne
        hg_meas.aestronglyMeasurable ?_
      filter_upwards with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn t)]
      exact hg_bdd t
    exact h1.integrable_of_forall_notMem_eq_zero hg_supp
  have hgti : Integrable (fun t => t * g t) := by
    have h1 : IntegrableOn (fun t => t * g t) (Set.Icc a b) :=
      (hgi.integrableOn).continuousOn_mul continuousOn_id isCompact_Icc
    refine h1.integrable_of_forall_notMem_eq_zero ?_
    intro t ht
    simp [hg_supp t ht]
  -- notation
  set P := ∫ t in Set.Ioi 0, g t with hPdef
  set Q := ∫ t in Set.Iio 0, g t with hQdef
  have hPici : ∫ t in Set.Ici 0, g t = P := integral_Ici_eq_integral_Ioi
  have hsplit : ∫ t, g t = Q + P := by
    rw [← hPici, ← integral_add_compl (measurableSet_Iio (a := (0:ℝ))) hgi, Set.compl_Iio]
  have hPnn : 0 ≤ P := integral_nonneg (fun t => hg_nn t)
  have hQnn : 0 ≤ Q := integral_nonneg (fun t => hg_nn t)
  rw [hPici, hsplit]
  -- first moments
  have hAB : ∫ t in Set.Iio 0, (-t) * g t = ∫ t in Set.Ioi 0, t * g t := by
    have h1 := integral_add_compl (measurableSet_Iio (a := (0:ℝ))) hgti
    rw [Set.compl_Iio, integral_Ici_eq_integral_Ioi, hmean] at h1
    have h2 : ∫ t in Set.Iio 0, (-t) * g t = -∫ t in Set.Iio 0, t * g t := by
      rw [← integral_neg]; simp only [neg_mul]
    rw [h2]; linarith
  -- P = 0 forces Q = 0
  have hP0_imp : P = 0 → Q = 0 := by
    intro hP0
    have h1 : g =ᵐ[volume.restrict (Set.Ioi 0)] 0 :=
      (integral_eq_zero_iff_of_nonneg (fun t => hg_nn t) hgi.integrableOn).mp hP0
    have h2 : ∀ᵐ t, t ∈ Set.Ioi (0:ℝ) → g t = 0 := (ae_restrict_iff' measurableSet_Ioi).mp h1
    have h3 : 0 ≤ᵐ[volume] (fun t => -(t * g t)) := by
      filter_upwards [h2] with t ht
      by_cases htp : 0 < t
      · simp [ht htp]
      · have : t ≤ 0 := not_lt.mp htp
        have := hg_nn t
        simp only [Pi.zero_apply]
        nlinarith
    have h4 : ∫ t, -(t * g t) = 0 := by rw [integral_neg, hmean, neg_zero]
    have h5 : (fun t => -(t * g t)) =ᵐ[volume] 0 :=
      (integral_eq_zero_iff_of_nonneg_ae h3 hgti.neg).mp h4
    have h6 : ∀ᵐ t : ℝ, t ≠ 0 := by
      rw [ae_iff]; simp
    have h7 : g =ᵐ[volume] 0 := by
      filter_upwards [h5, h6] with t ht ht0
      simp only [Pi.zero_apply, neg_eq_zero] at ht ⊢
      exact (mul_eq_zero.mp ht).resolve_left ht0
    have h8 : ∫ t, g t = 0 := integral_eq_zero_of_ae h7
    rw [hsplit, hP0] at h8
    linarith
  -- main case analysis
  by_cases hP0 : P = 0
  · rw [hP0, hP0_imp hP0]; simp
  have hPpos : 0 < P := lt_of_le_of_ne hPnn (Ne.symm hP0)
  by_cases hg0 : g 0 = 0
  · -- g 0 = 0 : g vanishes on one side
    have hside : (∀ t, 0 < t → g t = 0) ∨ (∀ s, s < 0 → g s = 0) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨⟨t, ht, hgt⟩, ⟨s, hs, hgs⟩⟩ := hcon
      have hts : 0 < t - s := by linarith
      obtain ⟨θ, hθ⟩ : ∃ θ, θ = t / (t - s) := ⟨_, rfl⟩
      have hθ0 : 0 < θ := hθ ▸ div_pos ht hts
      have hθ1 : θ < 1 := by rw [hθ, div_lt_one hts]; linarith
      have hcomb : θ * s + (1 - θ) * t = 0 := by
        rw [hθ]; field_simp; ring
      have hlc := hg_lc s t θ hθ0 hθ1
      rw [hcomb, hg0] at hlc
      have hnn : 0 ≤ g s ^ θ * g t ^ (1 - θ) :=
        mul_nonneg (Real.rpow_nonneg (hg_nn s) _) (Real.rpow_nonneg (hg_nn t) _)
      have heq : g s ^ θ * g t ^ (1 - θ) = 0 := le_antisymm hlc hnn
      rcases mul_eq_zero.mp heq with h | h
      · exact hgs ((Real.rpow_eq_zero_iff_of_nonneg (hg_nn s)).mp h).1
      · exact hgt ((Real.rpow_eq_zero_iff_of_nonneg (hg_nn t)).mp h).1
    rcases hside with h | h
    · exfalso
      apply hP0
      exact setIntegral_eq_zero_of_forall_eq_zero (fun t ht => h t ht)
    · have hQ0 : Q = 0 := setIntegral_eq_zero_of_forall_eq_zero (fun t ht => h t ht)
      rw [hQ0, zero_add]
      have : Real.exp (-1) ≤ 1 := by
        rw [Real.exp_le_one_iff]; norm_num
      nlinarith
  have hc : 0 < g 0 := lt_of_le_of_ne (hg_nn 0) (Ne.symm hg0)
  obtain ⟨β, hβdef⟩ : ∃ β, β = g 0 / P := ⟨_, rfl⟩
  have hβ : 0 < β := hβdef ▸ div_pos hc hPpos
  have hP : ∫ t in Set.Ioi 0, g t = g 0 / β := by
    show P = g 0 / β
    rw [hβdef]; field_simp
  have hup := grun_1d_upper g a b hg_supp hg_lc β hc hβ hP
  have hdom := grun_1d_dom g hg_nn hg_meas hg_lc β hc hβ hP
  have hbath := grun_1d_bathtub g hg_nn hg_meas a b M hg_supp hg_bdd (g 0) β hc hβ hdom
  rw [← hQdef] at hbath
  have hK : 0 < g 0 / β ^ 2 := by positivity
  obtain ⟨x, hxdef⟩ : ∃ x, x = β / g 0 * Q := ⟨_, rfl⟩
  rw [← hxdef] at hbath
  have hxnn : 0 ≤ x := by rw [hxdef]; positivity
  have h1 : (1 + x) * Real.log (1 + x) - x ≤ 1 := by
    have h0 := hbath.trans (hAB ▸ hup)
    by_contra hcon
    push_neg at hcon
    have : g 0 / β ^ 2 * 1 < g 0 / β ^ 2 * ((1 + x) * Real.log (1 + x) - x) :=
      mul_lt_mul_of_pos_left hcon hK
    linarith
  have h2 : Real.log (1 + x) ≤ 1 := by
    have h1x : 0 < 1 + x := by linarith
    by_contra hcon
    push_neg at hcon
    have : (1 + x) * 1 < (1 + x) * Real.log (1 + x) := mul_lt_mul_of_pos_left hcon h1x
    linarith
  have h3 : 1 + x ≤ Real.exp 1 := (Real.log_le_iff_le_exp (by linarith)).mp h2
  have hxP : x * P = Q := by
    rw [hxdef, hβdef]; field_simp
  have h4 : Q + P ≤ Real.exp 1 * P := by
    nlinarith
  have h5 : Real.exp (-1) * Real.exp 1 = 1 := by
    rw [← Real.exp_add]; norm_num
  calc Real.exp (-1) * (Q + P) ≤ Real.exp (-1) * (Real.exp 1 * P) :=
        mul_le_mul_of_nonneg_left h4 (Real.exp_pos _).le
    _ = P := by rw [← mul_assoc, h5, one_mul]







/-- Grünbaum's inequality in coordinates `ℝ × (Fin m → ℝ)`, halfspace `{0 ≤ p.1}`. -/
lemma grun_core (m : ℕ) (S : Set (ℝ × (Fin m → ℝ))) (hS : IsCompact S) (hSc : Convex ℝ S)
    (hmean : ∫ p in S, p.1 = 0) :
    Real.exp (-1) * (volume S).toReal ≤ (volume (S ∩ {p | 0 ≤ p.1})).toReal := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  set f : ℝ → ℝ≥0∞ := fun t => volume (Prod.mk t ⁻¹' S) with hf_def
  have hfm : Measurable f := measurable_measure_prodMk_left hSm
  set g : ℝ → ℝ := fun t => (f t).toReal with hg_def
  set T : Set (Fin m → ℝ) := Prod.snd '' S with hT_def
  have hTc : IsCompact T := hS.image continuous_snd
  have hslice_sub : ∀ t, Prod.mk t ⁻¹' S ⊆ T := fun t y hy => ⟨(t, y), hy, rfl⟩
  have hf_le : ∀ t, f t ≤ volume T := fun t => measure_mono (hslice_sub t)
  have hT_lt : volume T < ∞ := hTc.measure_lt_top
  have hf_lt : ∀ t, f t < ∞ := fun t => lt_of_le_of_lt (hf_le t) hT_lt
  have hslice_c : ∀ t, IsCompact (Prod.mk t ⁻¹' S) := fun t =>
    hTc.of_isClosed_subset (hS.isClosed.preimage (Continuous.prodMk_right t)) (hslice_sub t)
  obtain ⟨a, ha⟩ := (hS.image continuous_fst).bddBelow
  obtain ⟨b, hb⟩ := (hS.image continuous_fst).bddAbove
  have hg_supp : ∀ t, t ∉ Set.Icc a b → g t = 0 := by
    intro t ht
    have hempty : Prod.mk t ⁻¹' S = ∅ := by
      ext y
      simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
      intro hy
      exact ht ⟨ha ⟨(t, y), hy, rfl⟩, hb ⟨(t, y), hy, rfl⟩⟩
    show (volume (Prod.mk t ⁻¹' S)).toReal = 0
    rw [hempty]
    simp
  have hg_bdd : ∀ t, g t ≤ (volume T).toReal := fun t =>
    ENNReal.toReal_mono hT_lt.ne (hf_le t)
  have hg_lc : ∀ s t θ : ℝ, 0 < θ → θ < 1 →
      g s ^ θ * g t ^ (1 - θ) ≤ g (θ * s + (1 - θ) * t) := by
    intro s t θ hθ0 hθ1
    have hbm := grun_bm m (Prod.mk s ⁻¹' S) (Prod.mk t ⁻¹' S)
      (Prod.mk (θ * s + (1 - θ) * t) ⁻¹' S)
      (hslice_c s) (hslice_c t) (measurable_prodMk_left hSm) θ hθ0 hθ1 (by
        intro x hx y hy
        have h : θ • (s, x) + (1 - θ) • (t, y) ∈ S :=
          hSc (show (s, x) ∈ S from hx) (show (t, y) ∈ S from hy) hθ0.le
            (by linarith) (by ring)
        simp only [Set.mem_preimage]
        convert h using 1)
    show (f s).toReal ^ θ * (f t).toReal ^ (1 - θ) ≤ (f (θ * s + (1 - θ) * t)).toReal
    rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono (hf_lt _).ne hbm
  have hvolS : volume S = ∫⁻ t, f t := by
    rw [Measure.volume_eq_prod, Measure.prod_apply hSm]
  have hvolS' : volume (S ∩ {p | 0 ≤ p.1}) = ∫⁻ t in Set.Ici 0, f t := by
    have hHm : MeasurableSet {p : ℝ × (Fin m → ℝ) | 0 ≤ p.1} :=
      measurableSet_le measurable_const measurable_fst
    rw [Measure.volume_eq_prod, Measure.prod_apply (hSm.inter hHm),
      ← lintegral_indicator measurableSet_Ici]
    apply lintegral_congr
    intro t
    by_cases ht : 0 ≤ t
    · have h1 : Prod.mk t ⁻¹' (S ∩ {p | 0 ≤ p.1}) = Prod.mk t ⁻¹' S := by
        ext y; simp [ht]
      rw [h1, Set.indicator_of_mem (show t ∈ Set.Ici 0 from ht)]
    · have h1 : Prod.mk t ⁻¹' (S ∩ {p | 0 ≤ p.1}) = ∅ := by
        ext y; simp [ht]
      rw [h1, Set.indicator_of_notMem (show t ∉ Set.Ici 0 from ht)]
      simp
  have hint : ∫ t, g t = (volume S).toReal := by
    rw [hvolS]
    exact integral_toReal hfm.aemeasurable (ae_of_all _ hf_lt)
  have hint' : ∫ t in Set.Ici 0, g t = (volume (S ∩ {p | 0 ≤ p.1})).toReal := by
    rw [hvolS']
    exact integral_toReal hfm.aemeasurable (ae_of_all _ hf_lt)
  have hmean' : ∫ t, t * g t = 0 := by
    have hint_S : Integrable (S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1))
        ((volume : Measure ℝ).prod (volume : Measure (Fin m → ℝ))) := by
      rw [integrable_indicator_iff hSm]
      exact continuous_fst.continuousOn.integrableOn_compact hS
    rw [← integral_indicator hSm, Measure.volume_eq_prod, integral_prod _ hint_S] at hmean
    rw [← hmean]
    congr 1
    ext t
    have h1 : (fun y => S.indicator (fun p : ℝ × (Fin m → ℝ) => p.1) (t, y))
        = (Prod.mk t ⁻¹' S).indicator (fun _ => t) := by
      ext y
      by_cases hy : (t, y) ∈ S
      · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show y ∈ Prod.mk t ⁻¹' S from hy)]
      · rw [Set.indicator_of_notMem hy,
          Set.indicator_of_notMem (show y ∉ Prod.mk t ⁻¹' S from hy)]
    rw [h1, integral_indicator_const t (measurable_prodMk_left hSm), smul_eq_mul, mul_comm]
    rfl
  have key := grun_1d g (fun t => ENNReal.toReal_nonneg) hfm.ennreal_toReal a b
    (volume T).toReal hg_supp hg_bdd hg_lc hmean'
  rw [hint, hint'] at key
  exact key

theorem grunbaum {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (w : EuclideanSpace ℝ (Fin n))
  (hK_compact : IsCompact K)
  (hK_convex : Convex ℝ K)
  (hK_int : Set.Nonempty (interior K))
  (hK_centered : barycenter K = 0)
  (hw : w ≠ 0) :
  (volume (K ∩ {x | 0 ≤ inner ℝ w x})).toReal ≥
    Real.exp (-1) * (volume K).toReal := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := by
    rcases n with _ | m
    · exact absurd (by ext i; exact i.elim0) hw
    · exact ⟨m, rfl⟩
  have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw
  set u : EuclideanSpace ℝ (Fin (m+1)) := ‖w‖⁻¹ • w with hu
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hwn.ne']
  obtain ⟨b, hb⟩ : ∃ b : OrthonormalBasis (Fin (m+1)) ℝ (EuclideanSpace ℝ (Fin (m+1))),
      ∀ i ∈ ({0} : Set (Fin (m+1))), b i = (fun _ => u) i := by
    apply Orthonormal.exists_orthonormalBasis_extension_of_card_eq
    · simp
    · refine ⟨fun i => by simpa using hu1, fun i j hij => ?_⟩
      have h1 : (i : Fin (m+1)) = 0 := i.2
      have h2 : (j : Fin (m+1)) = 0 := j.2
      exact absurd (Subtype.ext (h1.trans h2.symm)) hij
  have hb0 : b 0 = u := hb 0 rfl
  let T : EuclideanSpace ℝ (Fin (m+1)) ≃ᵐ ℝ × (Fin m → ℝ) :=
    b.measurableEquiv.trans ((MeasurableEquiv.toLp 2 (Fin (m+1) → ℝ)).symm.trans
      (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0))
  have hT : MeasurePreserving T volume volume := by
    have h1 := b.measurePreserving_measurableEquiv
    have h2 := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin (m+1))
    have h3 := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (m+1) => ℝ) 0
    exact (h3.comp h2).comp h1
  have hT_apply : ∀ x, T x = (inner ℝ u x, fun i => inner ℝ (b i.succ) x) := by
    intro x
    simp only [T, MeasurableEquiv.trans_apply, MeasurableEquiv.piFinSuccAbove_apply,
      OrthonormalBasis.measurableEquiv]
    refine Prod.ext ?_ ?_
    · rw [← hb0, ← b.repr_apply_apply x 0]; rfl
    · funext i
      have := b.repr_apply_apply x i.succ
      simp only [Fin.insertNthEquiv, Equiv.coe_fn_symm_mk, Fin.removeNth, Fin.succAbove_zero] at this ⊢
      rw [← this]; rfl
  let L : EuclideanSpace ℝ (Fin (m+1)) →ₗ[ℝ] ℝ × (Fin m → ℝ) :=
    LinearMap.prod (innerₛₗ ℝ u) (LinearMap.pi fun i => innerₛₗ ℝ (b i.succ))
  have hLT : ⇑L = ⇑T := by
    funext x; rw [hT_apply]
    refine Prod.ext ?_ ?_
    · simp [L]
    · funext i; simp [L]
  set S : Set (ℝ × (Fin m → ℝ)) := T '' K with hS_def
  have hS_compact : IsCompact S := by
    rw [hS_def, ← hLT]; exact hK_compact.image (LinearMap.continuous_of_finiteDimensional L)
  have hS_convex : Convex ℝ S := by
    rw [hS_def, ← hLT]; exact hK_convex.linear_image L
  have hKS : T ⁻¹' S = K := Set.preimage_image_eq K T.injective
  have hvolK : volume K = volume S := by
    rw [← hKS]; exact hT.measure_preimage_equiv S
  have hhalf : K ∩ {x | 0 ≤ inner ℝ w x} = T ⁻¹' (S ∩ {p | 0 ≤ p.1}) := by
    rw [Set.preimage_inter, hKS]
    congr 1
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hT_apply, hu, inner_smul_left]
    simp only [conj_trivial]
    constructor
    · intro h; exact mul_nonneg (inv_nonneg.mpr (norm_nonneg w)) h
    · intro h
      exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hwn)).mp h
  have hvolH : volume (K ∩ {x | 0 ≤ inner ℝ w x}) = volume (S ∩ {p | 0 ≤ p.1}) := by
    rw [hhalf]; exact hT.measure_preimage_equiv _
  have hvolpos : 0 < volume K := MeasureTheory.Measure.measure_pos_of_nonempty_interior _ hK_int
  have hvolfin : volume K < ∞ := hK_compact.measure_lt_top
  have hint0 : ∫ x in K, x = 0 := by
    unfold barycenter at hK_centered
    rcases smul_eq_zero.mp hK_centered with h | h
    · exfalso
      have : 0 < volume.real K := ENNReal.toReal_pos hvolpos.ne' hvolfin.ne
      exact (inv_pos.mpr this).ne' h
    · exact h
  have hS_mean : ∫ p in S, p.1 = 0 := by
    have h1 := hT.setIntegral_preimage_emb T.measurableEmbedding
      (fun p : ℝ × (Fin m → ℝ) => p.1) S
    rw [← h1, hKS]
    simp only [hT_apply]
    have := integral_inner (𝕜 := ℝ) (μ := volume.restrict K)
      (f := fun x : EuclideanSpace ℝ (Fin (m+1)) => x)
      (continuous_id.continuousOn.integrableOn_compact hK_compact) u
    rw [this, hint0, inner_zero_right]
  have key := grun_core m S hS_compact hS_convex hS_mean
  rw [ge_iff_le, hvolK, hvolH]
  exact key

end grunbaum
