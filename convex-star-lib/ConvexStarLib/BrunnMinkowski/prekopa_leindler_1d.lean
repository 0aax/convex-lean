import ConvexStarLib.Defs

/-!
# `prekopa_leindler_1d`

Source: BrunnMinkowski.

Statement from the `convex-eval-v28-2h/prekopa_leindler_1d` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace prekopa_leindler_1d`, so the main result is `prekopa_leindler_1d.prekopa_leindler_1d`.
-/

namespace prekopa_leindler_1d

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Set


namespace PL1D

open Filter

/-- 1D Brunn–Minkowski for compact nonempty sets. -/
lemma bm_compact {K L : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hK0 : K.Nonempty) (hL0 : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  set a := sSup K with ha_def
  set b := sInf L with hb_def
  have ha : a ∈ K := hK.sSup_mem hK0
  have hb : b ∈ L := hL.sInf_mem hL0
  have haK : ∀ x ∈ K, x ≤ a := fun x hx => le_csSup hK.bddAbove hx
  have hbL : ∀ y ∈ L, b ≤ y := fun y hy => csInf_le hL.bddBelow hy
  set S := (fun x => x + b) '' K with hS_def
  set T := (fun y => a + y) '' L with hT_def
  have hS : volume S = volume K := by
    rw [hS_def, image_add_right, measure_preimage_add_right]
  have hT : volume T = volume L := by
    rw [hT_def, image_add_left, measure_preimage_add]
  have hTm : MeasurableSet T :=
    (hL.image (continuous_const.add continuous_id)).isClosed.measurableSet
  have hSub : S ∪ T ⊆ K + L := by
    rintro _ (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact add_mem_add hx hb
    · exact add_mem_add ha hy
  have hInter : S ∩ T ⊆ {a + b} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h1 := haK x hx
    have h2 := hbL y hy
    simp only [mem_singleton_iff]
    linarith
  calc volume K + volume L = volume S + volume T := by rw [hS, hT]
    _ = volume (S ∪ T) + volume (S ∩ T) := (measure_union_add_inter S hTm).symm
    _ ≤ volume (K + L) + 0 :=
        add_le_add (measure_mono hSub) ((measure_mono hInter).trans (by simp))
    _ = volume (K + L) := add_zero _

/-- 1D Brunn–Minkowski for measurable nonempty sets (outer measure of the sumset). -/
lemma bm {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : A.Nonempty) (hB0 : B.Nonempty) :
    volume A + volume B ≤ volume (A + B) := by
  have key : ∀ K ⊆ A, ∀ L ⊆ B, IsCompact K → IsCompact L →
      volume K + volume L ≤ volume (A + B) := by
    intro K hKA L hLB hK hL
    rcases K.eq_empty_or_nonempty with rfl | hK0
    · obtain ⟨a, ha⟩ := hA0
      rw [measure_empty, zero_add]
      calc volume L = volume ((fun y => a + y) '' L) := by
            rw [image_add_left, measure_preimage_add]
        _ ≤ volume (A + B) := measure_mono (by
            rintro _ ⟨y, hy, rfl⟩
            exact add_mem_add ha (hLB hy))
    rcases L.eq_empty_or_nonempty with rfl | hL0
    · obtain ⟨b, hb⟩ := hB0
      rw [measure_empty, add_zero]
      calc volume K = volume ((fun x => x + b) '' K) := by
            rw [image_add_right, measure_preimage_add_right]
        _ ≤ volume (A + B) := measure_mono (by
            rintro _ ⟨x, hx, rfl⟩
            exact add_mem_add (hKA hx) hb)
    exact (bm_compact hK hL hK0 hL0).trans (measure_mono (add_subset_add hKA hLB))
  refine le_of_forall_lt (fun c hc => ?_)
  rcases eq_or_ne (volume A) 0 with h | h
  · rw [h, zero_add] at hc
    rcases hB.exists_lt_isCompact hc with ⟨L, hLB, hL, hcL⟩
    have := key ∅ (empty_subset _) L hLB isCompact_empty hL
    rw [measure_empty, zero_add] at this
    exact hcL.trans_le this
  rcases eq_or_ne (volume B) 0 with h' | h'
  · rw [h', add_zero] at hc
    rcases hA.exists_lt_isCompact hc with ⟨K, hKA, hK, hcK⟩
    have := key K hKA ∅ (empty_subset _) hK isCompact_empty
    rw [measure_empty, add_zero] at this
    exact hcK.trans_le this
  rcases ENNReal.exists_lt_add_of_lt_add hc h h' with ⟨u, hu, v, hv, huv⟩
  rcases hA.exists_lt_isCompact hu with ⟨K, hKA, hK, huK⟩
  rcases hB.exists_lt_isCompact hv with ⟨L, hLB, hL, hvL⟩
  exact huv.trans_le ((add_le_add huK.le hvL.le).trans (key K hKA L hLB hK hL))

/-- Scaled 1D Brunn–Minkowski. -/
lemma bm_smul {A B : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hA0 : A.Nonempty) (hB0 : B.Nonempty) {s t : ℝ} (hs : 0 < s) (ht : 0 < t) :
    ENNReal.ofReal s * volume A + ENNReal.ofReal t * volume B ≤ volume (s • A + t • B) := by
  have h1 : volume (s • A) = ENNReal.ofReal s * volume A := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos hs]
  have h2 : volume (t • B) = ENNReal.ofReal t * volume B := by
    rw [Measure.addHaar_smul]; simp [abs_of_pos ht]
  rw [← h1, ← h2]
  exact bm (hA.const_smul₀ s) (hB.const_smul₀ t) hA0.smul_set hB0.smul_set


/-- Weighted AM-GM in `ℝ≥0∞`. -/
lemma amgm {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1) (X Y : ℝ≥0∞) :
    X ^ (1 - lam) * Y ^ lam ≤ ENNReal.ofReal (1 - lam) * X + ENNReal.ofReal lam * Y := by
  rcases eq_or_ne X ⊤ with rfl | hX
  · have : ENNReal.ofReal (1 - lam) * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
    simp [this]
  rcases eq_or_ne Y ⊤ with rfl | hY
  · have : ENNReal.ofReal lam * ⊤ = ⊤ :=
      ENNReal.mul_top (by simp only [ne_eq, ENNReal.ofReal_eq_zero, not_le]; linarith)
    simp [this]
  lift X to ℝ≥0 using hX
  lift Y to ℝ≥0 using hY
  have h := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - lam))
    (Real.toNNReal lam) X Y
    (by rw [← Real.toNNReal_add (by linarith) hlam_pos.le]; simp)
  rw [Real.coe_toNNReal _ (by linarith), Real.coe_toNNReal _ hlam_pos.le] at h
  rw [← ENNReal.coe_rpow_of_nonneg _ (by linarith), ← ENNReal.coe_rpow_of_nonneg _ hlam_pos.le,
    ENNReal.ofReal, ENNReal.ofReal]
  exact_mod_cast h

/-- Layer cake for functions bounded by `1`. -/
lemma layer {w : ℝ → ℝ≥0∞} (hw : Measurable w) (hw1 : ∀ x, w x ≤ 1) :
    ∫⁻ z, w z = ∫⁻ t in Ioi 0, volume {z | ENNReal.ofReal t < w z} := by
  have hwt : ∀ z, w z ≠ ⊤ := fun z => ne_top_of_le_ne_top one_ne_top (hw1 z)
  have := lintegral_eq_lintegral_meas_lt volume (f := fun z => (w z).toReal)
    (Eventually.of_forall (fun z => ENNReal.toReal_nonneg)) hw.ennreal_toReal.aemeasurable
  simp only [ENNReal.ofReal_toReal (hwt _)] at this
  rw [this]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  congr 1
  ext z
  simp only [mem_setOf_eq]
  rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hwt z)]

/-- Normalized Prékopa–Leindler (additive form). -/
lemma pl_normalized {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfs : ∀ t < 1, ∃ x, t < f x) (hgs : ∀ t < 1, ∃ y, t < g y)
    (hyp : ∀ x y : ℝ, h ((1 - lam) * x + lam * y) ≥ (f x) ^ (1 - lam) * (g y) ^ lam) :
    ENNReal.ofReal (1 - lam) * (∫⁻ z, f z) + ENNReal.ofReal lam * (∫⁻ z, g z) ≤ ∫⁻ z, h z := by
  set h' : ℝ → ℝ≥0∞ := fun z => min (h z) 1 with h'_def
  have hh' : Measurable h' := hh.min measurable_const
  have hh'1 : ∀ z, h' z ≤ 1 := fun z => min_le_right _ _
  have hyp' : ∀ x y : ℝ, (f x) ^ (1 - lam) * (g y) ^ lam ≤ h' ((1 - lam) * x + lam * y) := by
    intro x y
    refine le_min (hyp x y) ?_
    calc (f x) ^ (1 - lam) * (g y) ^ lam ≤ 1 * 1 := by
          gcongr
          · exact ENNReal.rpow_le_one (hf1 x) (by linarith)
          · exact ENNReal.rpow_le_one (hg1 y) hlam_pos.le
      _ = 1 := one_mul 1
  have level : ∀ t : ℝ, ENNReal.ofReal (1 - lam) * volume {z | ENNReal.ofReal t < f z}
      + ENNReal.ofReal lam * volume {z | ENNReal.ofReal t < g z}
      ≤ volume {z | ENNReal.ofReal t < h' z} := by
    intro t
    by_cases ht : ENNReal.ofReal t < 1
    · obtain ⟨x0, hx0⟩ := hfs _ ht
      obtain ⟨y0, hy0⟩ := hgs _ ht
      have hsub : (1 - lam) • {z | ENNReal.ofReal t < f z} + lam • {z | ENNReal.ofReal t < g z}
          ⊆ {z | ENNReal.ofReal t < h' z} := by
        rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
        simp only [mem_setOf_eq, smul_eq_mul] at hx hy ⊢
        calc ENNReal.ofReal t = ENNReal.ofReal t ^ ((1 - lam) + lam) := by simp
          _ = ENNReal.ofReal t ^ (1 - lam) * ENNReal.ofReal t ^ lam :=
              ENNReal.rpow_add_of_nonneg _ _ (by linarith) hlam_pos.le
          _ < f x ^ (1 - lam) * g y ^ lam :=
              ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx (by linarith))
                (ENNReal.rpow_lt_rpow hy hlam_pos)
          _ ≤ h' ((1 - lam) * x + lam * y) := hyp' x y
      calc _ ≤ volume ((1 - lam) • {z | ENNReal.ofReal t < f z}
              + lam • {z | ENNReal.ofReal t < g z}) :=
            bm_smul (measurableSet_lt measurable_const hf) (measurableSet_lt measurable_const hg)
              ⟨x0, hx0⟩ ⟨y0, hy0⟩ (by linarith) hlam_pos
        _ ≤ _ := measure_mono hsub
    · push_neg at ht
      have e1 : {z | ENNReal.ofReal t < f z} = ∅ := by
        ext z
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hf1 z).trans ht
      have e2 : {z | ENNReal.ofReal t < g z} = ∅ := by
        ext z
        simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
        exact (hg1 z).trans ht
      simp [e1, e2]
  calc ENNReal.ofReal (1 - lam) * (∫⁻ z, f z) + ENNReal.ofReal lam * (∫⁻ z, g z)
      = (∫⁻ t in Ioi 0, ENNReal.ofReal (1 - lam) * volume {z | ENNReal.ofReal t < f z})
        + ∫⁻ t in Ioi 0, ENNReal.ofReal lam * volume {z | ENNReal.ofReal t < g z} := by
        rw [layer hf hf1, layer hg hg1, lintegral_const_mul' _ _ ofReal_ne_top,
          lintegral_const_mul' _ _ ofReal_ne_top]
    _ ≤ ∫⁻ t in Ioi 0, (ENNReal.ofReal (1 - lam) * volume {z | ENNReal.ofReal t < f z}
        + ENNReal.ofReal lam * volume {z | ENNReal.ofReal t < g z}) := le_lintegral_add _ _
    _ ≤ ∫⁻ t in Ioi 0, volume {z | ENNReal.ofReal t < h' z} := lintegral_mono level
    _ = ∫⁻ z, h' z := (layer hh' hh'1).symm
    _ ≤ ∫⁻ z, h z := lintegral_mono (fun z => min_le_left _ _)


/-- Normalized Prékopa–Leindler (multiplicative form). -/
lemma pl_normalized' {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ y, g y ≤ 1)
    (hfs : ∀ t < 1, ∃ x, t < f x) (hgs : ∀ t < 1, ∃ y, t < g y)
    (hyp : ∀ x y : ℝ, h ((1 - lam) * x + lam * y) ≥ (f x) ^ (1 - lam) * (g y) ^ lam) :
    (∫⁻ z, f z) ^ (1 - lam) * (∫⁻ z, g z) ^ lam ≤ ∫⁻ z, h z :=
  (amgm hlam_pos hlam_lt _ _).trans (pl_normalized hlam_pos hlam_lt hf hg hh hf1 hg1 hfs hgs hyp)

/-- Normalization of a function with finite positive supremum. -/
lemma normalize_aux {f : ℝ → ℝ≥0∞} {a : ℝ≥0∞} (ha : a = ⨆ x, f x) (ha0 : a ≠ 0)
    (ha_top : a ≠ ⊤) :
    (∀ x, a⁻¹ * f x ≤ 1) ∧ (∀ t < 1, ∃ x, t < a⁻¹ * f x) := by
  refine ⟨fun x => ?_, fun t ht => ?_⟩
  · calc a⁻¹ * f x ≤ a⁻¹ * a := mul_le_mul_right (ha ▸ le_iSup f x) _
      _ = 1 := ENNReal.inv_mul_cancel ha0 ha_top
  · have h1 : a * t < a := by
      calc a * t < a * 1 := ENNReal.mul_lt_mul_right ha0 ha_top ht
        _ = a := mul_one a
    rw [ha] at h1
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 h1
    rw [← ha] at hx
    refine ⟨x, ?_⟩
    have h2 := ENNReal.mul_lt_mul_right (ENNReal.inv_ne_zero.2 ha_top) (ENNReal.inv_ne_top.2 ha0) hx
    rwa [← mul_assoc, ENNReal.inv_mul_cancel ha0 ha_top, one_mul] at h2

/-- Prékopa–Leindler for bounded `f`, `g`. -/
lemma pl_bounded {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
    {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {M : ℝ≥0∞} (hM : M ≠ ⊤) (hfM : ∀ x, f x ≤ M) (hgM : ∀ y, g y ≤ M)
    (hyp : ∀ x y : ℝ, h ((1 - lam) * x + lam * y) ≥ (f x) ^ (1 - lam) * (g y) ^ lam) :
    (∫⁻ z, f z) ^ (1 - lam) * (∫⁻ z, g z) ^ lam ≤ ∫⁻ z, h z := by
  have h1lam : 0 < 1 - lam := by linarith
  obtain ⟨a, ha⟩ : ∃ a, a = ⨆ x, f x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = ⨆ y, g y := ⟨_, rfl⟩
  have ha_top : a ≠ ⊤ := ne_top_of_le_ne_top hM (ha ▸ iSup_le hfM)
  have hb_top : b ≠ ⊤ := ne_top_of_le_ne_top hM (hb ▸ iSup_le hgM)
  rcases eq_or_ne a 0 with ha0 | ha0
  · have : ∀ x, f x = 0 := fun x => le_antisymm (ha0 ▸ ha ▸ le_iSup f x) (zero_le _)
    have hf0 : ∫⁻ z, f z = 0 := by simp [this]
    rw [hf0, ENNReal.zero_rpow_of_pos h1lam, zero_mul]
    exact zero_le _
  rcases eq_or_ne b 0 with hb0 | hb0
  · have : ∀ y, g y = 0 := fun y => le_antisymm (hb0 ▸ hb ▸ le_iSup g y) (zero_le _)
    have hg0 : ∫⁻ z, g z = 0 := by simp [this]
    rw [hg0, ENNReal.zero_rpow_of_pos hlam_pos, mul_zero]
    exact zero_le _
  obtain ⟨c, hc⟩ : ∃ c, c = a ^ (1 - lam) * b ^ lam := ⟨_, rfl⟩
  have hc0 : c ≠ 0 := hc ▸ mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha_top).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hb_top).ne'
  have hct : c ≠ ⊤ := hc ▸ ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg h1lam.le ha_top)
    (ENNReal.rpow_ne_top_of_nonneg hlam_pos.le hb_top)
  have iden : ∀ X Y : ℝ≥0∞, (a⁻¹ * X) ^ (1 - lam) * (b⁻¹ * Y) ^ lam
      = c⁻¹ * (X ^ (1 - lam) * Y ^ lam) := by
    intro X Y
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1lam.le, ENNReal.mul_rpow_of_nonneg _ _ hlam_pos.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hc,
      ENNReal.mul_inv (Or.inl (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha_top).ne')
        (Or.inl (ENNReal.rpow_ne_top_of_nonneg h1lam.le ha_top))]
    ring
  obtain ⟨hf1, hfs⟩ := normalize_aux ha ha0 ha_top
  obtain ⟨hg1, hgs⟩ := normalize_aux hb hb0 hb_top
  have hyp' : ∀ x y : ℝ, c⁻¹ * h ((1 - lam) * x + lam * y) ≥
      (a⁻¹ * f x) ^ (1 - lam) * (b⁻¹ * g y) ^ lam := by
    intro x y
    rw [iden]
    exact mul_le_mul_right (hyp x y) _
  have key := pl_normalized' hlam_pos hlam_lt (f := fun x => a⁻¹ * f x)
    (g := fun y => b⁻¹ * g y) (h := fun z => c⁻¹ * h z) (hf.const_mul _) (hg.const_mul _)
    (hh.const_mul _) hf1 hg1 hfs hgs hyp'
  rw [lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 ha0),
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hb0),
    lintegral_const_mul' _ _ (ENNReal.inv_ne_top.2 hc0), iden] at key
  exact (ENNReal.mul_le_mul_iff_right (ENNReal.inv_ne_zero.2 hct) (ENNReal.inv_ne_top.2 hc0)).1 key


theorem main
  {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  {f g h : ℝ → ℝ≥0∞}
  (hf : Measurable f) (hg : Measurable g)
  (hh : Measurable h)
  (hyp : ∀ x y : ℝ,
    h ((1 - lam) * x + lam * y) ≥
      (f x) ^ (1 - lam) * (g y) ^ lam) :
  ∫⁻ z, h z ≥
    (∫⁻ z, f z) ^ (1 - lam) *
    (∫⁻ z, g z) ^ lam := by
  have h1lam : 0 < 1 - lam := by linarith
  -- truncations
  obtain ⟨F, hF⟩ : ∃ F : ℕ → ℝ → ℝ≥0∞, F = fun (n : ℕ) x => min (f x) (n : ℝ≥0∞) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G : ℕ → ℝ → ℝ≥0∞, G = fun (n : ℕ) y => min (g y) (n : ℝ≥0∞) := ⟨_, rfl⟩
  have hFm : ∀ n, Measurable (F n) := fun n => hF ▸ hf.min measurable_const
  have hGm : ∀ n, Measurable (G n) := fun n => hG ▸ hg.min measurable_const
  have hbound : ∀ n, (∫⁻ z, F n z) ^ (1 - lam) * (∫⁻ z, G n z) ^ lam ≤ ∫⁻ z, h z := by
    intro n
    refine pl_bounded hlam_pos hlam_lt (hFm n) (hGm n) hh (M := n) (natCast_ne_top n)
      (fun x => hF ▸ min_le_right _ _) (fun y => hG ▸ min_le_right _ _) ?_
    intro x y
    calc (F n x) ^ (1 - lam) * (G n y) ^ lam ≤ f x ^ (1 - lam) * g y ^ lam :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hF ▸ min_le_left _ _) h1lam.le)
            (ENNReal.rpow_le_rpow (hG ▸ min_le_left _ _) hlam_pos.le)
      _ ≤ h ((1 - lam) * x + lam * y) := hyp x y
  have hFmono : Monotone F := by
    intro m n hmn x
    rw [hF]
    exact min_le_min_left _ (by exact_mod_cast hmn)
  have hGmono : Monotone G := by
    intro m n hmn x
    rw [hG]
    exact min_le_min_left _ (by exact_mod_cast hmn)
  have hFsup : ∀ x, ⨆ n, F n x = f x := by
    intro x
    rw [hF]
    refine le_antisymm (iSup_le fun n => min_le_left _ _) (le_of_forall_lt fun c hc => ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    exact lt_of_lt_of_le (lt_min hc hn) (le_iSup (fun n : ℕ => min (f x) (n : ℝ≥0∞)) n)
  have hGsup : ∀ y, ⨆ n, G n y = g y := by
    intro y
    rw [hG]
    refine le_antisymm (iSup_le fun n => min_le_left _ _) (le_of_forall_lt fun c hc => ?_)
    obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (ne_top_of_lt hc)
    exact lt_of_lt_of_le (lt_min hc hn) (le_iSup (fun n : ℕ => min (g y) (n : ℝ≥0∞)) n)
  have hFlim : Tendsto (fun n => ∫⁻ z, F n z) atTop (𝓝 (∫⁻ z, f z)) := by
    have := lintegral_iSup (μ := volume) hFm hFmono
    simp only [hFsup] at this
    rw [this]
    exact tendsto_atTop_iSup (fun m n hmn => lintegral_mono (hFmono hmn))
  have hGlim : Tendsto (fun n => ∫⁻ z, G n z) atTop (𝓝 (∫⁻ z, g z)) := by
    have := lintegral_iSup (μ := volume) hGm hGmono
    simp only [hGsup] at this
    rw [this]
    exact tendsto_atTop_iSup (fun m n hmn => lintegral_mono (hGmono hmn))
  rcases eq_or_ne (∫⁻ z, f z) 0 with hf0 | hf0
  · rw [hf0, ENNReal.zero_rpow_of_pos h1lam, zero_mul]
    exact zero_le _
  rcases eq_or_ne (∫⁻ z, g z) 0 with hg0 | hg0
  · rw [hg0, ENNReal.zero_rpow_of_pos hlam_pos, mul_zero]
    exact zero_le _
  have hlim : Tendsto (fun n => (∫⁻ z, F n z) ^ (1 - lam) * (∫⁻ z, G n z) ^ lam) atTop
      (𝓝 ((∫⁻ z, f z) ^ (1 - lam) * (∫⁻ z, g z) ^ lam)) := by
    apply ENNReal.Tendsto.mul
    · exact (ENNReal.continuous_rpow_const.tendsto _).comp hFlim
    · left
      intro h0
      rw [ENNReal.rpow_eq_zero_iff] at h0
      rcases h0 with ⟨h0, _⟩ | ⟨_, h0⟩
      · exact hf0 h0
      · linarith
    · exact (ENNReal.continuous_rpow_const.tendsto _).comp hGlim
    · left
      intro h0
      rw [ENNReal.rpow_eq_zero_iff] at h0
      rcases h0 with ⟨h0, _⟩ | ⟨_, h0⟩
      · exact hg0 h0
      · linarith
  exact le_of_tendsto' hlim hbound

end PL1D

theorem prekopa_leindler_1d
  {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  {f g h : ℝ → ℝ≥0∞}
  (hf : Measurable f) (hg : Measurable g)
  (hh : Measurable h)
  (hyp : ∀ x y : ℝ,
    h ((1 - lam) * x + lam * y) ≥
      (f x) ^ (1 - lam) * (g y) ^ lam) :
  ∫⁻ z, h z ≥
    (∫⁻ z, f z) ^ (1 - lam) *
    (∫⁻ z, g z) ^ lam := by
  exact PL1D.main hlam_pos hlam_lt hf hg hh hyp

end prekopa_leindler_1d
