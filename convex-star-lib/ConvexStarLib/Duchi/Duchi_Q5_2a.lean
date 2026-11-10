import ConvexStarLib.Defs

/-!
# `Duchi_Q5_2a`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q5_2a` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q5_2a`, so the main result is `Duchi_Q5_2a.Duchi_Q5_2a`.
-/

namespace Duchi_Q5_2a

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


namespace PrekopaAux

open Set Filter

/-- Prékopa–Leindler property of a measure space with a real vector space structure. -/
def PLProp (E : Type*) [AddCommGroup E] [Module ℝ E] [MeasureSpace E] : Prop :=
  ∀ (l : ℝ), 0 < l → l < 1 → ∀ (f g h : E → ℝ≥0∞), Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ l * g y ^ (1 - l) ≤ h (l • x + (1 - l) • y)) →
    (∫⁻ x, f x) ^ l * (∫⁻ x, g x) ^ (1 - l) ≤ ∫⁻ x, h x

/-- One-dimensional Brunn–Minkowski inequality for nonempty compact sets. -/
theorem bm_compact {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {K L C : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hC : ∀ x ∈ K, ∀ y ∈ L, l * x + (1 - l) * y ∈ C) :
    ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L ≤ volume C := by
  set a := sSup K with ha_def
  set b := sInf L with hb_def
  have ha : a ∈ K := hK.sSup_mem hKne
  have hb : b ∈ L := hL.sInf_mem hLne
  have hK' : volume (AffineMap.homothety b l '' K) = ENNReal.ofReal l * volume K := by
    rw [Measure.addHaar_image_homothety]
    simp [abs_of_pos hl0]
  have hL' : volume (AffineMap.homothety a (1 - l) '' L) = ENNReal.ofReal (1 - l) * volume L := by
    rw [Measure.addHaar_image_homothety]
    simp [abs_of_pos (sub_pos.2 hl1)]
  have hK'C : AffineMap.homothety b l '' K ⊆ C := by
    rintro _ ⟨x, hx, rfl⟩
    have := hC x hx b hb
    convert this using 1
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have hL'C : AffineMap.homothety a (1 - l) '' L ⊆ C := by
    rintro _ ⟨y, hy, rfl⟩
    have := hC a ha y hy
    convert this using 1
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]
    ring
  have hL'meas : MeasurableSet (AffineMap.homothety a (1 - l) '' L) :=
    (hL.image (AffineMap.homothety_continuous a (1 - l))).isClosed.measurableSet
  have hinter : AffineMap.homothety b l '' K ∩ AffineMap.homothety a (1 - l) '' L ⊆
      {l * a + (1 - l) * b} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have hxa : x ≤ a := le_csSup hK.bddAbove hx
    have hyb : b ≤ y := csInf_le hL.bddBelow hy
    simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul] at hxy ⊢
    simp only [mem_singleton_iff]
    have h1 : 0 ≤ l * (a - x) := mul_nonneg hl0.le (sub_nonneg.2 hxa)
    have h2 : 0 ≤ (1 - l) * (y - b) := mul_nonneg (sub_pos.2 hl1).le (sub_nonneg.2 hyb)
    nlinarith
  calc ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L
      = volume (AffineMap.homothety b l '' K) + volume (AffineMap.homothety a (1 - l) '' L) := by
        rw [hK', hL']
    _ = volume (AffineMap.homothety b l '' K ∪ AffineMap.homothety a (1 - l) '' L)
        + volume (AffineMap.homothety b l '' K ∩ AffineMap.homothety a (1 - l) '' L) :=
        (measure_union_add_inter _ hL'meas).symm
    _ = volume (AffineMap.homothety b l '' K ∪ AffineMap.homothety a (1 - l) '' L) := by
        rw [measure_mono_null hinter (measure_singleton _), add_zero]
    _ ≤ volume C := measure_mono (union_subset hK'C hL'C)

theorem iSup_compact_add_le {A : Set ℝ} (hA : MeasurableSet A) {c y z : ℝ≥0∞}
    (h : ∀ K ⊆ A, IsCompact K → c * volume K + y ≤ z) : c * volume A + y ≤ z := by
  rw [hA.measure_eq_iSup_isCompact, ENNReal.mul_iSup, ENNReal.iSup_add]
  refine iSup_le fun K => ?_
  by_cases hKA : K ⊆ A
  · by_cases hK : IsCompact K
    · simpa [hKA, hK] using h K hKA hK
    · simpa [hKA, hK] using h ∅ (empty_subset _) isCompact_empty
  · simpa [hKA] using h ∅ (empty_subset _) isCompact_empty

/-- One-dimensional Brunn–Minkowski inequality for nonempty measurable sets. -/
theorem bm_meas {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hC : ∀ x ∈ A, ∀ y ∈ B, l * x + (1 - l) * y ∈ C) :
    ENNReal.ofReal l * volume A + ENNReal.ofReal (1 - l) * volume B ≤ volume C := by
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  have key : ∀ K, K ⊆ A → IsCompact K → ∀ L, L ⊆ B → IsCompact L →
      ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L ≤ volume C := by
    intro K hKA hK L hLB hL
    calc ENNReal.ofReal l * volume K + ENNReal.ofReal (1 - l) * volume L
        ≤ ENNReal.ofReal l * volume (insert a₀ K)
          + ENNReal.ofReal (1 - l) * volume (insert b₀ L) := by
          gcongr <;> exact subset_insert _ _
      _ ≤ volume C := bm_compact hl0 hl1 (hK.insert a₀) (hL.insert b₀) (insert_nonempty _ _)
          (insert_nonempty _ _)
          (fun x hx y hy => hC x (insert_subset ha₀ hKA hx) y (insert_subset hb₀ hLB hy))
  rw [add_comm]
  refine iSup_compact_add_le hB fun L hLB hL => ?_
  rw [add_comm]
  exact iSup_compact_add_le hA fun K hKA hK => key K hKA hK L hLB hL

/-- Layer cake formula for finite-valued `ℝ≥0∞` functions. -/
theorem layer_cake {α : Type*} [MeasurableSpace α] (μ : Measure α) {F : α → ℝ≥0∞}
    (hF : Measurable F) (hFt : ∀ x, F x ≠ ∞) :
    ∫⁻ x, F x ∂μ = ∫⁻ t in Ioi (0:ℝ), μ {x | ENNReal.ofReal t < F x} := by
  have h := lintegral_eq_lintegral_meas_lt μ (f := fun x => (F x).toReal)
    (Eventually.of_forall fun x => ENNReal.toReal_nonneg) hF.ennreal_toReal.aemeasurable
  simp only [ne_eq, hFt, not_false_eq_true, ENNReal.ofReal_toReal] at h
  rw [h]
  refine setLIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
  congr 1
  ext x
  simp only [mem_setOf_eq]
  rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hFt x)]

/-- Normalized one-dimensional Prékopa–Leindler (additive form). -/
theorem pl_real_norm {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {F G H : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H)
    (hF1 : ∀ x, F x ≤ 1) (hG1 : ∀ x, G x ≤ 1)
    (hFs : ∀ s < 1, ∃ x, s < F x) (hGs : ∀ s < 1, ∃ x, s < G x)
    (hyp : ∀ x y, F x ^ l * G y ^ (1 - l) ≤ H (l * x + (1 - l) * y)) :
    ENNReal.ofReal l * (∫⁻ x, F x) + ENNReal.ofReal (1 - l) * (∫⁻ x, G x) ≤ ∫⁻ x, H x := by
  have hFt : ∀ x, F x ≠ ∞ := fun x => ne_top_of_le_ne_top one_ne_top (hF1 x)
  have hGt : ∀ x, G x ≠ ∞ := fun x => ne_top_of_le_ne_top one_ne_top (hG1 x)
  have hH'm : Measurable fun x => min (H x) 1 := hH.min measurable_const
  have hH't : ∀ x, min (H x) 1 ≠ ∞ := fun x => ne_top_of_le_ne_top one_ne_top (min_le_right _ _)
  rw [show (∫⁻ x, F x) = ∫⁻ t in Ioi (0:ℝ), volume {x | ENNReal.ofReal t < F x} from
      layer_cake volume hF hFt,
    show (∫⁻ x, G x) = ∫⁻ t in Ioi (0:ℝ), volume {x | ENNReal.ofReal t < G x} from
      layer_cake volume hG hGt]
  calc ENNReal.ofReal l * (∫⁻ t in Ioi (0:ℝ), volume {x | ENNReal.ofReal t < F x})
        + ENNReal.ofReal (1 - l) * (∫⁻ t in Ioi (0:ℝ), volume {x | ENNReal.ofReal t < G x})
      = (∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal l * volume {x | ENNReal.ofReal t < F x})
        + ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (1 - l) * volume {x | ENNReal.ofReal t < G x} := by
        rw [lintegral_const_mul' _ _ ofReal_ne_top, lintegral_const_mul' _ _ ofReal_ne_top]
    _ ≤ ∫⁻ t in Ioi (0:ℝ), (ENNReal.ofReal l * volume {x | ENNReal.ofReal t < F x}
        + ENNReal.ofReal (1 - l) * volume {x | ENNReal.ofReal t < G x}) := le_lintegral_add _ _
    _ ≤ ∫⁻ t in Ioi (0:ℝ), volume {x | ENNReal.ofReal t < min (H x) 1} := by
        refine setLIntegral_mono' measurableSet_Ioi (fun t ht => ?_)
        have ht0 : 0 < t := ht
        rcases lt_or_ge t 1 with ht1 | ht1
        · apply bm_meas hl0 hl1 (measurableSet_lt measurable_const hF)
            (measurableSet_lt measurable_const hG)
            (hFs _ (ENNReal.ofReal_lt_one.2 ht1)) (hGs _ (ENNReal.ofReal_lt_one.2 ht1))
          intro x hx y hy
          simp only [mem_setOf_eq] at hx hy ⊢
          refine lt_min ?_ (ENNReal.ofReal_lt_one.2 ht1)
          calc ENNReal.ofReal t = ENNReal.ofReal t ^ l * ENNReal.ofReal t ^ (1 - l) := by
                rw [← ENNReal.rpow_add _ _ (ENNReal.ofReal_pos.2 ht0).ne' ofReal_ne_top]
                simp
            _ < F x ^ l * G y ^ (1 - l) :=
                ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx hl0)
                  (ENNReal.rpow_lt_rpow hy (sub_pos.2 hl1))
            _ ≤ H (l * x + (1 - l) * y) := hyp x y
        · have h1 : {x | ENNReal.ofReal t < F x} = ∅ := by
            ext x
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
            exact (hF1 x).trans (ENNReal.one_le_ofReal.2 ht1)
          have h2 : {x | ENNReal.ofReal t < G x} = ∅ := by
            ext x
            simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
            exact (hG1 x).trans (ENNReal.one_le_ofReal.2 ht1)
          simp [h1, h2]
    _ = ∫⁻ x, min (H x) 1 := (layer_cake volume hH'm hH't).symm
    _ ≤ ∫⁻ x, H x := lintegral_mono (fun x => min_le_left _ _)

/-- Weighted AM-GM in `ℝ≥0∞`. -/
theorem amgm_ennreal {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) (a b : ℝ≥0∞) :
    a ^ l * b ^ (1 - l) ≤ ENNReal.ofReal l * a + ENNReal.ofReal (1 - l) * b := by
  have hl1' : 0 < 1 - l := sub_pos.2 hl1
  rcases eq_or_ne a ∞ with rfl | ha
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hl0).ne', top_add]
    exact le_top
  rcases eq_or_ne b ∞ with rfl | hb
  · rw [ENNReal.mul_top (ENNReal.ofReal_pos.2 hl1').ne', add_top]
    exact le_top
  rw [← ENNReal.ofReal_toReal ha, ← ENNReal.ofReal_toReal hb,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hl0.le,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hl1'.le,
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul hl0.le,
    ← ENNReal.ofReal_mul hl1'.le, ← ENNReal.ofReal_add (by positivity) (by positivity)]
  exact ENNReal.ofReal_le_ofReal (Real.geom_mean_le_arith_mean2_weighted hl0.le hl1'.le
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg (by ring))

/-- One-dimensional Prékopa–Leindler for bounded functions. -/
theorem pl_real_bdd {l : ℝ} (hl0 : 0 < l) (hl1 : l < 1) {F G H : ℝ → ℝ≥0∞}
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) {k : ℝ≥0∞} (hk : k ≠ ∞)
    (hFk : ∀ x, F x ≤ k) (hGk : ∀ x, G x ≤ k)
    (hyp : ∀ x y, F x ^ l * G y ^ (1 - l) ≤ H (l * x + (1 - l) * y)) :
    (∫⁻ x, F x) ^ l * (∫⁻ x, G x) ^ (1 - l) ≤ ∫⁻ x, H x := by
  have hl1' : 0 < 1 - l := sub_pos.2 hl1
  set a := ⨆ x, F x with ha_def
  set b := ⨆ x, G x with hb_def
  have hat : a ≠ ∞ := ne_top_of_le_ne_top hk (iSup_le hFk)
  have hbt : b ≠ ∞ := ne_top_of_le_ne_top hk (iSup_le hGk)
  rcases eq_or_ne a 0 with ha0 | ha0
  · have : ∀ x, F x = 0 := fun x => le_antisymm (ha0 ▸ le_iSup F x) (zero_le _)
    simp [this, ENNReal.zero_rpow_of_pos hl0]
  rcases eq_or_ne b 0 with hb0 | hb0
  · have : ∀ x, G x = 0 := fun x => le_antisymm (hb0 ▸ le_iSup G x) (zero_le _)
    simp [this, ENNReal.zero_rpow_of_pos hl1']
  set c := a ^ l * b ^ (1 - l) with hc_def
  have hlt : a ^ l ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hl0.le hat
  have hrt : b ^ (1 - l) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg hl1'.le hbt
  have hc0 : c ≠ 0 := mul_ne_zero (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hat).ne'
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbt).ne'
  have hct : c ≠ ∞ := ENNReal.mul_ne_top hlt hrt
  have hc' : a⁻¹ ^ l * b⁻¹ ^ (1 - l) = c⁻¹ := by
    rw [ENNReal.inv_rpow, ENNReal.inv_rpow, hc_def, ENNReal.mul_inv (Or.inr hrt) (Or.inl hlt)]
  have hFsup : ⨆ x, F x * a⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel ha0 hat]
  have hGsup : ⨆ x, G x * b⁻¹ = 1 := by
    rw [← ENNReal.iSup_mul, ENNReal.mul_inv_cancel hb0 hbt]
  have key := pl_real_norm hl0 hl1 (F := fun x => F x * a⁻¹) (G := fun x => G x * b⁻¹)
    (H := fun x => H x * c⁻¹) (hF.mul_const _) (hG.mul_const _) (hH.mul_const _)
    (fun x => hFsup ▸ le_iSup (fun x => F x * a⁻¹) x)
    (fun x => hGsup ▸ le_iSup (fun x => G x * b⁻¹) x)
    (fun s hs => lt_iSup_iff.1 (hFsup ▸ hs)) (fun s hs => lt_iSup_iff.1 (hGsup ▸ hs)) ?_
  · beta_reduce at key
    have h2 := (amgm_ennreal hl0 hl1 _ _).trans key
    rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 ha0),
      lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hb0),
      lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hc0), ENNReal.mul_rpow_of_nonneg _ _ hl0.le,
      ENNReal.mul_rpow_of_nonneg _ _ hl1'.le] at h2
    rw [show (∫⁻ x, F x) ^ l * a⁻¹ ^ l * ((∫⁻ x, G x) ^ (1 - l) * b⁻¹ ^ (1 - l))
        = (∫⁻ x, F x) ^ l * (∫⁻ x, G x) ^ (1 - l) * (a⁻¹ ^ l * b⁻¹ ^ (1 - l)) by ring, hc'] at h2
    exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hct) (ENNReal.inv_ne_top.2 hc0)).1 h2
  · intro x y
    simp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ hl0.le, ENNReal.mul_rpow_of_nonneg _ _ hl1'.le,
      show F x ^ l * a⁻¹ ^ l * (G y ^ (1 - l) * b⁻¹ ^ (1 - l))
        = F x ^ l * G y ^ (1 - l) * (a⁻¹ ^ l * b⁻¹ ^ (1 - l)) by ring, hc']
    exact mul_le_mul_left (hyp x y) _

/-- One-dimensional Prékopa–Leindler inequality. -/
theorem pl_real : PLProp ℝ := by
  intro l hl0 hl1 F G H hF hG hH hyp
  simp only [smul_eq_mul] at hyp
  have hl1' : 0 < 1 - l := sub_pos.2 hl1
  rcases eq_or_ne (∫⁻ x, F x) 0 with hF0 | hF0
  · rw [hF0, ENNReal.zero_rpow_of_pos hl0, zero_mul]
    exact zero_le _
  rcases eq_or_ne (∫⁻ x, G x) 0 with hG0 | hG0
  · rw [hG0, ENNReal.zero_rpow_of_pos hl1', mul_zero]
    exact zero_le _
  have hk : ∀ k : ℕ, (∫⁻ x, min (F x) k) ^ l * (∫⁻ x, min (G x) k) ^ (1 - l) ≤ ∫⁻ x, H x := by
    intro k
    refine pl_real_bdd hl0 hl1 (hF.min measurable_const) (hG.min measurable_const) hH
      (ENNReal.natCast_ne_top k) (fun x => min_le_right _ _) (fun x => min_le_right _ _)
      (fun x y => ?_)
    calc min (F x) k ^ l * min (G y) k ^ (1 - l) ≤ F x ^ l * G y ^ (1 - l) := by
          gcongr
          · exact min_le_left _ _
          · exact min_le_left _ _
      _ ≤ H (l * x + (1 - l) * y) := hyp x y
  have hlim : ∀ (F : ℝ → ℝ≥0∞), Measurable F →
      Tendsto (fun k : ℕ => ∫⁻ x, min (F x) k) atTop (𝓝 (∫⁻ x, F x)) := by
    intro F hF
    refine lintegral_tendsto_of_tendsto_of_monotone
      (fun k => (hF.min measurable_const).aemeasurable) ?_ ?_
    · exact Eventually.of_forall fun x i j hij => min_le_min_left _ (by exact_mod_cast hij)
    · refine Eventually.of_forall fun x => ?_
      have := (tendsto_const_nhds (x := F x)).min ENNReal.tendsto_nat_nhds_top
      simpa using this
  have hT := ENNReal.Tendsto.mul
    ((ENNReal.continuous_rpow_const.tendsto _).comp (hlim F hF))
    (Or.inl (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hF0) hl0.le).ne')
    ((ENNReal.continuous_rpow_const.tendsto _).comp (hlim G hG))
    (Or.inl (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hG0) hl1'.le).ne')
  exact le_of_tendsto' hT hk

/-- Prékopa–Leindler is stable under products (Tonelli). -/
theorem pl_prod {E F : Type*} [AddCommGroup E] [Module ℝ E] [MeasureSpace E]
    [AddCommGroup F] [Module ℝ F] [MeasureSpace F] [SFinite (volume : Measure F)]
    (hE : PLProp E) (hF : PLProp F) : PLProp (E × F) := by
  intro l hl0 hl1 f g h hf hg hh hyp
  have hsec : ∀ a₁ a₂ : E, (∫⁻ b, f (a₁, b)) ^ l * (∫⁻ b, g (a₂, b)) ^ (1 - l)
      ≤ ∫⁻ b, h (l • a₁ + (1 - l) • a₂, b) := by
    intro a₁ a₂
    refine hF l hl0 hl1 (fun b => f (a₁, b)) (fun b => g (a₂, b))
      (fun b => h (l • a₁ + (1 - l) • a₂, b))
      (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
      (hh.comp measurable_prodMk_left) ?_
    intro b₁ b₂
    have := hyp (a₁, b₁) (a₂, b₂)
    simpa only [Prod.smul_mk, Prod.mk_add_mk] using this
  have key := hE l hl0 hl1 (fun a => ∫⁻ b, f (a, b)) (fun a => ∫⁻ b, g (a, b))
    (fun a => ∫⁻ b, h (a, b))
    hf.lintegral_prod_right' hg.lintegral_prod_right' hh.lintegral_prod_right' hsec
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  exact key

/-- Prékopa–Leindler transfers along measure-preserving linear measurable equivalences. -/
theorem pl_transfer {E F : Type*} [AddCommGroup E] [Module ℝ E] [MeasureSpace E]
    [AddCommGroup F] [Module ℝ F] [MeasureSpace F]
    (e : E ≃ᵐ F) (he : MeasurePreserving e volume volume)
    (hlin : ∀ (l : ℝ) x y, e (l • x + (1 - l) • y) = l • e x + (1 - l) • e y)
    (hF : PLProp F) : PLProp E := by
  intro l hl0 hl1 f g h hf hg hh hyp
  have key := hF l hl0 hl1 (f ∘ e.symm) (g ∘ e.symm) (h ∘ e.symm) (hf.comp e.symm.measurable)
    (hg.comp e.symm.measurable) (hh.comp e.symm.measurable) (by
      intro u v
      have h2 : e.symm (l • u + (1 - l) • v) = l • e.symm u + (1 - l) • e.symm v := by
        apply e.injective
        rw [hlin]
        simp
      simp only [Function.comp, h2]
      exact hyp _ _)
  have hs := he.symm
  simp only [Function.comp] at key
  rwa [hs.lintegral_comp hf, hs.lintegral_comp hg, hs.lintegral_comp hh] at key

theorem pl_fin_zero : PLProp (Fin 0 → ℝ) := by
  intro l hl0 hl1 f g h hf hg hh hyp
  rw [volume_pi, Measure.pi_of_empty _ 0, lintegral_dirac, lintegral_dirac, lintegral_dirac]
  have := hyp 0 0
  rwa [show l • (0 : Fin 0 → ℝ) + (1 - l) • 0 = 0 by simp] at this

theorem pl_pi : ∀ m : ℕ, PLProp (Fin m → ℝ)
  | 0 => pl_fin_zero
  | m + 1 => by
    refine pl_transfer (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
      (volume_preserving_piFinSuccAbove (fun _ => ℝ) 0) ?_ (pl_prod pl_real (pl_pi m))
    intro l x y
    ext
    · simp [MeasurableEquiv.piFinSuccAbove]
    · simp [MeasurableEquiv.piFinSuccAbove, Fin.tail]

theorem pl_euclid (m : ℕ) : PLProp (EuclideanSpace ℝ (Fin m)) :=
  pl_transfer (MeasurableEquiv.toLp 2 (Fin m → ℝ)).symm
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin m)) (fun l x y => by simp)
    (pl_pi m)

theorem exists_measurable_ge_lintegral_eq {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ≥0∞} (hf : AEMeasurable f μ) :
    ∃ g : α → ℝ≥0∞, Measurable g ∧ f ≤ g ∧ ∫⁻ x, g x ∂μ = ∫⁻ x, f x ∂μ := by
  classical
  set N := toMeasurable μ {x | f x ≠ hf.mk f x} with hN_def
  have hN0 : μ N = 0 := by
    rw [hN_def, measure_toMeasurable]
    exact ae_iff.1 hf.ae_eq_mk
  refine ⟨N.piecewise (fun _ => ∞) (hf.mk f),
    Measurable.piecewise (measurableSet_toMeasurable _ _) measurable_const hf.measurable_mk, ?_, ?_⟩
  · intro x
    by_cases hx : x ∈ N
    · simp [Set.piecewise_eq_of_mem _ _ _ hx]
    · rw [Set.piecewise_eq_of_notMem _ _ _ hx]
      have : x ∉ {x | f x ≠ hf.mk f x} := fun h => hx (subset_toMeasurable _ _ h)
      simp only [mem_setOf_eq, not_not] at this
      exact this.le
  · apply lintegral_congr_ae
    have h1 : N.piecewise (fun _ => ∞) (hf.mk f) =ᵐ[μ] hf.mk f := by
      have : ∀ᵐ x ∂μ, x ∉ N := measure_eq_zero_iff_ae_notMem.1 hN0
      filter_upwards [this] with x hx
      rw [Set.piecewise_eq_of_notMem _ _ _ hx]
    exact h1.trans hf.ae_eq_mk.symm

end PrekopaAux

theorem Duchi_Q5_2a {n m : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin m) → ℝ)
  (hf_lc : IsJointlyLogConcave f)
  (hf_int : ∀ x, Integrable (f x)) :
  IsLogConcave (fun x => ∫ y, f x y) := by
  obtain ⟨hnn, hlc⟩ := hf_lc
  refine ⟨fun x => integral_nonneg (hnn x), ?_⟩
  intro x y t ht
  obtain ⟨ht0, ht1⟩ := ht
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · simp
  set z := t • x + (1 - t) • y with hz
  obtain ⟨F, hFm, hFle, hFeq⟩ :=
    exists_measurable_le_lintegral_eq volume (fun u => ENNReal.ofReal (f x u))
  obtain ⟨G, hGm, hGle, hGeq⟩ :=
    exists_measurable_le_lintegral_eq volume (fun u => ENNReal.ofReal (f y u))
  obtain ⟨H, hHm, hHge, hHeq⟩ :=
    PrekopaAux.exists_measurable_ge_lintegral_eq (hf_int z).aemeasurable.ennreal_ofReal
  have key := PrekopaAux.pl_euclid m t ht0' ht1' F G H hFm hGm hHm (fun u v => by
    calc F u ^ t * G v ^ (1 - t)
        ≤ ENNReal.ofReal (f x u) ^ t * ENNReal.ofReal (f y v) ^ (1 - t) :=
          mul_le_mul' (ENNReal.rpow_le_rpow (hFle u) ht0)
            (ENNReal.rpow_le_rpow (hGle v) (by linarith))
      _ = ENNReal.ofReal (f x u ^ t * f y v ^ (1 - t)) := by
          rw [ENNReal.ofReal_rpow_of_nonneg (hnn x u) ht0,
            ENNReal.ofReal_rpow_of_nonneg (hnn y v) (by linarith),
            ENNReal.ofReal_mul (Real.rpow_nonneg (hnn x u) _)]
      _ ≤ ENNReal.ofReal (f z (t • u + (1 - t) • v)) :=
          ENNReal.ofReal_le_ofReal (hlc x y u v t ⟨ht0, ht1⟩)
      _ ≤ H (t • u + (1 - t) • v) := hHge _)
  rw [← hFeq, ← hGeq, hHeq] at key
  show ∫ w, f z w ≥ Real.rpow (∫ w, f x w) t * Real.rpow (∫ w, f y w) (1 - t)
  simp only [Real.rpow_eq_pow, ge_iff_le]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn z))
      (hf_int z).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn x))
      (hf_int x).aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn y))
      (hf_int y).aestronglyMeasurable]
  rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono (hf_int z).lintegral_lt_top.ne key

end Duchi_Q5_2a
