import ConvexStarLib.Defs

/-!
# `Duchi_Q5_2b`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q5_2b` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q5_2b`, so the main result is `Duchi_Q5_2b.Duchi_Q5_2b`.
-/

namespace Duchi_Q5_2b

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


namespace DuchiPL

/-- Prékopa–Leindler property of a measure on a real vector space. -/
def PLProp (α : Type*) [AddCommGroup α] [Module ℝ α] [MeasurableSpace α] (μ : Measure α) :
    Prop :=
  ∀ (t : ℝ), 0 < t → t < 1 → ∀ (f g h : α → ℝ≥0∞), Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) →
    (∫⁻ x, f x ∂μ) ^ t * (∫⁻ x, g x ∂μ) ^ (1 - t) ≤ ∫⁻ x, h x ∂μ

/-! ### One-dimensional Brunn–Minkowski -/

lemma bm1_compact (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (K L C : Set ℝ)
    (hK : IsCompact K) (hL : IsCompact L) (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKLC : ∀ x ∈ K, ∀ y ∈ L, t * x + (1 - t) * y ∈ C) :
    ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L ≤ volume C := by
  have ht1' : 0 < 1 - t := by linarith
  obtain ⟨m, hm⟩ : ∃ m, m = sSup K := ⟨_, rfl⟩
  obtain ⟨m', hm'⟩ : ∃ m', m' = sInf L := ⟨_, rfl⟩
  have hmK : m ∈ K := hm ▸ hK.sSup_mem hKne
  have hm'L : m' ∈ L := hm' ▸ hL.sInf_mem hLne
  have hvol1 : volume ((fun x => t * x + (1 - t) * m') '' K) = ENNReal.ofReal t * volume K := by
    have : (fun x => t * x + (1 - t) * m') '' K = (fun y => y + (1 - t) * m') '' (t • K) := by
      rw [← Set.image_smul, Set.image_image]; rfl
    rw [this, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_smul,
      Module.finrank_self, pow_one, abs_of_pos ht0]
  have hvol2 : volume ((fun y => t * m + (1 - t) * y) '' L) = ENNReal.ofReal (1 - t) * volume L := by
    have : (fun y => t * m + (1 - t) * y) '' L = (fun y => t * m + y) '' ((1 - t) • L) := by
      rw [← Set.image_smul, Set.image_image]; rfl
    rw [this, Set.image_add_left, measure_preimage_add, Measure.addHaar_smul,
      Module.finrank_self, pow_one, abs_of_pos ht1']
  have hS2meas : MeasurableSet ((fun y => t * m + (1 - t) * y) '' L) :=
    (hL.image (by fun_prop)).measurableSet
  have hsub : (fun x => t * x + (1 - t) * m') '' K ∪ (fun y => t * m + (1 - t) * y) '' L ⊆ C := by
    rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hKLC x hx m' hm'L
    · exact hKLC m hmK y hy
  have hinter : (fun x => t * x + (1 - t) * m') '' K ∩ (fun y => t * m + (1 - t) * y) '' L ⊆
      {t * m + (1 - t) * m'} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hyz⟩⟩
    have h1 : x ≤ m := hm ▸ le_csSup hK.bddAbove hx
    have h2 : m' ≤ y := hm' ▸ csInf_le hL.bddBelow hy
    have h3 := mul_le_mul_of_nonneg_left h1 ht0.le
    have h4 := mul_le_mul_of_nonneg_left h2 ht1'.le
    simp only at hyz
    simp only [Set.mem_singleton_iff]
    linarith
  have hzero : volume ((fun x => t * x + (1 - t) * m') '' K ∩
      (fun y => t * m + (1 - t) * y) '' L) = 0 :=
    measure_mono_null hinter (measure_singleton _)
  calc ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L
      = volume ((fun x => t * x + (1 - t) * m') '' K) +
          volume ((fun y => t * m + (1 - t) * y) '' L) := by rw [hvol1, hvol2]
    _ = volume ((fun x => t * x + (1 - t) * m') '' K ∪ (fun y => t * m + (1 - t) * y) '' L) +
          volume ((fun x => t * x + (1 - t) * m') '' K ∩
            (fun y => t * m + (1 - t) * y) '' L) :=
        (measure_union_add_inter _ hS2meas).symm
    _ = volume ((fun x => t * x + (1 - t) * m') '' K ∪
          (fun y => t * m + (1 - t) * y) '' L) := by rw [hzero, add_zero]
    _ ≤ volume C := measure_mono hsub

lemma bm1 (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (A B C : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hABC : ∀ x ∈ A, ∀ y ∈ B, t * x + (1 - t) * y ∈ C) :
    ENNReal.ofReal t * volume A + ENNReal.ofReal (1 - t) * volume B ≤ volume C := by
  obtain ⟨a0, ha0⟩ := hAne
  obtain ⟨b0, hb0⟩ := hBne
  have key : ∀ K L : Set ℝ, K ⊆ A → IsCompact K → L ⊆ B → IsCompact L →
      ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L ≤ volume C := by
    intro K L hKA hKc hLB hLc
    have h := bm1_compact t ht0 ht1 (insert a0 K) (insert b0 L) C (hKc.insert a0) (hLc.insert b0)
      (Set.insert_nonempty _ _) (Set.insert_nonempty _ _) (by
        intro x hx y hy
        exact hABC x (Set.insert_subset ha0 hKA hx) y (Set.insert_subset hb0 hLB hy))
    calc ENNReal.ofReal t * volume K + ENNReal.ofReal (1 - t) * volume L
        ≤ ENNReal.ofReal t * volume (insert a0 K) +
            ENNReal.ofReal (1 - t) * volume (insert b0 L) := by
          gcongr <;> exact Set.subset_insert _ _
      _ ≤ volume C := h
  rw [hA.measure_eq_iSup_isCompact volume, hB.measure_eq_iSup_isCompact volume]
  simp only [ENNReal.mul_iSup]
  refine ENNReal.iSup_add_iSup_le fun K L => ?_
  have hf : ∃ K' : Set ℝ, K' ⊆ A ∧ IsCompact K' ∧
      (⨆ (_ : K ⊆ A), ⨆ (_ : IsCompact K), ENNReal.ofReal t * volume K) ≤
        ENNReal.ofReal t * volume K' := by
    by_cases h : K ⊆ A ∧ IsCompact K
    · exact ⟨K, h.1, h.2, iSup₂_le fun _ _ => le_rfl⟩
    · exact ⟨∅, Set.empty_subset _, isCompact_empty, iSup₂_le fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  have hg : ∃ L' : Set ℝ, L' ⊆ B ∧ IsCompact L' ∧
      (⨆ (_ : L ⊆ B), ⨆ (_ : IsCompact L), ENNReal.ofReal (1 - t) * volume L) ≤
        ENNReal.ofReal (1 - t) * volume L' := by
    by_cases h : L ⊆ B ∧ IsCompact L
    · exact ⟨L, h.1, h.2, iSup₂_le fun _ _ => le_rfl⟩
    · exact ⟨∅, Set.empty_subset _, isCompact_empty, iSup₂_le fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  obtain ⟨K', hK'A, hK'c, hK'⟩ := hf
  obtain ⟨L', hL'B, hL'c, hL'⟩ := hg
  exact (add_le_add hK' hL').trans (key K' L' hK'A hK'c hL'B hL'c)

/-! ### Layer cake for functions bounded by one -/

lemma layer_cake_le_one (u : ℝ → ℝ≥0∞) (hu : Measurable u) (h1 : ∀ x, u x ≤ 1) :
    ∫⁻ x, u x = ∫⁻ s in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal s < u x} := by
  have hfin : ∀ x, u x ≠ ⊤ := fun x => ne_top_of_le_ne_top ENNReal.one_ne_top (h1 x)
  have h2 : ∫⁻ x, u x = ∫⁻ x, ENNReal.ofReal ((u x).toReal) := by
    congr 1; ext x; rw [ENNReal.ofReal_toReal (hfin x)]
  rw [h2, lintegral_eq_lintegral_meas_lt volume
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg)) hu.ennreal_toReal.aemeasurable]
  rw [← Set.Ioo_union_Ici_eq_Ioi zero_lt_one, lintegral_union measurableSet_Ici
    (Set.disjoint_left.mpr (fun a ha hb => absurd (Set.mem_Ici.mp hb) (not_le.mpr ha.2)))]
  have hzero : ∫⁻ s in Set.Ici (1:ℝ), volume {a | s < (u a).toReal} = 0 := by
    apply setLIntegral_eq_zero measurableSet_Ici
    intro s hs
    have : {a | s < (u a).toReal} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      have : (u a).toReal ≤ 1 := by
        have := ENNReal.toReal_mono ENNReal.one_ne_top (h1 a)
        simpa using this
      exact this.trans (Set.mem_Ici.mp hs)
    simp [this]
  rw [hzero, add_zero]
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro s hs
  simp only
  congr 1; ext x; simp only [Set.mem_setOf_eq]
  rw [ENNReal.ofReal_lt_iff_lt_toReal hs.1.le (hfin x)]

/-! ### Key lemma (normalized 1D Prékopa–Leindler, additive form) -/

lemma kl (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ s < 1, ∃ x, s < f x) (hgs : ∀ s < 1, ∃ x, s < g x)
    (hyp : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t * x + (1 - t) * y)) :
    ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  have ht1' : 0 < 1 - t := by linarith
  have hmin_meas : Measurable (fun x => min (h x) 1) := hh.min measurable_const
  have key : ∀ s ∈ Set.Ioo (0:ℝ) 1,
      ENNReal.ofReal t * volume {x | ENNReal.ofReal s < f x} +
        ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal s < g x} ≤
      volume {x | ENNReal.ofReal s < min (h x) 1} := by
    intro s hs
    have hs1 : ENNReal.ofReal s < 1 := by
      rw [← ENNReal.ofReal_one]; exact (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).mpr hs.2
    have hs0 : ENNReal.ofReal s ≠ 0 := by simp [hs.1]
    have hstop : ENNReal.ofReal s ≠ ⊤ := ENNReal.ofReal_ne_top
    apply bm1 t ht0 ht1
    · exact measurableSet_lt measurable_const hf
    · exact measurableSet_lt measurable_const hg
    · obtain ⟨x, hx⟩ := hfs _ hs1; exact ⟨x, hx⟩
    · obtain ⟨y, hy⟩ := hgs _ hs1; exact ⟨y, hy⟩
    · intro x hx y hy
      simp only [Set.mem_setOf_eq] at hx hy ⊢
      refine lt_min ?_ hs1
      calc ENNReal.ofReal s = ENNReal.ofReal s ^ t * ENNReal.ofReal s ^ (1 - t) := by
            rw [← ENNReal.rpow_add _ _ hs0 hstop]; simp
        _ < f x ^ t * g y ^ (1 - t) :=
            ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx ht0) (ENNReal.rpow_lt_rpow hy ht1')
        _ ≤ h (t * x + (1 - t) * y) := hyp x y
  calc ENNReal.ofReal t * (∫⁻ x, f x) + ENNReal.ofReal (1 - t) * (∫⁻ x, g x)
      = (∫⁻ s in Set.Ioo (0:ℝ) 1, ENNReal.ofReal t * volume {x | ENNReal.ofReal s < f x}) +
        (∫⁻ s in Set.Ioo (0:ℝ) 1, ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal s < g x}) := by
        rw [layer_cake_le_one f hf hf1, layer_cake_le_one g hg hg1,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ s in Set.Ioo (0:ℝ) 1, (ENNReal.ofReal t * volume {x | ENNReal.ofReal s < f x} +
        ENNReal.ofReal (1 - t) * volume {x | ENNReal.ofReal s < g x}) := le_lintegral_add _ _
    _ ≤ ∫⁻ s in Set.Ioo (0:ℝ) 1, volume {x | ENNReal.ofReal s < min (h x) 1} :=
        setLIntegral_mono' measurableSet_Ioo key
    _ = ∫⁻ x, min (h x) 1 := (layer_cake_le_one _ hmin_meas (fun x => min_le_right _ _)).symm
    _ ≤ ∫⁻ x, h x := lintegral_mono (fun x => min_le_left _ _)

lemma amgm (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (X Y : ℝ≥0∞) :
    X ^ t * Y ^ (1 - t) ≤ ENNReal.ofReal t * X + ENNReal.ofReal (1 - t) * Y := by
  have ht1' : 0 < 1 - t := by linarith
  rcases eq_or_ne X ⊤ with rfl | hX
  · rcases eq_or_ne Y 0 with rfl | hY0
    · simp [ENNReal.zero_rpow_of_pos ht1']
    · have : ENNReal.ofReal t * ⊤ = ⊤ := ENNReal.mul_top (by simpa using ht0)
      simp [this]
  rcases eq_or_ne Y ⊤ with rfl | hY
  · rcases eq_or_ne X 0 with rfl | hX0
    · simp [ENNReal.zero_rpow_of_pos ht0]
    · have : ENNReal.ofReal (1 - t) * ⊤ = ⊤ := ENNReal.mul_top (by simpa using ht1')
      simp [this]
  lift X to ℝ≥0 using hX
  lift Y to ℝ≥0 using hY
  have key := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal t) (Real.toNNReal (1 - t)) X Y
    (by rw [← Real.toNNReal_add ht0.le ht1'.le]; simp)
  rw [Real.coe_toNNReal _ ht0.le, Real.coe_toNNReal _ ht1'.le] at key
  rw [← ENNReal.coe_rpow_of_nonneg _ ht0.le, ← ENNReal.coe_rpow_of_nonneg _ ht1'.le]
  unfold ENNReal.ofReal
  exact_mod_cast key

/-! ### 1D Prékopa–Leindler -/

lemma pl_real_bdd (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (C : ℝ≥0∞) (hC : C ≠ ⊤)
    (hfC : ∀ x, f x ≤ C) (hgC : ∀ x, g x ≤ C)
    (hyp : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ x, g x) ^ (1 - t) ≤ ∫⁻ x, h x := by
  have ht1' : 0 < 1 - t := by linarith
  set a := ⨆ x, f x with ha_def
  set b := ⨆ x, g x with hb_def
  have hfa : ∀ x, f x ≤ a := fun x => le_iSup f x
  have hgb : ∀ x, g x ≤ b := fun x => le_iSup g x
  have haC : a ≤ C := iSup_le hfC
  have hbC : b ≤ C := iSup_le hgC
  have ha_top : a ≠ ⊤ := ne_top_of_le_ne_top hC haC
  have hb_top : b ≠ ⊤ := ne_top_of_le_ne_top hC hbC
  by_cases ha0 : a = 0
  · have hf0 : ∀ x, f x = 0 := fun x => le_antisymm (ha0 ▸ hfa x) (zero_le _)
    have : ∫⁻ x, f x = 0 := by simp [hf0]
    rw [this, ENNReal.zero_rpow_of_pos ht0, zero_mul]
    exact zero_le _
  by_cases hb0 : b = 0
  · have hg0 : ∀ x, g x = 0 := fun x => le_antisymm (hb0 ▸ hgb x) (zero_le _)
    have : ∫⁻ x, g x = 0 := by simp [hg0]
    rw [this, ENNReal.zero_rpow_of_pos ht1', mul_zero]
    exact zero_le _
  set c := a ^ t * b ^ (1 - t) with hc_def
  have hat0 : a ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha_top).ne'
  have hbt0 : b ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hb_top).ne'
  have hat_top : a ^ t ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht0.le ha_top
  have hbt_top : b ^ (1 - t) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg ht1'.le hb_top
  have hc0 : c ≠ 0 := mul_ne_zero hat0 hbt0
  have hc_top : c ≠ ⊤ := ENNReal.mul_ne_top hat_top hbt_top
  -- key algebraic identity
  have key : ∀ X Y : ℝ≥0∞, (X * a⁻¹) ^ t * (Y * b⁻¹) ^ (1 - t) = X ^ t * Y ^ (1 - t) * c⁻¹ := by
    intro X Y
    rw [ENNReal.mul_rpow_of_nonneg _ _ ht0.le, ENNReal.mul_rpow_of_nonneg _ _ ht1'.le,
      ENNReal.inv_rpow, ENNReal.inv_rpow, hc_def, ENNReal.mul_inv (Or.inl hat0) (Or.inl hat_top)]
    ring
  have hf' : Measurable (fun x => f x * a⁻¹) := hf.mul_const _
  have hg' : Measurable (fun x => g x * b⁻¹) := hg.mul_const _
  have hh' : Measurable (fun x => h x * c⁻¹) := hh.mul_const _
  have hf1 : ∀ x, f x * a⁻¹ ≤ 1 := by
    intro x
    calc f x * a⁻¹ ≤ a * a⁻¹ := mul_le_mul_left (hfa x) _
      _ = 1 := ENNReal.mul_inv_cancel ha0 ha_top
  have hg1 : ∀ x, g x * b⁻¹ ≤ 1 := by
    intro x
    calc g x * b⁻¹ ≤ b * b⁻¹ := mul_le_mul_left (hgb x) _
      _ = 1 := ENNReal.mul_inv_cancel hb0 hb_top
  have hfs : ∀ s < 1, ∃ x, s < f x * a⁻¹ := by
    intro s hs
    have : s * a < a := by
      calc s * a < 1 * a := ENNReal.mul_lt_mul_left ha0 ha_top hs
        _ = a := one_mul a
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 this
    refine ⟨x, ?_⟩
    rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl ha_top)]
    exact hx
  have hgs : ∀ s < 1, ∃ x, s < g x * b⁻¹ := by
    intro s hs
    have : s * b < b := by
      calc s * b < 1 * b := ENNReal.mul_lt_mul_left hb0 hb_top hs
        _ = b := one_mul b
    obtain ⟨x, hx⟩ := lt_iSup_iff.1 this
    refine ⟨x, ?_⟩
    rw [← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inl hb0) (Or.inl hb_top)]
    exact hx
  have hyp' : ∀ x y, (f x * a⁻¹) ^ t * (g y * b⁻¹) ^ (1 - t) ≤ h (t * x + (1 - t) * y) * c⁻¹ := by
    intro x y
    rw [key]
    have := hyp x y
    simp only [smul_eq_mul] at this
    exact mul_le_mul_left this _
  have hkl : ENNReal.ofReal t * (∫⁻ x, f x * a⁻¹) + ENNReal.ofReal (1 - t) * (∫⁻ x, g x * b⁻¹)
      ≤ ∫⁻ x, h x * c⁻¹ := by
    have H := kl t ht0 ht1 (fun x => f x * a⁻¹) (fun x => g x * b⁻¹) (fun x => h x * c⁻¹)
      hf' hg' hh' hf1 hg1 hfs hgs hyp'
    beta_reduce at H
    exact H
  have ham := amgm t ht0 ht1 (∫⁻ x, f x * a⁻¹) (∫⁻ x, g x * b⁻¹)
  have hcomb := ham.trans hkl
  rw [lintegral_mul_const _ hf, lintegral_mul_const _ hg, lintegral_mul_const _ hh, key] at hcomb
  exact (ENNReal.mul_le_mul_iff_left (ENNReal.inv_ne_zero.2 hc_top)
    (ENNReal.inv_ne_top.2 hc0)).1 hcomb

lemma pl_real : PLProp ℝ volume := by
  intro t ht0 ht1 f g h hf hg hh hyp
  have ht1' : 0 < 1 - t := by linarith
  set F : ℕ → ℝ → ℝ≥0∞ := fun N x => min (f x) (N : ℝ≥0∞) with hF_def
  set G : ℕ → ℝ → ℝ≥0∞ := fun N x => min (g x) (N : ℝ≥0∞) with hG_def
  have hFm : ∀ N, Measurable (F N) := fun N => hf.min measurable_const
  have hGm : ∀ N, Measurable (G N) := fun N => hg.min measurable_const
  have hFmono : Monotone F := by
    intro N M hNM x
    exact min_le_min le_rfl (Nat.cast_le.2 hNM)
  have hGmono : Monotone G := by
    intro N M hNM x
    exact min_le_min le_rfl (Nat.cast_le.2 hNM)
  have hFsup : ∀ x, f x = ⨆ N, F N x := by
    intro x
    simp only [hF_def]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hGsup : ∀ x, g x = ⨆ N, G N x := by
    intro x
    simp only [hG_def]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hbdd : ∀ N, (∫⁻ x, F N x) ^ t * (∫⁻ x, G N x) ^ (1 - t) ≤ ∫⁻ x, h x := by
    intro N
    apply pl_real_bdd t ht0 ht1 (F N) (G N) h (hFm N) (hGm N) hh (N : ℝ≥0∞)
      (ENNReal.natCast_ne_top N) (fun x => min_le_right _ _) (fun x => min_le_right _ _)
    intro x y
    refine le_trans ?_ (hyp x y)
    exact mul_le_mul' (ENNReal.rpow_le_rpow (min_le_left _ _) ht0.le)
      (ENNReal.rpow_le_rpow (min_le_left _ _) ht1'.le)
  have hFint : ∫⁻ x, f x = ⨆ N, ∫⁻ x, F N x := by
    rw [← lintegral_iSup hFm hFmono]
    congr 1
    funext x
    exact hFsup x
  have hGint : ∫⁻ x, g x = ⨆ N, ∫⁻ x, G N x := by
    rw [← lintegral_iSup hGm hGmono]
    congr 1
    funext x
    exact hGsup x
  rw [hFint, hGint]
  have e1 := (ENNReal.orderIsoRpow t ht0).map_iSup (fun N => ∫⁻ x, F N x)
  have e2 := (ENNReal.orderIsoRpow (1 - t) ht1').map_iSup (fun N => ∫⁻ x, G N x)
  simp only [ENNReal.orderIsoRpow_apply] at e1 e2
  rw [e1, e2, ENNReal.iSup_mul]
  refine iSup_le fun N => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun M => ?_
  calc (∫⁻ x, F N x) ^ t * (∫⁻ x, G M x) ^ (1 - t)
      ≤ (∫⁻ x, F (max N M) x) ^ t * (∫⁻ x, G (max N M) x) ^ (1 - t) := by
        apply mul_le_mul'
        · exact ENNReal.rpow_le_rpow (lintegral_mono fun x => hFmono (le_max_left N M) x) ht0.le
        · exact ENNReal.rpow_le_rpow (lintegral_mono fun x => hGmono (le_max_right N M) x) ht1'.le
    _ ≤ ∫⁻ x, h x := hbdd (max N M)

/-! ### Tensorization -/

lemma PLProp.prod {α β : Type*} [AddCommGroup α] [Module ℝ α] [MeasurableSpace α]
    [AddCommGroup β] [Module ℝ β] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    [SFinite ν] (hα : PLProp α μ) (hβ : PLProp β ν) : PLProp (α × β) (μ.prod ν) := by
  intro t ht0 ht1 f g h hf hg hh hyp
  rw [lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  refine hα t ht0 ht1 (fun a => ∫⁻ b, f (a, b) ∂ν) (fun a => ∫⁻ b, g (a, b) ∂ν)
    (fun a => ∫⁻ b, h (a, b) ∂ν) hf.lintegral_prod_right' hg.lintegral_prod_right'
    hh.lintegral_prod_right' ?_
  intro a1 a2
  refine hβ t ht0 ht1 (fun b => f (a1, b)) (fun b => g (a2, b))
    (fun b => h (t • a1 + (1 - t) • a2, b))
    (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
    (hh.comp measurable_prodMk_left) ?_
  intro b1 b2
  have := hyp (a1, b1) (a2, b2)
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

lemma PLProp.of_equiv {α β : Type*} [AddCommGroup α] [Module ℝ α] [MeasurableSpace α]
    [AddCommGroup β] [Module ℝ β] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : α), e (a • x + b • y) = a • e x + b • e y)
    (h : PLProp α μ) : PLProp β ν := by
  intro t ht0 ht1 f g k hf hg hk hyp
  have key := h t ht0 ht1 (fun x => f (e x)) (fun x => g (e x)) (fun x => k (e x))
    (hf.comp e.measurable) (hg.comp e.measurable) (hk.comp e.measurable) (by
      intro x y
      simp only [hlin]
      exact hyp (e x) (e y))
  rwa [he.lintegral_comp_emb e.measurableEmbedding f, he.lintegral_comp_emb e.measurableEmbedding g,
    he.lintegral_comp_emb e.measurableEmbedding k] at key

lemma pl_pi_zero : PLProp (Fin 0 → ℝ) volume := by
  intro t ht0 ht1 f g h hf hg hh hyp
  rw [lintegral_unique, lintegral_unique, lintegral_unique]
  have hvol : (volume : Measure (Fin 0 → ℝ)) Set.univ = 1 := by
    rw [volume_pi, Measure.pi_of_empty]
    simp
  rw [hvol, mul_one, mul_one, mul_one]
  convert hyp default default using 4

lemma pl_pi : ∀ n : ℕ, PLProp (Fin n → ℝ) volume := by
  intro n
  induction n with
  | zero => exact pl_pi_zero
  | succ n ih =>
    have he := (measurePreserving_piFinSuccAbove
      (fun (_ : Fin (n+1)) => (volume : Measure ℝ)) 0).symm
    refine PLProp.of_equiv (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).symm ?_ ?_
      (pl_real.prod ih)
    · simpa [volume_pi] using he
    · intro a b x y
      funext i
      refine Fin.cases ?_ ?_ i
      · simp [MeasurableEquiv.piFinSuccAbove]
      · intro j
        simp [MeasurableEquiv.piFinSuccAbove]

lemma pl_euclidean (n : ℕ) : PLProp (EuclideanSpace ℝ (Fin n)) volume := by
  refine PLProp.of_equiv (MeasurableEquiv.toLp 2 (Fin n → ℝ))
    (PiLp.volume_preserving_toLp (Fin n)) ?_ (pl_pi n)
  intro a b x y
  simp [WithLp.toLp_add, WithLp.toLp_smul]

lemma pl_euclidean_ae {n : ℕ} (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1)
    (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : AEMeasurable h)
    (hyp : ∀ x y, f x ^ t * g y ^ (1 - t) ≤ h (t • x + (1 - t) • y)) :
    (∫⁻ x, f x) ^ t * (∫⁻ x, g x) ^ (1 - t) ≤ ∫⁻ x, h x := by
  obtain ⟨f', hf'm, hf'le, hf'eq⟩ := exists_measurable_le_lintegral_eq volume f
  obtain ⟨g', hg'm, hg'le, hg'eq⟩ := exists_measurable_le_lintegral_eq volume g
  set N := toMeasurable volume {x | h x ≠ hh.mk h x} with hN
  have hN0 : volume N = 0 := by
    rw [hN, measure_toMeasurable]
    exact hh.ae_eq_mk
  set h' : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ :=
    fun x => hh.mk h x + N.indicator (fun _ => ⊤) x with hh'
  have hh'm : Measurable h' :=
    hh.measurable_mk.add (measurable_const.indicator (measurableSet_toMeasurable _ _))
  have hle : ∀ x, h x ≤ h' x := by
    intro x
    by_cases hx : x ∈ N
    · simp [h', Set.indicator_of_mem hx]
    · have : h x = hh.mk h x := by
        by_contra hne
        exact hx (subset_toMeasurable _ _ hne)
      simp [h', Set.indicator_of_notMem hx, this]
  have heq : ∫⁻ x, h' x = ∫⁻ x, h x := by
    apply lintegral_congr_ae
    have : ∀ᵐ x ∂volume, x ∉ N := measure_eq_zero_iff_ae_notMem.mp hN0
    filter_upwards [this, hh.ae_eq_mk] with x hx hx2
    simp [h', Set.indicator_of_notMem hx, hx2]
  rw [hf'eq, hg'eq, ← heq]
  refine pl_euclidean n t ht0 ht1 f' g' h' hf'm hg'm hh'm ?_
  intro x y
  calc f' x ^ t * g' y ^ (1 - t) ≤ f x ^ t * g y ^ (1 - t) :=
        mul_le_mul' (ENNReal.rpow_le_rpow (hf'le x) ht0.le)
          (ENNReal.rpow_le_rpow (hg'le y) (by linarith))
    _ ≤ h (t • x + (1 - t) • y) := hyp x y
    _ ≤ h' _ := hle _

/-! ### Integrable log-concave functions are bounded -/

lemma logconcave_bdd {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : IsLogConcave f)
    (hint : Integrable f) (hne : ¬ (f =ᵐ[volume] 0)) : ∃ M, ∀ x, f x ≤ M := by
  obtain ⟨hnn, hlc⟩ := hf
  set g : EuclideanSpace ℝ (Fin n) → ℝ := fun y => min (f y) 1 with hg_def
  have hg_nn : ∀ y, 0 ≤ g y := fun y => le_min (hnn y) zero_le_one
  have hg_le : ∀ y, g y ≤ f y := fun y => min_le_left _ _
  have hg_int : Integrable g := by
    refine hint.mono' ?_ ?_
    · exact (hint.aemeasurable.min aemeasurable_const).aestronglyMeasurable
    · filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (hg_nn y)]
      exact hg_le y
  have hsupp : Function.support g = Function.support f := by
    ext y
    simp only [Function.mem_support, ne_eq, g]
    constructor
    · intro h hf0
      apply h
      rw [hf0]
      exact min_eq_left zero_le_one
    · intro h hg0
      apply h
      rcases min_choice (f y) 1 with h1 | h1
      · rw [← h1]; exact hg0
      · rw [h1] at hg0; exact absurd hg0 one_ne_zero
  have hI : 0 < ∫ y, g y := by
    rw [integral_pos_iff_support_of_nonneg_ae (Filter.Eventually.of_forall hg_nn) hg_int, hsupp,
      pos_iff_ne_zero]
    intro h0
    apply hne
    rw [Filter.EventuallyEq, ae_iff]
    exact h0
  refine ⟨(2 ^ n * (∫ y, f y) / (∫ y, g y)) ^ 2, fun x0 => ?_⟩
  have hpt : ∀ y, √(f x0) * g y ≤ f ((1/2 : ℝ) • x0 + (1/2 : ℝ) • y) := by
    intro y
    have h := hlc x0 y (1/2) ⟨by norm_num, by norm_num⟩
    have h2 : (1 : ℝ) - 1/2 = 1/2 := by norm_num
    rw [h2] at h
    have hgy : g y ≤ √(f y) := by
      rw [Real.le_sqrt (hg_nn y) (hnn y)]
      calc g y ^ 2 = g y * g y := sq _
        _ ≤ g y * 1 := mul_le_mul_of_nonneg_left (min_le_right _ _) (hg_nn y)
        _ = g y := mul_one _
        _ ≤ f y := hg_le y
    calc √(f x0) * g y ≤ √(f x0) * √(f y) := mul_le_mul_of_nonneg_left hgy (Real.sqrt_nonneg _)
      _ = Real.rpow (f x0) (1/2) * Real.rpow (f y) (1/2) := by
        rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]; rfl
      _ ≤ f ((1/2 : ℝ) • x0 + (1/2 : ℝ) • y) := h
  have hint2 : Integrable (fun y => f ((1/2 : ℝ) • x0 + (1/2 : ℝ) • y)) :=
    (hint.comp_add_left ((1/2 : ℝ) • x0)).comp_smul (by norm_num : (1/2 : ℝ) ≠ 0)
  have hmono : ∫ y, √(f x0) * g y ≤ ∫ y, f ((1/2 : ℝ) • x0 + (1/2 : ℝ) • y) :=
    integral_mono (hg_int.const_mul _) hint2 hpt
  have heq : ∫ y, f ((1/2 : ℝ) • x0 + (1/2 : ℝ) • y) = 2 ^ n * ∫ y, f y := by
    rw [Measure.integral_comp_smul volume (fun z => f ((1/2 : ℝ) • x0 + z)) (1/2 : ℝ)]
    rw [integral_add_left_eq_self]
    rw [finrank_euclideanSpace_fin]
    rw [smul_eq_mul]
    congr 1
    rw [one_div, inv_pow, inv_inv, abs_of_nonneg (by positivity)]
  rw [integral_const_mul, heq] at hmono
  have hsq : √(f x0) ≤ 2 ^ n * (∫ y, f y) / (∫ y, g y) := by
    rw [le_div_iff₀ hI]
    exact hmono
  calc f x0 = √(f x0) ^ 2 := (Real.sq_sqrt (hnn x0)).symm
    _ ≤ (2 ^ n * (∫ y, f y) / (∫ y, g y)) ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) hsq 2

end DuchiPL

theorem Duchi_Q5_2b {n : ℕ}
  (p q : EuclideanSpace ℝ (Fin n) → ℝ)
  (hp_lc : IsLogConcave p)
  (hq_lc : IsLogConcave q)
  (hp_int : Integrable p)
  (hq_int : Integrable q) :
  IsLogConcave (fun z => ∫ x, p x * q (z - x)) := by
  have hp0 := hp_lc.1
  have hq0 := hq_lc.1
  have hnn : ∀ z x, 0 ≤ p x * q (z - x) := fun z x => mul_nonneg (hp0 x) (hq0 _)
  refine ⟨fun z => integral_nonneg (fun x => hnn z x), ?_⟩
  intro z1 z2 t ht
  have hmeas : ∀ z, AEStronglyMeasurable (fun x => p x * q (z - x)) volume := by
    intro z
    exact hp_int.aestronglyMeasurable.mul
      (hq_int.aestronglyMeasurable.comp_measurePreserving
        (Measure.measurePreserving_sub_left volume z))
  simp only [Real.rpow_eq_pow]
  rcases ht with ⟨ht0, ht1⟩
  rcases eq_or_lt_of_le ht0 with rfl | ht0'
  · simp
  rcases eq_or_lt_of_le ht1 with rfl | ht1'
  · simp
  show (∫ x, p x * q (z1 - x)) ^ t * (∫ x, p x * q (z2 - x)) ^ (1 - t)
      ≤ ∫ x, p x * q ((t • z1 + (1 - t) • z2) - x)
  by_cases hz : (∫ x, p x * q (z1 - x)) = 0 ∨ (∫ x, p x * q (z2 - x)) = 0
  · rcases hz with hz | hz
    · rw [hz, Real.zero_rpow ht0'.ne', zero_mul]
      exact integral_nonneg (fun x => hnn _ x)
    · rw [hz, Real.zero_rpow (by linarith : (1:ℝ) - t ≠ 0), mul_zero]
      exact integral_nonneg (fun x => hnn _ x)
  push_neg at hz
  have hq_ne : ¬ (q =ᵐ[volume] 0) := by
    intro hq
    apply hz.1
    have h1 := (Measure.measurePreserving_sub_left volume z1).quasiMeasurePreserving.ae_eq_comp hq
    have h2 : (fun x => p x * q (z1 - x)) =ᵐ[volume] 0 := by
      filter_upwards [h1] with x hx
      simp only [Function.comp_apply, Pi.zero_apply] at hx ⊢
      rw [hx, mul_zero]
    rw [integral_congr_ae h2]
    simp
  obtain ⟨M, hM⟩ := DuchiPL.logconcave_bdd q hq_lc hq_int hq_ne
  have hint : ∀ z, Integrable (fun x => p x * q (z - x)) := by
    intro z
    refine Integrable.mono' (hp_int.mul_const M) (hmeas z) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (hnn z x)]
    exact mul_le_mul_of_nonneg_left (hM _) (hp0 x)
  set z := t • z1 + (1 - t) • z2 with hz_def
  have key := DuchiPL.pl_euclidean_ae t ht0' ht1'
    (fun x => ENNReal.ofReal (p x * q (z1 - x)))
    (fun x => ENNReal.ofReal (p x * q (z2 - x)))
    (fun x => ENNReal.ofReal (p x * q (z - x)))
    (hmeas z).aemeasurable.ennreal_ofReal ?_
  · rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn z1)) (hmeas z1),
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn z2)) (hmeas z2),
      integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall (hnn z)) (hmeas z)]
    have hfin := (hint z).lintegral_lt_top
    rw [ENNReal.toReal_rpow, ENNReal.toReal_rpow, ← ENNReal.toReal_mul]
    exact ENNReal.toReal_mono hfin.ne key
  · intro x y
    have hx1 := hnn z1 x
    have hy2 := hnn z2 y
    rw [ENNReal.ofReal_rpow_of_nonneg hx1 ht0'.le,
      ENNReal.ofReal_rpow_of_nonneg hy2 (by linarith),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hx1 _)]
    apply ENNReal.ofReal_le_ofReal
    have e : z - (t • x + (1 - t) • y) = t • (z1 - x) + (1 - t) • (z2 - y) := by
      simp only [hz_def, smul_sub]; abel
    rw [e, Real.mul_rpow (hp0 x) (hq0 _), Real.mul_rpow (hp0 y) (hq0 _)]
    have hp := hp_lc.2 x y t ⟨ht0, ht1⟩
    have hq := hq_lc.2 (z1 - x) (z2 - y) t ⟨ht0, ht1⟩
    simp only [Real.rpow_eq_pow, ge_iff_le] at hp hq
    calc p x ^ t * q (z1 - x) ^ t * (p y ^ (1 - t) * q (z2 - y) ^ (1 - t))
        = (p x ^ t * p y ^ (1 - t)) * (q (z1 - x) ^ t * q (z2 - y) ^ (1 - t)) := by ring
      _ ≤ p (t • x + (1 - t) • y) * q (t • (z1 - x) + (1 - t) • (z2 - y)) :=
          mul_le_mul hp hq (mul_nonneg (Real.rpow_nonneg (hq0 _) _) (Real.rpow_nonneg (hq0 _) _)) (hp0 _)

end Duchi_Q5_2b
