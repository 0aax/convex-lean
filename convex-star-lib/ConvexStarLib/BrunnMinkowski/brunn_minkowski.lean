import ConvexStarLib.Defs

/-!
# `brunn_minkowski`

Source: BrunnMinkowski.

Statement from the `convex-eval-v28-2h/brunn_minkowski` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace brunn_minkowski`, so the main result is `brunn_minkowski.brunn_minkowski`.
-/

namespace brunn_minkowski

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

namespace BrunnMinkowskiAux

open Set

/-- The Prékopa–Leindler property of a measure on a real vector space. -/
def PLProp {X : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X] (μ : Measure X) :
    Prop :=
  ∀ t : ℝ, 0 < t → t < 1 → ∀ f g h : X → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) • x + t • y)) →
    (∫⁻ x, f x ∂μ) ^ (1 - t) * (∫⁻ x, g x ∂μ) ^ t ≤ ∫⁻ x, h x ∂μ

/-- Weighted AM-GM in `ℝ≥0∞`. -/
lemma ennreal_amgm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) (X Y : ℝ≥0∞) :
    X ^ (1 - t) * Y ^ t ≤ ENNReal.ofReal (1 - t) * X + ENNReal.ofReal t * Y := by
  have h1t : 0 < 1 - t := by linarith
  rcases eq_or_ne X ∞ with rfl | hX
  · have : ENNReal.ofReal (1 - t) ≠ 0 := by simpa using h1t
    simp [ENNReal.mul_top this]
  rcases eq_or_ne Y ∞ with rfl | hY
  · have : ENNReal.ofReal t ≠ 0 := by simpa using ht0
    simp [ENNReal.mul_top this]
  lift X to ℝ≥0 using hX
  lift Y to ℝ≥0 using hY
  have key := NNReal.geom_mean_le_arith_mean2_weighted ⟨1 - t, h1t.le⟩ ⟨t, ht0.le⟩ X Y
    (by ext; simp)
  rw [ENNReal.ofReal_eq_coe_nnreal h1t.le, ENNReal.ofReal_eq_coe_nnreal ht0.le,
    ← ENNReal.coe_rpow_of_nonneg _ h1t.le, ← ENNReal.coe_rpow_of_nonneg _ ht0.le]
  exact_mod_cast key

/-- Helper: one-dimensional Brunn–Minkowski for nonempty compact sets. -/
lemma bm1_compact {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {K L C : Set ℝ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hKLC : ∀ x ∈ K, ∀ y ∈ L, (1 - t) * x + t * y ∈ C) :
    ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L ≤ volume C := by
  set a := sSup K with ha_def
  set b := sInf L with hb_def
  have ha : a ∈ K := hK.sSup_mem hKne
  have hb : b ∈ L := hL.sInf_mem hLne
  have haK : ∀ x ∈ K, x ≤ a := fun x hx => le_csSup hK.bddAbove hx
  have hbL : ∀ y ∈ L, b ≤ y := fun y hy => csInf_le hL.bddBelow hy
  have hf1 : (fun x : ℝ => (1 - t) * x + t * b) = AffineMap.homothety b (1 - t) := by
    funext x; simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]; ring
  have hf2 : (fun y : ℝ => (1 - t) * a + t * y) = AffineMap.homothety a t := by
    funext y; simp only [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_eq_mul]; ring
  set S1 := (fun x : ℝ => (1 - t) * x + t * b) '' K with hS1
  set S2 := (fun y : ℝ => (1 - t) * a + t * y) '' L with hS2
  have hS2c : IsCompact S2 := hL.image (by fun_prop)
  have hvol1 : volume S1 = ENNReal.ofReal (1 - t) * volume K := by
    rw [hS1, hf1, Measure.addHaar_image_homothety, Module.finrank_self, pow_one,
      abs_of_pos (sub_pos.2 ht1)]
  have hvol2 : volume S2 = ENNReal.ofReal t * volume L := by
    rw [hS2, hf2, Measure.addHaar_image_homothety, Module.finrank_self, pow_one,
      abs_of_pos ht0]
  have hsub : S1 ∪ S2 ⊆ C := by
    rintro z (⟨x, hx, rfl⟩ | ⟨y, hy, rfl⟩)
    · exact hKLC x hx b hb
    · exact hKLC a ha y hy
  have hinter : S1 ∩ S2 ⊆ {(1 - t) * a + t * b} := by
    rintro z ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h1 := haK x hx
    have h2 := hbL y hy
    simp only at hxy
    simp only [mem_singleton_iff]
    have ht1' : 0 < 1 - t := sub_pos.2 ht1
    apply le_antisymm
    · nlinarith
    · nlinarith
  have hdisj : AEDisjoint volume S1 S2 :=
    measure_mono_null hinter (measure_singleton _)
  calc ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L
      = volume S1 + volume S2 := by rw [hvol1, hvol2]
    _ = volume (S1 ∪ S2) := (measure_union₀ hS2c.measurableSet.nullMeasurableSet hdisj).symm
    _ ≤ volume C := measure_mono hsub

/-- One-dimensional Brunn–Minkowski for measurable sets. -/
lemma bm_one_dim {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A B C : Set ℝ}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hABC : ∀ x ∈ A, ∀ y ∈ B, (1 - t) * x + t * y ∈ C) :
    ENNReal.ofReal (1 - t) * volume A + ENNReal.ofReal t * volume B ≤ volume C := by
  -- `hC` is not needed: `measure_mono` works for arbitrary `C`.
  have _ := hC
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  have key : ∀ K, K ⊆ A ∧ IsCompact K → ∀ L, L ⊆ B ∧ IsCompact L →
      ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L ≤ volume C := by
    rintro K ⟨hKA, hK⟩ L ⟨hLB, hL⟩
    calc ENNReal.ofReal (1 - t) * volume K + ENNReal.ofReal t * volume L
        ≤ ENNReal.ofReal (1 - t) * volume (insert a₀ K)
          + ENNReal.ofReal t * volume (insert b₀ L) := by
          gcongr <;> exact subset_insert _ _
      _ ≤ volume C :=
          bm1_compact ht0 ht1 (hK.insert a₀) (hL.insert b₀) (insert_nonempty _ _)
            (insert_nonempty _ _) (fun x hx y hy =>
              hABC x (insert_subset ha₀ hKA hx) y (insert_subset hb₀ hLB hy))
  have hAsup : volume A = ⨆ K, ⨆ (_ : K ⊆ A ∧ IsCompact K), volume K := by
    rw [hA.measure_eq_iSup_isCompact]; simp only [iSup_and']
  have hBsup : volume B = ⨆ L, ⨆ (_ : L ⊆ B ∧ IsCompact L), volume L := by
    rw [hB.measure_eq_iSup_isCompact]; simp only [iSup_and']
  rw [hAsup, hBsup]
  simp only [ENNReal.mul_iSup]
  exact ENNReal.biSup_add_biSup_le' ⟨∅, empty_subset _, isCompact_empty⟩
    ⟨∅, empty_subset _, isCompact_empty⟩ key

/-- Layer cake formula for finite-valued `ℝ≥0∞` functions. -/
lemma layercake {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℝ≥0∞}
    (hf : Measurable f) (hfin : ∀ x, f x ≠ ∞) :
    ∫⁻ x, f x ∂μ = ∫⁻ s in Ioi (0 : ℝ), μ {x | ENNReal.ofReal s < f x} := by
  have h1 := MeasureTheory.lintegral_eq_lintegral_meas_lt μ (f := fun x => (f x).toReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg)) hf.ennreal_toReal.aemeasurable
  simp only [ENNReal.ofReal_toReal (hfin _)] at h1
  rw [h1]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro s hs
  have : {a | s < (f a).toReal} = {x | ENNReal.ofReal s < f x} := by
    ext x
    simp only [mem_setOf_eq]
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hs) (hfin x)).symm
  simp only [this]

/-- Corrected (parenthesized) version of `pl_one_dim_norm`.
NOTE: the statement of `pl_one_dim_norm` below parses as
`ofReal (1 - t) * ∫⁻ x, (f x + ofReal t * ∫⁻ x, g x) ≤ ∫⁻ x, h x`
(the `∫⁻ x, _` body is parsed at precedence 60, so it swallows the `+`), which is FALSE
(e.g. `f = g = h = indicator of [0,1]`, `t = 1/2`: LHS = ∞, RHS = 1).
This lemma is the intended statement, fully proven. -/
lemma nrm_pl_one_dim_norm_fixed {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) (hh1 : ∀ x, h x ≤ 1)
    (hfs : ∀ s < 1, ∃ x, s < f x) (hgs : ∀ s < 1, ∃ x, s < g x)
    (hfgh : ∀ x y, min (f x) (g y) ≤ h ((1 - t) * x + t * y)) :
    ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  have hfin : ∀ {k : ℝ → ℝ≥0∞}, (∀ x, k x ≤ 1) → ∀ x, k x ≠ ∞ :=
    fun hk x => ne_top_of_le_ne_top ENNReal.one_ne_top (hk x)
  have hLf := layercake volume hf (hfin hf1)
  have hLg := layercake volume hg (hfin hg1)
  have hLh := layercake volume hh (hfin hh1)
  rw [hLf, hLg, hLh]
  have hanti : ∀ (k : ℝ → ℝ≥0∞),
      Antitone (fun s : ℝ => volume {x : ℝ | ENNReal.ofReal s < k x}) := by
    intro k a b hab
    apply measure_mono
    intro x hx
    simp only [mem_setOf_eq] at hx ⊢
    exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal hab) hx
  have hmeas : ∀ k : ℝ → ℝ≥0∞,
      Measurable (fun s : ℝ => volume {x : ℝ | ENNReal.ofReal s < k x}) :=
    fun k => (hanti k).measurable
  rw [← lintegral_const_mul (ENNReal.ofReal (1 - t)) (hmeas f),
    ← lintegral_const_mul (ENNReal.ofReal t) (hmeas g),
    ← lintegral_add_left ((hmeas f).const_mul _)]
  apply setLIntegral_mono (hmeas h)
  intro s hs
  by_cases hs1 : ENNReal.ofReal s < 1
  · apply bm_one_dim ht0 ht1 (measurableSet_lt measurable_const hf)
      (measurableSet_lt measurable_const hg) (measurableSet_lt measurable_const hh)
      (hfs _ hs1) (hgs _ hs1)
    intro x hx y hy
    simp only [mem_setOf_eq] at hx hy ⊢
    exact lt_of_lt_of_le (lt_min hx hy) (hfgh x y)
  · push_neg at hs1
    have hfe : {x | ENNReal.ofReal s < f x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hf1 x).trans hs1
    have hge : {x | ENNReal.ofReal s < g x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      exact (hg1 x).trans hs1
    simp [hfe, hge]

/-- Normalized one-dimensional Prékopa–Leindler (Henstock–Macbeath form).
WARNING: as written this statement is FALSE (parsing issue, see `nrm_pl_one_dim_norm_fixed`).
Fix: parenthesize the integrals, i.e. `ENNReal.ofReal (1 - t) * (∫⁻ x, f x) +
ENNReal.ofReal t * (∫⁻ x, g x) ≤ ∫⁻ x, h x`; then the proof is
`nrm_pl_one_dim_norm_fixed ht0 ht1 hf hg hh hf1 hg1 hh1 hfs hgs hfgh`. -/
lemma pl_one_dim_norm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) (hh1 : ∀ x, h x ≤ 1)
    (hfs : ∀ s < 1, ∃ x, s < f x) (hgs : ∀ s < 1, ∃ x, s < g x)
    (hfgh : ∀ x y, min (f x) (g y) ≤ h ((1 - t) * x + t * y)) :
    ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * (∫⁻ x, g x) ≤ ∫⁻ x, h x :=
  nrm_pl_one_dim_norm_fixed ht0 ht1 hf hg hh hf1 hg1 hh1 hfs hgs hfgh

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- The intended (parenthesized) form of `pl_one_dim_norm`. The skeleton statement of
`pl_one_dim_norm` parses as `ofReal (1 - t) * ∫⁻ x, (f x + ofReal t * ∫⁻ x, g x) ≤ ∫⁻ x, h x`,
which implies this form; if that statement gets parenthesized, the first branch applies. -/
lemma trc_pl_norm {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1) (hh1 : ∀ x, h x ≤ 1)
    (hfs : ∀ s < 1, ∃ x, s < f x) (hgs : ∀ s < 1, ∃ x, s < g x)
    (hfgh : ∀ x y, min (f x) (g y) ≤ h ((1 - t) * x + t * y)) :
    ENNReal.ofReal (1 - t) * (∫⁻ x, f x) + ENNReal.ofReal t * (∫⁻ x, g x) ≤ ∫⁻ x, h x := by
  have H := pl_one_dim_norm ht0 ht1 hf hg hh hf1 hg1 hh1 hfs hgs hfgh
  first
  | exact H
  | by_cases hC : ENNReal.ofReal t * ∫⁻ x, g x = 0
    · rw [hC] at H ⊢
      simpa using H
    · have h1 : ∫⁻ x, (f x + ENNReal.ofReal t * ∫⁻ y, g y) = ∞ := by
        apply eq_top_iff.2
        calc ∞ = ∫⁻ _ : ℝ, (ENNReal.ofReal t * ∫⁻ y, g y) := by
              rw [lintegral_const, Real.volume_univ, ENNReal.mul_top hC]
          _ ≤ _ := lintegral_mono (fun x => le_add_self)
      have h2 : ENNReal.ofReal (1 - t) ≠ 0 := by simpa using (by linarith : 0 < 1 - t)
      rw [h1, ENNReal.mul_top h2, top_le_iff] at H
      rw [H]
      exact le_top

/-- Truncated one-dimensional Prékopa–Leindler. -/
lemma pl_one_dim_trunc {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {f g h : ℝ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    {a b : ℝ≥0∞} (ha0 : a ≠ 0) (hatop : a ≠ ∞) (hb0 : b ≠ 0) (hbtop : b ≠ ∞)
    (hfa : ∀ s < a, ∃ x, s < f x) (hgb : ∀ s < b, ∃ x, s < g x)
    (hfgh : ∀ x y, f x ^ (1 - t) * g y ^ t ≤ h ((1 - t) * x + t * y)) :
    (∫⁻ x, min (f x) a) ^ (1 - t) * (∫⁻ x, min (g x) b) ^ t ≤ ∫⁻ x, h x := by
  have h1t : 0 < 1 - t := by linarith
  set c := a ^ (1 - t) * b ^ t with hc_def
  have hat0 : a ^ (1 - t) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) hatop).ne'
  have hbt0 : b ^ t ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hb0) hbtop).ne'
  have hattop : a ^ (1 - t) ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg h1t.le hatop
  have hbttop : b ^ t ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg ht0.le hbtop
  have hc0 : c ≠ 0 := mul_ne_zero hat0 hbt0
  have hctop : c ≠ ∞ := ENNReal.mul_ne_top hattop hbttop
  set f' : ℝ → ℝ≥0∞ := fun x => min (f x) a / a with hf'_def
  set g' : ℝ → ℝ≥0∞ := fun y => min (g y) b / b with hg'_def
  set h' : ℝ → ℝ≥0∞ := fun z => min (h z / c) 1 with hh'_def
  have hf'm : Measurable f' := (hf.min measurable_const).div_const a
  have hg'm : Measurable g' := (hg.min measurable_const).div_const b
  have hh'm : Measurable h' := (hh.div_const c).min measurable_const
  have hf'1 : ∀ x, f' x ≤ 1 := fun x => (ENNReal.div_le_iff ha0 hatop).2 (by simp)
  have hg'1 : ∀ x, g' x ≤ 1 := fun x => (ENNReal.div_le_iff hb0 hbtop).2 (by simp)
  have hh'1 : ∀ x, h' x ≤ 1 := fun x => min_le_right _ _
  have hf's : ∀ s < 1, ∃ x, s < f' x := by
    intro s hs
    have hsa : s * a < a := ENNReal.mul_lt_of_lt_div (by rwa [ENNReal.div_self ha0 hatop])
    obtain ⟨x, hx⟩ := hfa (s * a) hsa
    refine ⟨x, ?_⟩
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl ha0) (Or.inl hatop)]
    exact lt_min hx hsa
  have hg's : ∀ s < 1, ∃ x, s < g' x := by
    intro s hs
    have hsb : s * b < b := ENNReal.mul_lt_of_lt_div (by rwa [ENNReal.div_self hb0 hbtop])
    obtain ⟨x, hx⟩ := hgb (s * b) hsb
    refine ⟨x, ?_⟩
    rw [ENNReal.lt_div_iff_mul_lt (Or.inl hb0) (Or.inl hbtop)]
    exact lt_min hx hsb
  have hmin : ∀ p q : ℝ≥0∞, min p q ≤ p ^ (1 - t) * q ^ t := by
    intro p q
    calc min p q = (min p q) ^ ((1 - t) + t) := by simp
      _ = (min p q) ^ (1 - t) * (min p q) ^ t := ENNReal.rpow_add_of_nonneg _ _ h1t.le ht0.le
      _ ≤ p ^ (1 - t) * q ^ t := by
        gcongr
        · exact min_le_left _ _
        · exact min_le_right _ _
  have hfgh' : ∀ x y, min (f' x) (g' y) ≤ h' ((1 - t) * x + t * y) := by
    intro x y
    refine le_min ?_ ((min_le_left _ _).trans (hf'1 x))
    calc min (f' x) (g' y) ≤ f' x ^ (1 - t) * g' y ^ t := hmin _ _
      _ ≤ (f x / a) ^ (1 - t) * (g y / b) ^ t := by
        gcongr
        · exact ENNReal.div_le_div_right (min_le_left _ _) _
        · exact ENNReal.div_le_div_right (min_le_left _ _) _
      _ = (f x ^ (1 - t) * g y ^ t) / c := by
        rw [ENNReal.div_rpow_of_nonneg _ _ h1t.le, ENNReal.div_rpow_of_nonneg _ _ ht0.le,
          div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, hc_def,
          ENNReal.mul_inv (Or.inl hat0) (Or.inl hattop)]
        ring
      _ ≤ h ((1 - t) * x + t * y) / c := by gcongr; exact hfgh x y
  have key := trc_pl_norm ht0 ht1 hf'm hg'm hh'm hf'1 hg'1 hh'1 hf's hg's hfgh'
  have hFa : ∫⁻ x, min (f x) a = (∫⁻ x, f' x) * a := by
    rw [← lintegral_mul_const _ hf'm]
    congr 1; ext x
    simp only [hf'_def]
    rw [ENNReal.div_mul_cancel ha0 hatop]
  have hGb : ∫⁻ x, min (g x) b = (∫⁻ x, g' x) * b := by
    rw [← lintegral_mul_const _ hg'm]
    congr 1; ext x
    simp only [hg'_def]
    rw [ENNReal.div_mul_cancel hb0 hbtop]
  have hH : (∫⁻ x, h' x) * c ≤ ∫⁻ x, h x := by
    calc (∫⁻ x, h' x) * c ≤ ∫⁻ x, h' x * c := lintegral_mul_const_le _ _
      _ ≤ ∫⁻ x, h x := by
        apply lintegral_mono
        intro x
        calc h' x * c ≤ h x / c * c := by gcongr; exact min_le_left _ _
          _ = h x := ENNReal.div_mul_cancel hc0 hctop
  rw [hFa, hGb, ENNReal.mul_rpow_of_nonneg _ _ h1t.le, ENNReal.mul_rpow_of_nonneg _ _ ht0.le]
  calc (∫⁻ x, f' x) ^ (1 - t) * a ^ (1 - t) * ((∫⁻ x, g' x) ^ t * b ^ t)
      = ((∫⁻ x, f' x) ^ (1 - t) * (∫⁻ x, g' x) ^ t) * c := by rw [hc_def]; ring
    _ ≤ (ENNReal.ofReal (1 - t) * (∫⁻ x, f' x) + ENNReal.ofReal t * (∫⁻ x, g' x)) * c := by
        gcongr; exact ennreal_amgm ht0 ht1 _ _
    _ ≤ (∫⁻ x, h' x) * c := by gcongr
    _ ≤ ∫⁻ x, h x := hH

lemma rl_iSup_min_natCast (c : ℝ≥0∞) : (⨆ k : ℕ, min c ((k : ℝ≥0∞) + 1)) = c := by
  refine le_antisymm (iSup_le fun k => min_le_left _ _) ?_
  refine le_of_forall_lt fun d hd => ?_
  obtain ⟨n, hn⟩ := ENNReal.exists_nat_gt (hd.trans_le le_top).ne
  have h1 : d < min c ((n : ℝ≥0∞) + 1) :=
    lt_min hd (hn.trans_le (le_self_add : (n : ℝ≥0∞) ≤ n + 1))
  exact h1.trans_le (le_iSup (fun k : ℕ => min c ((k : ℝ≥0∞) + 1)) n)

lemma rl_lintegral_eq_iSup_min {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ x, f x = ⨆ k : ℕ, ∫⁻ x, min (f x) ((k : ℝ≥0∞) + 1) := by
  rw [← lintegral_iSup]
  · simp only [rl_iSup_min_natCast]
  · intro k
    exact hf.min measurable_const
  · intro i j hij x
    dsimp only
    gcongr

lemma rl_monotone_lintegral_min {f : ℝ → ℝ≥0∞} :
    Monotone (fun k : ℕ => ∫⁻ x, min (f x) ((k : ℝ≥0∞) + 1)) := by
  intro i j hij
  dsimp only
  gcongr

lemma rl_iSup_rpow_mul_le {P Q : ℕ → ℝ≥0∞} (hP : Monotone P) (hQ : Monotone Q)
    {p q : ℝ} (hp : 0 < p) (hq : 0 < q) {C : ℝ≥0∞} (h : ∀ k, P k ^ p * Q k ^ q ≤ C) :
    (⨆ k, P k) ^ p * (⨆ k, Q k) ^ q ≤ C := by
  have e1 : (⨆ k, P k) ^ p = ⨆ k, P k ^ p := (ENNReal.orderIsoRpow p hp).map_iSup P
  have e2 : (⨆ k, Q k) ^ q = ⨆ k, Q k ^ q := (ENNReal.orderIsoRpow q hq).map_iSup Q
  rw [e1, e2, ENNReal.iSup_mul]
  refine iSup_le fun i => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun j => ?_
  calc P i ^ p * Q j ^ q ≤ P (max i j) ^ p * Q (max i j) ^ q := by
        gcongr
        · exact hP (le_max_left i j)
        · exact hQ (le_max_right i j)
    _ ≤ C := h _

/-- One-dimensional Prékopa–Leindler. -/
lemma plProp_real : PLProp (volume : Measure ℝ) := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  simp only [smul_eq_mul] at hfgh
  have ht1' : 0 < 1 - t := by linarith
  by_cases hSf : (⨆ x, f x) = 0
  · have hf0 : ∀ x, f x = 0 := fun x => le_antisymm (hSf ▸ le_iSup f x) (zero_le _)
    have hint : ∫⁻ x, f x = 0 := by simp [hf0]
    rw [hint, ENNReal.zero_rpow_of_pos ht1', zero_mul]
    exact zero_le _
  by_cases hSg : (⨆ x, g x) = 0
  · have hg0 : ∀ x, g x = 0 := fun x => le_antisymm (hSg ▸ le_iSup g x) (zero_le _)
    have hint : ∫⁻ x, g x = 0 := by simp [hg0]
    rw [hint, ENNReal.zero_rpow_of_pos ht0, mul_zero]
    exact zero_le _
  have key : ∀ k : ℕ, (∫⁻ x, min (f x) ((k : ℝ≥0∞) + 1)) ^ (1 - t) *
      (∫⁻ x, min (g x) ((k : ℝ≥0∞) + 1)) ^ t ≤ ∫⁻ x, h x := by
    intro k
    have hk0 : ((k : ℝ≥0∞) + 1) ≠ 0 := by simp
    have hktop : ((k : ℝ≥0∞) + 1) ≠ ∞ := by simp
    have H := pl_one_dim_trunc ht0 ht1 hf hg hh
      (a := min (⨆ x, f x) ((k : ℝ≥0∞) + 1)) (b := min (⨆ x, g x) ((k : ℝ≥0∞) + 1))
      ((lt_min (pos_iff_ne_zero.2 hSf) (pos_iff_ne_zero.2 hk0)).ne')
      (ne_top_of_le_ne_top hktop (min_le_right _ _))
      ((lt_min (pos_iff_ne_zero.2 hSg) (pos_iff_ne_zero.2 hk0)).ne')
      (ne_top_of_le_ne_top hktop (min_le_right _ _))
      (fun s hs => lt_iSup_iff.1 (hs.trans_le (min_le_left _ _)))
      (fun s hs => lt_iSup_iff.1 (hs.trans_le (min_le_left _ _))) hfgh
    have ef : ∀ x, min (f x) (min (⨆ x, f x) ((k : ℝ≥0∞) + 1)) = min (f x) ((k : ℝ≥0∞) + 1) := by
      intro x
      rw [← min_assoc, min_eq_left (le_iSup f x)]
    have eg : ∀ x, min (g x) (min (⨆ x, g x) ((k : ℝ≥0∞) + 1)) = min (g x) ((k : ℝ≥0∞) + 1) := by
      intro x
      rw [← min_assoc, min_eq_left (le_iSup g x)]
    simpa only [ef, eg] using H
  rw [rl_lintegral_eq_iSup_min hf, rl_lintegral_eq_iSup_min hg]
  exact rl_iSup_rpow_mul_le rl_monotone_lintegral_min rl_monotone_lintegral_min ht1' ht0 key

lemma PLProp.prod {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    [SFinite μ] [SFinite ν] (hX : PLProp μ) (hY : PLProp ν) : PLProp (μ.prod ν) := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  rw [lintegral_prod_symm' f hf, lintegral_prod_symm' g hg, lintegral_prod_symm' h hh]
  refine hY t ht0 ht1 (fun y => ∫⁻ x, f (x, y) ∂μ) (fun y => ∫⁻ x, g (x, y) ∂μ)
    (fun y => ∫⁻ x, h (x, y) ∂μ) hf.lintegral_prod_left' hg.lintegral_prod_left'
    hh.lintegral_prod_left' ?_
  intro y y'
  refine hX t ht0 ht1 (fun x => f (x, y)) (fun x => g (x, y'))
    (fun x => h (x, (1 - t) • y + t • y')) (hf.comp measurable_prodMk_right)
    (hg.comp measurable_prodMk_right) (hh.comp measurable_prodMk_right) ?_
  intro x x'
  have := hfgh (x, y) (x', y')
  simpa only [Prod.smul_mk, Prod.mk_add_mk] using this

lemma PLProp.of_equiv {X Y : Type*} [AddCommGroup X] [Module ℝ X] [MeasurableSpace X]
    [AddCommGroup Y] [Module ℝ Y] [MeasurableSpace Y] {μ : Measure X} {ν : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e μ ν)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y)
    (hX : PLProp μ) : PLProp ν := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  rw [← he.lintegral_comp_emb e.measurableEmbedding f,
    ← he.lintegral_comp_emb e.measurableEmbedding g,
    ← he.lintegral_comp_emb e.measurableEmbedding h]
  refine hX t ht0 ht1 (fun x => f (e x)) (fun x => g (e x)) (fun x => h (e x))
    (hf.comp e.measurable) (hg.comp e.measurable) (hh.comp e.measurable) ?_
  intro x y
  simp only
  rw [hlin]
  exact hfgh (e x) (e y)

lemma plProp_pi_zero : PLProp (volume : Measure (Fin 0 → ℝ)) := by
  intro t ht0 ht1 f g h hf hg hh hfgh
  rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), lintegral_dirac' _ hf, lintegral_dirac' _ hg,
    lintegral_dirac' _ hh]
  have := hfgh 0 0
  simpa only [smul_zero, add_zero] using this

lemma plProp_pi (n : ℕ) : PLProp (volume : Measure (Fin n → ℝ)) := by
  induction n with
  | zero => exact plProp_pi_zero
  | succ n ih =>
    let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have he : MeasurePreserving e ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ)))
        volume :=
      (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0).symm
    have hlin : ∀ (a b : ℝ) (x y : ℝ × (Fin n → ℝ)), e (a • x + b • y) = a • e x + b • e y := by
      intro a b x y
      ext i
      refine Fin.cases ?_ ?_ i
      · simp [e]
      · intro j; simp [e]
    exact PLProp.of_equiv e he hlin (PLProp.prod plProp_real ih)

lemma plProp_euclidean (n : ℕ) : PLProp (volume : Measure (EuclideanSpace ℝ (Fin n))) := by
  let e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  have he : MeasurePreserving e volume volume :=
    (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).symm
  have hlin : ∀ (a b : ℝ) (x y : Fin n → ℝ), e (a • x + b • y) = a • e x + b • e y := by
    intro a b x y
    simp [e]
  exact PLProp.of_equiv e he hlin (plProp_pi n)

/-- Multiplicative Brunn–Minkowski for compact sets. -/
lemma bm_mul {n : ℕ} {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) {A B : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hB : IsCompact B) :
    volume A ^ (1 - t) * volume B ^ t ≤ volume ((1 - t) • A + t • B) := by
  have hC : IsCompact ((1 - t) • A + t • B) := (hA.smul (1 - t)).add (hB.smul t)
  have hAm : MeasurableSet A := hA.measurableSet
  have hBm : MeasurableSet B := hB.measurableSet
  have hCm : MeasurableSet ((1 - t) • A + t • B) := hC.measurableSet
  have h1t : 0 < 1 - t := by linarith
  have key := plProp_euclidean n t ht0 ht1 (A.indicator 1) (B.indicator 1)
    (((1 - t) • A + t • B).indicator 1) (measurable_one.indicator hAm)
    (measurable_one.indicator hBm) (measurable_one.indicator hCm) ?_
  · rwa [lintegral_indicator_one hAm, lintegral_indicator_one hBm,
      lintegral_indicator_one hCm] at key
  · intro x y
    by_cases hx : x ∈ A
    · by_cases hy : y ∈ B
      · have hxy : (1 - t) • x + t • y ∈ (1 - t) • A + t • B :=
          Set.add_mem_add (Set.smul_mem_smul_set hx) (Set.smul_mem_smul_set hy)
        simp [Set.indicator_of_mem hx, Set.indicator_of_mem hy, Set.indicator_of_mem hxy]
      · simp [Set.indicator_of_notMem hy, ENNReal.zero_rpow_of_pos ht0]
    · simp [Set.indicator_of_notMem hx, ENNReal.zero_rpow_of_pos h1t]

/-- Translating `B` by a point of `A` shows `vol B ≤ vol (A + B)`. -/
lemma mn_vol_le_vol_add {n : ℕ} {A B : Set (EuclideanSpace ℝ (Fin n))} (hA : A.Nonempty) :
    volume B ≤ volume (A + B) := by
  obtain ⟨x, hx⟩ := hA
  calc volume B = volume (x +ᵥ B) := (measure_vadd _ _ _).symm
    _ ≤ volume (A + B) := measure_mono (Set.vadd_set_subset_add hx)

end BrunnMinkowskiAux

open BrunnMinkowskiAux

theorem brunn_minkowski {n : ℕ}
  (hn : 0 < n)
  (A B : Set (EuclideanSpace ℝ (Fin n)))
  (hA_compact : IsCompact A)
  (hB_compact : IsCompact B)
  (hA_nonempty : A.Nonempty)
  (hB_nonempty : B.Nonempty) :
  Real.rpow ((volume (A + B)).toReal) (1 / (n : ℝ)) ≥
    Real.rpow ((volume A).toReal) (1 / (n : ℝ)) +
    Real.rpow ((volume B).toReal) (1 / (n : ℝ)) := by
  simp only [Real.rpow_eq_pow, one_div, ge_iff_le]
  have hAB : IsCompact (A + B) := hA_compact.add hB_compact
  have hAfin : volume A ≠ ∞ := hA_compact.measure_lt_top.ne
  have hBfin : volume B ≠ ∞ := hB_compact.measure_lt_top.ne
  have hABfin : volume (A + B) ≠ ∞ := hAB.measure_lt_top.ne
  have hbc : (volume B).toReal ≤ (volume (A + B)).toReal :=
    ENNReal.toReal_mono hABfin (mn_vol_le_vol_add hA_nonempty)
  have hac : (volume A).toReal ≤ (volume (A + B)).toReal := by
    rw [add_comm A B]
    exact ENNReal.toReal_mono (by rwa [add_comm B A]) (mn_vol_le_vol_add hB_nonempty)
  have hvolA : volume A = ENNReal.ofReal (volume A).toReal := (ENNReal.ofReal_toReal hAfin).symm
  have hvolB : volume B = ENNReal.ofReal (volume B).toReal := (ENNReal.ofReal_toReal hBfin).symm
  have hvolAB : volume (A + B) = ENNReal.ofReal (volume (A + B)).toReal :=
    (ENNReal.ofReal_toReal hABfin).symm
  set a := (volume A).toReal with ha_def
  set b := (volume B).toReal with hb_def
  set c := (volume (A + B)).toReal with hc_def
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have hb0 : 0 ≤ b := ENNReal.toReal_nonneg
  have hn' : (n : ℝ)⁻¹ ≠ 0 := by positivity
  have hn0 : (0:ℝ) ≤ (n : ℝ)⁻¹ := by positivity
  -- degenerate cases: one of the volumes is zero
  rcases ha0.eq_or_lt with ha | ha
  · rw [← ha, Real.zero_rpow hn', zero_add]
    exact Real.rpow_le_rpow hb0 hbc hn0
  rcases hb0.eq_or_lt with hb | hb
  · rw [← hb, Real.zero_rpow hn', add_zero]
    exact Real.rpow_le_rpow ha0 hac hn0
  -- main case: both volumes positive; rescale to unit volume and apply `bm_mul`
  set α := a ^ (n:ℝ)⁻¹ with hα_def
  set β := b ^ (n:ℝ)⁻¹ with hβ_def
  have hα : 0 < α := Real.rpow_pos_of_pos ha _
  have hβ : 0 < β := Real.rpow_pos_of_pos hb _
  have hαn : α ^ n = a := Real.rpow_inv_natCast_pow ha0 hn.ne'
  have hβn : β ^ n = b := Real.rpow_inv_natCast_pow hb0 hn.ne'
  have hαβ : 0 < α + β := by linarith
  set t := β / (α + β) with ht_def
  have ht0 : 0 < t := div_pos hβ hαβ
  have ht1 : t < 1 := (div_lt_one hαβ).2 (by linarith)
  have h1t : 1 - t = α / (α + β) := by
    rw [ht_def]; field_simp; ring
  have key := bm_mul ht0 ht1 (hA_compact.smul α⁻¹) (hB_compact.smul β⁻¹)
  have hA' : volume (α⁻¹ • A) = 1 := by
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, hvolA, inv_pow, hαn,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.2 ha), inv_mul_cancel₀ ha.ne',
      ENNReal.ofReal_one]
  have hB' : volume (β⁻¹ • B) = 1 := by
    rw [Measure.addHaar_smul, finrank_euclideanSpace_fin, hvolB, inv_pow, hβn,
      ← ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (inv_pos.2 hb), inv_mul_cancel₀ hb.ne',
      ENNReal.ofReal_one]
  have hset : (1 - t) • (α⁻¹ • A) + t • (β⁻¹ • B) = (α + β)⁻¹ • (A + B) := by
    rw [smul_smul, smul_smul, smul_add]
    congr 2
    · rw [h1t]; field_simp
    · rw [ht_def]; field_simp
  rw [hA', hB', ENNReal.one_rpow, ENNReal.one_rpow, one_mul, hset, Measure.addHaar_smul,
    finrank_euclideanSpace_fin, hvolAB, ← ENNReal.ofReal_mul (abs_nonneg _),
    ENNReal.one_le_ofReal, abs_of_pos (by positivity), inv_pow] at key
  have hpow : (α + β) ^ n ≤ c := by
    rw [inv_mul_eq_div, le_div_iff₀ (by positivity), one_mul] at key
    exact key
  calc α + β = ((α + β) ^ n) ^ (n:ℝ)⁻¹ := (Real.pow_rpow_inv_natCast hαβ.le hn.ne').symm
    _ ≤ c ^ (n:ℝ)⁻¹ := Real.rpow_le_rpow (by positivity) hpow hn0

end brunn_minkowski
