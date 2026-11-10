import ConvexStarLib.Defs

/-!
# `Duchi_Q5_2c`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_Q5_2c` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_Q5_2c`, so the main result is `Duchi_Q5_2c.Duchi_Q5_2c`.
-/

namespace Duchi_Q5_2c

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


namespace DuchiAux

open Set

/-! ### 1-D Brunn–Minkowski (midpoint form) -/

/-- The affine map `a ↦ (a + c) / 2` doubles the (outer) Lebesgue measure of preimages. -/
lemma bm1_volume_preimage_half_add (c : ℝ) (S : Set ℝ) :
    volume ((fun a : ℝ => (a + c) / 2) ⁻¹' S) = 2 * volume S := by
  have h1 : (fun a : ℝ => (a + c) / 2) ⁻¹' S =
      (fun a : ℝ => a + c) ⁻¹' ((fun x : ℝ => (2⁻¹ : ℝ) * x) ⁻¹' S) := by
    ext a
    simp only [mem_preimage, div_eq_inv_mul]
  rw [h1, measure_preimage_add_right, Real.volume_preimage_mul_left (by norm_num)]
  norm_num

theorem bm1_compact {K L C : Set ℝ} (hK : IsCompact K) (hL : IsCompact L)
    (hKne : K.Nonempty) (hLne : L.Nonempty)
    (hC : ∀ a ∈ K, ∀ b ∈ L, (a + b) / 2 ∈ C) :
    volume K + volume L ≤ 2 * volume C := by
  obtain ⟨k, hk, hkmax⟩ : ∃ k ∈ K, ∀ a ∈ K, a ≤ k :=
    ⟨sSup K, hK.sSup_mem hKne, fun a ha => le_csSup hK.bddAbove ha⟩
  obtain ⟨l, hl, hlmin⟩ : ∃ l ∈ L, ∀ b ∈ L, l ≤ b :=
    ⟨sInf L, hL.sInf_mem hLne, fun b hb => csInf_le hL.bddBelow hb⟩
  have h1 : K ⊆ (fun a : ℝ => (a + l) / 2) ⁻¹' (C ∩ Iic ((k + l) / 2)) := by
    intro a ha
    simp only [mem_preimage, mem_inter_iff, mem_Iic]
    refine ⟨hC a ha l hl, ?_⟩
    have := hkmax a ha
    linarith
  have h2 : L ⊆ (fun b : ℝ => (b + k) / 2) ⁻¹' (C ∩ Ici ((k + l) / 2)) := by
    intro b hb
    simp only [mem_preimage, mem_inter_iff, mem_Ici]
    refine ⟨?_, ?_⟩
    · rw [add_comm]
      exact hC k hk b hb
    · have := hlmin b hb
      linarith
  have hK' : volume K ≤ 2 * volume (C ∩ Iic ((k + l) / 2)) :=
    (measure_mono h1).trans (bm1_volume_preimage_half_add l _).le
  have hL' : volume L ≤ 2 * volume (C ∩ Ici ((k + l) / 2)) :=
    (measure_mono h2).trans (bm1_volume_preimage_half_add k _).le
  have h3 : volume (C ∩ Ici ((k + l) / 2)) ≤ volume (C \ Iic ((k + l) / 2)) := by
    have hsub : C ∩ Ici ((k + l) / 2) ⊆ (C \ Iic ((k + l) / 2)) ∪ {(k + l) / 2} := by
      intro x hx
      rcases eq_or_lt_of_le (show (k + l) / 2 ≤ x from hx.2) with h | h
      · exact Or.inr h.symm
      · exact Or.inl ⟨hx.1, not_le.mpr h⟩
    calc volume (C ∩ Ici ((k + l) / 2))
        ≤ volume ((C \ Iic ((k + l) / 2)) ∪ {(k + l) / 2}) := measure_mono hsub
      _ ≤ volume (C \ Iic ((k + l) / 2)) + volume ({(k + l) / 2} : Set ℝ) :=
          measure_union_le _ _
      _ = volume (C \ Iic ((k + l) / 2)) := by rw [Real.volume_singleton, add_zero]
  have h4 : volume (C ∩ Iic ((k + l) / 2)) + volume (C \ Iic ((k + l) / 2)) = volume C :=
    measure_inter_add_diff C measurableSet_Iic
  calc volume K + volume L
      ≤ 2 * volume (C ∩ Iic ((k + l) / 2)) + 2 * volume (C ∩ Ici ((k + l) / 2)) :=
        add_le_add hK' hL'
    _ ≤ 2 * volume (C ∩ Iic ((k + l) / 2)) + 2 * volume (C \ Iic ((k + l) / 2)) := by
        gcongr
    _ = 2 * volume C := by rw [← mul_add, h4]

theorem bm1 {A B C : Set ℝ} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAne : A.Nonempty) (hBne : B.Nonempty)
    (hC : ∀ a ∈ A, ∀ b ∈ B, (a + b) / 2 ∈ C) :
    volume A + volume B ≤ 2 * volume C := by
  obtain ⟨a₀, ha₀⟩ := hAne
  obtain ⟨b₀, hb₀⟩ := hBne
  have key : ∀ K : Set ℝ, K ⊆ A ∧ IsCompact K → ∀ L : Set ℝ, L ⊆ B ∧ IsCompact L →
      volume K + volume L ≤ 2 * volume C := by
    rintro K ⟨hKA, hKc⟩ L ⟨hLB, hLc⟩
    calc volume K + volume L ≤ volume (insert a₀ K) + volume (insert b₀ L) := by
          gcongr <;> exact subset_insert _ _
      _ ≤ 2 * volume C := by
          refine bm1_compact (hKc.insert a₀) (hLc.insert b₀) (insert_nonempty _ _)
            (insert_nonempty _ _) ?_
          intro a ha b hb
          exact hC a (insert_subset ha₀ hKA ha) b (insert_subset hb₀ hLB hb)
  rw [hA.measure_eq_iSup_isCompact, hB.measure_eq_iSup_isCompact]
  simp only [iSup_and']
  exact ENNReal.biSup_add_biSup_le' ⟨∅, empty_subset _, isCompact_empty⟩
    ⟨∅, empty_subset _, isCompact_empty⟩ key

/-! ### 1-D Prékopa–Leindler (λ = 1/2) -/

/-- Layer cake formula for a finite-valued measurable `ℝ≥0∞`-valued function on `ℝ`. -/
theorem layercake_toReal {u : ℝ → ℝ≥0∞} (hu : Measurable u) (hu1 : ∀ x, u x ≠ ∞) :
    ∫⁻ x, u x = ∫⁻ t in Ioi (0:ℝ), volume {x | t < (u x).toReal} := by
  have h := lintegral_eq_lintegral_meas_lt (volume : Measure ℝ) (f := fun x => (u x).toReal)
    (Filter.Eventually.of_forall fun x => ENNReal.toReal_nonneg) hu.ennreal_toReal.aemeasurable
  rw [← h]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_toReal (hu1 x)]

theorem pl1_normalized {f g k : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    (hfs : ∀ t < 1, ∃ x, t < f x) (hgs : ∀ t < 1, ∃ x, t < g x)
    (H : ∀ x y, min (f x) (g y) ≤ k ((x + y) / 2)) :
    (∫⁻ x, f x) + (∫⁻ x, g x) ≤ 2 * ∫⁻ x, k x := by
  obtain ⟨k', hk'_def⟩ : ∃ k' : ℝ → ℝ≥0∞, k' = fun x => min (k x) 1 := ⟨_, rfl⟩
  have hk' : Measurable k' := hk'_def ▸ hk.min measurable_const
  have hk'1 : ∀ x, k' x ≤ 1 := fun x => by rw [hk'_def]; exact min_le_right _ _
  have H' : ∀ x y, min (f x) (g y) ≤ k' ((x + y) / 2) := fun x y => by
    rw [hk'_def]; exact le_min (H x y) (min_le_of_left_le (hf1 x))
  have hkk' : ∫⁻ x, k' x ≤ ∫⁻ x, k x :=
    lintegral_mono fun x => by rw [hk'_def]; exact min_le_left _ _
  have ne_top_of_le_one : ∀ a : ℝ≥0∞, a ≤ 1 → a ≠ ∞ := fun a ha =>
    ne_top_of_le_ne_top one_ne_top ha
  -- nonemptiness of superlevel sets below level `1`
  have nonempty_of : ∀ u : ℝ → ℝ≥0∞, (∀ x, u x ≤ 1) → (∀ t < 1, ∃ x, t < u x) →
      ∀ t : ℝ, t < 1 → {x | t < (u x).toReal}.Nonempty := by
    intro u hu1 hus t ht
    obtain ⟨x, hx⟩ := hus (ENNReal.ofReal t) (ENNReal.ofReal_lt_one.mpr ht)
    refine ⟨x, ?_⟩
    show t < (u x).toReal
    have := ENNReal.toReal_strict_mono (ne_top_of_le_one _ (hu1 x)) hx
    rw [ENNReal.toReal_ofReal'] at this
    exact lt_of_le_of_lt (le_max_left _ _) this
  -- emptiness of superlevel sets above level `1`
  have empty_of : ∀ u : ℝ → ℝ≥0∞, (∀ x, u x ≤ 1) →
      ∀ t : ℝ, 1 ≤ t → {x | t < (u x).toReal} = ∅ := by
    intro u hu1 t ht
    ext x
    simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
    have := ENNReal.toReal_mono one_ne_top (hu1 x)
    rw [ENNReal.toReal_one] at this
    exact le_trans this ht
  -- pointwise inequality between the measures of superlevel sets
  have key : ∀ t : ℝ, volume {x | t < (f x).toReal} + volume {x | t < (g x).toReal}
      ≤ 2 * volume {x | t < (k' x).toReal} := by
    intro t
    by_cases ht : t < 1
    · apply bm1
      · exact measurableSet_lt measurable_const hf.ennreal_toReal
      · exact measurableSet_lt measurable_const hg.ennreal_toReal
      · exact nonempty_of f hf1 hfs t ht
      · exact nonempty_of g hg1 hgs t ht
      · intro a ha b hb
        simp only [mem_setOf_eq] at ha hb ⊢
        have h1 := ENNReal.toReal_mono (ne_top_of_le_one _ (hk'1 _)) (H' a b)
        rw [ENNReal.toReal_min (ne_top_of_le_one _ (hf1 a)) (ne_top_of_le_one _ (hg1 b))] at h1
        exact lt_of_lt_of_le (lt_min ha hb) h1
    · push_neg at ht
      rw [empty_of f hf1 t ht, empty_of g hg1 t ht]
      simp
  calc (∫⁻ x, f x) + (∫⁻ x, g x)
      = (∫⁻ t in Ioi (0:ℝ), volume {x | t < (f x).toReal})
        + ∫⁻ t in Ioi (0:ℝ), volume {x | t < (g x).toReal} := by
        rw [layercake_toReal hf (fun x => ne_top_of_le_one _ (hf1 x)),
          layercake_toReal hg (fun x => ne_top_of_le_one _ (hg1 x))]
    _ ≤ ∫⁻ t in Ioi (0:ℝ), (volume {x | t < (f x).toReal} + volume {x | t < (g x).toReal}) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ t in Ioi (0:ℝ), 2 * volume {x | t < (k' x).toReal} := lintegral_mono key
    _ = 2 * ∫⁻ t in Ioi (0:ℝ), volume {x | t < (k' x).toReal} :=
        lintegral_const_mul' _ _ (by norm_num)
    _ = 2 * ∫⁻ x, k' x := by
        rw [layercake_toReal hk' (fun x => ne_top_of_le_one _ (hk'1 x))]
    _ ≤ 2 * ∫⁻ x, k x := by gcongr

/-- AM–GM in `ℝ≥0∞`. -/
lemma pl1_amgm_aux (u v : ℝ≥0∞) : 4 * u * v ≤ (u + v) ^ 2 := by
  rcases eq_or_ne u ∞ with rfl | hu
  · simp
  rcases eq_or_ne v ∞ with rfl | hv
  · simp
  lift u to ℝ≥0 using hu
  lift v to ℝ≥0 using hv
  have := four_mul_le_sq_add u v
  exact_mod_cast this

/-- Algebraic final step of `pl1_bounded`. -/
lemma pl1_bounded_aux {P Q R a b c : ℝ≥0∞} (ha0 : a ≠ 0) (hatop : a ≠ ∞) (hb0 : b ≠ 0)
    (hbtop : b ≠ ∞) (hc0 : c ≠ 0) (hctop : c ≠ ∞) (hc2 : c ^ 2 = a * b)
    (key : P / a + Q / b ≤ 2 * (R / c)) : P * Q ≤ R ^ 2 := by
  have hP : P = P / a * a := (ENNReal.div_mul_cancel ha0 hatop).symm
  have hQ : Q = Q / b * b := (ENNReal.div_mul_cancel hb0 hbtop).symm
  have huv : (P / a + Q / b) * c ≤ 2 * R := by
    calc (P / a + Q / b) * c ≤ 2 * (R / c) * c := by gcongr
      _ = 2 * R := by rw [mul_assoc, ENNReal.div_mul_cancel hc0 hctop]
  have h4 : 4 * (P * Q) ≤ 4 * R ^ 2 := by
    calc 4 * (P * Q) = 4 * (P / a) * (Q / b) * c ^ 2 := by
          rw [hc2]; nth_rewrite 1 [hP]; nth_rewrite 1 [hQ]; ring
      _ ≤ (P / a + Q / b) ^ 2 * c ^ 2 := by
          gcongr; exact pl1_amgm_aux _ _
      _ = ((P / a + Q / b) * c) ^ 2 := by ring
      _ ≤ (2 * R) ^ 2 := by gcongr
      _ = 4 * R ^ 2 := by ring
  exact (ENNReal.mul_le_mul_iff_right (by norm_num) (by norm_num)).mp h4

theorem pl1_bounded {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h) (hfb : (⨆ x, f x) ≠ ∞) (hgb : (⨆ x, g x) ≠ ∞)
    (H : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  obtain ⟨a, ha⟩ : ∃ a : ℝ≥0, (⨆ x, f x) = a := ⟨_, (ENNReal.coe_toNNReal hfb).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ≥0, (⨆ x, g x) = b := ⟨_, (ENNReal.coe_toNNReal hgb).symm⟩
  have hfa : ∀ x, f x ≤ a := fun x => ha ▸ le_iSup f x
  have hgb' : ∀ x, g x ≤ b := fun x => hb ▸ le_iSup g x
  rcases eq_or_ne a 0 with rfl | ha0
  · have : ∀ x, f x = 0 := fun x => le_antisymm (by simpa using hfa x) (zero_le _)
    simp [this]
  rcases eq_or_ne b 0 with rfl | hb0
  · have : ∀ x, g x = 0 := fun x => le_antisymm (by simpa using hgb' x) (zero_le _)
    simp [this]
  set c : ℝ≥0 := NNReal.sqrt (a * b) with hc
  have hc2 : (c : ℝ≥0∞) ^ 2 = a * b := by
    rw [← ENNReal.coe_pow, hc, NNReal.sq_sqrt, ENNReal.coe_mul]
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (NNReal.sqrt_pos.mpr (mul_pos (pos_iff_ne_zero.mpr ha0) (pos_iff_ne_zero.mpr hb0))).ne'
  have ha0' : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha0
  have hb0' : (b : ℝ≥0∞) ≠ 0 := by exact_mod_cast hb0
  have hc0' : (c : ℝ≥0∞) ≠ 0 := by exact_mod_cast hc0
  have hf1 : ∀ x, f x / a ≤ 1 := fun x => ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hfa x)
  have hg1 : ∀ x, g x / b ≤ 1 := fun x => ENNReal.div_le_of_le_mul (by rw [one_mul]; exact hgb' x)
  have hfs : ∀ t < 1, ∃ x, t < f x / a := by
    intro t ht
    have h1 : t * a < ⨆ x, f x := by
      rw [ha]
      have : t * (a : ℝ≥0∞) < 1 * a := ENNReal.mul_lt_mul_left ha0' ENNReal.coe_ne_top ht
      rwa [one_mul] at this
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp h1
    exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl ha0') (Or.inl ENNReal.coe_ne_top)).mpr hx⟩
  have hgs : ∀ t < 1, ∃ x, t < g x / b := by
    intro t ht
    have h1 : t * b < ⨆ x, g x := by
      rw [hb]
      have : t * (b : ℝ≥0∞) < 1 * b := ENNReal.mul_lt_mul_left hb0' ENNReal.coe_ne_top ht
      rwa [one_mul] at this
    obtain ⟨x, hx⟩ := lt_iSup_iff.mp h1
    exact ⟨x, (ENNReal.lt_div_iff_mul_lt (Or.inl hb0') (Or.inl ENNReal.coe_ne_top)).mpr hx⟩
  have hH : ∀ x y, min (f x / a) (g y / b) ≤ h ((x + y) / 2) / c := by
    intro x y
    rw [← ENNReal.pow_le_pow_left_iff two_ne_zero]
    calc min (f x / a) (g y / b) ^ 2
        = min (f x / a) (g y / b) * min (f x / a) (g y / b) := sq _
      _ ≤ f x / a * (g y / b) := mul_le_mul' (min_le_left _ _) (min_le_right _ _)
      _ = f x * g y / (a * b) :=
          (ENNReal.mul_div_mul_comm (Or.inl ha0') (Or.inl ENNReal.coe_ne_top)).symm
      _ ≤ h ((x + y) / 2) ^ 2 / (a * b) := ENNReal.div_le_div_right (H x y) _
      _ = h ((x + y) / 2) ^ 2 / (c : ℝ≥0∞) ^ 2 := by rw [hc2]
      _ = (h ((x + y) / 2) / c) ^ 2 := by
          simp only [div_eq_mul_inv, mul_pow, ENNReal.inv_pow]
  have key := pl1_normalized (f := fun x => f x / a) (g := fun x => g x / b)
    (k := fun x => h x / c) (hf.div_const _) (hg.div_const _) (hh.div_const _) hf1 hg1 hfs hgs hH
  have e : ∀ (F : ℝ → ℝ≥0∞) (r : ℝ≥0∞), Measurable F → ∫⁻ x, F x / r = (∫⁻ x, F x) / r := by
    intro F r hF
    simp_rw [div_eq_mul_inv]
    exact lintegral_mul_const _ hF
  rw [e f _ hf, e g _ hg, e h _ hh] at key
  exact pl1_bounded_aux ha0' ENNReal.coe_ne_top hb0' ENNReal.coe_ne_top hc0' ENNReal.coe_ne_top
    hc2 key

theorem pl1 {f g h : ℝ → ℝ≥0∞} (hf : Measurable f) (hg : Measurable g)
    (hh : Measurable h)
    (H : ∀ x y, f x * g y ≤ h ((x + y) / 2) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  have hN : ∀ N : ℕ, (∫⁻ x, min (f x) (N : ℝ≥0∞)) * (∫⁻ x, min (g x) (N : ℝ≥0∞)) ≤
      (∫⁻ x, h x) ^ 2 := by
    intro N
    refine pl1_bounded (hf.min measurable_const) (hg.min measurable_const) hh ?_ ?_ ?_
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (iSup_le fun x => min_le_right _ _)
    · exact ne_top_of_le_ne_top (ENNReal.natCast_ne_top N) (iSup_le fun x => min_le_right _ _)
    · intro x y
      exact (mul_le_mul' (min_le_left _ _) (min_le_left _ _)).trans (H x y)
  have hmono : ∀ F : ℝ → ℝ≥0∞, Monotone (fun (N : ℕ) x => min (F x) (N : ℝ≥0∞)) := by
    intro F M N hMN x
    exact min_le_min_left _ (by exact_mod_cast hMN)
  have hsup : ∀ F : ℝ → ℝ≥0∞, Measurable F →
      ∫⁻ x, F x = ⨆ N : ℕ, ∫⁻ x, min (F x) (N : ℝ≥0∞) := by
    intro F hF
    rw [← lintegral_iSup (fun N => hF.min measurable_const) (hmono F)]
    congr 1
    funext x
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  rw [hsup f hf, hsup g hg, ENNReal.iSup_mul]
  refine iSup_le fun M => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun N => ?_
  have h1 : ∫⁻ x, min (f x) (M : ℝ≥0∞) ≤ ∫⁻ x, min (f x) ((max M N : ℕ) : ℝ≥0∞) :=
    lintegral_mono fun x => hmono f (le_max_left M N) x
  have h2 : ∫⁻ x, min (g x) (N : ℝ≥0∞) ≤ ∫⁻ x, min (g x) ((max M N : ℕ) : ℝ≥0∞) :=
    lintegral_mono fun x => hmono g (le_max_right M N) x
  exact (mul_le_mul' h1 h2).trans (hN (max M N))

/-! ### Tensorization -/

/-- Prékopa–Leindler property (with `λ = 1/2`) of a measure space with a midpoint operation. -/
def PLProp (E : Type*) [MeasureSpace E] [Add E] [SMul ℝ E] : Prop :=
  ∀ f g h : E → ℝ≥0∞, Measurable f → Measurable g → Measurable h →
    (∀ x y, f x * g y ≤ h ((2:ℝ)⁻¹ • (x + y)) ^ 2) →
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2

theorem plProp_real : PLProp ℝ := by
  intro f g h hf hg hh H
  refine pl1 hf hg hh (fun x y => ?_)
  have hxy := H x y
  rwa [smul_eq_mul, inv_mul_eq_div] at hxy

theorem plProp_prod {E F : Type*} [MeasureSpace E] [MeasureSpace F] [Add E] [SMul ℝ E]
    [Add F] [SMul ℝ F] [SFinite (volume : Measure E)] [SFinite (volume : Measure F)]
    (hE : PLProp E) (hF : PLProp F) : PLProp (E × F) := by
  intro f g h hf hg hh H
  have key : ∀ x₁ x₂ : E, (∫⁻ y, f (x₁, y)) * (∫⁻ y, g (x₂, y)) ≤
      (∫⁻ y, h ((2:ℝ)⁻¹ • (x₁ + x₂), y)) ^ 2 := by
    intro x₁ x₂
    refine hF (fun y => f (x₁, y)) (fun y => g (x₂, y))
      (fun y => h ((2:ℝ)⁻¹ • (x₁ + x₂), y))
      (hf.comp measurable_prodMk_left) (hg.comp measurable_prodMk_left)
      (hh.comp measurable_prodMk_left) (fun y₁ y₂ => ?_)
    exact H (x₁, y₁) (x₂, y₂)
  have h1 := hE (fun x => ∫⁻ y, f (x, y)) (fun x => ∫⁻ y, g (x, y))
    (fun x => ∫⁻ y, h (x, y))
    hf.lintegral_prod_right' hg.lintegral_prod_right' hh.lintegral_prod_right' key
  rw [Measure.volume_eq_prod, lintegral_prod _ hf.aemeasurable, lintegral_prod _ hg.aemeasurable,
    lintegral_prod _ hh.aemeasurable]
  exact h1

theorem plProp_equiv {E F : Type*} [MeasureSpace E] [MeasureSpace F] [Add E] [SMul ℝ E]
    [Add F] [SMul ℝ F] (e : E ≃ᵐ F) (he : MeasurePreserving e volume volume)
    (hlin : ∀ x y : E, e ((2:ℝ)⁻¹ • (x + y)) = (2:ℝ)⁻¹ • (e x + e y))
    (hE : PLProp E) : PLProp F := by
  intro f g h hf hg hh H
  have h1 := hE (fun x => f (e x)) (fun x => g (e x)) (fun x => h (e x))
    (hf.comp e.measurable) (hg.comp e.measurable) (hh.comp e.measurable)
    (fun x y => by
      show f (e x) * g (e y) ≤ h (e ((2:ℝ)⁻¹ • (x + y))) ^ 2
      rw [hlin]; exact H (e x) (e y))
  rwa [he.lintegral_comp_emb e.measurableEmbedding f, he.lintegral_comp_emb e.measurableEmbedding g,
    he.lintegral_comp_emb e.measurableEmbedding h] at h1

theorem plProp_fin (n : ℕ) : PLProp (Fin n → ℝ) := by
  induction n with
  | zero =>
    intro f g h hf hg hh H
    rw [Measure.volume_pi_eq_dirac (0 : Fin 0 → ℝ), lintegral_dirac' _ hf, lintegral_dirac' _ hg,
      lintegral_dirac' _ hh]
    simpa using H 0 0
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
    have hlin : ∀ x y : Fin (n+1) → ℝ, e ((2:ℝ)⁻¹ • (x + y)) = (2:ℝ)⁻¹ • (e x + e y) := by
      intro x y
      ext j
      · simp [e, mul_add]
      · simp [e, Fin.tail]
    refine plProp_equiv e.symm he.symm ?_ (plProp_prod plProp_real ih)
    intro x y
    apply e.injective
    rw [hlin]
    simp

theorem plProp_euclid (n : ℕ) : PLProp (EuclideanSpace ℝ (Fin n)) := by
  refine plProp_equiv (MeasurableEquiv.toLp 2 (Fin n → ℝ)) (PiLp.volume_preserving_toLp (Fin n))
    ?_ (plProp_fin n)
  intro x y
  simp [MeasurableEquiv.toLp_apply]

/-- Prékopa–Leindler on Euclidean space, with `f`, `g` arbitrary and `h` a.e.-measurable. -/
theorem pl_euclid_ae {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℝ≥0∞) (hh : AEMeasurable h)
    (H : ∀ x y, f x * g y ≤ h ((2:ℝ)⁻¹ • (x + y)) ^ 2) :
    (∫⁻ x, f x) * (∫⁻ x, g x) ≤ (∫⁻ x, h x) ^ 2 := by
  classical
  obtain ⟨f₀, hf₀m, hf₀le, hf₀eq⟩ := exists_measurable_le_lintegral_eq volume f
  obtain ⟨g₀, hg₀m, hg₀le, hg₀eq⟩ := exists_measurable_le_lintegral_eq volume g
  set N := toMeasurable volume {x | h x ≠ hh.mk h x} with hN
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hN0 : volume N = 0 := by
    rw [hN, measure_toMeasurable]
    exact ae_iff.1 hh.ae_eq_mk
  let h₀ : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := N.piecewise (fun _ => ∞) (hh.mk h)
  have hh₀m : Measurable h₀ := Measurable.piecewise hNm measurable_const hh.measurable_mk
  have hhle : ∀ x, h x ≤ h₀ x := by
    intro x
    by_cases hx : x ∈ N
    · simp [h₀, Set.piecewise_eq_of_mem _ _ _ hx]
    · have : h x = hh.mk h x := by
        by_contra hne
        exact hx (subset_toMeasurable _ _ hne)
      simp [h₀, Set.piecewise_eq_of_notMem _ _ _ hx, this]
  have hh₀eq : ∫⁻ x, h₀ x = ∫⁻ x, h x := by
    apply lintegral_congr_ae
    have h1 : h₀ =ᵐ[volume] hh.mk h := by
      have : ∀ᵐ x ∂volume, x ∉ N := by
        rw [ae_iff]; simpa using hN0
      filter_upwards [this] with x hx
      simp [h₀, Set.piecewise_eq_of_notMem _ _ _ hx]
    exact h1.trans hh.ae_eq_mk.symm
  rw [hf₀eq, hg₀eq, ← hh₀eq]
  apply plProp_euclid n f₀ g₀ h₀ hf₀m hg₀m hh₀m
  intro x y
  calc f₀ x * g₀ y ≤ f x * g y := mul_le_mul' (hf₀le x) (hg₀le y)
    _ ≤ h ((2:ℝ)⁻¹ • (x + y)) ^ 2 := H x y
    _ ≤ h₀ ((2:ℝ)⁻¹ • (x + y)) ^ 2 := by gcongr; exact hhle _

/-! ### Anderson's inequality for sublevel sets -/

theorem sublevel_mass_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (L : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_lc : IsLogConcave f) (hf_sym : IsSymmetricFun f) (hL_qc : IsQuasiConvex L)
    (hL_sym : IsSymmetricFun L) (hf_meas : AEMeasurable f) (hL_meas : Measurable L)
    (x : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    ∫⁻ z in {z | L (x + z) ≤ t}, ENNReal.ofReal (f z) ≤
      ∫⁻ z in {z | L z ≤ t}, ENNReal.ofReal (f z) := by
  set F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun z => ENNReal.ofReal (f z) with hF
  have hA : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | L (x + z) ≤ t} :=
    measurableSet_le (hL_meas.comp (measurable_const_add x)) measurable_const
  have hC : MeasurableSet {z : EuclideanSpace ℝ (Fin n) | L z ≤ t} :=
    measurableSet_le hL_meas measurable_const
  rw [← lintegral_indicator hA, ← lintegral_indicator hC]
  have hFm : AEMeasurable F := hf_meas.ennreal_ofReal
  have hw : AEMeasurable ({z | L z ≤ t}.indicator F) := hFm.indicator hC
  have hPL := pl_euclid_ae ({z | L (x + z) ≤ t}.indicator F)
    ({z | L (-x + z) ≤ t}.indicator F) ({z | L z ≤ t}.indicator F) hw ?_
  · have heq : ∫⁻ z, {z | L (-x + z) ≤ t}.indicator F z
        = ∫⁻ z, {z | L (x + z) ≤ t}.indicator F z := by
      rw [← lintegral_neg_eq_self]
      congr 1
      ext z
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
      have h1 : L (-x + -z) = L (x + z) := by rw [← neg_add, hL_sym]
      simp only [h1, hF, hf_sym z]
    rw [heq, ← pow_two] at hPL
    exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 hPL
  · intro z₁ z₂
    by_cases h1 : L (x + z₁) ≤ t
    · by_cases h2 : L (-x + z₂) ≤ t
      · have hm : (2:ℝ)⁻¹ • (z₁ + z₂) = (2:ℝ)⁻¹ • (x + z₁) + (1 - (2:ℝ)⁻¹) • (-x + z₂) := by
          module
        have h3 : L ((2:ℝ)⁻¹ • (z₁ + z₂)) ≤ t := by
          rw [hm]
          exact (hL_qc _ _ _ ⟨by norm_num, by norm_num⟩).trans (max_le h1 h2)
        have hm' : (2:ℝ)⁻¹ • (z₁ + z₂) = (2:ℝ)⁻¹ • z₁ + (1 - (2:ℝ)⁻¹) • z₂ := by module
        have hlc := hf_lc.2 z₁ z₂ (2:ℝ)⁻¹ ⟨by norm_num, by norm_num⟩
        rw [← hm'] at hlc
        have key : f z₁ * f z₂ ≤ f ((2:ℝ)⁻¹ • (z₁ + z₂)) ^ 2 := by
          have h0 : 0 ≤ (f z₁) ^ (2⁻¹:ℝ) * (f z₂) ^ (2⁻¹:ℝ) := by
            have := hf_lc.1 z₁
            have := hf_lc.1 z₂
            positivity
          have h4 : (f z₁) ^ (2⁻¹:ℝ) * (f z₂) ^ (2⁻¹:ℝ) ≤ f ((2:ℝ)⁻¹ • (z₁ + z₂)) := by
            have e : (1:ℝ) - 2⁻¹ = 2⁻¹ := by norm_num
            rw [e] at hlc
            exact hlc
          calc f z₁ * f z₂ = ((f z₁) ^ (2⁻¹:ℝ) * (f z₂) ^ (2⁻¹:ℝ)) ^ 2 := by
                rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_natCast,
                  ← Real.rpow_mul (hf_lc.1 _), ← Real.rpow_mul (hf_lc.1 _)]
                norm_num
            _ ≤ _ := pow_le_pow_left₀ h0 h4 2
        rw [Set.indicator_of_mem (show z₁ ∈ {z | L (x + z) ≤ t} from h1),
          Set.indicator_of_mem (show z₂ ∈ {z | L (-x + z) ≤ t} from h2),
          Set.indicator_of_mem (show (2:ℝ)⁻¹ • (z₁ + z₂) ∈ {z | L z ≤ t} from h3), hF]
        dsimp only
        rw [← ENNReal.ofReal_mul (hf_lc.1 _), ← ENNReal.ofReal_pow (hf_lc.1 _)]
        exact ENNReal.ofReal_le_ofReal key
      · rw [Set.indicator_of_notMem (show z₂ ∉ {z | L (-x + z) ≤ t} from h2), mul_zero]
        exact zero_le _
    · rw [Set.indicator_of_notMem (show z₁ ∉ {z | L (x + z) ≤ t} from h1), zero_mul]
      exact zero_le _

end DuchiAux

theorem Duchi_Q5_2c {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (L : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_lc : IsLogConcave f)
  (hf_sym : IsSymmetricFun f)
  (hL_qc : IsQuasiConvex L)
  (hL_sym : IsSymmetricFun L)
  (hL_nn : ∀ x, 0 ≤ L x)
  (hf_int : Integrable f)
  (hL_meas : Measurable L)
  (hLf_int : ∀ x, Integrable (fun z => L (x + z) * f z))
  (x : EuclideanSpace ℝ (Fin n)) :
  ∫ z, L z * f z ≤ ∫ z, L (x + z) * f z := by
  classical
  have hf_nn : ∀ z, 0 ≤ f z := hf_lc.1
  have hf_meas : AEMeasurable f := hf_int.aestronglyMeasurable.aemeasurable
  set F : EuclideanSpace ℝ (Fin n) → ℝ≥0∞ := fun z => ENNReal.ofReal (f z) with hF
  have hF_meas : AEMeasurable F := hf_meas.ennreal_ofReal
  set ν : Measure (EuclideanSpace ℝ (Fin n)) := volume.withDensity F with hν
  have hν_fin : ν Set.univ ≠ ∞ := by
    rw [hν, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    have h2 := hf_int.2
    rw [HasFiniteIntegral] at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr (fun z => ?_)
    simp [hF, Real.enorm_eq_ofReal (hf_nn z)]
  have layer : ∀ y, ∫⁻ z, ENNReal.ofReal (L (y + z) * f z) =
      ∫⁻ t in Set.Ioi 0, ν {z | t < L (y + z)} := by
    intro y
    have hLy : Measurable (fun z => L (y + z)) := hL_meas.comp (measurable_const_add y)
    have h1 : ∫⁻ z, ENNReal.ofReal (L (y + z) * f z) =
        ∫⁻ z, ENNReal.ofReal (L (y + z)) ∂ν := by
      rw [hν, lintegral_withDensity_eq_lintegral_mul₀ hF_meas
        hLy.ennreal_ofReal.aemeasurable]
      refine lintegral_congr (fun z => ?_)
      simp only [Pi.mul_apply, hF]
      rw [ENNReal.ofReal_mul (hL_nn _), mul_comm]
    rw [h1, lintegral_eq_lintegral_meas_lt ν (ae_of_all _ (fun z => hL_nn _))
      hLy.aemeasurable]
  have tail : ∀ t : ℝ, ν {z | t < L z} ≤ ν {z | t < L (x + z)} := by
    intro t
    have hS1 : MeasurableSet {z | L z ≤ t} := measurableSet_le hL_meas measurable_const
    have hS2 : MeasurableSet {z | L (x + z) ≤ t} :=
      measurableSet_le (hL_meas.comp (measurable_const_add x)) measurable_const
    have key := DuchiAux.sublevel_mass_le f L hf_lc hf_sym hL_qc hL_sym hf_meas hL_meas x t
    have key' : ν {z | L (x + z) ≤ t} ≤ ν {z | L z ≤ t} := by
      rw [hν, withDensity_apply _ hS1, withDensity_apply _ hS2]
      exact key
    have e1 : {z | t < L z} = {z | L z ≤ t}ᶜ := by
      ext z; simp [not_le]
    have e2 : {z | t < L (x + z)} = {z | L (x + z) ≤ t}ᶜ := by
      ext z; simp [not_le]
    rw [e1, e2, measure_compl hS1 (ne_top_of_le_ne_top hν_fin (measure_mono (Set.subset_univ _))),
      measure_compl hS2 (ne_top_of_le_ne_top hν_fin (measure_mono (Set.subset_univ _)))]
    exact tsub_le_tsub_left key' _
  have hint0 : Integrable (fun z => L z * f z) := by simpa using hLf_int 0
  have hintx := hLf_int x
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => mul_nonneg (hL_nn _) (hf_nn _)))
      hint0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun z => mul_nonneg (hL_nn _) (hf_nn _)))
      hintx.aestronglyMeasurable]
  apply ENNReal.toReal_mono
  · have h2 := hintx.2
    rw [HasFiniteIntegral] at h2
    refine ne_of_lt (lt_of_le_of_lt (le_of_eq ?_) h2)
    refine lintegral_congr (fun z => ?_)
    rw [Real.enorm_eq_ofReal (mul_nonneg (hL_nn _) (hf_nn _))]
  · have h0 := layer 0
    simp only [zero_add] at h0
    rw [h0, layer x]
    exact lintegral_mono (fun t => tail t)

end Duchi_Q5_2c
