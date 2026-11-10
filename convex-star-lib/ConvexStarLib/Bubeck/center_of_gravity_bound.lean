import ConvexStarLib.Defs

/-!
# `center_of_gravity_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/center_of_gravity_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace center_of_gravity_bound`, so the main result is `center_of_gravity_bound.center_of_gravity_bound`.
-/

namespace center_of_gravity_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Prékopa–Leindler in dimension 1 -/
lemma pl1_amgm (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (a b : ℝ≥0∞) :
    a ^ θ * b ^ (1 - θ) ≤ ENNReal.ofReal θ * a + ENNReal.ofReal (1 - θ) * b := by
  have h1θ : 0 < 1 - θ := by linarith
  rcases eq_or_ne a ⊤ with rfl | ha
  · have : ENNReal.ofReal θ * ⊤ = ⊤ := ENNReal.mul_top (by simpa using hθ0)
    rw [this, top_add]; exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have : ENNReal.ofReal (1 - θ) * ⊤ = ⊤ := ENNReal.mul_top (by simpa using h1θ)
    rw [this, add_top]; exact le_top
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have key := NNReal.geom_mean_le_arith_mean2_weighted θ.toNNReal (1 - θ).toNNReal a b
    (by
      apply NNReal.coe_injective
      simp [Real.coe_toNNReal _ hθ0.le, Real.coe_toNNReal _ h1θ.le])
  rw [Real.coe_toNNReal _ hθ0.le, Real.coe_toNNReal _ h1θ.le] at key
  rw [← ENNReal.coe_rpow_of_nonneg _ hθ0.le, ← ENNReal.coe_rpow_of_nonneg _ h1θ.le,
    ENNReal.ofReal, ENNReal.ofReal]
  exact_mod_cast key

lemma pl1_bmc_vol_affine (c d : ℝ) (hc : 0 < c) (S : Set ℝ) :
    volume ((fun x => c * x + d) '' S) = ENNReal.ofReal c * volume S := by
  have h1 : (fun x => c * x + d) '' S = (fun y => y + d) '' (c • S) := by
    rw [← Set.image_smul, Set.image_image]; rfl
  rw [h1, Set.image_add_right, measure_preimage_add_right, Measure.addHaar_smul]
  simp [abs_of_pos hc]

lemma pl1_BM_compact (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (A B C : Set ℝ)
    (hA : IsCompact A) (hB : IsCompact B) (hA' : A.Nonempty) (hB' : B.Nonempty)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, θ * a + (1 - θ) * b ∈ C) :
    ENNReal.ofReal θ * volume A + ENNReal.ofReal (1 - θ) * volume B ≤ volume C := by
  have hθ1' : 0 < 1 - θ := by linarith
  set a₀ := sSup A with ha₀
  set b₀ := sInf B with hb₀
  have ha₀A : a₀ ∈ A := hA.sSup_mem hA'
  have hb₀B : b₀ ∈ B := hB.sInf_mem hB'
  set p := θ * a₀ + (1 - θ) * b₀ with hp
  set S₁ := (fun a => θ * a + (1 - θ) * b₀) '' A with hS₁
  set S₂ := (fun b => (1 - θ) * b + θ * a₀) '' B with hS₂
  have hS₁C : S₁ ⊆ C := by
    rintro x ⟨a, ha, rfl⟩
    exact hsub a ha b₀ hb₀B
  have hS₂C : S₂ ⊆ C := by
    rintro x ⟨b, hb, rfl⟩
    have := hsub a₀ ha₀A b hb
    simpa [add_comm] using this
  have hS₁p : ∀ x ∈ S₁, x ≤ p := by
    rintro x ⟨a, ha, rfl⟩
    have : a ≤ a₀ := le_csSup hA.bddAbove ha
    simp only [hp]
    nlinarith
  have hS₂p : ∀ x ∈ S₂, p ≤ x := by
    rintro x ⟨b, hb, rfl⟩
    have : b₀ ≤ b := csInf_le hB.bddBelow hb
    simp only [hp]
    nlinarith
  have hinter : S₁ ∩ S₂ ⊆ {p} := by
    rintro x ⟨h1, h2⟩
    exact le_antisymm (hS₁p x h1) (hS₂p x h2)
  have hS₂meas : MeasurableSet S₂ :=
    (hB.image (by fun_prop)).isClosed.measurableSet
  have hvol1 : volume S₁ = ENNReal.ofReal θ * volume A :=
    pl1_bmc_vol_affine θ _ hθ0 A
  have hvol2 : volume S₂ = ENNReal.ofReal (1 - θ) * volume B :=
    pl1_bmc_vol_affine (1 - θ) _ hθ1' B
  have hinter0 : volume (S₁ ∩ S₂) = 0 :=
    measure_mono_null hinter (measure_singleton p)
  have key := measure_union_add_inter S₁ hS₂meas (μ := volume)
  rw [hinter0, add_zero, hvol1, hvol2] at key
  rw [← key]
  exact measure_mono (Set.union_subset hS₁C hS₂C)

lemma pl1_bm_aux (c : ℝ≥0∞) (A K : Set ℝ) (hA' : A.Nonempty) :
    ∃ K', IsCompact K' ∧ K'.Nonempty ∧ K' ⊆ A ∧
      (⨆ (_ : K ⊆ A) (_ : IsCompact K), c * volume K) ≤ c * volume K' := by
  obtain ⟨a, ha⟩ := hA'
  by_cases h : K ⊆ A ∧ IsCompact K
  · refine ⟨insert a K, h.2.insert a, Set.insert_nonempty a K, Set.insert_subset ha h.1, ?_⟩
    exact iSup_le fun _ => iSup_le fun _ =>
      mul_le_mul_right (measure_mono (Set.subset_insert a K)) c
  · refine ⟨{a}, isCompact_singleton, Set.singleton_nonempty a, Set.singleton_subset_iff.2 ha, ?_⟩
    exact iSup_le fun h1 => iSup_le fun h2 => (h ⟨h1, h2⟩).elim

lemma pl1_BM (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (A B C : Set ℝ)
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hA' : A.Nonempty) (hB' : B.Nonempty)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, θ * a + (1 - θ) * b ∈ C) :
    ENNReal.ofReal θ * volume A + ENNReal.ofReal (1 - θ) * volume B ≤ volume C := by
  rw [hA.measure_eq_iSup_isCompact, hB.measure_eq_iSup_isCompact]
  simp only [ENNReal.mul_iSup]
  refine ENNReal.iSup_add_iSup_le fun K L => ?_
  obtain ⟨K', hK'c, hK'ne, hK'A, hK'⟩ := pl1_bm_aux (ENNReal.ofReal θ) A K hA'
  obtain ⟨L', hL'c, hL'ne, hL'B, hL'⟩ := pl1_bm_aux (ENNReal.ofReal (1 - θ)) B L hB'
  calc _ ≤ ENNReal.ofReal θ * volume K' + ENNReal.ofReal (1 - θ) * volume L' :=
        add_le_add hK' hL'
    _ ≤ volume C := pl1_BM_compact θ hθ0 hθ1 K' L' C hK'c hL'c hK'ne hL'ne
          (fun x hx y hy => hsub x (hK'A hx) y (hL'B hy))

lemma pl1_layer (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ a, f a = ∫⁻ t in Set.Ioi (0:ℝ), volume {a | ENNReal.ofReal t < f a} := by
  by_cases h : volume {a | f a = ⊤} = 0
  · have hae : ∀ᵐ a ∂(volume : Measure ℝ), f a ≠ ⊤ := by
      rw [ae_iff]; simpa using h
    have h1 : ∫⁻ a, f a = ∫⁻ a, ENNReal.ofReal ((f a).toReal) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with a ha
      rw [ENNReal.ofReal_toReal ha]
    rw [h1, lintegral_eq_lintegral_meas_lt volume
      (Filter.Eventually.of_forall (fun a => ENNReal.toReal_nonneg))
      hf.ennreal_toReal.aemeasurable]
    apply setLIntegral_congr_fun measurableSet_Ioi
    intro t ht
    apply measure_congr
    rw [Filter.eventuallyEq_set]
    filter_upwards [hae] with a ha
    exact (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) ha).symm
  · have hL : ∫⁻ a, f a = ⊤ := lintegral_eq_top_of_measure_eq_top_ne_zero hf.aemeasurable h
    rw [hL]
    symm
    apply eq_top_iff.mpr
    calc (⊤ : ℝ≥0∞) = ∫⁻ t in Set.Ioi (0:ℝ), volume {a | f a = ⊤} := by
          rw [setLIntegral_const, Real.volume_Ioi, ENNReal.mul_top h]
      _ ≤ ∫⁻ t in Set.Ioi (0:ℝ), volume {a | ENNReal.ofReal t < f a} := by
          apply lintegral_mono
          intro t
          apply measure_mono
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          rw [ha]
          exact ENNReal.ofReal_lt_top

lemma pl1_norm_level (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g)
    (H : ∀ a b, f a ^ θ * g b ^ (1 - θ) ≤ h (θ * a + (1 - θ) * b))
    (M : ℝ≥0∞) (hfM : ⨆ a, f a = M) (hgM : ⨆ a, g a = M) (t : ℝ) :
    ENNReal.ofReal θ * volume {a | ENNReal.ofReal t < f a}
      + ENNReal.ofReal (1 - θ) * volume {b | ENNReal.ofReal t < g b}
      ≤ volume {c | ENNReal.ofReal t < h c} := by
  by_cases ht : ENNReal.ofReal t < M
  · have hA' : {a | ENNReal.ofReal t < f a}.Nonempty := by
      rw [← hfM] at ht
      obtain ⟨a, ha⟩ := lt_iSup_iff.mp ht
      exact ⟨a, ha⟩
    have hB' : {b | ENNReal.ofReal t < g b}.Nonempty := by
      rw [← hgM] at ht
      obtain ⟨b, hb⟩ := lt_iSup_iff.mp ht
      exact ⟨b, hb⟩
    apply pl1_BM θ hθ0 hθ1 _ _ _ (measurableSet_lt measurable_const hf)
      (measurableSet_lt measurable_const hg) hA' hB'
    intro a ha b hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    refine lt_of_lt_of_le ?_ (H a b)
    have h1 : ENNReal.ofReal t = (ENNReal.ofReal t) ^ θ * (ENNReal.ofReal t) ^ (1 - θ) := by
      rw [← ENNReal.rpow_add_of_nonneg _ _ hθ0.le (by linarith)]
      simp
    rw [h1]
    have hθ1' : 0 < 1 - θ := by linarith
    exact ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow ha hθ0) (ENNReal.rpow_lt_rpow hb hθ1')
  · push_neg at ht
    have hA : {a | ENNReal.ofReal t < f a} = ∅ := by
      ext a
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      calc f a ≤ ⨆ a, f a := le_iSup f a
        _ = M := hfM
        _ ≤ ENNReal.ofReal t := ht
    have hB : {b | ENNReal.ofReal t < g b} = ∅ := by
      ext b
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      calc g b ≤ ⨆ b, g b := le_iSup g b
        _ = M := hgM
        _ ≤ ENNReal.ofReal t := ht
    rw [hA, hB]
    simp

lemma pl1_normalized (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (H : ∀ a b, f a ^ θ * g b ^ (1 - θ) ≤ h (θ * a + (1 - θ) * b))
    (M : ℝ≥0∞) (hfM : ⨆ a, f a = M) (hgM : ⨆ a, g a = M) :
    (∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ) ≤ ∫⁻ a, h a := by
  calc (∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ)
      ≤ ENNReal.ofReal θ * (∫⁻ a, f a) + ENNReal.ofReal (1 - θ) * (∫⁻ a, g a) :=
        pl1_amgm θ hθ0 hθ1 _ _
    _ = ENNReal.ofReal θ * (∫⁻ t in Set.Ioi (0:ℝ), volume {a | ENNReal.ofReal t < f a})
        + ENNReal.ofReal (1 - θ) *
          (∫⁻ t in Set.Ioi (0:ℝ), volume {a | ENNReal.ofReal t < g a}) := by
        rw [pl1_layer f hf, pl1_layer g hg]
    _ = (∫⁻ t in Set.Ioi (0:ℝ), ENNReal.ofReal θ * volume {a | ENNReal.ofReal t < f a})
        + (∫⁻ t in Set.Ioi (0:ℝ),
            ENNReal.ofReal (1 - θ) * volume {a | ENNReal.ofReal t < g a}) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ t in Set.Ioi (0:ℝ), (ENNReal.ofReal θ * volume {a | ENNReal.ofReal t < f a}
        + ENNReal.ofReal (1 - θ) * volume {a | ENNReal.ofReal t < g a}) :=
        le_lintegral_add _ _
    _ ≤ ∫⁻ t in Set.Ioi (0:ℝ), volume {a | ENNReal.ofReal t < h a} :=
        lintegral_mono (fun t => pl1_norm_level θ hθ0 hθ1 f g h hf hg H M hfM hgM t)
    _ = ∫⁻ a, h a := (pl1_layer h hh).symm

lemma pl1_bounded (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (H : ∀ a b, f a ^ θ * g b ^ (1 - θ) ≤ h (θ * a + (1 - θ) * b))
    (hfb : ⨆ a, f a ≠ ⊤) (hgb : ⨆ a, g a ≠ ⊤) :
    (∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ) ≤ ∫⁻ a, h a := by
  have h1θ : 0 < 1 - θ := sub_pos.mpr hθ1
  by_cases hMf0 : (⨆ a, f a) = 0
  · have hf0 : ∀ a, f a = 0 := fun a => le_antisymm (hMf0 ▸ le_iSup f a) (zero_le _)
    have hI : ∫⁻ a, f a = 0 := by simp [hf0]
    rw [hI, ENNReal.zero_rpow_of_pos hθ0, zero_mul]
    exact zero_le _
  by_cases hMg0 : (⨆ a, g a) = 0
  · have hg0 : ∀ a, g a = 0 := fun a => le_antisymm (hMg0 ▸ le_iSup g a) (zero_le _)
    have hI : ∫⁻ a, g a = 0 := by simp [hg0]
    rw [hI, ENNReal.zero_rpow_of_pos h1θ, mul_zero]
    exact zero_le _
  set c : ℝ≥0∞ := (⨆ a, f a) / (⨆ a, g a) with hc
  have hc0 : c ≠ 0 := by
    rw [hc]
    exact (ENNReal.div_pos_iff.mpr ⟨hMf0, hgb⟩).ne'
  have hctop : c ≠ ⊤ := ENNReal.div_ne_top hfb hMg0
  have hcp : c ^ (1 - θ) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.mpr hc0) hctop).ne'
  have hcpt : c ^ (1 - θ) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h1θ.le hctop
  have key := pl1_normalized θ hθ0 hθ1 f (fun b => c * g b) (fun x => c ^ (1 - θ) * h x)
    hf (hg.const_mul c) (hh.const_mul _) ?_ (⨆ a, f a) rfl ?_
  · rw [lintegral_const_mul _ hg, lintegral_const_mul _ hh,
      ENNReal.mul_rpow_of_nonneg _ _ h1θ.le] at key
    rw [← ENNReal.mul_le_mul_iff_right hcp hcpt]
    calc c ^ (1 - θ) * ((∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ))
        = (∫⁻ a, f a) ^ θ * (c ^ (1 - θ) * (∫⁻ a, g a) ^ (1 - θ)) := by ring
      _ ≤ c ^ (1 - θ) * ∫⁻ a, h a := key
  · intro a b
    simp only
    rw [ENNReal.mul_rpow_of_nonneg _ _ h1θ.le]
    calc f a ^ θ * (c ^ (1 - θ) * g b ^ (1 - θ))
        = c ^ (1 - θ) * (f a ^ θ * g b ^ (1 - θ)) := by ring
      _ ≤ c ^ (1 - θ) * h (θ * a + (1 - θ) * b) := _root_.mul_le_mul_right (H a b) _
  · show ⨆ b, c * g b = ⨆ a, f a
    rw [← ENNReal.mul_iSup, hc, ENNReal.div_mul_cancel hMg0 hgb]

theorem PL_one (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (f g h : ℝ → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (H : ∀ a b, f a ^ θ * g b ^ (1 - θ) ≤ h (θ * a + (1 - θ) * b)) :
    (∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ) ≤ ∫⁻ a, h a := by
  have h1θ : 0 < 1 - θ := by linarith
  set F : ℕ → ℝ → ℝ≥0∞ := fun n a => min (f a) n with hF
  set G : ℕ → ℝ → ℝ≥0∞ := fun n a => min (g a) n with hG
  have hFm : ∀ n, Measurable (F n) := fun n => hf.min measurable_const
  have hGm : ∀ n, Measurable (G n) := fun n => hg.min measurable_const
  have hFmono : Monotone F := by
    intro m n hmn a
    exact min_le_min le_rfl (by exact_mod_cast hmn)
  have hGmono : Monotone G := by
    intro m n hmn a
    exact min_le_min le_rfl (by exact_mod_cast hmn)
  have hFsup : ∀ a, ⨆ n, F n a = f a := by
    intro a
    simp only [hF]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have hGsup : ∀ a, ⨆ n, G n a = g a := by
    intro a
    simp only [hG]
    rw [← inf_iSup_eq, ENNReal.iSup_natCast, inf_top_eq]
  have key : ∀ n, (∫⁻ a, F n a) ^ θ * (∫⁻ a, G n a) ^ (1 - θ) ≤ ∫⁻ a, h a := by
    intro n
    apply pl1_bounded θ hθ0 hθ1 (F n) (G n) h (hFm n) (hGm n) hh
    · intro a b
      calc F n a ^ θ * G n b ^ (1 - θ) ≤ f a ^ θ * g b ^ (1 - θ) := by
            gcongr
            · exact min_le_left _ _
            · exact min_le_left _ _
        _ ≤ _ := H a b
    · apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
      exact iSup_le fun a => min_le_right _ _
    · apply ne_top_of_le_ne_top (ENNReal.natCast_ne_top n)
      exact iSup_le fun a => min_le_right _ _
  have hIF : ∫⁻ a, f a = ⨆ n, ∫⁻ a, F n a := by
    rw [← lintegral_iSup hFm hFmono]
    simp only [hFsup]
  have hIG : ∫⁻ a, g a = ⨆ n, ∫⁻ a, G n a := by
    rw [← lintegral_iSup hGm hGmono]
    simp only [hGsup]
  have hr1 : (⨆ n, ∫⁻ a, F n a) ^ θ = ⨆ n, (∫⁻ a, F n a) ^ θ :=
    (ENNReal.orderIsoRpow θ hθ0).map_iSup _
  have hr2 : (⨆ n, ∫⁻ a, G n a) ^ (1 - θ) = ⨆ n, (∫⁻ a, G n a) ^ (1 - θ) :=
    (ENNReal.orderIsoRpow (1 - θ) h1θ).map_iSup _
  rw [hIF, hIG, hr1, hr2, ENNReal.iSup_mul]
  refine iSup_le fun m => ?_
  rw [ENNReal.mul_iSup]
  refine iSup_le fun n => ?_
  calc (∫⁻ a, F m a) ^ θ * (∫⁻ a, G n a) ^ (1 - θ)
      ≤ (∫⁻ a, F (max m n) a) ^ θ * (∫⁻ a, G (max m n) a) ^ (1 - θ) := by
        gcongr
        · exact hFmono (le_max_left m n) _
        · exact hGmono (le_max_right m n) _
    _ ≤ _ := key _

theorem plpi_cons_smul (θ : ℝ) {n : ℕ} (a b : ℝ) (y z : Fin n → ℝ) :
    (Fin.cons (θ * a + (1 - θ) * b) (θ • y + (1 - θ) • z) : Fin (n+1) → ℝ) =
      θ • (Fin.cons a y : Fin (n+1) → ℝ) + (1 - θ) • (Fin.cons b z : Fin (n+1) → ℝ) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

theorem plpi_lintegral_split {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x, f x = ∫⁻ a : ℝ, ∫⁻ y : Fin n → ℝ, f (Fin.cons a y) := by
  have e := MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0
  have e' := e.symm
  rw [← e'.lintegral_comp_emb (MeasurableEquiv.measurableEmbedding _) f]
  rw [Measure.volume_eq_prod]
  rw [lintegral_prod]
  · simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.consEquiv]
  · exact (hf.comp (MeasurableEquiv.measurable _)).aemeasurable

theorem plpi_measurable_section {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    Measurable (fun a : ℝ => ∫⁻ y : Fin n → ℝ, f (Fin.cons a y)) := by
  have hm : Measurable (fun p : ℝ × (Fin n → ℝ) => f (Fin.cons p.1 p.2)) := by
    have : Measurable (fun p : ℝ × (Fin n → ℝ) => (Fin.cons p.1 p.2 : Fin (n+1) → ℝ)) := by
      have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
      simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] using this
    exact hf.comp this
  exact hm.lintegral_prod_right'

theorem plpi_measurable_cons {n : ℕ} (f : (Fin (n+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) (a : ℝ) :
    Measurable (fun y : Fin n → ℝ => f (Fin.cons a y)) := by
  have : Measurable (fun y : Fin n → ℝ => (Fin.cons a y : Fin (n+1) → ℝ)) := by
    have := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => ℝ) 0).symm.measurable
    have h2 : Measurable (fun y : Fin n → ℝ => ((a, y) : ℝ × (Fin n → ℝ))) := measurable_prodMk_left
    simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero'] using this.comp h2
  exact hf.comp this

/-! ## Prékopa–Leindler in dimension n -/
theorem PL_pi (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) : ∀ (n : ℕ) (f g h : (Fin n → ℝ) → ℝ≥0∞),
    Measurable f → Measurable g → Measurable h →
    (∀ a b, f a ^ θ * g b ^ (1 - θ) ≤ h (θ • a + (1 - θ) • b)) →
    (∫⁻ a, f a) ^ θ * (∫⁻ a, g a) ^ (1 - θ) ≤ ∫⁻ a, h a := by
  intro n
  induction n with
  | zero =>
    intro f g h hf hg hh H
    have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac default := Measure.volume_pi_eq_dirac _
    rw [hvol, lintegral_dirac, lintegral_dirac, lintegral_dirac]
    have := H default default
    convert this using 2
  | succ n ih =>
    intro f g h hf hg hh H
    rw [plpi_lintegral_split f hf, plpi_lintegral_split g hg, plpi_lintegral_split h hh]
    apply PL_one θ hθ0 hθ1 _ _ _ (plpi_measurable_section f hf) (plpi_measurable_section g hg)
      (plpi_measurable_section h hh)
    intro a b
    apply ih _ _ _ (plpi_measurable_cons f hf a) (plpi_measurable_cons g hg b)
      (plpi_measurable_cons h hh _)
    intro y z
    rw [plpi_cons_smul]
    exact H _ _

/-! ## Multiplicative Brunn–Minkowski in Euclidean space -/
theorem mult_BM {n : ℕ} (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (A B C : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hB : MeasurableSet B) (hC : MeasurableSet C)
    (hsub : ∀ a ∈ A, ∀ b ∈ B, θ • a + (1 - θ) • b ∈ C) :
    volume A ^ θ * volume B ^ (1 - θ) ≤ volume C := by
  have hp := PiLp.volume_preserving_toLp (Fin n)
  rw [← hp.measure_preimage hA.nullMeasurableSet, ← hp.measure_preimage hB.nullMeasurableSet,
    ← hp.measure_preimage hC.nullMeasurableSet]
  have hA' : MeasurableSet ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' A) :=
    hp.measurable hA
  have hB' : MeasurableSet ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' B) :=
    hp.measurable hB
  have hC' : MeasurableSet ((WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' C) :=
    hp.measurable hC
  rw [← lintegral_indicator_one hA', ← lintegral_indicator_one hB', ← lintegral_indicator_one hC']
  apply PL_pi θ hθ0 hθ1 n
  · exact measurable_one.indicator hA'
  · exact measurable_one.indicator hB'
  · exact measurable_one.indicator hC'
  · intro a b
    by_cases ha : a ∈ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' A
    · by_cases hb : b ∈ (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' B
      · have hc : θ • a + (1 - θ) • b ∈
            (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) ⁻¹' C := by
          have := hsub _ ha _ hb
          simpa using this
        rw [Set.indicator_of_mem ha, Set.indicator_of_mem hb, Set.indicator_of_mem hc]
        simp
      · rw [Set.indicator_of_notMem hb,
          ENNReal.zero_rpow_of_pos (by linarith : (0:ℝ) < 1 - θ), mul_zero]
        exact zero_le _
    · rw [Set.indicator_of_notMem ha, ENNReal.zero_rpow_of_pos hθ0, zero_mul]
      exact zero_le _

/-! ## The one-dimensional `1/e` lemma for log-concave tails -/
lemma oe_iUnion_le {α : Type*} [MeasurableSpace α] (μ : Measure α) (E : ℕ → Set α)
    (hmono : Monotone E) (C : ℝ≥0∞) (h : ∀ n, μ (E n) ≤ C) : μ (⋃ n, E n) ≤ C := by
  rw [hmono.measure_iUnion]
  exact iSup_le h

/-- Probability integral transform bound. -/
lemma oe_pit {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (ℓ : α → ℝ) (c : ℝ) (hc : 0 < c) :
    μ {x | (μ {y | ℓ x ≤ ℓ y}).toReal < c} ≤ ENNReal.ofReal c := by
  set T : Set ℝ := {s | (μ {y | s ≤ ℓ y}).toReal < c} with hT
  have hup : ∀ s t, s ∈ T → s ≤ t → t ∈ T := by
    intro s t hs hst
    simp only [hT, Set.mem_setOf_eq] at hs ⊢
    refine lt_of_le_of_lt ?_ hs
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun y hy => le_trans hst hy))
  have hbd : ∀ s ∈ T, μ {y | s ≤ ℓ y} ≤ ENNReal.ofReal c := by
    intro s hs
    rw [ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hc.le]
    exact hs.le
  have hS : {x | (μ {y | ℓ x ≤ ℓ y}).toReal < c} = ℓ ⁻¹' T := rfl
  rw [hS]
  by_cases hne : T.Nonempty
  swap
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]; simp
  by_cases hbdd : BddBelow T
  · set a := sInf T with ha
    by_cases haT : a ∈ T
    · calc μ (ℓ ⁻¹' T) ≤ μ {y | a ≤ ℓ y} := by
            apply measure_mono
            intro x hx
            exact csInf_le hbdd hx
        _ ≤ ENNReal.ofReal c := hbd a haT
    · have hsub : ℓ ⁻¹' T ⊆ ⋃ n : ℕ, {y | a + 1 / ((n:ℝ) + 1) ≤ ℓ y} := by
        intro x hx
        have h1 : a ≤ ℓ x := csInf_le hbdd hx
        have h2 : a ≠ ℓ x := by
          intro h; apply haT; rw [h]; exact hx
        have h3 : 0 < ℓ x - a := by
          have := lt_of_le_of_ne h1 h2; linarith
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt h3
        exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_setOf_eq]; linarith⟩
      refine le_trans (measure_mono hsub) ?_
      apply oe_iUnion_le
      · intro n k hnk y hy
        simp only [Set.mem_setOf_eq] at hy ⊢
        have : 1 / ((k:ℝ) + 1) ≤ 1 / ((n:ℝ) + 1) := by
          apply one_div_le_one_div_of_le
          · positivity
          · have : (n:ℝ) ≤ k := by exact_mod_cast hnk
            linarith
        linarith
      · intro n
        apply hbd
        have hlt : sInf T < a + 1 / ((n:ℝ) + 1) := by
          have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
          linarith
        obtain ⟨t, ht, htlt⟩ := exists_lt_of_csInf_lt hne hlt
        exact hup t _ ht htlt.le
  · have hall : ∀ s : ℝ, s ∈ T := by
      intro s
      rw [not_bddBelow_iff] at hbdd
      obtain ⟨t, ht, hts⟩ := hbdd s
      exact hup t s ht hts.le
    have hsub : ℓ ⁻¹' T ⊆ ⋃ n : ℕ, {y | -(n:ℝ) ≤ ℓ y} := by
      intro x _
      obtain ⟨n, hn⟩ := exists_nat_ge (-(ℓ x))
      exact Set.mem_iUnion.mpr ⟨n, by simp only [Set.mem_setOf_eq]; linarith⟩
    refine le_trans (measure_mono hsub) ?_
    apply oe_iUnion_le
    · intro n k hnk y hy
      simp only [Set.mem_setOf_eq] at hy ⊢
      have : (n:ℝ) ≤ k := by exact_mod_cast hnk
      linarith
    · intro n
      exact hbd _ (hall _)

lemma oe_logconc {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (ℓ : α → ℝ)
    (hlc : ∀ s t θ : ℝ, 0 < θ → θ < 1 →
      μ {x | s ≤ ℓ x} ^ θ * μ {x | t ≤ ℓ x} ^ (1 - θ) ≤ μ {x | θ * s + (1 - θ) * t ≤ ℓ x})
    (s t θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hs : μ {x | s ≤ ℓ x} ≠ 0) (ht : μ {x | t ≤ ℓ x} ≠ 0) :
    θ * Real.log (μ {x | s ≤ ℓ x}).toReal + (1 - θ) * Real.log (μ {x | t ≤ ℓ x}).toReal
      ≤ Real.log (μ {x | θ * s + (1 - θ) * t ≤ ℓ x}).toReal := by
  have h := hlc s t θ hθ0 hθ1
  have h2 := ENNReal.toReal_mono (measure_ne_top _ _) h
  rw [ENNReal.toReal_mul, ← ENNReal.toReal_rpow, ← ENNReal.toReal_rpow] at h2
  have hsp : 0 < (μ {x | s ≤ ℓ x}).toReal := ENNReal.toReal_pos hs (measure_ne_top _ _)
  have htp : 0 < (μ {x | t ≤ ℓ x}).toReal := ENNReal.toReal_pos ht (measure_ne_top _ _)
  have hpos : 0 < (μ {x | s ≤ ℓ x}).toReal ^ θ * (μ {x | t ≤ ℓ x}).toReal ^ (1 - θ) := by
    positivity
  have h3 := Real.log_le_log hpos h2
  rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hsp, Real.log_rpow htp] at h3
  exact h3

lemma oe_support (L : ℝ → ℝ) (P : ℝ → Prop)
    (hconc : ∀ s t θ, 0 < θ → θ < 1 → P s → P t →
      θ * L s + (1 - θ) * L t ≤ L (θ * s + (1 - θ) * t))
    (hneg : ∀ s, s ≤ 0 → P s) (s₁ : ℝ) (hs₁ : 0 < s₁) (hPs₁ : P s₁) :
    ∃ κ : ℝ, ∀ s, P s → L s ≤ L 0 + κ * s := by
  have key : ∀ s t, s < 0 → 0 < t → P t → (L t - L 0) / t ≤ (L 0 - L s) / (-s) := by
    intro s t hs ht hPt
    have hts : 0 < t - s := by linarith
    have hθ0 : 0 < t / (t - s) := div_pos ht hts
    have hθ1 : t / (t - s) < 1 := by rw [div_lt_one hts]; linarith
    have h := hconc s t (t / (t - s)) hθ0 hθ1 (hneg s hs.le) hPt
    have hz : t / (t - s) * s + (1 - t / (t - s)) * t = 0 := by
      field_simp; ring
    rw [hz] at h
    have h' : t * L s + (-s) * L t ≤ (t - s) * L 0 := by
      have : t / (t - s) * L s + (1 - t / (t - s)) * L t = (t * L s + (-s) * L t) / (t - s) := by
        field_simp; ring
      rw [this, div_le_iff₀ hts] at h
      linarith
    rw [div_le_div_iff₀ ht (by linarith)]
    nlinarith
  set A : Set ℝ := {k | ∃ t, 0 < t ∧ P t ∧ k = (L t - L 0) / t} with hA
  have hAne : A.Nonempty := ⟨_, s₁, hs₁, hPs₁, rfl⟩
  have hAbdd : BddAbove A := by
    refine ⟨(L 0 - L (-1)) / (-(-1)), ?_⟩
    rintro k ⟨t, ht, hPt, rfl⟩
    exact key (-1) t (by norm_num) ht hPt
  refine ⟨sSup A, ?_⟩
  intro s hPs
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have hle : sSup A ≤ (L 0 - L s) / (-s) := by
      apply csSup_le hAne
      rintro k ⟨t, ht, hPt, rfl⟩
      exact key s t hs ht hPt
    rw [le_div_iff₀ (by linarith)] at hle
    nlinarith
  · subst hs; simp
  · have hle : (L s - L 0) / s ≤ sSup A := le_csSup hAbdd ⟨s, hs, hPs, rfl⟩
    rw [div_le_iff₀ hs] at hle
    linarith

theorem one_over_e_lemma {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (ℓ : α → ℝ) (hℓ : Measurable ℓ) (hint : Integrable ℓ μ) (hmean : ∫ x, ℓ x ∂μ = 0)
    (hlc : ∀ s t θ : ℝ, 0 < θ → θ < 1 →
      μ {x | s ≤ ℓ x} ^ θ * μ {x | t ≤ ℓ x} ^ (1 - θ) ≤ μ {x | θ * s + (1 - θ) * t ≤ ℓ x}) :
    μ Set.univ ≤ ENNReal.ofReal (Real.exp 1) * μ {x | 0 ≤ ℓ x} := by
  have he1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp 1) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (1:ℝ)])
  by_cases hpos : μ {x | 0 < ℓ x} = 0
  · -- Case 1: ℓ ≤ 0 a.e., hence ℓ = 0 a.e.
    have hle : ∀ᵐ x ∂μ, ℓ x ≤ 0 := by
      rw [ae_iff]
      simpa [not_le] using hpos
    have hnn : 0 ≤ᵐ[μ] (fun x => -ℓ x) := hle.mono (fun x hx => by simp; linarith)
    have hint' : ∫ x, -ℓ x ∂μ = 0 := by rw [integral_neg, hmean, neg_zero]
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnn hint.neg).mp hint'
    have hneg0 : μ {x | ℓ x < 0} = 0 := by
      have : μ {x | ¬ ((fun x => -ℓ x) x = (0 : α → ℝ) x)} = 0 := ae_iff.mp hz
      refine measure_mono_null ?_ this
      intro x hx
      simp only [Set.mem_setOf_eq, Pi.zero_apply] at hx ⊢
      intro h; linarith
    calc μ Set.univ ≤ μ {x | 0 ≤ ℓ x} + μ {x | ℓ x < 0} := by
          calc μ Set.univ = μ ({x | 0 ≤ ℓ x} ∪ {x | ℓ x < 0}) := by
                congr 1; ext x
                simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
                exact le_or_gt _ _
            _ ≤ _ := measure_union_le _ _
      _ = μ {x | 0 ≤ ℓ x} := by rw [hneg0, add_zero]
      _ = 1 * μ {x | 0 ≤ ℓ x} := (one_mul _).symm
      _ ≤ ENNReal.ofReal (Real.exp 1) * μ {x | 0 ≤ ℓ x} := by gcongr
  · -- Case 2
    obtain ⟨s₁, hs₁, hGs₁⟩ : ∃ s₁ : ℝ, 0 < s₁ ∧ μ {x | s₁ ≤ ℓ x} ≠ 0 := by
      by_contra hcon
      push_neg at hcon
      apply hpos
      have : {x | 0 < ℓ x} = ⋃ n : ℕ, {x | 1 / ((n:ℝ) + 1) ≤ ℓ x} := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_iUnion]
        constructor
        · intro hx
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hx
          exact ⟨n, hn.le⟩
        · rintro ⟨n, hn⟩
          have : (0:ℝ) < 1 / ((n:ℝ) + 1) := by positivity
          linarith
      rw [this]
      exact measure_iUnion_null (fun n => hcon _ (by positivity))
    have hG0 : μ {x | 0 ≤ ℓ x} ≠ 0 := by
      intro h
      apply hGs₁
      exact measure_mono_null (fun y hy => le_trans hs₁.le hy) h
    have hmono : ∀ s t : ℝ, s ≤ t → μ {x | t ≤ ℓ x} ≤ μ {x | s ≤ ℓ x} :=
      fun s t hst => measure_mono (fun y hy => le_trans hst hy)
    -- supporting line
    obtain ⟨κ, hκ⟩ := oe_support (fun s => Real.log (μ {x | s ≤ ℓ x}).toReal)
      (fun s => μ {x | s ≤ ℓ x} ≠ 0)
      (fun s t θ h0 h1 hs ht => oe_logconc μ ℓ hlc s t θ h0 h1 hs ht)
      (fun s hs h => hG0 (le_antisymm (le_trans (hmono s 0 hs) (le_of_eq h)) (_root_.zero_le _)))
      s₁ hs₁ hGs₁
    -- basic quantities
    have hmne : μ Set.univ ≠ 0 := by
      intro h; apply hG0; exact measure_mono_null (Set.subset_univ _) h
    set mR : ℝ := (μ Set.univ).toReal with hmR
    have hmRpos : 0 < mR := ENNReal.toReal_pos hmne (measure_ne_top _ _)
    set g0 : ℝ := (μ {x | 0 ≤ ℓ x}).toReal with hg0
    have hg0pos : 0 < g0 := ENNReal.toReal_pos hG0 (measure_ne_top _ _)
    -- a.e. positivity
    have hnull : μ {x | μ {y | ℓ x ≤ ℓ y} = 0} = 0 := by
      apply le_antisymm _ (_root_.zero_le _)
      apply ENNReal.le_of_forall_pos_le_add
      intro ε hε _
      rw [zero_add]
      calc μ {x | μ {y | ℓ x ≤ ℓ y} = 0} ≤ μ {x | (μ {y | ℓ x ≤ ℓ y}).toReal < ε} := by
            apply measure_mono
            intro x hx
            simp only [Set.mem_setOf_eq] at hx ⊢
            rw [hx]; simpa using hε
        _ ≤ ENNReal.ofReal ε := oe_pit μ ℓ ε (by exact_mod_cast hε)
        _ = ε := ENNReal.ofReal_coe_nnreal
    have haeP : ∀ᵐ x ∂μ, μ {y | ℓ x ≤ ℓ y} ≠ 0 := by
      rw [ae_iff]; simpa using hnull
    -- the function Φ
    set Φ : α → ℝ := fun x => -Real.log ((μ {y | ℓ x ≤ ℓ y}).toReal / mR) with hΦ
    have hGmeas : Measurable (fun s : ℝ => μ {y | s ≤ ℓ y}) := by
      apply Antitone.measurable
      intro s t hst
      exact hmono s t hst
    have hΦmeas : Measurable Φ :=
      ((hGmeas.comp hℓ).ennreal_toReal.div_const mR).log.neg
    have hΦnn : ∀ x, 0 ≤ Φ x := by
      intro x
      simp only [hΦ, neg_nonneg]
      apply Real.log_nonpos
      · positivity
      · rw [div_le_one hmRpos]
        exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (Set.subset_univ _))
    have hlayer : ∫⁻ x, ENNReal.ofReal (Φ x) ∂μ ≤ ENNReal.ofReal mR := by
      rw [lintegral_eq_lintegral_meas_lt μ (ae_of_all _ hΦnn) hΦmeas.aemeasurable]
      calc ∫⁻ t in Set.Ioi 0, μ {a | t < Φ a}
          ≤ ∫⁻ t in Set.Ioi 0, ENNReal.ofReal (mR * Real.exp (-t)) := by
            apply setLIntegral_mono' measurableSet_Ioi
            intro t ht
            calc μ {a | t < Φ a}
                ≤ μ {x | (μ {y | ℓ x ≤ ℓ y}).toReal < mR * Real.exp (-t)} := by
                  apply measure_mono
                  intro a ha
                  simp only [Set.mem_setOf_eq, hΦ] at ha ⊢
                  rcases eq_or_lt_of_le (ENNReal.toReal_nonneg :
                      0 ≤ (μ {y | ℓ a ≤ ℓ y}).toReal) with h0 | h0
                  · rw [← h0]; positivity
                  · have h1 : Real.log ((μ {y | ℓ a ≤ ℓ y}).toReal / mR) < -t := by linarith
                    rw [Real.log_lt_iff_lt_exp (by positivity)] at h1
                    rw [div_lt_iff₀ hmRpos] at h1
                    linarith
              _ ≤ ENNReal.ofReal (mR * Real.exp (-t)) := oe_pit μ ℓ _ (by positivity)
        _ = ENNReal.ofReal (∫ t in Set.Ioi 0, mR * Real.exp (-t)) := by
            rw [ofReal_integral_eq_lintegral_ofReal]
            · exact (integrableOn_exp_neg_Ioi 0).const_mul mR
            · exact ae_of_all _ (fun t => by positivity)
        _ = ENNReal.ofReal mR := by
            rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
    have hΦint : Integrable Φ μ := by
      rw [← lintegral_ofReal_ne_top_iff_integrable hΦmeas.aestronglyMeasurable (ae_of_all _ hΦnn)]
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlayer
    have hΦle : ∫ x, Φ x ∂μ ≤ mR := by
      rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hΦnn) hΦmeas.aestronglyMeasurable]
      have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlayer
      rwa [ENNReal.toReal_ofReal hmRpos.le] at this
    -- Jensen at the supporting line
    have hae : ∀ᵐ x ∂μ, (Real.log mR - Real.log g0) - κ * ℓ x ≤ Φ x := by
      filter_upwards [haeP] with x hx
      have h1 := hκ (ℓ x) hx
      have hpx : 0 < (μ {y | ℓ x ≤ ℓ y}).toReal := ENNReal.toReal_pos hx (measure_ne_top _ _)
      simp only [hΦ]
      rw [Real.log_div hpx.ne' hmRpos.ne']
      linarith
    have hint2 : Integrable (fun x => (Real.log mR - Real.log g0) - κ * ℓ x) μ :=
      (integrable_const _).sub (hint.const_mul κ)
    have hineq := integral_mono_ae hint2 hΦint hae
    rw [integral_sub (integrable_const _) (hint.const_mul κ), integral_const, integral_const_mul,
      hmean] at hineq
    have hreal : μ.real Set.univ = mR := rfl
    rw [hreal, smul_eq_mul, mul_zero, sub_zero] at hineq
    have hfin : Real.log mR - Real.log g0 ≤ 1 := by
      have := le_trans hineq hΦle
      by_contra hcon
      push_neg at hcon
      nlinarith
    have hfin2 : mR ≤ Real.exp 1 * g0 := by
      have h1 : Real.log mR ≤ 1 + Real.log g0 := by linarith
      calc mR = Real.exp (Real.log mR) := (Real.exp_log hmRpos).symm
        _ ≤ Real.exp (1 + Real.log g0) := Real.exp_le_exp.mpr h1
        _ = Real.exp 1 * g0 := by rw [Real.exp_add, Real.exp_log hg0pos]
    calc μ Set.univ = ENNReal.ofReal mR := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ ≤ ENNReal.ofReal (Real.exp 1 * g0) := ENNReal.ofReal_le_ofReal hfin2
      _ = ENNReal.ofReal (Real.exp 1) * μ {x | 0 ≤ ℓ x} := by
        rw [ENNReal.ofReal_mul (Real.exp_pos 1).le, hg0, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-! ## Grünbaum's inequality -/
theorem grunbaum {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKc : Convex ℝ K) (hKpos : 0 < volume K) (w : EuclideanSpace ℝ (Fin n)) (hw : w ≠ 0) :
    volume (K ∩ {x | inner ℝ (x - barycenter K) w ≤ 0})
      ≤ ENNReal.ofReal (1 - 1 / Real.exp 1) * volume K := by
  set c := barycenter K with hc_def
  set ℓ : EuclideanSpace ℝ (Fin n) → ℝ := fun x => inner ℝ (x - c) w with hℓ_def
  have hℓc : Continuous ℓ := by
    simp only [hℓ_def]; fun_prop
  have hℓm : Measurable ℓ := hℓc.measurable
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hKfin : volume K < ⊤ := hK.measure_lt_top
  haveI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.2 hKfin.ne
  have hint : Integrable ℓ (volume.restrict K) :=
    hℓc.continuousOn.integrableOn_compact hK
  have hidint : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x) (volume.restrict K) :=
    continuous_id.continuousOn.integrableOn_compact hK
  have hmean : ∫ x, ℓ x ∂(volume.restrict K) = 0 := by
    have h1 : Integrable (fun x : EuclideanSpace ℝ (Fin n) => x - c) (volume.restrict K) :=
      hidint.sub (integrable_const c)
    simp only [hℓ_def]
    simp_rw [real_inner_comm w]
    rw [integral_inner h1, integral_sub hidint (integrable_const c), setIntegral_const]
    have hreal : volume.real K ≠ 0 := by
      rw [Measure.real]
      exact ENNReal.toReal_ne_zero.2 ⟨hKpos.ne', hKfin.ne⟩
    have : volume.real K • c = ∫ x in K, x := by
      rw [hc_def, barycenter, smul_smul, mul_inv_cancel₀ hreal, one_smul]
    rw [this, sub_self, inner_zero_right]
  have hlc : ∀ s t θ : ℝ, 0 < θ → θ < 1 →
      (volume.restrict K) {x | s ≤ ℓ x} ^ θ * (volume.restrict K) {x | t ≤ ℓ x} ^ (1 - θ)
        ≤ (volume.restrict K) {x | θ * s + (1 - θ) * t ≤ ℓ x} := by
    intro s t θ h0 h1
    rw [Measure.restrict_apply (measurableSet_le measurable_const hℓm),
      Measure.restrict_apply (measurableSet_le measurable_const hℓm),
      Measure.restrict_apply (measurableSet_le measurable_const hℓm)]
    apply mult_BM θ h0 h1
    · exact (measurableSet_le measurable_const hℓm).inter hKm
    · exact (measurableSet_le measurable_const hℓm).inter hKm
    · exact (measurableSet_le measurable_const hℓm).inter hKm
    · intro a ha b hb
      refine ⟨?_, hKc ha.2 hb.2 h0.le (by linarith) (by ring)⟩
      have ha1 : s ≤ ℓ a := ha.1
      have hb1 : t ≤ ℓ b := hb.1
      show θ * s + (1 - θ) * t ≤ ℓ (θ • a + (1 - θ) • b)
      have : ℓ (θ • a + (1 - θ) • b) = θ * ℓ a + (1 - θ) * ℓ b := by
        simp only [hℓ_def]
        have : θ • a + (1 - θ) • b - c = θ • (a - c) + (1 - θ) • (b - c) := by
          rw [smul_sub, smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
        rw [this, inner_add_left, real_inner_smul_left, real_inner_smul_left]
      rw [this]
      have := mul_le_mul_of_nonneg_left ha1 h0.le
      have := mul_le_mul_of_nonneg_left hb1 (by linarith : (0:ℝ) ≤ 1 - θ)
      linarith
  have key := one_over_e_lemma (volume.restrict K) ℓ hℓm hint hmean hlc
  rw [Measure.restrict_apply_univ, Measure.restrict_apply (measurableSet_le measurable_const hℓm)]
    at key
  -- the hyperplane `{ℓ = 0}` is null
  have hnull : volume {x | ℓ x = 0} = 0 := by
    let V : Submodule ℝ (EuclideanSpace ℝ (Fin n)) := LinearMap.ker (innerₛₗ ℝ w)
    have hV : V ≠ ⊤ := by
      intro hV
      have : w ∈ V := hV ▸ Submodule.mem_top
      simp only [V, LinearMap.mem_ker, innerₛₗ_apply_apply] at this
      exact hw (inner_self_eq_zero.1 this)
    have hset : {x | ℓ x = 0} = (fun x => x + (-c)) ⁻¹' (V : Set (EuclideanSpace ℝ (Fin n))) := by
      ext x
      simp only [hℓ_def, Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, V,
        LinearMap.mem_ker, innerₛₗ_apply_apply, ← sub_eq_add_neg]
      rw [real_inner_comm]
    rw [hset, measure_preimage_add_right]
    exact Measure.addHaar_submodule volume V hV
  -- conclude
  set P := volume ({x | 0 ≤ ℓ x} ∩ K) with hP
  set Q := volume (K ∩ {x | ℓ x ≤ 0}) with hQ
  set P' := volume (K ∩ {x | 0 < ℓ x}) with hP'
  have hPP' : P = P' := by
    apply le_antisymm
    · calc P ≤ volume ((K ∩ {x | 0 < ℓ x}) ∪ {x | ℓ x = 0}) := by
            apply measure_mono
            intro x hx
            rcases (show (0:ℝ) ≤ ℓ x from hx.1).lt_or_eq with h | h
            · exact Or.inl ⟨hx.2, h⟩
            · exact Or.inr h.symm
        _ ≤ P' + volume {x | ℓ x = 0} := measure_union_le _ _
        _ = P' := by rw [hnull, add_zero]
    · apply measure_mono
      intro x hx
      exact ⟨show (0:ℝ) ≤ ℓ x from le_of_lt hx.2, hx.1⟩
  have hsum : Q + P' = volume K := by
    rw [hQ, hP', ← measure_union]
    · congr 1
      ext x
      simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
      constructor
      · rintro (h | h) <;> exact h.1
      · intro hx
        rcases le_or_gt (ℓ x) 0 with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr ⟨hx, h⟩
    · rw [Set.disjoint_left]
      rintro x ⟨_, h1⟩ ⟨_, h2⟩
      exact absurd (show ℓ x ≤ 0 from h1) (not_le.2 h2)
    · exact hKm.inter (measurableSet_lt measurable_const hℓm)
  have hQfin : Q ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono Set.inter_subset_left)
  have hP'fin : P' ≠ ⊤ := ne_top_of_le_ne_top hKfin.ne (measure_mono Set.inter_subset_left)
  rw [hPP'] at key
  have hsumR : Q.toReal + P'.toReal = (volume K).toReal := by
    rw [← ENNReal.toReal_add hQfin hP'fin, hsum]
  have keyR : (volume K).toReal ≤ Real.exp 1 * P'.toReal := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP'fin) key
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos 1).le] at this
  rw [← ENNReal.ofReal_toReal hQfin, ← ENNReal.ofReal_toReal hKfin.ne,
    ← ENNReal.ofReal_mul (by
      have := Real.add_one_le_exp 1
      rw [sub_nonneg, div_le_one (Real.exp_pos 1)]; linarith)]
  apply ENNReal.ofReal_le_ofReal
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hP'le : (volume K).toReal / Real.exp 1 ≤ P'.toReal := by
    rw [div_le_iff₀ he]; linarith
  have : (1 - 1 / Real.exp 1) * (volume K).toReal = (volume K).toReal - (volume K).toReal / Real.exp 1 := by
    ring
  rw [this]
  linarith

lemma cog_halfspace_closed {n : ℕ} (p v : EuclideanSpace ℝ (Fin n)) :
    IsClosed {y : EuclideanSpace ℝ (Fin n) | inner ℝ (y - p) v ≤ 0} :=
  isClosed_le (by fun_prop) continuous_const

lemma cog_halfspace_convex {n : ℕ} (p v : EuclideanSpace ℝ (Fin n)) :
    Convex ℝ {y : EuclideanSpace ℝ (Fin n) | inner ℝ (y - p) v ≤ 0} := by
  intro x hx y hy a b ha hb hab
  simp only [Set.mem_setOf_eq] at *
  have h : a • x + b • y - p = a • (x - p) + b • (y - p) := by
    rw [smul_sub, smul_sub]
    have : p = a • p + b • p := by rw [← add_smul, hab, one_smul]
    rw [this]; abel_nf
    rw [← this]
  rw [h, inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith [mul_nonpos_of_nonneg_of_nonpos ha hx, mul_nonpos_of_nonneg_of_nonpos hb hy]

lemma cog_S_props {n : ℕ} (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
    (S : ℕ → Set (EuclideanSpace ℝ (Fin n))) (w : ℕ → EuclideanSpace ℝ (Fin n))
    (h0 : S 0 = 𝓧) (hS : ∀ t, S (t + 1) = (centerOfGravityStep (S t) (w t)).2)
    (hc : IsCompact 𝓧) (hcv : Convex ℝ 𝓧) :
    ∀ s, IsCompact (S s) ∧ Convex ℝ (S s) ∧ S s ⊆ 𝓧 := by
  intro s
  induction s with
  | zero => rw [h0]; exact ⟨hc, hcv, subset_rfl⟩
  | succ k ih =>
    rw [hS k]
    simp only [centerOfGravityStep]
    exact ⟨ih.1.inter_right (cog_halfspace_closed _ _), ih.2.1.inter (cog_halfspace_convex _ _),
      Set.inter_subset_left.trans ih.2.2⟩

lemma cog_barycenter_mem {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) (hK : IsCompact K)
    (hKc : Convex ℝ K) (hpos : volume K ≠ 0) : barycenter K ∈ K := by
  have h1 : barycenter K = ⨍ x in K, x := by
    rw [MeasureTheory.setAverage_eq]; rfl
  rw [h1]
  apply hKc.set_average_mem hK.isClosed hpos hK.measure_lt_top.ne
  · exact ae_restrict_mem hK.measurableSet
  · exact continuousOn_id.integrableOn_compact hK

set_option linter.unusedVariables false in
theorem center_of_gravity_bound {n t : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (c : ℕ → EuclideanSpace ℝ (Fin n)) (S : ℕ → Set (EuclideanSpace ℝ (Fin n)))
  (w : ℕ → EuclideanSpace ℝ (Fin n)) (x : ℕ → EuclideanSpace ℝ (Fin n))
  (B R r : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty (interior 𝓧))
  (h𝓧_contained : 𝓧 ⊆ Metric.ball 0 R ∧ Metric.ball 0 r ⊆ 𝓧)
  (hf_continuous : Continuous f)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_bounded : ∀ x ∈ 𝓧, f x ≤ B ∧ f x ≥ -B)
  (h_cog_sequence : IsCenterOfGravitySequence 𝓧 f c S w x)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hn : n > 0) :
  f (x t) - f x_star ≤ 2 * B * (1 - 1 / (Real.exp 1)) ^ ((t : ℝ) / (n : ℝ)) := by
  obtain ⟨hc0, hS0, hc, hS, hsub, hmin⟩ := h_cog_sequence
  set q : ℝ := 1 - 1 / Real.exp 1 with hq_def
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have hq0 : 0 < q := by
    rw [hq_def, sub_pos, div_lt_one (by positivity)]; exact he1
  have hq1 : q < 1 := by
    rw [hq_def]
    have : 0 < 1 / Real.exp 1 := by positivity
    linarith
  have hSprops := cog_S_props 𝓧 S w hS0 hS h𝓧_compact h𝓧_convex
  have hVpos : 0 < volume 𝓧 := Measure.measure_pos_of_nonempty_interior (μ := volume) h𝓧_nonempty
  have hVfin : volume 𝓧 < ⊤ := h𝓧_compact.measure_lt_top
  have hc0mem : c 0 ∈ 𝓧 := by
    rw [hc0, hS0]; exact cog_barycenter_mem 𝓧 h𝓧_compact h𝓧_convex hVpos.ne'
  have hxt_le : f (x t) ≤ f (c 0) := (hmin t).1 0 (Nat.zero_le _)
  have hB1 : f (c 0) ≤ B := (hf_bounded _ hc0mem).1
  have hB2 : f x_star ≥ -B := (hf_bounded _ hx_star_mem).2
  by_contra hcon
  push_neg at hcon
  set p : ℝ := q ^ ((t:ℝ) / (n:ℝ)) with hp_def
  have hp0 : 0 ≤ p := Real.rpow_nonneg hq0.le _
  have hp1 : p ≤ 1 := Real.rpow_le_one hq0.le hq1.le (by positivity)
  have hBpos : 0 < B := by
    by_contra hB
    push_neg at hB
    have : 2 * B ≤ 2 * B * p := by nlinarith
    linarith
  set ε : ℝ := (f (x t) - f x_star) / (2 * B) with hε_def
  have hε_gt : p < ε := by
    rw [hε_def, lt_div_iff₀ (by positivity)]; linarith
  have hε_le : ε ≤ 1 := by
    rw [hε_def, div_le_one (by positivity)]; linarith
  have hε_pos : 0 < ε := lt_of_le_of_lt hp0 hε_gt
  have hδ : 2 * B * ε = f (x t) - f x_star := by
    rw [hε_def]; field_simp
  have hhom_mem : ∀ z ∈ 𝓧, AffineMap.homothety x_star ε z ∈ 𝓧 ∧
      f (AffineMap.homothety x_star ε z) ≤ f (x t) := by
    intro z hz
    have heq : AffineMap.homothety x_star ε z = (1 - ε) • x_star + ε • z := by
      rw [AffineMap.homothety_apply, vsub_eq_sub, vadd_eq_add, smul_sub, sub_smul, one_smul]; abel
    rw [heq]
    have h1 : 0 ≤ 1 - ε := by linarith
    refine ⟨h𝓧_convex hx_star_mem hz h1 hε_pos.le (by ring), ?_⟩
    have hcv := hf_convex.2 hx_star_mem hz h1 hε_pos.le (by ring)
    have hz' := (hf_bounded z hz).1
    simp only [smul_eq_mul] at hcv
    nlinarith [mul_nonneg hε_pos.le (sub_nonneg.mpr hz'),
      mul_nonneg hε_pos.le (show 0 ≤ f x_star + B by linarith)]
  have hhom_S : ∀ s, s ≤ t → AffineMap.homothety x_star ε '' 𝓧 ⊆ S s := by
    intro s
    induction s with
    | zero => intro _; rw [hS0]; rintro y ⟨z, hz, rfl⟩; exact (hhom_mem z hz).1
    | succ k ih =>
      intro hk
      rintro y ⟨z, hz, rfl⟩
      have hmemk := ih (Nat.le_of_succ_le hk) ⟨z, hz, rfl⟩
      rw [hS k]
      simp only [centerOfGravityStep]
      refine ⟨hmemk, ?_⟩
      simp only [Set.mem_setOf_eq]
      have hsg := hsub k _ (hhom_mem z hz).1
      have hfx : f (x t) ≤ f (c (k + 1)) := (hmin t).1 (k + 1) hk
      rw [hc k] at hsg hfx
      simp only [centerOfGravityStep] at hsg hfx
      linarith [(hhom_mem z hz).2]
  have hvol_hom : volume (AffineMap.homothety x_star ε '' 𝓧) =
      ENNReal.ofReal (ε ^ n) * volume 𝓧 := by
    rw [MeasureTheory.Measure.addHaar_image_homothety, finrank_euclideanSpace_fin,
      abs_of_nonneg (pow_nonneg hε_pos.le n)]
  have hlow : ∀ s, s ≤ t → ENNReal.ofReal (ε ^ n) * volume 𝓧 ≤ volume (S s) := by
    intro s hs
    rw [← hvol_hom]
    exact measure_mono (hhom_S s hs)
  have hlowpos : 0 < ENNReal.ofReal (ε ^ n) * volume 𝓧 := by
    apply ENNReal.mul_pos
    · exact (ENNReal.ofReal_pos.mpr (pow_pos hε_pos n)).ne'
    · exact hVpos.ne'
  have hw_ne : ∀ s, s < t → w s ≠ 0 := by
    intro s hs hw0
    have hsg := hsub s x_star hx_star_mem
    rw [hw0, inner_zero_right, add_zero] at hsg
    have hfx : f (x t) ≤ f (c (s + 1)) := (hmin t).1 (s + 1) hs
    have : 0 < 2 * B * ε := by positivity
    linarith
  have hup : ∀ s, s ≤ t → volume (S s) ≤ ENNReal.ofReal q ^ s * volume 𝓧 := by
    intro s
    induction s with
    | zero => intro _; simp [hS0]
    | succ k ih =>
      intro hk
      have hk' : k < t := hk
      have ihk := ih hk'.le
      have hposk : 0 < volume (S k) := lt_of_lt_of_le hlowpos (hlow k hk'.le)
      calc volume (S (k + 1)) ≤ ENNReal.ofReal q * volume (S k) := by
            rw [hS k]
            exact grunbaum (S k) (hSprops k).1 (hSprops k).2.1 hposk (w k) (hw_ne k hk')
        _ ≤ ENNReal.ofReal q * (ENNReal.ofReal q ^ k * volume 𝓧) := by gcongr
        _ = ENNReal.ofReal q ^ (k + 1) * volume 𝓧 := by ring
  have hfinal := (hlow t le_rfl).trans (hup t le_rfl)
  rw [← ENNReal.ofReal_pow hq0.le] at hfinal
  have hfinal2 : ENNReal.ofReal (ε ^ n) ≤ ENNReal.ofReal (q ^ t) :=
    (ENNReal.mul_le_mul_iff_left hVpos.ne' hVfin.ne).mp hfinal
  have hfinal3 : ε ^ n ≤ q ^ t :=
    (ENNReal.ofReal_le_ofReal_iff (pow_nonneg hq0.le t)).mp hfinal2
  have hpn : p ^ n = q ^ t := by
    rw [hp_def, ← Real.rpow_natCast (q ^ ((t:ℝ) / (n:ℝ))) n, ← Real.rpow_mul hq0.le,
      div_mul_cancel₀ _ (by exact_mod_cast hn.ne' : (n:ℝ) ≠ 0), Real.rpow_natCast]
  have := pow_lt_pow_left₀ hε_gt hp0 hn.ne'
  linarith

end center_of_gravity_bound
