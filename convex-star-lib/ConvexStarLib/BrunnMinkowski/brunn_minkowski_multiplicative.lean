import ConvexStarLib.Defs

/-!
# `brunn_minkowski_multiplicative`

Source: BrunnMinkowski.

Statement from the `convex-eval-v28-2h/brunn_minkowski_multiplicative` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace brunn_minkowski_multiplicative`, so the main result is `brunn_minkowski_multiplicative.brunn_minkowski_multiplicative`.
-/

namespace brunn_minkowski_multiplicative

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

namespace BMAux

open Set

/-- 1D Brunn–Minkowski for nonempty compact sets. -/
lemma bm1_compact (K L : Set ℝ) (hK : IsCompact K) (hL : IsCompact L)
    (hK0 : K.Nonempty) (hL0 : L.Nonempty) :
    volume K + volume L ≤ volume (K + L) := by
  obtain ⟨a, ha, hKa⟩ := hK.exists_isGreatest hK0
  obtain ⟨b, hb, hLb⟩ := hL.exists_isLeast hL0
  have h1 : K + {b} ⊆ K + L := Set.add_subset_add_left (Set.singleton_subset_iff.2 hb)
  have h2 : {a} + L ⊆ K + L := Set.add_subset_add_right (Set.singleton_subset_iff.2 ha)
  have hv1 : volume (K + {b}) = volume K := by
    rw [Set.add_singleton, Set.image_add_right, measure_preimage_add_right]
  have hv2 : volume ({a} + L) = volume L := by
    rw [Set.singleton_add, Set.image_add_left, measure_preimage_add]
  have hint : (K + {b}) ∩ ({a} + L) ⊆ {a + b} := by
    rintro x ⟨⟨k, hk, y, hy, hx⟩, ⟨z, hz, l, hl, hx'⟩⟩
    rw [mem_singleton_iff] at hy hz ⊢
    subst hy hz
    have := hKa hk
    have := hLb hl
    linarith
  have hmeas : MeasurableSet ({a} + L) := (isCompact_singleton.add hL).measurableSet
  calc volume K + volume L = volume (K + {b}) + volume ({a} + L) := by rw [hv1, hv2]
    _ = volume ((K + {b}) ∪ ({a} + L)) + volume ((K + {b}) ∩ ({a} + L)) :=
        (measure_union_add_inter _ hmeas).symm
    _ ≤ volume (K + L) + 0 :=
        add_le_add (measure_mono (Set.union_subset h1 h2))
          ((measure_mono hint).trans (measure_singleton _).le)
    _ = volume (K + L) := add_zero _

/-- 1D Brunn–Minkowski for nonempty measurable sets. -/
lemma bm1_meas (S T : Set ℝ) (hS : MeasurableSet S) (hT : MeasurableSet T)
    (hS0 : S.Nonempty) (hT0 : T.Nonempty) :
    volume S + volume T ≤ volume (S + T) := by
  obtain ⟨s, hs⟩ := hS0
  obtain ⟨t, ht⟩ := hT0
  by_cases hS' : volume S = 0
  · rw [hS', zero_add]
    calc volume T = volume ({s} + T) := by
          rw [Set.singleton_add, Set.image_add_left, measure_preimage_add]
      _ ≤ volume (S + T) :=
          measure_mono (Set.add_subset_add_right (Set.singleton_subset_iff.2 hs))
  by_cases hT' : volume T = 0
  · rw [hT', add_zero]
    calc volume S = volume (S + {t}) := by
          rw [Set.add_singleton, Set.image_add_right, measure_preimage_add_right]
      _ ≤ volume (S + T) :=
          measure_mono (Set.add_subset_add_left (Set.singleton_subset_iff.2 ht))
  by_contra hlt
  push_neg at hlt
  obtain ⟨y', hy', z', hz', hlt'⟩ := ENNReal.exists_lt_add_of_lt_add hlt hS' hT'
  obtain ⟨K, hKS, hK, hyK⟩ := hS.exists_lt_isCompact hy'
  obtain ⟨L, hLT, hL, hzL⟩ := hT.exists_lt_isCompact hz'
  have hK0 : K.Nonempty := nonempty_of_measure_ne_zero ((_root_.zero_le y').trans_lt hyK).ne'
  have hL0 : L.Nonempty := nonempty_of_measure_ne_zero ((_root_.zero_le z').trans_lt hzL).ne'
  have h1 := bm1_compact K L hK hL hK0 hL0
  have h2 : volume (K + L) ≤ volume (S + T) := measure_mono (Set.add_subset_add hKS hLT)
  exact absurd (hlt'.trans_le ((add_le_add hyK.le hzL.le).trans (h1.trans h2))) (lt_irrefl _)

/-- Scaled 1D Brunn–Minkowski. -/
lemma bm1_scaled {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (S T : Set ℝ)
    (hS : MeasurableSet S) (hT : MeasurableSet T) (hS0 : S.Nonempty) (hT0 : T.Nonempty) :
    ENNReal.ofReal (1 - lam) * volume S + ENNReal.ofReal lam * volume T ≤
      volume ((1 - lam) • S + lam • T) := by
  have e : ∀ (c : ℝ), 0 < c → ∀ U : Set ℝ, volume (c • U) = ENNReal.ofReal c * volume U := by
    intro c hc U
    rw [Measure.addHaar_smul, Module.finrank_self, pow_one, abs_of_pos hc]
  rw [← e _ (by linarith) S, ← e _ h0 T]
  exact bm1_meas _ _ (hS.const_smul₀ _) (hT.const_smul₀ _) (hS0.smul_set) (hT0.smul_set)

/-- Weighted AM-GM in `ℝ≥0∞`. -/
lemma amgm {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (a b : ℝ≥0∞) :
    a ^ (1 - lam) * b ^ lam ≤ ENNReal.ofReal (1 - lam) * a + ENNReal.ofReal lam * b := by
  have h0' : 0 < 1 - lam := by linarith
  rcases eq_or_ne a ⊤ with rfl | ha
  · have : ENNReal.ofReal (1 - lam) * ⊤ = ⊤ := ENNReal.mul_top (ENNReal.ofReal_pos.2 h0').ne'
    rw [this, top_add]; exact le_top
  rcases eq_or_ne b ⊤ with rfl | hb
  · have : ENNReal.ofReal lam * ⊤ = ⊤ := ENNReal.mul_top (ENNReal.ofReal_pos.2 h0).ne'
    rw [this, add_top]; exact le_top
  lift a to ℝ≥0 using ha
  lift b to ℝ≥0 using hb
  have key := NNReal.geom_mean_le_arith_mean2_weighted (Real.toNNReal (1 - lam))
    (Real.toNNReal lam) a b (by rw [← Real.toNNReal_add h0'.le h0.le]; simp)
  rw [Real.coe_toNNReal _ h0'.le, Real.coe_toNNReal _ h0.le] at key
  rw [← ENNReal.coe_rpow_of_nonneg _ h0'.le, ← ENNReal.coe_rpow_of_nonneg _ h0.le]
  unfold ENNReal.ofReal
  exact_mod_cast key

/-- Layer cake formula for finite-valued functions into `ℝ≥0∞`. -/
lemma layercake (F : ℝ → ℝ≥0∞) (hF : Measurable F) (hFfin : ∀ x, F x ≠ ⊤) :
    ∫⁻ x, F x = ∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < F x} := by
  have key := lintegral_eq_lintegral_meas_lt volume (f := fun x => (F x).toReal)
    (Filter.Eventually.of_forall (fun x => ENNReal.toReal_nonneg))
    hF.ennreal_toReal.aemeasurable
  have hc : ∀ x, ENNReal.ofReal (F x).toReal = F x := fun x => ENNReal.ofReal_toReal (hFfin x)
  simp only [hc] at key
  rw [key]
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  simp only
  congr 1
  ext x
  simp only [mem_setOf_eq]
  rw [ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt ht) (hFfin x)]

lemma level_antitone (F : ℝ → ℝ≥0∞) :
    Measurable (fun t : ℝ => volume {x | ENNReal.ofReal t < F x}) := by
  apply Antitone.measurable
  intro t₁ t₂ ht
  apply measure_mono
  intro x hx
  exact lt_of_le_of_lt (ENNReal.ofReal_le_ofReal ht) hx

/-- Prékopa–Leindler in dimension one, when both functions have the same finite supremum. -/
lemma pl1_eq {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (F G H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) (hHfin : ∀ x, H x ≠ ⊤)
    (M : ℝ≥0∞) (hMtop : M ≠ ⊤) (hFM : ⨆ x, F x = M) (hGM : ⨆ x, G x = M)
    (hFGH : ∀ x y, F x ^ (1 - lam) * G y ^ lam ≤ H ((1 - lam) * x + lam * y)) :
    ENNReal.ofReal (1 - lam) * (∫⁻ x, F x) + ENNReal.ofReal lam * (∫⁻ x, G x) ≤ ∫⁻ x, H x := by
  have h0' : 0 < 1 - lam := by linarith
  have hFle : ∀ x, F x ≤ M := fun x => hFM ▸ le_iSup F x
  have hGle : ∀ x, G x ≤ M := fun x => hGM ▸ le_iSup G x
  have hFfin : ∀ x, F x ≠ ⊤ := fun x => ne_top_of_le_ne_top hMtop (hFle x)
  have hGfin : ∀ x, G x ≠ ⊤ := fun x => ne_top_of_le_ne_top hMtop (hGle x)
  rw [layercake F hF hFfin, layercake G hG hGfin, layercake H hH hHfin]
  set m := M.toReal with hm
  have hvan : ∀ K : ℝ → ℝ≥0∞, (∀ x, K x ≤ M) → ∀ t, m ≤ t →
      volume {x | ENNReal.ofReal t < K x} = 0 := by
    intro K hK t ht
    have : {x | ENNReal.ofReal t < K x} = ∅ := by
      ext x
      simp only [mem_setOf_eq, mem_empty_iff_false, iff_false, not_lt]
      calc K x ≤ M := hK x
        _ = ENNReal.ofReal m := (ENNReal.ofReal_toReal hMtop).symm
        _ ≤ ENNReal.ofReal t := ENNReal.ofReal_le_ofReal ht
    rw [this, measure_empty]
  have hsplit : ∀ g : ℝ → ℝ≥0∞, (∀ t, m ≤ t → g t = 0) →
      (∫⁻ t in Ioi 0, g t) ≤ ∫⁻ t in Ioo 0 m, g t := by
    intro g hg
    calc (∫⁻ t in Ioi 0, g t) ≤ ∫⁻ t in Ioo 0 m ∪ Ici m, g t := by
          apply lintegral_mono_set
          intro t ht
          by_cases htm : t < m
          · exact Or.inl ⟨ht, htm⟩
          · exact Or.inr (not_lt.1 htm)
      _ ≤ (∫⁻ t in Ioo 0 m, g t) + ∫⁻ t in Ici m, g t := lintegral_union_le _ _ _
      _ = ∫⁻ t in Ioo 0 m, g t := by
          rw [setLIntegral_eq_zero measurableSet_Ici (fun t ht => hg t ht), add_zero]
  have key : ∀ t ∈ Ioo 0 m,
      ENNReal.ofReal (1 - lam) * volume {x | ENNReal.ofReal t < F x} +
        ENNReal.ofReal lam * volume {x | ENNReal.ofReal t < G x} ≤
        volume {x | ENNReal.ofReal t < H x} := by
    intro t ht
    have htM : ENNReal.ofReal t < M := by
      rw [← ENNReal.ofReal_toReal hMtop]
      exact (ENNReal.ofReal_lt_ofReal_iff (ht.1.trans ht.2)).2 ht.2
    have hneF : {x | ENNReal.ofReal t < F x}.Nonempty := by
      have h := htM
      rw [← hFM, lt_iSup_iff] at h
      exact h
    have hneG : {x | ENNReal.ofReal t < G x}.Nonempty := by
      have h := htM
      rw [← hGM, lt_iSup_iff] at h
      exact h
    have hsub : (1 - lam) • {x | ENNReal.ofReal t < F x} + lam • {x | ENNReal.ofReal t < G x} ⊆
        {x | ENNReal.ofReal t < H x} := by
      rintro _ ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, rfl⟩
      simp only [mem_setOf_eq, smul_eq_mul] at hx hy ⊢
      calc ENNReal.ofReal t = ENNReal.ofReal t ^ (1 - lam) * ENNReal.ofReal t ^ lam := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ h0'.le h0.le]; simp
        _ < F x ^ (1 - lam) * G y ^ lam :=
            ENNReal.mul_lt_mul (ENNReal.rpow_lt_rpow hx h0') (ENNReal.rpow_lt_rpow hy h0)
        _ ≤ H ((1 - lam) * x + lam * y) := hFGH x y
    exact (bm1_scaled h0 h1 _ _ (measurableSet_lt measurable_const hF)
      (measurableSet_lt measurable_const hG) hneF hneG).trans (measure_mono hsub)
  calc ENNReal.ofReal (1 - lam) * (∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < F x}) +
        ENNReal.ofReal lam * (∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < G x})
      ≤ ENNReal.ofReal (1 - lam) * (∫⁻ t in Ioo 0 m, volume {x | ENNReal.ofReal t < F x}) +
        ENNReal.ofReal lam * (∫⁻ t in Ioo 0 m, volume {x | ENNReal.ofReal t < G x}) := by
        gcongr ?_ * ?_ + ?_ * ?_
        · exact hsplit _ (hvan F hFle)
        · exact hsplit _ (hvan G hGle)
    _ = ∫⁻ t in Ioo 0 m, (ENNReal.ofReal (1 - lam) * volume {x | ENNReal.ofReal t < F x} +
        ENNReal.ofReal lam * volume {x | ENNReal.ofReal t < G x}) := by
        rw [lintegral_add_left ((level_antitone F).const_mul _),
          lintegral_const_mul _ (level_antitone F), lintegral_const_mul _ (level_antitone G)]
    _ ≤ ∫⁻ t in Ioo 0 m, volume {x | ENNReal.ofReal t < H x} :=
        setLIntegral_mono' measurableSet_Ioo key
    _ ≤ ∫⁻ t in Ioi 0, volume {x | ENNReal.ofReal t < H x} :=
        lintegral_mono_set Ioo_subset_Ioi_self

/-- Prékopa–Leindler in dimension one (bounded version). -/
lemma pl1 {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (F G H : ℝ → ℝ≥0∞)
    (hF : Measurable F) (hG : Measurable G) (hH : Measurable H) (hHfin : ∀ x, H x ≠ ⊤)
    (MF : ℝ≥0∞) (hMF : MF ≠ ⊤) (hFM : ∀ x, F x ≤ MF)
    (MG : ℝ≥0∞) (hMG : MG ≠ ⊤) (hGM : ∀ x, G x ≤ MG)
    (hFGH : ∀ x y, F x ^ (1 - lam) * G y ^ lam ≤ H ((1 - lam) * x + lam * y)) :
    (∫⁻ x, F x) ^ (1 - lam) * (∫⁻ x, G x) ^ lam ≤ ∫⁻ x, H x := by
  have h0' : 0 < 1 - lam := by linarith
  have hα : (⨆ x, F x) ≠ ⊤ := ne_top_of_le_ne_top hMF (iSup_le hFM)
  have hβ : (⨆ x, G x) ≠ ⊤ := ne_top_of_le_ne_top hMG (iSup_le hGM)
  rcases eq_or_ne (⨆ x, F x) 0 with hα0 | hα0
  · have hF0 : ∀ x, F x = 0 := fun x => le_antisymm (hα0 ▸ le_iSup F x) (zero_le _)
    simp [hF0, ENNReal.zero_rpow_of_pos h0']
  rcases eq_or_ne (⨆ x, G x) 0 with hβ0 | hβ0
  · have hG0 : ∀ x, G x = 0 := fun x => le_antisymm (hβ0 ▸ le_iSup G x) (zero_le _)
    simp [hG0, ENNReal.zero_rpow_of_pos h0]
  set c := (⨆ x, G x) / (⨆ x, F x) with hc_def
  have hc0 : c ≠ 0 := (ENNReal.div_pos hβ0 hα).ne'
  have hctop : c ≠ ⊤ := ENNReal.div_ne_top hβ hα0
  have hcp0 : c ^ (1 - lam) ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hc0) hctop).ne'
  have hcptop : c ^ (1 - lam) ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg h0'.le hctop
  have key := pl1_eq h0 h1 (fun x => c * F x) G (fun x => c ^ (1 - lam) * H x)
    (hF.const_mul c) hG (hH.const_mul _)
    (fun x => ENNReal.mul_ne_top hcptop (hHfin x)) (⨆ x, G x) hβ
    (by rw [← ENNReal.mul_iSup]; exact ENNReal.div_mul_cancel hα0 hα) rfl
    (by
      intro x y
      simp only
      rw [ENNReal.mul_rpow_of_nonneg _ _ h0'.le, mul_assoc]
      gcongr
      exact hFGH x y)
  simp only at key
  have e1 : (∫⁻ x, c * F x) = c * ∫⁻ x, F x := lintegral_const_mul c hF
  have e2 : (∫⁻ x, c ^ (1 - lam) * H x) = c ^ (1 - lam) * ∫⁻ x, H x :=
    lintegral_const_mul _ hH
  rw [e1, e2] at key
  have h2 := (amgm h0 h1 (c * ∫⁻ x, F x) (∫⁻ x, G x)).trans key
  rw [ENNReal.mul_rpow_of_nonneg _ _ h0'.le, mul_assoc] at h2
  exact (ENNReal.mul_le_mul_iff_right hcp0 hcptop).1 h2

/-- Inductive step: Brunn–Minkowski on `X` implies Brunn–Minkowski on `ℝ × X`. -/
lemma bm_step {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) (n : ℕ)
    (hX : ∀ A B : Set (Fin n → ℝ), IsCompact A → IsCompact B →
      volume A ^ (1 - lam) * volume B ^ lam ≤ volume ((1 - lam) • A + lam • B)) :
    ∀ A B : Set (ℝ × (Fin n → ℝ)), IsCompact A → IsCompact B →
      volume A ^ (1 - lam) * volume B ^ lam ≤ volume ((1 - lam) • A + lam • B) := by
  intro A B hA hB
  have hC : IsCompact ((1 - lam) • A + lam • B) := (hA.smul _).add (hB.smul _)
  have hsec : ∀ (K : Set (ℝ × (Fin n → ℝ))), IsCompact K → ∀ s : ℝ,
      IsCompact (Prod.mk s ⁻¹' K) := by
    intro K hK s
    apply (hK.image continuous_snd).of_isClosed_subset
      (hK.isClosed.preimage (Continuous.prodMk_right s))
    intro y hy
    exact ⟨(s, y), hy, rfl⟩
  have hbound : ∀ (K : Set (ℝ × (Fin n → ℝ))), ∀ s : ℝ,
      volume (Prod.mk s ⁻¹' K) ≤ volume (Prod.snd '' K) := by
    intro K s
    apply measure_mono
    intro y hy
    exact ⟨(s, y), hy, rfl⟩
  rw [Measure.volume_eq_prod, Measure.prod_apply hA.measurableSet,
    Measure.prod_apply hB.measurableSet, Measure.prod_apply hC.measurableSet]
  refine pl1 h0 h1 _ _ _ (measurable_measure_prodMk_left hA.measurableSet)
    (measurable_measure_prodMk_left hB.measurableSet)
    (measurable_measure_prodMk_left hC.measurableSet) ?_
    (volume (Prod.snd '' A)) (hA.image continuous_snd).measure_lt_top.ne (hbound A)
    (volume (Prod.snd '' B)) (hB.image continuous_snd).measure_lt_top.ne (hbound B) ?_
  · intro t
    exact ne_top_of_le_ne_top (hC.image continuous_snd).measure_lt_top.ne (hbound _ t)
  · intro s r
    refine (hX _ _ (hsec A hA s) (hsec B hB r)).trans (measure_mono ?_)
    rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨(1 - lam) • (s, a), ⟨(s, a), ha, rfl⟩, lam • (r, b), ⟨(r, b), hb, rfl⟩, by simp⟩

/-- Transfer of Brunn–Minkowski along a measure-preserving linear homeomorphism. -/
lemma bm_transfer {lam : ℝ} {X Y : Type*} [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
    [MeasureSpace X] [AddCommGroup Y] [Module ℝ Y] [TopologicalSpace Y] [MeasureSpace Y]
    (e : X ≃ᵐ Y) (he : MeasurePreserving e volume volume) (hc : Continuous e)
    (hlin : ∀ (a b : ℝ) (x y : X), e (a • x + b • y) = a • e x + b • e y)
    (hY : ∀ A B : Set Y, IsCompact A → IsCompact B →
      volume A ^ (1 - lam) * volume B ^ lam ≤ volume ((1 - lam) • A + lam • B)) :
    ∀ A B : Set X, IsCompact A → IsCompact B →
      volume A ^ (1 - lam) * volume B ^ lam ≤ volume ((1 - lam) • A + lam • B) := by
  intro A B hA hB
  have hvol : ∀ S : Set X, volume (e '' S) = volume S := by
    intro S
    rw [← he.map_eq, MeasurableEquiv.map_apply, e.preimage_image]
  have himg : e '' ((1 - lam) • A + lam • B) = (1 - lam) • (e '' A) + lam • (e '' B) := by
    ext z
    constructor
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨e a, ⟨a, ha, rfl⟩, rfl⟩, _, ⟨e b, ⟨b, hb, rfl⟩, rfl⟩, (hlin _ _ a b).symm⟩
    · rintro ⟨_, ⟨_, ⟨a, ha, rfl⟩, rfl⟩, _, ⟨_, ⟨b, hb, rfl⟩, rfl⟩, rfl⟩
      exact ⟨_, ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩, hlin _ _ a b⟩
  have := hY (e '' A) (e '' B) (hA.image hc) (hB.image hc)
  rwa [← himg, hvol, hvol, hvol] at this

/-- Brunn–Minkowski (multiplicative) on `Fin n → ℝ`. -/
lemma bm_pi {lam : ℝ} (h0 : 0 < lam) (h1 : lam < 1) : ∀ n : ℕ,
    ∀ A B : Set (Fin n → ℝ), IsCompact A → IsCompact B →
      volume A ^ (1 - lam) * volume B ^ lam ≤ volume ((1 - lam) • A + lam • B) := by
  have h0' : 0 < 1 - lam := by linarith
  intro n
  induction n with
  | zero =>
    intro A B hA hB
    rcases A.eq_empty_or_nonempty with rfl | hA0
    · simp [ENNReal.zero_rpow_of_pos h0']
    rcases B.eq_empty_or_nonempty with rfl | hB0
    · simp [ENNReal.zero_rpow_of_pos h0]
    have hC0 : ((1 - lam) • A + lam • B).Nonempty := hA0.smul_set.add hB0.smul_set
    have hu : volume (Set.univ : Set (Fin 0 → ℝ)) = 1 := by
      simp [volume_pi]
    rw [hC0.eq_univ, hu]
    calc volume A ^ (1 - lam) * volume B ^ lam ≤ 1 ^ (1 - lam) * 1 ^ lam := by
          gcongr
          · exact hu ▸ measure_mono (Set.subset_univ A)
          · exact hu ▸ measure_mono (Set.subset_univ B)
      _ = 1 := by simp
  | succ n ih =>
    apply bm_transfer (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
    · exact measurePreserving_piFinSuccAbove (fun _ => volume) 0
    · exact (continuous_apply 0).prodMk (continuous_pi fun j => continuous_apply _)
    · intro a b x y
      rfl
    · exact bm_step h0 h1 n ih

end BMAux

set_option linter.unusedVariables false in
theorem brunn_minkowski_multiplicative {n : ℕ}
  (hn : 0 < n)
  {lam : ℝ} (hlam_pos : 0 < lam) (hlam_lt : lam < 1)
  (A B : Set (EuclideanSpace ℝ (Fin n)))
  (hA_compact : IsCompact A) (hB_compact : IsCompact B) :
  volume ((1 - lam) • A + lam • B) ≥
    (volume A) ^ (1 - lam) * (volume B) ^ lam := by
  apply BMAux.bm_transfer (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  · exact EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  · exact PiLp.continuous_ofLp 2 _
  · intro a b x y
    rfl
  · exact BMAux.bm_pi hlam_pos hlam_lt n
  · exact hA_compact
  · exact hB_compact

end brunn_minkowski_multiplicative
