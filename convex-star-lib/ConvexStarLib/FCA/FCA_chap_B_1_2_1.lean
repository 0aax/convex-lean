import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_2_1`, so the main result is `FCA_chap_B_1_2_1.FCA_chap_B_1_2_1`.
-/

namespace FCA_chap_B_1_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_1_2_1
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ (x₀ : E), (x₀ ∈ intrinsicInterior ℝ (effDom f)) →
  ∃ (s : E), ∀ (x : E),
  (s ∈ parallelSubspace (affineHull (effDom f))) ∧
  (f x ≥ f x₀ + inner ℝ s (x - x₀)) := by
  intro x₀ hx₀
  set D := effDom f with hD_def
  set A := affineSpan ℝ D with hA_def
  set V := A.direction with hV_def
  have hepi : Convex ℝ (epigraph f) := hf_convex.2.2
  have hx₀D : x₀ ∈ D := intrinsicInterior_subset hx₀
  have hx₀A : x₀ ∈ A := subset_affineSpan ℝ D hx₀D
  -- Step 1: a ball around x₀ inside the affine span lies in D
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, ∀ y ∈ A, dist y x₀ < r → y ∈ D := by
    rw [mem_intrinsicInterior] at hx₀
    obtain ⟨y, hy, hyx⟩ := hx₀
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hy
    obtain ⟨ε, hε, hεsub⟩ := hy
    refine ⟨ε, hε, fun z hz hdist => ?_⟩
    have : (⟨z, hz⟩ : A) ∈ Metric.ball y ε := by
      rw [Metric.mem_ball, Subtype.dist_eq, hyx]
      exact hdist
    exact hεsub this
  have hfin : ∀ y, y ∈ D → (((f y).toReal : ℝ) : EReal) = f y := by
    intro y hy
    exact EReal.coe_toReal (ne_of_lt hy) (ne_of_gt (f_ne_bot y))
  -- Step 2: restricted function
  set g : V → ℝ := fun v => (f (x₀ + (v : E))).toReal with hg_def
  set B : Set V := Metric.ball (0 : V) r with hB_def
  have hmemA : ∀ v : V, x₀ + (v : E) ∈ A := by
    intro v
    have := AffineSubspace.vadd_mem_of_mem_direction v.2 hx₀A
    rw [vadd_eq_add, add_comm] at this
    exact this
  have hBD : ∀ v ∈ B, x₀ + (v : E) ∈ D := by
    intro v hv
    apply hball _ (hmemA v)
    rw [dist_eq_norm, add_sub_cancel_left]
    rw [hB_def, Metric.mem_ball, _root_.dist_zero_right] at hv
    simpa using hv
  have hgB : ∀ v ∈ B, ((g v : ℝ) : EReal) = f (x₀ + (v : E)) := fun v hv => hfin _ (hBD v hv)
  -- Step 3: g convex on B
  have hgconv : ConvexOn ℝ B g := by
    refine ⟨convex_ball _ _, ?_⟩
    intro u hu w hw a b ha hb hab
    have h1 : ((x₀ + (u : E)), g u) ∈ epigraph f := by
      show f (x₀ + (u : E)) ≤ ((g u : ℝ) : EReal)
      rw [hgB u hu]
    have h2 : ((x₀ + (w : E)), g w) ∈ epigraph f := by
      show f (x₀ + (w : E)) ≤ ((g w : ℝ) : EReal)
      rw [hgB w hw]
    have h3 := hepi h1 h2 ha hb hab
    have hmem : a • u + b • w ∈ B := convex_ball _ _ hu hw ha hb hab
    have key : f (x₀ + ((a • u + b • w : V) : E)) ≤ ((a * g u + b * g w : ℝ) : EReal) := by
      have hx : x₀ = (a + b) • x₀ := by rw [hab, one_smul]
      have : a • (x₀ + (u : E), g u) + b • (x₀ + (w : E), g w)
          = (x₀ + ((a • u + b • w : V) : E), a * g u + b * g w) := by
        ext
        · simp only [Prod.fst_add, Prod.smul_fst, Submodule.coe_add, Submodule.coe_smul]
          conv_rhs => rw [hx]
          module
        · simp
      rw [this] at h3
      exact h3
    rw [← hgB _ hmem] at key
    exact_mod_cast key
  have hgcont : ContinuousOn g B := hgconv.continuousOn Metric.isOpen_ball
  -- Step 5: open convex set
  set O : Set (V × ℝ) := {p | p.1 ∈ B ∧ g p.1 < p.2} with hO_def
  have hOconv : Convex ℝ O := hgconv.convex_strict_epigraph
  have hOopen : IsOpen O := by
    have h1 : IsOpen (Prod.fst ⁻¹' B : Set (V × ℝ)) := Metric.isOpen_ball.preimage continuous_fst
    have h2 : ContinuousOn (fun p : V × ℝ => p.2 - g p.1) (Prod.fst ⁻¹' B) := by
      apply ContinuousOn.sub continuous_snd.continuousOn
      exact hgcont.comp continuous_fst.continuousOn (fun p hp => hp)
    have := h2.isOpen_inter_preimage h1 (isOpen_Ioi (a := (0:ℝ)))
    convert this using 1
    ext p
    simp [O, sub_pos]
  have hp₀ : ((0 : V), g 0) ∉ O := by
    intro h
    exact lt_irrefl _ h.2
  obtain ⟨Φ, hΦ⟩ := geometric_hahn_banach_open_point hOconv hOopen hp₀
  set c : ℝ := Φ ((0 : V), (1 : ℝ)) with hc_def
  set ℓ : V →L[ℝ] ℝ := Φ.comp (ContinuousLinearMap.inl ℝ V ℝ) with hℓ_def
  have hΦapply : ∀ v : V, ∀ t : ℝ, Φ (v, t) = ℓ v + t * c := by
    intro v t
    have : (v, t) = (v, (0:ℝ)) + t • ((0 : V), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have h0B : (0 : V) ∈ B := Metric.mem_ball_self hr
  have hc : c < 0 := by
    have h := hΦ ((0 : V), g 0 + 1) ⟨h0B, by linarith⟩
    rw [hΦapply, hΦapply] at h
    linarith
  have hc0 : c ≠ 0 := ne_of_lt hc
  have hsub : ∀ v ∈ B, g 0 + (-c)⁻¹ * ℓ v ≤ g v := by
    intro v hv
    have key : ℓ v + g v * c ≤ ℓ 0 + g 0 * c := by
      by_contra hlt
      push_neg at hlt
      set δ := ℓ v + g v * c - (ℓ 0 + g 0 * c) with hδ
      have hδpos : 0 < δ := by linarith
      have hq : 0 < δ / (-c) := div_pos hδpos (by linarith)
      have h := hΦ (v, g v + δ / (-c)) ⟨hv, by linarith⟩
      rw [hΦapply, hΦapply] at h
      have : (g v + δ / (-c)) * c = g v * c - δ := by
        field_simp
        ring
      linarith
    rw [map_zero] at key
    have hnc : 0 < -c := by linarith
    rw [← sub_nonneg]
    have : g v - (g 0 + (-c)⁻¹ * ℓ v) = (-c)⁻¹ * (g 0 * c - ℓ v - g v * c) := by
      field_simp
      ring
    rw [this]
    apply mul_nonneg (inv_nonneg.mpr hnc.le)
    linarith
  set L : V →L[ℝ] ℝ := (-c)⁻¹ • ℓ with hL_def
  set s₀ : V := (InnerProductSpace.toDual ℝ V).symm L with hs₀_def
  have hs₀ : ∀ v : V, inner ℝ (s₀ : E) (v : E) = (-c)⁻¹ * ℓ v := by
    intro v
    rw [← Submodule.coe_inner, hs₀_def, InnerProductSpace.toDual_symm_apply]
    simp [hL_def]
  refine ⟨(s₀ : E), fun x => ⟨?_, ?_⟩⟩
  · -- s₀ ∈ parallelSubspace (affineHull D)
    have hsV : (s₀ : E) ∈ V := s₀.2
    set ε : ℝ := r / (‖(s₀ : E)‖ + 1) with hε_def
    have hεpos : 0 < ε := div_pos hr (by positivity)
    have hx₁A : x₀ + ε • (s₀ : E) ∈ A := by
      have := AffineSubspace.vadd_mem_of_mem_direction (V.smul_mem ε hsV) hx₀A
      rw [vadd_eq_add, add_comm] at this
      exact this
    have hx₁D : x₀ + ε • (s₀ : E) ∈ D := by
      apply hball _ hx₁A
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hεpos]
      rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      rw [mul_add, mul_one]
      linarith
    refine ⟨x₀ + (s₀ : E), x₀, ?_, ?_, by abel⟩
    · simp only [affineHull, Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨2, by norm_num, ![x₀, x₀ + ε • (s₀ : E)], ?_, ![1 - 1/ε, 1/ε], ?_, ?_⟩
      · intro i; fin_cases i <;> simp [hx₀D, hx₁D]
      · simp [Fin.sum_univ_two]
      · simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
        rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hεpos.ne', one_smul, sub_smul, one_smul]
        abel
    · simp only [affineHull, Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨1, by norm_num, fun _ => x₀, fun _ => hx₀D, fun _ => 1, by simp, by simp⟩
  · -- the subgradient inequality
    by_cases hxD : x ∈ D
    · have hxA : x ∈ A := subset_affineSpan ℝ D hxD
      have hwV : x - x₀ ∈ V := by
        have := AffineSubspace.vsub_mem_direction hxA hx₀A
        simpa [vsub_eq_sub] using this
      set w : V := ⟨x - x₀, hwV⟩ with hw_def
      set y : ℝ := (f x).toReal with hy_def
      have hfx : (y : EReal) = f x := hfin x hxD
      have hfx₀ : ((g 0 : ℝ) : EReal) = f x₀ := by
        rw [hgB 0 h0B]; simp
      set t : ℝ := r / (r + ‖w‖) with ht_def
      have htpos : 0 < t := div_pos hr (by positivity)
      have htle : t ≤ 1 := by
        rw [ht_def, div_le_one (by positivity)]
        linarith [norm_nonneg w]
      have htB : t • w ∈ B := by
        rw [hB_def, Metric.mem_ball, _root_.dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos htpos]
        rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        have := mul_pos hr hr
        rw [mul_add]
        linarith
      have hlow := hsub (t • w) htB
      have hup : g (t • w) ≤ (1 - t) * g 0 + t * y := by
        have h1 : (x₀, g 0) ∈ epigraph f := by
          show f x₀ ≤ ((g 0 : ℝ) : EReal)
          rw [hfx₀]
        have h2 : (x, y) ∈ epigraph f := by
          show f x ≤ (y : EReal)
          rw [hfx]
        have h3 := hepi h1 h2 (by linarith : (0:ℝ) ≤ 1 - t) htpos.le (by ring)
        have : (1 - t) • (x₀, g 0) + t • (x, y)
            = (x₀ + ((t • w : V) : E), (1 - t) * g 0 + t * y) := by
          ext
          · simp only [Prod.fst_add, Prod.smul_fst, Submodule.coe_smul, hw_def]
            module
          · simp
        rw [this] at h3
        change f (x₀ + ((t • w : V) : E)) ≤ (((1 - t) * g 0 + t * y : ℝ) : EReal) at h3
        rw [← hgB _ htB] at h3
        exact_mod_cast h3
      have hLw : (-c)⁻¹ * ℓ (t • w) = t * ((-c)⁻¹ * ℓ w) := by
        rw [map_smul, smul_eq_mul]; ring
      have hineq : g 0 + (-c)⁻¹ * ℓ w ≤ y := by
        rw [hLw] at hlow
        have : t * (g 0 + (-c)⁻¹ * ℓ w) ≤ t * y := by linarith
        exact le_of_mul_le_mul_left this htpos
      rw [ge_iff_le, ← hfx, ← hfx₀]
      have : inner ℝ (s₀ : E) (x - x₀) = (-c)⁻¹ * ℓ w := by
        rw [← hs₀ w]
      rw [this]
      exact_mod_cast hineq
    · have : f x = ⊤ := by
        simp only [hD_def, effDom, Set.mem_setOf_eq, not_lt, top_le_iff] at hxD
        exact hxD
      rw [this]
      exact le_top

end FCA_chap_B_1_2_1
