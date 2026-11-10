import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_1_9`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_1_9` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_1_9`, so the main result is `FCA_chap_B_1_1_9.FCA_chap_B_1_1_9`.
-/

namespace FCA_chap_B_1_1_9

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_1_1_9
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  intrinsicInterior ℝ (epigraph f) =
  {p : E × ℝ |
  p.1 ∈ intrinsicInterior ℝ (effDom f) ∧ p.2 > f p.1} := by
  have FCA_aux_mem_intrinsicInterior_iff : ∀ {P : Type u_1} [NormedAddCommGroup P]
      [NormedSpace ℝ P] (s : Set P) (p : P), p ∈ intrinsicInterior ℝ s ↔
        p ∈ affineSpan ℝ s ∧ ∃ u ∈ 𝓝 p, ∀ z ∈ affineSpan ℝ s, z ∈ u → z ∈ s := by
    intro P _ _ s p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨q.2, ?_⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hq
      obtain ⟨u, hu, hus⟩ := hq
      exact ⟨u, hu, fun z hz hzu =>
        hus (show (⟨z, hz⟩ : affineSpan ℝ s) ∈ Subtype.val ⁻¹' u from hzu)⟩
    · rintro ⟨hp, u, hu, hus⟩
      refine ⟨⟨p, hp⟩, ?_, rfl⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
      exact ⟨u, hu, fun z hz => hus z.1 z.2 hz⟩
  have hCconv : Convex ℝ (epigraph f) := hf_convex.2.2
  have hreal : ∀ x, f x < ⊤ → ((f x).toReal : EReal) = f x := fun x hx =>
    EReal.coe_toReal hx.ne (f_ne_bot x).ne'
  -- membership in the affine span of the epigraph forces membership of the first coordinate
  have hSC_fst : ∀ p ∈ affineSpan ℝ (epigraph f), p.1 ∈ affineSpan ℝ (effDom f) := by
    intro p hp
    have hle : affineSpan ℝ (epigraph f) ≤
        (affineSpan ℝ (effDom f)).comap (AffineMap.fst : E × ℝ →ᵃ[ℝ] E) := by
      rw [affineSpan_le]
      intro q hq
      rw [SetLike.mem_coe, AffineSubspace.mem_comap, AffineMap.coe_fst]
      exact subset_affineSpan ℝ _ (lt_of_le_of_lt hq (EReal.coe_lt_top _))
    exact AffineSubspace.mem_comap.mp (hle hp)
  -- vertical lines over the domain lie in the affine span of the epigraph
  have hSC_mk : ∀ y ∈ affineSpan ℝ (effDom f), ∀ s : ℝ, (y, s) ∈ affineSpan ℝ (epigraph f) := by
    intro y hy s
    let ι : E →ᵃ[ℝ] E × ℝ :=
      { toFun := fun y => (y, s)
        linear := LinearMap.inl ℝ E ℝ
        map_vadd' := fun p v => by
          simp [vadd_eq_add] }
    have hle : affineSpan ℝ (effDom f) ≤ (affineSpan ℝ (epigraph f)).comap ι := by
      rw [affineSpan_le]
      intro z hz
      rw [SetLike.mem_coe, AffineSubspace.mem_comap]
      show (z, s) ∈ affineSpan ℝ (epigraph f)
      set t := (f z).toReal with ht
      have h0 : (z, t) ∈ affineSpan ℝ (epigraph f) := by
        apply subset_affineSpan
        show f z ≤ (t : EReal)
        rw [ht, hreal z hz]
      have h1 : (z, t + 1) ∈ affineSpan ℝ (epigraph f) := by
        apply subset_affineSpan
        show f z ≤ ((t + 1 : ℝ) : EReal)
        rw [← hreal z hz, EReal.coe_le_coe_iff]
        linarith
      have := AffineMap.lineMap_mem (s - t) h0 h1
      convert this using 1
      rw [AffineMap.lineMap_apply]
      ext
      · simp
      · simp
    exact AffineSubspace.mem_comap.mp (hle hy)

  -- convexity of the domain
  have hDconv : Convex ℝ (effDom f) := by
    intro y₁ hy₁ y₂ hy₂ a b ha hb hab
    have h₁ : (y₁, (f y₁).toReal) ∈ epigraph f := by
      show f y₁ ≤ ((f y₁).toReal : EReal)
      rw [hreal y₁ hy₁]
    have h₂ : (y₂, (f y₂).toReal) ∈ epigraph f := by
      show f y₂ ≤ ((f y₂).toReal : EReal)
      rw [hreal y₂ hy₂]
    have := hCconv h₁ h₂ ha hb hab
    show f (a • y₁ + b • y₂) < ⊤
    exact lt_of_le_of_lt this (EReal.coe_lt_top _)
  -- relative upper semicontinuity at points of the intrinsic interior of the domain
  have key : ∀ x ∈ intrinsicInterior ℝ (effDom f), ∀ r' : ℝ, f x < r' →
      ∃ ε > 0, ∀ y ∈ affineSpan ℝ (effDom f), dist y x < ε → f y < r' := by
    intro x hx r' hr'
    rw [FCA_aux_mem_intrinsicInterior_iff] at hx
    obtain ⟨hxS, u, hu, hus⟩ := hx
    set V := (affineSpan ℝ (effDom f)).direction with hV
    let ψ : V → E := fun v => (v : E) + x
    have hψc : Continuous ψ := by fun_prop
    have hψS : ∀ v : V, ψ v ∈ affineSpan ℝ (effDom f) := fun v =>
      AffineSubspace.vadd_mem_of_mem_direction v.2 hxS
    let D' : Set V := ψ ⁻¹' (effDom f)
    let g : V → ℝ := fun v => (f (ψ v)).toReal
    have hψaff : ∀ (v w : V) (a b : ℝ), a + b = 1 → ψ (a • v + b • w) = a • ψ v + b • ψ w := by
      intro v w a b hab
      simp only [ψ, Submodule.coe_add, Submodule.coe_smul]
      calc a • (v : E) + b • (w : E) + x = a • (v : E) + b • (w : E) + (a + b) • x := by
            rw [hab, one_smul]
        _ = a • ((v : E) + x) + b • ((w : E) + x) := by
            rw [add_smul, smul_add, smul_add]; abel
    have hg : ConvexOn ℝ D' g := by
      refine ⟨?_, ?_⟩
      · intro v hv w hw a b ha hb hab
        show ψ (a • v + b • w) ∈ effDom f
        rw [hψaff v w a b hab]
        exact hDconv hv hw ha hb hab
      · intro v hv w hw a b ha hb hab
        have h₁ : (ψ v, g v) ∈ epigraph f := by
          show f (ψ v) ≤ ((f (ψ v)).toReal : EReal)
          rw [hreal _ hv]
        have h₂ : (ψ w, g w) ∈ epigraph f := by
          show f (ψ w) ≤ ((f (ψ w)).toReal : EReal)
          rw [hreal _ hw]
        have := hCconv h₁ h₂ ha hb hab
        have hm : ψ (a • v + b • w) ∈ effDom f := by
          rw [hψaff v w a b hab]
          exact hDconv hv hw ha hb hab
        show (f (ψ (a • v + b • w))).toReal ≤ a • g v + b • g w
        rw [← EReal.coe_le_coe_iff, hreal _ hm, hψaff v w a b hab]
        exact this
    have h0 : (0 : V) ∈ interior D' := by
      rw [mem_interior_iff_mem_nhds]
      have : ψ ⁻¹' u ∈ 𝓝 (0 : V) := by
        apply hψc.continuousAt.preimage_mem_nhds
        simpa [ψ] using hu
      filter_upwards [this] with v hv
      exact hus _ (hψS v) hv
    have hcont : ContinuousAt g 0 :=
      hg.continuousOn_interior.continuousAt (isOpen_interior.mem_nhds h0)
    have hg0 : g 0 < r' := by
      have hx0 : ψ 0 = x := by simp [ψ]
      have hxD : x ∈ effDom f := lt_of_lt_of_le hr' le_top
      show (f (ψ 0)).toReal < r'
      rw [hx0, ← EReal.coe_lt_coe_iff, hreal _ hxD]
      exact hr'
    have hW : {v | g v < r'} ∩ D' ∈ 𝓝 (0 : V) :=
      Filter.inter_mem (hcont (Iio_mem_nhds hg0)) (mem_interior_iff_mem_nhds.mp h0)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hW
    refine ⟨ε, hε, fun y hy hyx => ?_⟩
    have hv : y - x ∈ V := AffineSubspace.vsub_mem_direction hy hxS
    have hmem := hball (show (⟨y - x, hv⟩ : V) ∈ Metric.ball 0 ε by
      rw [Metric.mem_ball, _root_.dist_zero_right]
      show ‖y - x‖ < ε
      rw [← dist_eq_norm]
      exact hyx)
    have hψy : ψ ⟨y - x, hv⟩ = y := by simp [ψ]
    obtain ⟨hlt, hD⟩ := hmem
    simp only [Set.mem_setOf_eq, g] at hlt
    simp only [D', Set.mem_preimage] at hD
    rw [hψy] at hlt hD
    rw [← hreal y hD, EReal.coe_lt_coe_iff]
    exact hlt

  ext ⟨x, r⟩
  simp only [Set.mem_setOf_eq]
  rw [FCA_aux_mem_intrinsicInterior_iff]
  constructor
  · rintro ⟨hpS, u, hu, hus⟩
    have hpC : (x, r) ∈ epigraph f := hus _ hpS (mem_of_mem_nhds hu)
    have hxD : x ∈ effDom f := lt_of_le_of_lt hpC (EReal.coe_lt_top r)
    have hxS : x ∈ affineSpan ℝ (effDom f) := subset_affineSpan ℝ _ hxD
    refine ⟨?_, ?_⟩
    · rw [FCA_aux_mem_intrinsicInterior_iff]
      refine ⟨hxS, {y | (y, r) ∈ u}, ?_, ?_⟩
      · have hc : Continuous (fun y : E => (y, r)) := by fun_prop
        exact hc.continuousAt.preimage_mem_nhds hu
      · intro y hy hyu
        have := hus (y, r) (hSC_mk y hy r) hyu
        exact lt_of_le_of_lt this (EReal.coe_lt_top r)
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hu
      have hmem : (x, r - ε / 2) ∈ u := by
        apply hball
        rw [Metric.mem_ball, Prod.dist_eq]
        show max (dist x x) (dist (r - ε / 2) r) < ε
        rw [_root_.dist_self, Real.dist_eq,
          show r - ε / 2 - r = -(ε / 2) by ring, abs_neg, abs_of_pos (by linarith)]
        exact max_lt hε (by linarith)
      have := hus _ (hSC_mk x hxS _) hmem
      show f x < (r : EReal)
      calc f x ≤ ((r - ε / 2 : ℝ) : EReal) := this
        _ < (r : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  · rintro ⟨hx, hfx⟩
    have hxD : x ∈ effDom f := intrinsicInterior_subset hx
    have hxS : x ∈ affineSpan ℝ (effDom f) := subset_affineSpan ℝ _ hxD
    set a := (f x).toReal with ha
    have hfa : f x = a := (hreal x hxD).symm
    have har : a < r := by
      have h : f x < (r : EReal) := hfx
      rw [hfa] at h
      exact EReal.coe_lt_coe_iff.mp h
    obtain ⟨ε, hε, hεf⟩ := key x hx ((a + r) / 2)
      (by rw [hfa]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
    refine ⟨hSC_mk x hxS r, Metric.ball (x, r) (min ε ((r - a) / 2)),
      Metric.ball_mem_nhds _ (lt_min hε (by linarith)), ?_⟩
    rintro ⟨y, s⟩ hz hzb
    have hy : y ∈ affineSpan ℝ (effDom f) := hSC_fst _ hz
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff, lt_min_iff, lt_min_iff] at hzb
    obtain ⟨⟨hyx, -⟩, -, hsr⟩ := hzb
    have h1 := hεf y hy hyx
    rw [Real.dist_eq, abs_lt] at hsr
    show f y ≤ (s : EReal)
    exact (h1.trans (EReal.coe_lt_coe_iff.mpr (by linarith))).le

end FCA_chap_B_1_1_9
