import ConvexStarLib.Defs

/-!
# `BC_chap_16_17`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_16_17` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_16_17`, so the main result is `BC_chap_16_17.BC_chap_16_17`.
-/

namespace BC_chap_16_17

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

set_option linter.unusedVariables false in
theorem BC_chap_16_17
  (f : E → EReal)
  (x : E)
  (hx : x ∈ effDom f)
  (hf_proper : IsProper f)
  (hf_convex : ConvexEReal f) :
  ((Set.Nonempty (interior (effDom f))) →
    (x ∈ frontier (effDom f)) →
      (convexSubdifferential f x = ∅) ∨ ¬(Bornology.IsBounded (convexSubdifferential f x))) ∧
  ((x ∈ cont f) →
    ((Set.Nonempty (convexSubdifferential f x)) ∧
    (IsCompact (Set.image (toWeakSpace ℝ E) (convexSubdifferential f x))))) ∧
  ((x ∈ cont f) →
    (∃ (ρ : ℝ),
      (0 < ρ) ∧
      (Bornology.IsBounded (⋃ v ∈ Metric.ball x ρ, convexSubdifferential f v)))) ∧
  ((Set.Nonempty (cont f)) →
    intrinsicInterior ℝ (effDom f) ⊆ opDom (convexSubdifferential f)) := by
  have BC1617_effDom_convex {f : E → EReal} (hf_convex : ConvexEReal f) :
      Convex ℝ (effDom f) := by
    have h : effDom f = (LinearMap.fst ℝ E ℝ) '' epigraph f := by
      ext y
      constructor
      · intro hy
        exact ⟨(y, (f y).toReal), EReal.le_coe_toReal (ne_of_lt hy), rfl⟩
      · rintro ⟨⟨y', r⟩, hr, rfl⟩
        exact lt_of_le_of_lt hr (EReal.coe_lt_top r)
    rw [h]
    exact hf_convex.linear_image (LinearMap.fst ℝ E ℝ)
  have BC1617_subdiff_nonempty {f : E → EReal} (hf_proper : IsProper f)
      (hf_convex : ConvexEReal f)
      {x : E} (hx : x ∈ interior (effDom f)) (hepi : (interior (epigraph f)).Nonempty) :
      (convexSubdifferential f x).Nonempty := by
    have hxdom : x ∈ effDom f := interior_subset hx
    have hxbot : ⊥ < f x := hf_proper.1 x
    set a := (f x).toReal with ha_def
    have ha : f x = (a : EReal) := (EReal.coe_toReal hxdom.ne hxbot.ne').symm
    have hp : ((x, a) : E × ℝ) ∉ interior (epigraph f) := by
      intro hp
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hp
      obtain ⟨ε, hε, hball⟩ := hp
      have hmem : ((x, a - ε/2) : E × ℝ) ∈ Metric.ball (x, a) ε := by
        rw [Metric.mem_ball, Prod.dist_eq]
        simp only [_root_.dist_self, Real.dist_eq]
        rw [show a - ε / 2 - a = -(ε/2) by ring, abs_neg, abs_of_pos (by positivity)]
        rw [max_lt_iff]
        constructor <;> linarith
      have h2 := hball hmem
      simp only [epigraph, Set.mem_setOf_eq] at h2
      rw [ha] at h2
      have := EReal.coe_le_coe_iff.mp h2
      linarith
    obtain ⟨Lf, hLf⟩ := geometric_hahn_banach_open_point (Convex.interior hf_convex) isOpen_interior hp
    have hle : ∀ q ∈ epigraph f, Lf q ≤ Lf (x, a) := by
      have hsub : closure (interior (epigraph f)) ⊆ {q | Lf q ≤ Lf (x, a)} :=
        closure_minimal (fun q hq => (hLf q hq).le) (isClosed_le Lf.continuous continuous_const)
      rw [Convex.closure_interior_eq_closure_of_nonempty_interior hf_convex hepi] at hsub
      exact fun q hq => hsub (subset_closure hq)
    set c := Lf (0, 1) with hc_def
    set ψ := Lf.comp (ContinuousLinearMap.inl ℝ E ℝ) with hψ_def
    have hdecomp : ∀ y t, Lf (y, t) = ψ y + t * c := by
      intro y t
      have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by simp
      rw [this, map_add, map_smul]
      simp [ψ, c, smul_eq_mul]
    obtain ⟨⟨y0, t0⟩, hq0⟩ := hepi
    have hq0' := hLf _ hq0
    have hq0epi : f y0 ≤ (t0 : EReal) := (interior_subset hq0 : (y0, t0) ∈ epigraph f)
    rw [hdecomp, hdecomp] at hq0'
    have hc_le : c ≤ 0 := by
      by_contra hcpos
      push_neg at hcpos
      set D := ψ x + a * c - (ψ y0 + t0 * c) with hD_def
      have hD : 0 < D := by rw [hD_def]; linarith
      have hmem : ((y0, t0 + (D / c + 1)) : E × ℝ) ∈ epigraph f := by
        show f y0 ≤ ((t0 + (D / c + 1) : ℝ) : EReal)
        refine hq0epi.trans (EReal.coe_le_coe_iff.mpr ?_)
        have : 0 ≤ D / c + 1 := by positivity
        linarith
      have := hle _ hmem
      rw [hdecomp, hdecomp] at this
      have h3 : (t0 + (D / c + 1)) * c = t0 * c + D + c := by field_simp; ring
      rw [h3, hD_def] at this
      linarith
    have hc_ne : c ≠ 0 := by
      intro hc0
      have hdomle : ∀ y ∈ effDom f, ψ y ≤ ψ x := by
        intro y hy
        have hyb : ⊥ < f y := hf_proper.1 y
        have hmem : ((y, (f y).toReal) : E × ℝ) ∈ epigraph f := by
          show f y ≤ ((f y).toReal : EReal)
          rw [EReal.coe_toReal (ne_of_lt hy) hyb.ne']
        have := hle _ hmem
        rw [hdecomp, hdecomp, hc0] at this
        simpa using this
      rw [hc0] at hq0'
      simp only [mul_zero, add_zero] at hq0'
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior x hx
      set d := x - y0 with hd_def
      have hd : ψ d = ψ x - ψ y0 := by simp [d]
      have hdpos : 0 < ψ d := by rw [hd]; linarith
      have hd0 : d ≠ 0 := by intro h; rw [h, map_zero] at hdpos; exact lt_irrefl _ hdpos
      have hdn : 0 < ‖d‖ := norm_pos_iff.mpr hd0
      set y1 := x + (ε / (2 * ‖d‖)) • d with hy1_def
      have hy1 : y1 ∈ Metric.ball x ε := by
        rw [Metric.mem_ball, dist_eq_norm]
        simp only [y1, add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
        rw [abs_of_pos (by positivity)]
        field_simp
        linarith
      have := hdomle y1 (interior_subset (hball hy1))
      simp only [y1, map_add, map_smul, smul_eq_mul] at this
      have : 0 < ε / (2 * ‖d‖) * ψ d := by positivity
      linarith
    have hc_neg : c < 0 := lt_of_le_of_ne hc_le hc_ne
    set ℓ : E →L[ℝ] ℝ := (-c)⁻¹ • ψ with hℓ_def
    refine ⟨(InnerProductSpace.toDual ℝ E).symm ℓ, ?_⟩
    intro y
    rw [InnerProductSpace.toDual_symm_apply]
    by_cases hy : f y = ⊤
    · rw [hy]; exact le_top
    · have hyb : ⊥ < f y := hf_proper.1 y
      set b := (f y).toReal with hb_def
      have hb : f y = (b : EReal) := (EReal.coe_toReal hy hyb.ne').symm
      have hmem : ((y, b) : E × ℝ) ∈ epigraph f := by
        show f y ≤ (b : EReal)
        rw [hb]
      have := hle _ hmem
      rw [hdecomp, hdecomp] at this
      rw [hb, ha, ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff]
      simp only [ℓ, ContinuousLinearMap.smul_apply, map_sub, smul_eq_mul]
      have hnc : 0 < -c := by linarith
      have key : 0 ≤ (-c)⁻¹ * ((ψ x + a * c) - (ψ y + b * c)) :=
        mul_nonneg (inv_nonneg.mpr hnc.le) (by linarith)
      have expand : (-c)⁻¹ * ((ψ x + a * c) - (ψ y + b * c))
          = b - (a + ((-c)⁻¹ * ψ y - (-c)⁻¹ * ψ x)) := by
        field_simp
        ring
      linarith
  have BC1617_cont_aux {f : E → EReal} {x : E} (hx : x ∈ cont f) :
      x ∈ interior (effDom f) ∧ (interior (epigraph f)).Nonempty := by
    obtain ⟨hxtop, hxbot, hxcont⟩ := hx
    set a := (f x).toReal with ha_def
    have ha : f x = (a : EReal) := (EReal.coe_toReal hxtop hxbot).symm
    have hnhds : Set.Iio ((a + 1 : ℝ) : EReal) ∈ 𝓝 (f x) :=
      Iio_mem_nhds (by rw [ha]; exact EReal.coe_lt_coe_iff.mpr (by linarith))
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hxcont hnhds)
    have hball_dom : Metric.ball x δ ⊆ effDom f :=
      fun y hy => lt_trans (hball hy) (EReal.coe_lt_top _)
    refine ⟨mem_interior.mpr ⟨_, hball_dom, Metric.isOpen_ball, Metric.mem_ball_self hδ⟩, ?_⟩
    refine ⟨(x, a + 2), mem_interior.mpr
      ⟨Metric.ball x δ ×ˢ Set.Ioi (a + 1), ?_, Metric.isOpen_ball.prod isOpen_Ioi, ?_⟩⟩
    · rintro ⟨y, t⟩ ⟨hy, ht⟩
      show f y ≤ (t : EReal)
      exact (hball hy).le.trans (EReal.coe_le_coe_iff.mpr (le_of_lt ht))
    · refine ⟨Metric.mem_ball_self hδ, ?_⟩
      show a + 1 < a + 2
      linarith
  have BC1617_local_bound {f : E → EReal} {x : E} (hx : x ∈ cont f) :
      ∃ ρ > 0, ∃ R, ∀ v ∈ Metric.ball x ρ, ∀ u ∈ convexSubdifferential f v, ‖u‖ ≤ R := by
    obtain ⟨hxtop, hxbot, hcont⟩ := hx
    set a := (f x).toReal with ha_def
    have ha : f x = (a : EReal) := (EReal.coe_toReal hxtop hxbot).symm
    have hnhds : Set.Ioo ((a - 1 : ℝ) : EReal) ((a + 1 : ℝ) : EReal) ∈ 𝓝 (f x) := by
      rw [ha]
      apply Ioo_mem_nhds
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (hcont hnhds)
    refine ⟨δ / 2, by positivity, 8 / δ, ?_⟩
    intro v hv u hu
    by_cases hu0 : u = 0
    · rw [hu0, norm_zero]; positivity
    have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
    set y := v + (δ / 4 / ‖u‖) • u with hy_def
    have hvx : dist v x < δ / 2 := hv
    have hy_ball : y ∈ Metric.ball x δ := by
      rw [Metric.mem_ball, dist_eq_norm]
      have : y - x = (v - x) + (δ / 4 / ‖u‖) • u := by rw [hy_def]; abel
      rw [this]
      calc ‖(v - x) + (δ / 4 / ‖u‖) • u‖ ≤ ‖v - x‖ + ‖(δ / 4 / ‖u‖) • u‖ := norm_add_le _ _
        _ = ‖v - x‖ + δ / 4 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]; field_simp
        _ < δ := by rw [← dist_eq_norm]; linarith
    have hv_ball : v ∈ Metric.ball x δ := by
      rw [Metric.mem_ball]; linarith
    have hfy := hball hy_ball
    have hfv := hball hv_ball
    simp only [Set.mem_preimage, Set.mem_Ioo] at hfy hfv
    have hfy_top : f y ≠ ⊤ := ne_top_of_lt hfy.2
    have hfy_bot : f y ≠ ⊥ := ne_bot_of_gt hfy.1
    have hfv_top : f v ≠ ⊤ := ne_top_of_lt hfv.2
    have hfv_bot : f v ≠ ⊥ := ne_bot_of_gt hfv.1
    set yr := (f y).toReal
    set vr := (f v).toReal
    have hyr : f y = (yr : EReal) := (EReal.coe_toReal hfy_top hfy_bot).symm
    have hvr : f v = (vr : EReal) := (EReal.coe_toReal hfv_top hfv_bot).symm
    have hsub := hu y
    have hinner : inner ℝ u (y - v) = δ / 4 * ‖u‖ := by
      rw [hy_def, add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hinner, hyr, hvr, ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff] at hsub
    rw [hyr, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff] at hfy
    rw [hvr, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff] at hfv
    have h1 : δ / 4 * ‖u‖ < 2 := by linarith [hfy.2, hfv.1]
    rw [le_div_iff₀ hδ]
    nlinarith
  have BC1617_weak_compact {f : E → EReal} {x : E} (hxtop : f x ≠ ⊤) (hxbot : f x ≠ ⊥)
      {R : ℝ} (hR : ∀ u ∈ convexSubdifferential f x, ‖u‖ ≤ R) :
      IsCompact (Set.image (toWeakSpace ℝ E) (convexSubdifferential f x)) := by
    set S := convexSubdifferential f x with hS_def
    set a := (f x).toReal with ha_def
    have ha : f x = (a : EReal) := (EReal.coe_toReal hxtop hxbot).symm
    let g : WeakDual ℝ E → E := fun Lf =>
      (InnerProductSpace.toDual ℝ E).symm (WeakDual.toStrongDual Lf)
    have hg_apply : ∀ (Lf : WeakDual ℝ E) (z : E), inner ℝ (g Lf) z = Lf z := by
      intro Lf z
      simp only [g]
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    have hg_surj : Function.Surjective g := by
      intro u
      refine ⟨StrongDual.toWeakDual (InnerProductSpace.toDual ℝ E u), ?_⟩
      simp [g]
    set T : Set (WeakDual ℝ E) := g ⁻¹' S with hT_def
    have hT_closed : IsClosed T := by
      have : T = ⋂ y, {Lf : WeakDual ℝ E | ((a + Lf (y - x) : ℝ) : EReal) ≤ f y} := by
        ext Lf
        simp only [hT_def, Set.mem_preimage, Set.mem_iInter, Set.mem_setOf_eq, hS_def,
          convexSubdifferential, hg_apply, ha, EReal.coe_add, ge_iff_le]
      rw [this]
      refine isClosed_iInter fun y => isClosed_le ?_ continuous_const
      exact continuous_coe_real_ereal.comp (continuous_const.add (WeakDual.eval_continuous (y - x)))
    have hT_bdd : Bornology.IsBounded (StrongDual.toWeakDual ⁻¹' T) := by
      rw [isBounded_iff_forall_norm_le]
      refine ⟨R, fun ψ hψ => ?_⟩
      have h1 := hR _ hψ
      simp only [g] at h1
      rw [LinearIsometryEquiv.norm_map] at h1
      exact h1
    have hT_compact : IsCompact T := WeakDual.isCompact_of_bounded_of_closed hT_bdd hT_closed
    let Φ : WeakDual ℝ E → WeakSpace ℝ E := fun Lf => toWeakSpace ℝ E (g Lf)
    have hΦ_cont : Continuous Φ := by
      apply WeakBilin.continuous_of_continuous_eval
      intro l
      have : (fun Lf : WeakDual ℝ E => (topDualPairing ℝ E).flip (Φ Lf) l) =
          fun Lf => Lf ((InnerProductSpace.toDual ℝ E).symm l) := by
        ext Lf
        simp only [Φ, LinearMap.flip_apply, topDualPairing_apply]
        show l (g Lf) = Lf ((InnerProductSpace.toDual ℝ E).symm l)
        rw [← InnerProductSpace.toDual_symm_apply (𝕜 := ℝ) (E := E) (x := g Lf) (y := l),
          real_inner_comm, hg_apply]
      rw [this]
      exact WeakDual.eval_continuous _
    have himage : Φ '' T = Set.image (toWeakSpace ℝ E) S := by
      show ((toWeakSpace ℝ E) ∘ g) '' (g ⁻¹' S) = _
      rw [Set.image_comp, Set.image_preimage_eq S hg_surj]
    rw [← himage]
    exact hT_compact.image hΦ_cont
  have BC1617_intrinsicInterior_subset {s : Set E} (hs : (interior s).Nonempty) :
      intrinsicInterior ℝ s ⊆ interior s := by
    have htop : affineSpan ℝ s = ⊤ :=
      affineSpan_eq_top_of_nonempty_interior (hs.mono (interior_mono (subset_convexHull ℝ s)))
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_interior] at hy
    obtain ⟨t, hts, ht_open, hyt⟩ := hy
    obtain ⟨V, hV_open, rfl⟩ := isOpen_induced_iff.mp ht_open
    rw [mem_interior]
    refine ⟨V, ?_, hV_open, hyt⟩
    intro v hv
    have hvmem : v ∈ affineSpan ℝ s := by rw [htop]; exact AffineSubspace.mem_top ℝ E v
    exact hts (show (⟨v, hvmem⟩ : affineSpan ℝ s) ∈ Subtype.val ⁻¹' V from hv)
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (i)
    intro hint hfr
    by_cases hS : convexSubdifferential f x = ∅
    · left; exact hS
    right
    obtain ⟨u, hu⟩ := Set.nonempty_iff_ne_empty.mpr hS
    have hxint : x ∉ interior (effDom f) := hfr.2
    have hdomconv : Convex ℝ (effDom f) := BC1617_effDom_convex hf_convex
    obtain ⟨L, hL⟩ := geometric_hahn_banach_open_point hdomconv.interior isOpen_interior hxint
    have hle : ∀ y ∈ effDom f, L y ≤ L x := by
      have hsub : closure (interior (effDom f)) ⊆ {y | L y ≤ L x} :=
        closure_minimal (fun y hy => (hL y hy).le) (isClosed_le L.continuous continuous_const)
      rw [hdomconv.closure_interior_eq_closure_of_nonempty_interior hint] at hsub
      exact fun y hy => hsub (subset_closure hy)
    set w := (InnerProductSpace.toDual ℝ E).symm L with hw_def
    have hw : ∀ z, inner ℝ w z = L z := fun z => InnerProductSpace.toDual_symm_apply
    have hw0 : w ≠ 0 := by
      intro h
      obtain ⟨y0, hy0⟩ := hint
      have := hL y0 hy0
      rw [← hw, ← hw, h, inner_zero_left, inner_zero_left] at this
      exact lt_irrefl _ this
    have hray : ∀ t : ℝ, 0 ≤ t → u + t • w ∈ convexSubdifferential f x := by
      intro t ht y
      by_cases hy : f y = ⊤
      · rw [hy]; exact le_top
      · have hyd : y ∈ effDom f := lt_top_iff_ne_top.mpr hy
        have h1 := hu y
        have h2 : inner ℝ (u + t • w) (y - x) ≤ inner ℝ u (y - x) := by
          rw [inner_add_left, real_inner_smul_left, hw]
          have : L (y - x) ≤ 0 := by rw [map_sub]; linarith [hle y hyd]
          nlinarith
        calc f x + ((inner ℝ (u + t • w) (y - x) : ℝ) : EReal)
            ≤ f x + ((inner ℝ u (y - x) : ℝ) : EReal) :=
              add_le_add le_rfl (EReal.coe_le_coe_iff.mpr h2)
          _ ≤ f y := h1
    intro hbdd
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hbdd
    have hwn : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have hRu : ‖u‖ ≤ R := hR u hu
    set t := (R + ‖u‖ + 1) / ‖w‖ with ht_def
    have ht : 0 ≤ t := div_nonneg (by linarith [norm_nonneg u]) hwn.le
    have h4 := hR _ (hray t ht)
    have h3 : ‖t • w‖ ≤ ‖u + t • w‖ + ‖u‖ := by
      calc ‖t • w‖ = ‖(u + t • w) - u‖ := by rw [add_sub_cancel_left]
        _ ≤ ‖u + t • w‖ + ‖u‖ := norm_sub_le _ _
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at h3
    have h5 : t * ‖w‖ = R + ‖u‖ + 1 := by rw [ht_def]; field_simp
    linarith
  · -- (ii)
    intro hxc
    obtain ⟨hxi, hepi⟩ := BC1617_cont_aux hxc
    refine ⟨BC1617_subdiff_nonempty hf_proper hf_convex hxi hepi, ?_⟩
    obtain ⟨ρ, hρ, R, hR⟩ := BC1617_local_bound hxc
    exact BC1617_weak_compact hxc.1 hxc.2.1 (fun u hu => hR x (Metric.mem_ball_self hρ) u hu)
  · -- (iii)
    intro hxc
    obtain ⟨ρ, hρ, R, hR⟩ := BC1617_local_bound hxc
    refine ⟨ρ, hρ, ?_⟩
    rw [isBounded_iff_forall_norm_le]
    refine ⟨R, fun u hu => ?_⟩
    simp only [Set.mem_iUnion] at hu
    obtain ⟨v, hv, hu⟩ := hu
    exact hR v hv u hu
  · -- (iv)
    rintro ⟨x0, hx0⟩ z hz
    obtain ⟨hx0i, hepi⟩ := BC1617_cont_aux hx0
    have hz' : z ∈ interior (effDom f) := BC1617_intrinsicInterior_subset ⟨x0, hx0i⟩ hz
    exact BC1617_subdiff_nonempty hf_proper hf_convex hz' hepi

end BC_chap_16_17
