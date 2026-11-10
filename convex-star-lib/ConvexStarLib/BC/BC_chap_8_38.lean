import ConvexStarLib.Defs

/-!
# `BC_chap_8_38`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_8_38` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_8_38`, so the main result is `BC_chap_8_38.BC_chap_8_38`.
-/

namespace BC_chap_8_38

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem BC_chap_8_38
  (f : E → EReal)
  (x₀ : E)
  (hx₀ : x₀ ∈ effDom f)
  (hf_proper : IsProper f)
  (hf_convex : ConvexEReal f) :
  List.TFAE [
    IsLocallyLipschitzNearEReal f x₀,
    ContinuousAt f x₀,
    (∃ U ∈ 𝓝 x₀, ∃ (a b : ℝ),
      ∀ y ∈ U,
        (a : EReal) ≤ f y ∧ f y ≤ (b : EReal)),
    (∃ U ∈ 𝓝 x₀, ∃ (a : ℝ),
      ∀ y ∈ U, f y ≤ (a : EReal))
  ] ∧
  (ContinuousAt f x₀ →
    IsLocallyLipschitzOnEReal f (intrinsicInterior ℝ (effDom f))) := by
  obtain ⟨hbot, -⟩ := hf_proper
  set D := effDom f with hD_def
  set g : E → ℝ := fun x => (f x).toReal with hg_def
  -- f equals coe of g on D
  have hfg : ∀ x ∈ D, f x = ((g x : ℝ) : EReal) := by
    intro x hx
    exact (EReal.coe_toReal (ne_of_lt hx) (hbot x).ne').symm
  -- convexity of g on D
  have hconvD : ConvexOn ℝ D g := by
    have key : ∀ x ∈ D, ∀ y ∈ D, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        f (a • x + b • y) ≤ ((a * g x + b * g y : ℝ) : EReal) := by
      intro x hx y hy a b ha hb hab
      have hxe : (x, g x) ∈ epigraph f := by
        show f x ≤ ((g x : ℝ) : EReal)
        rw [hfg x hx]
      have hye : (y, g y) ∈ epigraph f := by
        show f y ≤ ((g y : ℝ) : EReal)
        rw [hfg y hy]
      have := hf_convex hxe hye ha hb hab
      simpa [epigraph] using this
    refine ⟨?_, ?_⟩
    · intro x hx y hy a b ha hb hab
      show f (a • x + b • y) < ⊤
      exact lt_of_le_of_lt (key x hx y hy a b ha hb hab) (EReal.coe_lt_top _)
    · intro x hx y hy a b ha hb hab
      have h := key x hx y hy a b ha hb hab
      show (f (a • x + b • y)).toReal ≤ a • g x + b • g y
      have := EReal.toReal_le_toReal h (hbot _).ne' (EReal.coe_ne_top _)
      simpa using this
  have hCopen : IsOpen (interior D) := isOpen_interior
  have hconvC : ConvexOn ℝ (interior D) g := hconvD.subset interior_subset hconvD.1.interior
  -- From local Lipschitz of g on C to local Lipschitz of f near x
  have hL : ∀ x ∈ interior D, LocallyLipschitzOn (interior D) g →
      IsLocallyLipschitzNearEReal f x := by
    intro x hx hLL
    obtain ⟨K, t, ht, hK⟩ := hLL hx
    rw [hCopen.nhdsWithin_eq hx] at ht
    obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht (hCopen.mem_nhds hx))
    refine ⟨ε, hε, K, K.2, ?_, ?_⟩
    · intro y hy
      have hyD : y ∈ D := interior_subset (hεsub hy).2
      exact ⟨(show f y < ⊤ from hyD).ne, (hbot y).ne'⟩
    · intro y z hy hz
      have := hK.dist_le_mul y (hεsub hy).1 z (hεsub hz).1
      rw [Real.dist_eq] at this
      simpa [Real.norm_eq_abs, smul_eq_mul] using this
  -- From boundedness above to local Lipschitz of g on C
  have hB : ∀ x : E, (∃ U ∈ 𝓝 x, ∃ (a : ℝ), ∀ y ∈ U, f y ≤ (a : EReal)) →
      x ∈ interior D ∧ LocallyLipschitzOn (interior D) g := by
    rintro x ⟨U, hU, a, ha⟩
    have hUD : U ⊆ D := fun y hy => lt_of_le_of_lt (ha y hy) (EReal.coe_lt_top a)
    have hxC : x ∈ interior D := mem_interior_iff_mem_nhds.2 (Filter.mem_of_superset hU hUD)
    refine ⟨hxC, ?_⟩
    have hbdd : (𝓝 x).IsBoundedUnder (· ≤ ·) g := by
      refine Filter.isBoundedUnder_of_eventually_le (a := a) ?_
      filter_upwards [hU] with y hy
      have := EReal.toReal_le_toReal (ha y hy) (hbot y).ne' (EReal.coe_ne_top a)
      simpa using this
    have htfae := hconvC.continuousOn_tfae hCopen ⟨x, hxC⟩
    have h30 : (∃ x₀ ∈ interior D, (𝓝 x₀).IsBoundedUnder (· ≤ ·) g) →
        LocallyLipschitzOn (interior D) g := (htfae.out 3 0).1
    exact h30 ⟨x, hxC, hbdd⟩
  -- f x₀ is finite
  have hfx₀ := hfg x₀ hx₀
  -- continuity gives two-sided bounds
  have h23 : ContinuousAt f x₀ → (∃ U ∈ 𝓝 x₀, ∃ (a b : ℝ),
      ∀ y ∈ U, (a : EReal) ≤ f y ∧ f y ≤ (b : EReal)) := by
    intro hc
    refine ⟨f ⁻¹' Set.Icc ((g x₀ - 1 : ℝ) : EReal) ((g x₀ + 1 : ℝ) : EReal), ?_,
      g x₀ - 1, g x₀ + 1, fun y hy => hy⟩
    apply hc.preimage_mem_nhds
    rw [hfx₀]
    apply _root_.Icc_mem_nhds
    · exact EReal.coe_lt_coe_iff.2 (by linarith)
    · exact EReal.coe_lt_coe_iff.2 (by linarith)
  have h34 : (∃ U ∈ 𝓝 x₀, ∃ (a b : ℝ),
      ∀ y ∈ U, (a : EReal) ≤ f y ∧ f y ≤ (b : EReal)) →
      (∃ U ∈ 𝓝 x₀, ∃ (a : ℝ), ∀ y ∈ U, f y ≤ (a : EReal)) := by
    rintro ⟨U, hU, a, b, h⟩
    exact ⟨U, hU, b, fun y hy => (h y hy).2⟩
  have h41 : (∃ U ∈ 𝓝 x₀, ∃ (a : ℝ), ∀ y ∈ U, f y ≤ (a : EReal)) →
      IsLocallyLipschitzNearEReal f x₀ := by
    intro h
    obtain ⟨hxC, hLL⟩ := hB x₀ h
    exact hL x₀ hxC hLL
  have h12 : IsLocallyLipschitzNearEReal f x₀ → ContinuousAt f x₀ := by
    rintro ⟨ρ, hρ, β, hβ, hfin, hlip⟩
    have hgL : LipschitzOnWith (Real.toNNReal β) g (Metric.ball x₀ ρ) := by
      apply LipschitzOnWith.of_dist_le'
      intro y hy z hz
      have := hlip y z hy hz
      rw [Real.dist_eq]
      simpa [Real.norm_eq_abs, smul_eq_mul] using this
    have hgc : ContinuousAt g x₀ := hgL.continuousOn.continuousAt (Metric.ball_mem_nhds x₀ hρ)
    have heq : (fun y => ((g y : ℝ) : EReal)) =ᶠ[𝓝 x₀] f := by
      filter_upwards [Metric.ball_mem_nhds x₀ hρ] with y hy
      exact EReal.coe_toReal (hfin y hy).1 (hfin y hy).2
    exact (continuous_coe_real_ereal.continuousAt.comp hgc).congr heq
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := h12
    tfae_have 2 → 3 := h23
    tfae_have 3 → 4 := h34
    tfae_have 4 → 1 := h41
    tfae_finish
  · intro hc x hx
    obtain ⟨hx₀C, hLL⟩ := hB x₀ (h34 (h23 hc))
    -- affine span of D is everything
    have hspan : affineSpan ℝ D = ⊤ :=
      top_unique ((hCopen.affineSpan_eq_top ⟨x₀, hx₀C⟩).symm.le.trans
        (affineSpan_mono ℝ interior_subset))
    have hxC : x ∈ interior D := by
      obtain ⟨y, hy, rfl⟩ := hx
      rw [mem_interior_iff_mem_nhds] at hy ⊢
      obtain ⟨u, hu, hsub⟩ := (mem_nhds_subtype _ _ _).1 hy
      apply Filter.mem_of_superset hu
      intro z hz
      have hzspan : z ∈ affineSpan ℝ D := by rw [hspan]; trivial
      exact hsub (show (⟨z, hzspan⟩ : affineSpan ℝ D) ∈ Subtype.val ⁻¹' u from hz)
    exact hL x hxC hLL

end BC_chap_8_38
