import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex4`, so the main result is `FCA_chap_E_ex4.FCA_chap_E_ex4`.
-/

namespace FCA_chap_E_ex4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex4
  (G : Set E)
  (f g : E → EReal)
  (hf_closed_convex : InClosedConvRn f)
  (hri_subset : intrinsicInterior ℝ (effDom f) ⊆ G)
  (hG_subset : G ⊆ effDom f)
  (hfg : ∀ (x : E), f x ≤ g x)
  (h_eq_on_ri : ∀ (x : E),
    x ∈ intrinsicInterior ℝ (effDom f) →
    g x = f x)
  (f_ne_bot : ∀ x, ⊥ < f x)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (sInf (Set.image g G)) = (sInf (Set.image g Set.univ)) ∧
  (sInf (Set.image g Set.univ)) = (sInf (Set.image f Set.univ)) := by
  obtain ⟨⟨_, ⟨xd, hxd⟩, hconvepi⟩, _⟩ := hf_closed_convex
  -- the effective domain is convex
  have hconv : Convex ℝ (effDom f) := by
    intro x hx y hy a b ha hb hab
    have hx' : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hx.ne (f_ne_bot x).ne').symm
    have hy' : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hy.ne (f_ne_bot y).ne').symm
    have h1 : (x, (f x).toReal) ∈ epigraph f := by
      show f x ≤ _
      rw [← hx']
    have h2 : (y, (f y).toReal) ∈ epigraph f := by
      show f y ≤ _
      rw [← hy']
    have h3 := hconvepi h1 h2 ha hb hab
    have h4 : f (a • x + b • y) ≤ ((a * (f x).toReal + b * (f y).toReal : ℝ) : EReal) := h3
    exact lt_of_le_of_lt h4 (EReal.coe_lt_top _)
  -- segments from a relative interior point stay in the relative interior
  have hri_seg : ∀ x0 ∈ intrinsicInterior ℝ (effDom f), ∀ x ∈ effDom f, ∀ t : ℝ, 0 < t →
      t ≤ 1 → t • x0 + (1 - t) • x ∈ intrinsicInterior ℝ (effDom f) := by
    intro x0 hx0 x hx t ht0 ht1
    rw [mem_intrinsicInterior] at hx0 ⊢
    obtain ⟨⟨x0', hx0A⟩, hint, rfl⟩ := hx0
    have hx0C : x0' ∈ effDom f := by
      have h := interior_subset hint
      exact h
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hint
    obtain ⟨u, hu, hsub⟩ := hint
    have hyC : t • x0' + (1 - t) • x ∈ effDom f :=
      hconv hx0C hx ht0.le (by linarith) (by ring)
    refine ⟨⟨t • x0' + (1 - t) • x, subset_affineSpan ℝ _ hyC⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
    have ht' : t ≠ 0 := ht0.ne'
    refine ⟨(fun z => x + t⁻¹ • (z - x)) ⁻¹' u, ?_, ?_⟩
    · apply ContinuousAt.preimage_mem_nhds
      · fun_prop
      · convert hu using 2
        have e : t • x0' + (1 - t) • x - x = t • (x0' - x) := by
          rw [smul_sub, sub_smul, one_smul]; abel
        simp only
        rw [e, smul_smul, inv_mul_cancel₀ ht', one_smul]
        abel
    · rintro ⟨z, hzA⟩ hz
      simp only [Set.mem_preimage] at hz ⊢
      have hψA : x + t⁻¹ • (z - x) ∈ affineSpan ℝ (effDom f) := by
        have := AffineMap.lineMap_mem t⁻¹ (subset_affineSpan ℝ _ hx) hzA
        convert this using 1
        rw [AffineMap.lineMap_apply, vsub_eq_sub, vadd_eq_add, add_comm]
      have hψC : x + t⁻¹ • (z - x) ∈ effDom f :=
        hsub (show (⟨x + t⁻¹ • (z - x), hψA⟩ : affineSpan ℝ (effDom f)) ∈ Subtype.val ⁻¹' u
          from hz)
      have e : z = t • (x + t⁻¹ • (z - x)) + (1 - t) • x := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ ht', one_smul, sub_smul, one_smul]
        abel
      rw [e]
      exact hconv hψC hx ht0.le (by linarith) (by ring)
  obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior hconv ⟨xd, hxd⟩
  -- the infimum over the relative interior is a lower bound of `f`
  have key : ∀ x, sInf (f '' intrinsicInterior ℝ (effDom f)) ≤ f x := by
    intro x
    by_cases hx : f x < ⊤
    · have hx0C : x0 ∈ effDom f := intrinsicInterior_subset hx0
      have ha : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hx.ne (f_ne_bot x).ne').symm
      have hb : f x0 = ((f x0).toReal : EReal) :=
        (EReal.coe_toReal hx0C.ne (f_ne_bot x0).ne').symm
      have hlim : Tendsto (fun t : ℝ => ((t * (f x0).toReal + (1 - t) * (f x).toReal : ℝ) : EReal))
          (𝓝[>] 0) (𝓝 ((f x).toReal : EReal)) := by
        have hc : Continuous (fun t : ℝ => t * (f x0).toReal + (1 - t) * (f x).toReal) := by
          fun_prop
        have := hc.tendsto 0
        simp only [zero_mul, sub_zero, one_mul, zero_add] at this
        exact (continuous_coe_real_ereal.tendsto _).comp (this.mono_left nhdsWithin_le_nhds)
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), sInf (f '' intrinsicInterior ℝ (effDom f)) ≤
          ((t * (f x0).toReal + (1 - t) * (f x).toReal : ℝ) : EReal) := by
        filter_upwards [Ioc_mem_nhdsGT (by norm_num : (0:ℝ) < 1)] with t ht
        have hmem := hri_seg x0 hx0 x hx t ht.1 ht.2
        refine le_trans (sInf_le ⟨_, hmem, rfl⟩) ?_
        have h1 : (x0, (f x0).toReal) ∈ epigraph f := by
          show f x0 ≤ _
          rw [← hb]
        have h2 : (x, (f x).toReal) ∈ epigraph f := by
          show f x ≤ _
          rw [← ha]
        exact hconvepi h1 h2 ht.1.le (by linarith [ht.2]) (by ring)
      rw [ha]
      exact ge_of_tendsto hlim hev
    · rw [not_lt, top_le_iff] at hx
      rw [hx]
      exact le_top
  have h1 : sInf (f '' Set.univ) ≤ sInf (g '' Set.univ) := by
    apply le_sInf
    rintro _ ⟨x, _, rfl⟩
    exact (sInf_le (Set.mem_image_of_mem f (Set.mem_univ x))).trans (hfg x)
  have h2 : sInf (g '' Set.univ) ≤ sInf (g '' G) :=
    sInf_le_sInf (Set.image_mono (Set.subset_univ _))
  have h3 : sInf (g '' G) ≤ sInf (g '' intrinsicInterior ℝ (effDom f)) :=
    sInf_le_sInf (Set.image_mono hri_subset)
  have h4 : g '' intrinsicInterior ℝ (effDom f) = f '' intrinsicInterior ℝ (effDom f) :=
    Set.image_congr h_eq_on_ri
  have h5 : sInf (f '' intrinsicInterior ℝ (effDom f)) ≤ sInf (f '' Set.univ) := by
    apply le_sInf
    rintro _ ⟨x, _, rfl⟩
    exact key x
  rw [h4] at h3
  exact ⟨le_antisymm (h3.trans (h5.trans h1)) h2, le_antisymm (h2.trans (h3.trans h5)) h1⟩

end FCA_chap_E_ex4
