import ConvexStarLib.Defs

/-!
# `FCA_chap_E_4_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_4_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_4_1_2`, so the main result is `FCA_chap_E_4_1_2.FCA_chap_E_4_1_2`.
-/

namespace FCA_chap_E_4_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_4_1_2
  (f : E → EReal)
  (g : E → ℝ)
  (hf_closed_convex : InClosedConvRn f)
  (hg_eq : ∀ x ∈ interior (effDom f),
    (f x) = (g x : EReal))
  (hg_diff : DifferentiableOn ℝ g (interior (effDom f)))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let Ω := interior (effDom f)
  let gradImage := Set.image (gradient g) Ω
  ∀ (C : Set E),
  (C ⊆ gradImage) → (Convex ℝ C) →
  ∀ s₁ ∈ C, ∀ s₂ ∈ C, s₁ ≠ s₂ →
  ∀ (α : ℝ), α ∈ Set.Ioo 0 1 →
  (conjugate f (α • s₁ + (1 - α) • s₂)) <
  (α * (conjugate f s₁) + (1 - α) * (conjugate f s₂)) := by
  intro Ω gradImage C hC hCconv s₁ hs₁ s₂ hs₂ hne α hα
  obtain ⟨hα0, hα1⟩ := hα
  set s := α • s₁ + (1 - α) • s₂ with hs_def
  have hsC : s ∈ C := hCconv hs₁ hs₂ hα0.le (by linarith) (by ring)
  obtain ⟨x, hxΩ, hgx⟩ := hC hsC
  have hΩopen : IsOpen Ω := isOpen_interior
  have hgdiff : DifferentiableAt ℝ g x := hg_diff.differentiableAt (hΩopen.mem_nhds hxΩ)
  have hfx : f x = (g x : EReal) := hg_eq x hxΩ
  have hconv : Convex ℝ (epigraph f) := hf_closed_convex.1.2.2
  have hgrad : ∀ v, fderiv ℝ g x v = inner ℝ s v := by
    intro v
    rw [← hgx, inner_gradient_left hgdiff]
  -- Claim A: gradient inequality
  have hA : ∀ y, ((inner ℝ s y : ℝ) : EReal) - f y ≤ ((inner ℝ s x - g x : ℝ) : EReal) := by
    intro y
    by_cases hy : f y = ⊤
    · rw [hy, EReal.sub_top]
      exact bot_le
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, f y = (r : EReal) :=
        ⟨(f y).toReal, (EReal.coe_toReal hy (f_ne_bot y).ne').symm⟩
      rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      set d := y - x with hd
      have hseg : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
          f (x + t • d) ≤ (((1 - t) * g x + t * r : ℝ) : EReal) := by
        intro t ht0 ht1
        have hxmem : (x, g x) ∈ epigraph f := by
          show f x ≤ (g x : EReal)
          rw [hfx]
        have hymem : (y, r) ∈ epigraph f := by
          show f y ≤ (r : EReal)
          rw [hr]
        have hmem := hconv hxmem hymem (sub_nonneg.mpr ht1) ht0 (by ring)
        have heq : x + t • d = (1 - t) • x + t • y := by
          simp only [hd, smul_sub, sub_smul, one_smul]; abel
        rw [heq]
        exact hmem
      have hev : ∀ᶠ t in 𝓝 (0:ℝ), x + t • d ∈ Ω := by
        have hcont : Continuous (fun t : ℝ => x + t • d) := by fun_prop
        apply hcont.continuousAt.preimage_mem_nhds
        simpa using hΩopen.mem_nhds hxΩ
      let phi : ℝ → ℝ := fun t => g (x + t • d) - t * (r - g x)
      have hmax : IsLocalMaxOn phi (Set.Icc 0 1) 0 := by
        have hev' : ∀ᶠ t in 𝓝[Set.Icc 0 1] (0:ℝ), x + t • d ∈ Ω ∧ t ∈ Set.Icc (0:ℝ) 1 :=
          (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
        filter_upwards [hev'] with t ⟨htΩ, ht0, ht1⟩
        have h1 := hseg t ht0 ht1
        rw [hg_eq _ htΩ, EReal.coe_le_coe_iff] at h1
        simp only [phi, zero_smul, add_zero, zero_mul, sub_zero]
        linarith
      have hderiv : HasDerivAt phi (inner ℝ s d - (r - g x)) 0 := by
        have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
          simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
        have h2 : HasFDerivAt g (fderiv ℝ g x) (x + (0:ℝ) • d) := by
          simpa using hgdiff.hasFDerivAt
        have h3 := h2.comp_hasDerivAt (0:ℝ) h1
        have h4 : HasDerivAt (fun t : ℝ => t * (r - g x)) (r - g x) 0 := by
          simpa using (hasDerivAt_id (0:ℝ)).mul_const (r - g x)
        have h5 := h3.sub h4
        rw [hgrad] at h5
        exact h5
      have hcone : (1:ℝ) ∈ posTangentConeAt (Set.Icc (0:ℝ) 1) 0 := by
        apply mem_posTangentConeAt_of_segment_subset
        rw [segment_eq_Icc (by norm_num)]
        simp
      have hnp := hmax.hasFDerivWithinAt_nonpos hderiv.hasFDerivAt.hasFDerivWithinAt hcone
      simp at hnp
      have hinner : inner ℝ s d = inner ℝ s y - inner ℝ s x := inner_sub_right _ _ _
      linarith
  -- Claim B
  have hB : ∀ v, (((inner ℝ v x - g x : ℝ)) : EReal) ≤ conjugate f v := by
    intro v
    apply le_sSup
    refine ⟨x, Set.mem_univ _, ?_⟩
    simp only [hfx]
    rw [EReal.coe_sub]
  -- Claim C
  have hC1 : ((inner ℝ s₁ x - g x : ℝ) : EReal) < conjugate f s₁ := by
    by_contra hcon
    push_neg at hcon
    have hloc : IsLocalMax (fun z => inner ℝ s₁ z - g z) x := by
      filter_upwards [hΩopen.mem_nhds hxΩ] with z hz
      have h1 : ((inner ℝ s₁ z : ℝ) : EReal) - f z ≤ conjugate f s₁ :=
        le_sSup ⟨z, Set.mem_univ _, rfl⟩
      rw [hg_eq z hz, ← EReal.coe_sub] at h1
      have h2 := h1.trans hcon
      rw [EReal.coe_le_coe_iff] at h2
      exact h2
    have hderiv : HasFDerivAt (fun z => inner ℝ s₁ z - g z) (innerSL ℝ s₁ - fderiv ℝ g x) x :=
      (innerSL ℝ s₁).hasFDerivAt.sub hgdiff.hasFDerivAt
    have hzero := hloc.hasFDerivAt_eq_zero hderiv
    have hv := congrArg (fun L => L (s₁ - s)) hzero
    simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply, ContinuousLinearMap.zero_apply,
      hgrad] at hv
    rw [← inner_sub_left, inner_self_eq_zero, sub_eq_zero] at hv
    apply hne
    have h1 : (1 - α) • s₁ = (1 - α) • s₂ := by
      calc (1 - α) • s₁ = s₁ - α • s₁ := by rw [sub_smul, one_smul]
        _ = (α • s₁ + (1 - α) • s₂) - α • s₁ := by rw [← hs_def, ← hv]
        _ = (1 - α) • s₂ := by abel
    exact smul_right_injective E (sub_ne_zero.mpr hα1.ne') h1
  have hfs : conjugate f s ≤ ((inner ℝ s x - g x : ℝ) : EReal) := by
    apply sSup_le
    rintro _ ⟨y, _, rfl⟩
    exact hA y
  have hB2 := hB s₂
  have hlin : inner ℝ s x - g x =
      α * (inner ℝ s₁ x - g x) + (1 - α) * (inner ℝ s₂ x - g x) := by
    rw [hs_def, inner_add_left, real_inner_smul_left, real_inner_smul_left]
    ring
  have h1α : ((1:EReal) - (α:EReal)) = ((1 - α : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_one]
  rw [h1α]
  refine lt_of_le_of_lt hfs ?_
  rw [hlin]
  generalize conjugate f s₁ = A at hC1 ⊢
  generalize conjugate f s₂ = B at hB2 ⊢
  have h1α_pos : (0:ℝ) < 1 - α := by linarith
  induction A using EReal.rec with
  | bot => exact absurd hC1 not_lt_bot
  | top =>
    rw [EReal.coe_mul_top_of_pos hα0, EReal.top_add_of_ne_bot]
    · exact EReal.coe_lt_top _
    · induction B using EReal.rec with
      | bot => exact absurd hB2 (not_le.mpr (EReal.bot_lt_coe _))
      | coe b => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
      | top => rw [EReal.coe_mul_top_of_pos h1α_pos]; exact top_ne_bot
  | coe A' =>
    induction B using EReal.rec with
    | bot => exact absurd hB2 (not_le.mpr (EReal.bot_lt_coe _))
    | coe B' =>
      rw [← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, EReal.coe_lt_coe_iff]
      rw [EReal.coe_lt_coe_iff] at hC1
      rw [EReal.coe_le_coe_iff] at hB2
      have k1 := mul_lt_mul_of_pos_left hC1 hα0
      have k2 := mul_le_mul_of_nonneg_left hB2 h1α_pos.le
      linarith
    | top =>
      rw [EReal.coe_mul_top_of_pos h1α_pos, ← EReal.coe_mul,
        EReal.add_top_of_ne_bot (EReal.coe_ne_bot _)]
      exact EReal.coe_lt_top _

end FCA_chap_E_4_1_2
