import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex5`, so the main result is `FCA_chap_D_ex5.FCA_chap_D_ex5`.
-/

namespace FCA_chap_D_ex5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_D_ex5
  (f : E → ℝ)
  (x : E)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hE : Nontrivial E) :
  let lf_0 := fun x => sSup (Set.image (fun x' => ((f x) - (f x')) / ‖x' - x‖) {x' | x' ≠ x})
  let lf := fun x => max 0 (lf_0 x)
  lf x = sInf (Set.image (fun v => ‖v‖) (directionalSubdifferential (liftRealtoEReal f) x)) := by
  intro lf_0 lf
  -- convexity
  have hconv : ConvexOn ℝ Set.univ f := by
    rw [convexOn_iff_convex_epigraph]
    have h := hf_convex.2.2
    unfold ConvexEReal epigraph liftRealtoEReal at h
    convert h using 1
    ext p
    simp [EReal.coe_le_coe_iff]
  have hline : ∀ d : E, ConvexOn ℝ Set.univ (fun r : ℝ => f (x + r • d)) := by
    intro d
    refine ⟨convex_univ, fun r _ s _ a b ha hb hab => ?_⟩
    have := hconv.2 (Set.mem_univ (x + r • d)) (Set.mem_univ (x + s • d)) ha hb hab
    convert this using 2
    obtain rfl : b = 1 - a := by linarith
    simp only [smul_eq_mul]
    module
  -- difference quotient
  set q : E → ℝ → ℝ := fun d t => (f (x + t • d) - f x) / t with hq
  have hmono : ∀ d, MonotoneOn (q d) (Set.Ioi 0) := by
    intro d s hs t ht hst
    have := (hline d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ s) (Set.mem_univ t)
      (ne_of_gt hs) (ne_of_gt ht) hst
    simpa [q] using this
  have hlow : ∀ d, ∀ t > 0, f x - f (x - d) ≤ q d t := by
    intro d t ht
    have := (hline d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ (-1)) (Set.mem_univ t)
      (by norm_num) (ne_of_gt ht) (by linarith)
    simp only [q]
    simp only [neg_smul, one_smul, ← sub_eq_add_neg, zero_smul, add_zero, sub_zero] at this
    rw [div_neg, div_one] at this
    linarith
  have hlim : ∀ d, Tendsto (q d) (𝓝[>] 0) (𝓝 (sInf (q d '' Set.Ioi 0))) := by
    intro d
    apply MonotoneOn.tendsto_nhdsGT (hmono d)
    exact ⟨f x - f (x - d), by rintro _ ⟨t, ht, rfl⟩; exact hlow d t ht⟩
  set p : E → ℝ := fun d => sInf (q d '' Set.Ioi 0) with hp
  have hlim' : ∀ d, Tendsto (q d) (𝓝[>] 0) (𝓝 (p d)) := hlim
  clear_value p
  -- p ≤ q
  have hple : ∀ d, ∀ t > 0, p d ≤ q d t := by
    intro d t ht
    apply le_of_tendsto (hlim' d)
    filter_upwards [Ioo_mem_nhdsGT ht] with s hs
    exact hmono d hs.1 ht hs.2.le
  -- directional derivative
  have hdd : ∀ d, directionalDeriv (liftRealtoEReal f) x d = (p d : EReal) := by
    intro d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have h1 : Tendsto (fun t => ((q d t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (p d : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (hlim' d)
    apply h1.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [differenceQuotient, liftRealtoEReal, q]
    rw [EReal.coe_div, EReal.coe_sub]
  -- scaling
  have hscale : ∀ c : ℝ, 0 < c → Tendsto (fun t : ℝ => t * c) (𝓝[>] 0) (𝓝[>] 0) := by
    intro c hc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Tendsto (fun t : ℝ => t * c) (𝓝 0) (𝓝 (0 * c)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact mul_pos ht hc
  have hhom : ∀ c : ℝ, 0 < c → ∀ d, p (c • d) = c * p d := by
    intro c hc d
    have h1 : Tendsto (fun t => c * q d (t * c)) (𝓝[>] 0) (𝓝 (c * p d)) :=
      ((hlim' d).comp (hscale c hc)).const_mul c
    have h2 : Tendsto (q (c • d)) (𝓝[>] 0) (𝓝 (c * p d)) := by
      apply h1.congr'
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      simp only [q, mul_smul]
      field_simp
    exact tendsto_nhds_unique (hlim' (c • d)) h2
  have hp0 : p 0 = 0 := by
    have := hhom 2 two_pos 0
    rw [smul_zero] at this
    linarith
  have hsub : ∀ d₁ d₂, p (d₁ + d₂) ≤ p d₁ + p d₂ := by
    intro d₁ d₂
    have h1 : Tendsto (fun t => q d₁ (t * 2) + q d₂ (t * 2)) (𝓝[>] 0) (𝓝 (p d₁ + p d₂)) :=
      ((hlim' d₁).comp (hscale 2 two_pos)).add ((hlim' d₂).comp (hscale 2 two_pos))
    apply le_of_tendsto_of_tendsto (hlim' (d₁ + d₂)) h1
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have hc := hconv.2 (Set.mem_univ (x + (t * 2) • d₁)) (Set.mem_univ (x + (t * 2) • d₂))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have heq : (1/2 : ℝ) • (x + (t * 2) • d₁) + (1/2 : ℝ) • (x + (t * 2) • d₂) = x + t • (d₁ + d₂) := by
      module
    rw [heq] at hc
    simp only [q, smul_eq_mul] at hc ⊢
    rw [← add_div, div_le_div_iff₀ ht (by positivity)]
    nlinarith
  -- a subgradient bounds the slopes
  have hquot : ∀ v : E, (∀ d, inner ℝ v d ≤ p d) → ∀ x', x' ≠ x →
      (f x - f x') / ‖x' - x‖ ≤ ‖v‖ := by
    intro v hv x' hx'
    have hpos : 0 < ‖x' - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx')
    have h1 := hv (x' - x)
    have h2 := hple (x' - x) 1 one_pos
    simp only [q, one_smul, div_one, add_sub_cancel] at h2
    have h3 : -inner ℝ v (x' - x) ≤ ‖v‖ * ‖x' - x‖ := by
      have := abs_real_inner_le_norm v (x' - x)
      rw [abs_le] at this
      linarith
    rw [div_le_iff₀ hpos]
    linarith
  -- Hahn-Banach: a first subgradient
  obtain ⟨g0, -, hg0⟩ := exists_extension_of_le_sublinear (⟨⊥, 0⟩ : E →ₗ.[ℝ] ℝ) p hhom hsub (by
    rintro ⟨z, hz⟩
    rw [Submodule.mem_bot] at hz
    subst hz
    simp [hp0])
  set s0 := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g0)
  have hs0 : ∀ d, inner ℝ s0 d ≤ p d := by
    intro d
    rw [InnerProductSpace.toDual_symm_apply]
    simpa using hg0 d
  have hbdd : BddAbove ((fun x' => (f x - f x') / ‖x' - x‖) '' {x' | x' ≠ x}) := by
    refine ⟨‖s0‖, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    exact hquot s0 hs0 x' hx'
  -- the constant L
  set L : ℝ := lf x with hL
  have hL0 : 0 ≤ L := le_max_left _ _
  have hLS : ∀ x', x' ≠ x → (f x - f x') / ‖x' - x‖ ≤ L := fun x' hx' =>
    (le_csSup hbdd ⟨x', hx', rfl⟩).trans (le_max_right _ _)
  have hpL : ∀ d, -(L * ‖d‖) ≤ p d := by
    intro d
    by_cases hd : d = 0
    · subst hd; simp [hp0]
    · apply ge_of_tendsto (hlim' d)
      filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      have hx' : x + t • d ≠ x := by
        intro h
        have : t • d = 0 := by simpa using h
        rcases smul_eq_zero.mp this with h | h
        · linarith
        · exact hd h
      have := hLS (x + t • d) hx'
      simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht] at this
      have hpos : 0 < t * ‖d‖ := mul_pos ht (norm_pos_iff.mpr hd)
      rw [div_le_iff₀ hpos] at this
      simp only [q]
      rw [le_div_iff₀ ht]
      nlinarith
  -- Hahn-Banach on E × E
  set P : E × E → ℝ := fun z => p z.1 + L * ‖z.2‖ with hP
  have hPhom : ∀ c : ℝ, 0 < c → ∀ z, P (c • z) = c * P z := by
    intro c hc z
    simp only [P, Prod.smul_fst, Prod.smul_snd, hhom c hc, norm_smul, Real.norm_eq_abs,
      abs_of_pos hc]
    ring
  have hPsub : ∀ z w, P (z + w) ≤ P z + P w := by
    intro z w
    simp only [P, Prod.fst_add, Prod.snd_add]
    have := hsub z.1 w.1
    have := norm_add_le z.2 w.2
    nlinarith
  set A : Submodule ℝ (E × E) := LinearMap.ker (LinearMap.fst ℝ E E + LinearMap.snd ℝ E E)
    with hA
  obtain ⟨g, hgA, hgP⟩ := exists_extension_of_le_sublinear (⟨A, 0⟩ : (E × E) →ₗ.[ℝ] ℝ) P
    hPhom hPsub (by
      rintro ⟨z, hz⟩
      simp only [A, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.fst_apply,
        LinearMap.snd_apply] at hz
      have : z.2 = -z.1 := eq_neg_of_add_eq_zero_right hz
      simp only [LinearPMap.mk_apply, LinearMap.zero_apply]
      simp only [P, this, norm_neg]
      linarith [hpL z.1])
  set ℓ : E →ₗ[ℝ] ℝ := g.comp (LinearMap.inl ℝ E E)
  set s := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap ℓ)
  have hs_apply : ∀ d, inner ℝ s d = g (d, 0) := by
    intro d
    rw [InnerProductSpace.toDual_symm_apply]
    simp [ℓ]
  have hs_sub : ∀ d, inner ℝ s d ≤ p d := by
    intro d
    rw [hs_apply]
    have := hgP (d, 0)
    simpa [P] using this
  have hs_norm : ‖s‖ ≤ L := by
    have key : ∀ d, inner ℝ s d ≤ L * ‖d‖ := by
      intro d
      rw [hs_apply]
      have h1 : g (d, -d) = 0 := by
        have := hgA ⟨(d, -d), by simp [A]⟩
        simpa using this
      have h2 : g (d, 0) = g (d, -d) + g (0, d) := by
        rw [← map_add]; simp
      have h3 := hgP (0, d)
      simp only [P, hp0, zero_add] at h3
      linarith
    have := key s
    rw [real_inner_self_eq_norm_sq] at this
    by_cases hs0' : ‖s‖ = 0
    · rw [hs0']; exact hL0
    · have hpos : 0 < ‖s‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hs0')
      nlinarith
  have hmem : ∀ v, v ∈ directionalSubdifferential (liftRealtoEReal f) x ↔
      ∀ d, inner ℝ v d ≤ p d := by
    intro v
    simp only [directionalSubdifferential, Set.mem_setOf_eq, hdd, EReal.coe_le_coe_iff]
  apply le_antisymm
  · apply le_csInf
    · exact ⟨‖s‖, s, (hmem s).mpr hs_sub, rfl⟩
    · rintro _ ⟨v, hv, rfl⟩
      rw [hmem] at hv
      apply max_le (norm_nonneg _)
      apply Real.sSup_le _ (norm_nonneg _)
      rintro _ ⟨x', hx', rfl⟩
      exact hquot v hv x' hx'
  · have hbdd' : BddBelow ((fun v => ‖v‖) '' directionalSubdifferential (liftRealtoEReal f) x) :=
      ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg _⟩
    exact (csInf_le hbdd' ⟨s, (hmem s).mpr hs_sub, rfl⟩).trans hs_norm

end FCA_chap_D_ex5
