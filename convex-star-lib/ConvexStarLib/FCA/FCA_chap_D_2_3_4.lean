import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_3_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_3_4`, so the main result is `FCA_chap_D_2_3_4.FCA_chap_D_2_3_4`.
-/

namespace FCA_chap_D_2_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_2_3_4 (f : E → ℝ)
    (x₁ x₂ : E)
    (hf_convex : ConvexOn ℝ Set.univ f) :
    ∀ (s : ℝ → E),
    (∀ α ∈ Set.Icc (0 : ℝ) 1, s α ∈ directionalSubdifferential (liftRealtoEReal f) ((1 - α) • x₁ + α • x₂)) →
    IntervalIntegrable (fun α => inner ℝ (s α) (x₂ - x₁)) MeasureTheory.volume 0 1 ∧
    f x₂ - f x₁ = ∫ α in (0 : ℝ)..1, inner ℝ (s α) (x₂ - x₁) := by
  intro s hs
  -- Step 1: subgradient inequality
  have hsub : ∀ (x y v : E), v ∈ directionalSubdifferential (liftRealtoEReal f) x →
      inner ℝ v (y - x) ≤ f y - f x := by
    intro x y v hv
    set d := y - x with hd
    set q : ℝ → ℝ := fun t => (f (x + t • d) - f x) / t with hq
    have hQ : ∀ t, differenceQuotient (liftRealtoEReal f) x d t = ((q t : ℝ) : EReal) := by
      intro t
      simp only [differenceQuotient, liftRealtoEReal, hq]
      rw [EReal.coe_div, EReal.coe_sub]
    have hmono : MonotoneOn q (Set.Ioi 0) := by
      intro a ha b hb hab
      simp only [Set.mem_Ioi] at ha hb
      have hc1 : (0:ℝ) ≤ 1 - a / b := by rw [sub_nonneg, div_le_one hb]; exact hab
      have hc2 : (0:ℝ) ≤ a / b := by positivity
      have hc3 : (1 - a / b) + a / b = 1 := by ring
      have hconv := hf_convex.2 (Set.mem_univ x) (Set.mem_univ (x + b • d)) hc1 hc2 hc3
      have heq : (1 - a / b) • x + (a / b) • (x + b • d) = x + a • d := by
        rw [smul_add, smul_smul, div_mul_cancel₀ a (ne_of_gt hb), sub_smul, one_smul]; abel
      rw [heq, smul_eq_mul, smul_eq_mul] at hconv
      simp only [hq]
      rw [div_le_div_iff₀ ha hb]
      have h1 : (f (x + a • d) - f x) * b ≤ ((a / b) * (f (x + b • d) - f x)) * b := by
        apply mul_le_mul_of_nonneg_right _ hb.le; linarith
      calc (f (x + a • d) - f x) * b ≤ ((a / b) * (f (x + b • d) - f x)) * b := h1
        _ = (f (x + b • d) - f x) * a := by field_simp
    have hmonoE : MonotoneOn (fun t => differenceQuotient (liftRealtoEReal f) x d t)
        (Set.Ioi 0) := by
      intro a ha b hb hab
      simp only [hQ]
      exact EReal.coe_le_coe_iff.mpr (hmono ha hb hab)
    have htend := hmonoE.tendsto_nhdsGT (OrderBot.bddBelow _)
    have hlim : directionalDeriv (liftRealtoEReal f) x d
        = sInf ((fun t => differenceQuotient (liftRealtoEReal f) x d t) '' Set.Ioi 0) := by
      unfold directionalDeriv
      exact htend.limUnder_eq
    have hle : directionalDeriv (liftRealtoEReal f) x d ≤ ((f y - f x : ℝ) : EReal) := by
      rw [hlim]
      refine sInf_le_of_le (b := differenceQuotient (liftRealtoEReal f) x d 1) ?_ ?_
      · exact ⟨1, by norm_num, rfl⟩
      rw [hQ]
      simp [hq, hd]
    simp only [directionalSubdifferential, Set.mem_setOf_eq] at hv
    exact EReal.coe_le_coe_iff.mp ((hv d).trans hle)
  -- Step 2: key inequality along the segment
  set phi : ℝ → ℝ := fun α => f ((1 - α) • x₁ + α • x₂) with hphi
  set g : ℝ → ℝ := fun α => inner ℝ (s α) (x₂ - x₁) with hg
  have hkey : ∀ α ∈ Set.Icc (0:ℝ) 1, ∀ β, (β - α) * g α ≤ phi β - phi α := by
    intro α hα β
    have h := hsub ((1 - α) • x₁ + α • x₂) ((1 - β) • x₁ + β • x₂) (s α) (hs α hα)
    have : (1 - β) • x₁ + β • x₂ - ((1 - α) • x₁ + α • x₂) = (β - α) • (x₂ - x₁) := by module
    rw [this, real_inner_smul_right] at h
    exact h
  -- Step 3: monotonicity and integrability
  have hgmono : MonotoneOn g (Set.Icc 0 1) := by
    intro a ha b hb hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have h1 := hkey a ha b
      have h2 := hkey b hb a
      have hpos : 0 < b - a := sub_pos.mpr h
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hpos
      nlinarith
  have hint : IntervalIntegrable g volume 0 1 := by
    apply MonotoneOn.intervalIntegrable
    rw [Set.uIcc_of_le zero_le_one]
    exact hgmono
  -- Step 4: continuity of phi
  have hfcont : Continuous f := hf_convex.locallyLipschitz.continuous
  have hphicont : Continuous phi := by
    apply hfcont.comp
    fun_prop
  -- Step 5: derivative off a countable set
  set S := {x ∈ Set.Icc (0:ℝ) 1 | ¬ContinuousWithinAt g (Set.Icc 0 1) x} with hS
  have hScount : S.Countable := hgmono.countable_not_continuousWithinAt
  have hderiv : ∀ x ∈ Set.Ioo (0:ℝ) 1 \ S, HasDerivAt phi (g x) x := by
    intro x hx
    obtain ⟨hxI, hxS⟩ := hx
    have hxIcc : x ∈ Set.Icc (0:ℝ) 1 := Set.Ioo_subset_Icc_self hxI
    have hcw : ContinuousWithinAt g (Set.Icc 0 1) x := by
      by_contra h; exact hxS ⟨hxIcc, h⟩
    have hnhds : Set.Icc (0:ℝ) 1 ∈ 𝓝 x := Icc_mem_nhds hxI.1 hxI.2
    have hca : ContinuousAt g x := hcw.continuousAt hnhds
    rw [hasDerivAt_iff_tendsto_slope]
    have hgt : Filter.Tendsto g (𝓝[≠] x) (𝓝 (g x)) := hca.tendsto.mono_left nhdsWithin_le_nhds
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (g := fun y => min (g x) (g y))
      (h := fun y => max (g x) (g y))
    · simpa using (tendsto_const_nhds (x := g x)).min hgt
    · simpa using (tendsto_const_nhds (x := g x)).max hgt
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnhds] with y hy1 hy2
      rw [slope_def_field]
      have h1 := hkey x hxIcc y
      have h2 := hkey y hy2 x
      rcases lt_or_gt_of_ne hy1 with h | h
      · have hneg : y - x < 0 := sub_neg.mpr h
        refine (min_le_right _ _).trans ?_
        rw [le_div_iff_of_neg hneg]
        nlinarith
      · have hpos : 0 < y - x := sub_pos.mpr h
        refine (min_le_left _ _).trans ?_
        rw [le_div_iff₀ hpos]
        nlinarith
    · filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hnhds] with y hy1 hy2
      rw [slope_def_field]
      have h1 := hkey x hxIcc y
      have h2 := hkey y hy2 x
      rcases lt_or_gt_of_ne hy1 with h | h
      · have hneg : y - x < 0 := sub_neg.mpr h
        refine le_trans ?_ (le_max_left _ _)
        rw [div_le_iff_of_neg hneg]
        nlinarith
      · have hpos : 0 < y - x := sub_pos.mpr h
        refine le_trans ?_ (le_max_right _ _)
        rw [div_le_iff₀ hpos]
        nlinarith
  -- Step 6: conclude
  refine ⟨hint, ?_⟩
  have hftc := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le phi g zero_le_one
    hScount hphicont.continuousOn hderiv hint
  rw [hftc]
  simp [hphi]

end FCA_chap_D_2_3_4
