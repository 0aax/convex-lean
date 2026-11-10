import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_3_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_3_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_3_5`, so the main result is `FCA_chap_D_1_3_5.FCA_chap_D_1_3_5`.
-/

namespace FCA_chap_D_1_3_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace FCA_D135

set_option linter.unusedSectionVars false

open Set Filter

/-- Real difference quotient. -/
noncomputable def dq (f : E → ℝ) (x h : E) (t : ℝ) : ℝ := (f (x + t • h) - f x) / t

/-- Real directional derivative (as an infimum of difference quotients). -/
noncomputable def dd (f : E → ℝ) (x h : E) : ℝ := sInf (dq f x h '' Ioi 0)

lemma tendsto_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

section
variable {f : E → ℝ} (hf : ConvexOn ℝ univ f) (x : E)
include hf

lemma line_convex (h : E) : ConvexOn ℝ univ (fun τ : ℝ => f (x + τ • h)) := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  have e : x + (μ • a + ν • b) • h = μ • (x + a • h) + ν • (x + b • h) := by
    conv_lhs => rw [← one_smul ℝ x, ← hμν]
    simp only [add_smul, smul_add, smul_smul, smul_eq_mul]
    abel
  simpa only [e] using hf.2 (mem_univ (x + a • h)) (mem_univ (x + b • h)) hμ hν hμν

lemma dq_mono (h : E) : MonotoneOn (dq f x h) (Ioi 0) := by
  intro s hs t ht hst
  have := (line_convex hf x h).secant_mono (mem_univ 0) (mem_univ s) (mem_univ t)
    (ne_of_gt hs) (ne_of_gt ht) hst
  simpa [dq] using this

lemma dq_lower (h : E) {t : ℝ} (ht : 0 < t) : f x - f (x - h) ≤ dq f x h t := by
  have := (line_convex hf x h).secant_mono (mem_univ 0) (mem_univ (-1)) (mem_univ t)
    (by norm_num) (ne_of_gt ht) (by linarith)
  simp only [zero_smul, add_zero, sub_zero, neg_smul, one_smul, ← sub_eq_add_neg] at this
  unfold dq
  convert this using 1
  field_simp
  ring

lemma bdd (h : E) : BddBelow (dq f x h '' Ioi 0) :=
  ⟨f x - f (x - h), by rintro _ ⟨t, ht, rfl⟩; exact dq_lower hf x h ht⟩

lemma tendsto_dd (h : E) : Tendsto (dq f x h) (𝓝[>] 0) (𝓝 (dd f x h)) :=
  (dq_mono hf x h).tendsto_nhdsGT (bdd hf x h)

lemma dd_le (h : E) {t : ℝ} (ht : 0 < t) : dd f x h ≤ dq f x h t :=
  csInf_le (bdd hf x h) (mem_image_of_mem _ ht)

lemma le_dd (h : E) {c : ℝ} (hc : ∀ t, 0 < t → c ≤ dq f x h t) : c ≤ dd f x h :=
  le_csInf (nonempty_Ioi.image _) (by rintro _ ⟨t, ht, rfl⟩; exact hc t ht)

lemma directionalDeriv_eq (h : E) :
    directionalDeriv (liftRealtoEReal f) x h = (dd f x h : EReal) := by
  apply Tendsto.limUnder_eq
  have : Tendsto (fun t => (dq f x h t : EReal)) (𝓝[>] 0) (𝓝 (dd f x h : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp (tendsto_dd hf x h)
  refine this.congr' ?_
  filter_upwards with t
  rfl

lemma dd_smul (h : E) {c : ℝ} (hc : 0 < c) : dd f x (c • h) = c * dd f x h := by
  apply tendsto_nhds_unique (tendsto_dd hf x (c • h))
  have h2 := ((tendsto_dd hf x h).comp (tendsto_mul_nhdsGT hc)).const_mul c
  refine h2.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [Function.comp, dq]
  rw [smul_smul, mul_comm t c]
  have : (0:ℝ) < t := ht
  field_simp

lemma dd_add (h₁ h₂ : E) : dd f x (h₁ + h₂) ≤ dd f x h₁ + dd f x h₂ := by
  have key : ∀ t : ℝ, 0 < t → dq f x (h₁ + h₂) t ≤ dq f x h₁ (2 * t) + dq f x h₂ (2 * t) := by
    intro t ht
    have hc := hf.2 (mem_univ (x + (2 * t) • h₁)) (mem_univ (x + (2 * t) • h₂))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have e : (1/2 : ℝ) • (x + (2 * t) • h₁) + (1/2 : ℝ) • (x + (2 * t) • h₂) = x + t • (h₁ + h₂) := by
      module
    rw [e] at hc
    simp only [smul_eq_mul] at hc
    unfold dq
    rw [div_add_div _ _ (by positivity) (by positivity), div_le_div_iff₀ ht (by positivity)]
    nlinarith
  have hA := tendsto_dd hf x (h₁ + h₂)
  have hB := ((tendsto_dd hf x h₁).comp (tendsto_mul_nhdsGT two_pos)).add
    ((tendsto_dd hf x h₂).comp (tendsto_mul_nhdsGT two_pos))
  refine le_of_tendsto_of_tendsto hA hB ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact key t ht

lemma exists_subgrad (M : Submodule ℝ E) (hM : ∀ m ∈ M, 0 ≤ dd f x m) :
    ∃ s : E, (∀ h, inner ℝ s h ≤ dd f x h) ∧ ∀ m ∈ M, inner ℝ s m = 0 := by
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear ⟨M, 0⟩ (dd f x)
    (fun c hc h => dd_smul hf x h hc) (fun h₁ h₂ => dd_add hf x h₁ h₂)
    (fun m => by simpa using hM m.1 m.2)
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g), ?_, ?_⟩
  · intro h
    rw [InnerProductSpace.toDual_symm_apply]
    exact hg2 h
  · intro m hm
    rw [InnerProductSpace.toDual_symm_apply]
    simpa using hg1 ⟨m, hm⟩

lemma mem_dirSub_iff (s : E) :
    s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔ ∀ h, inner ℝ s h ≤ dd f x h := by
  unfold directionalSubdifferential
  simp only [Set.mem_setOf_eq, directionalDeriv_eq hf x, EReal.coe_le_coe_iff]

end

end FCA_D135

theorem FCA_chap_D_1_3_5
    (f : E → ℝ)
    (x d : E)
    (hf_convex : ConvexOn ℝ Set.univ f)
    (hf_subdiff : 0 ∉ directionalSubdifferential (liftRealtoEReal f) x) :
    let S := sublevelSetFun (liftRealtoEReal f) x
    (d ∈ convexNormalCone x S) ↔
    (∃ (t : ℝ) (s : E),
    (t ≥ 0) ∧ (s ∈ directionalSubdifferential (liftRealtoEReal f) x) ∧ (d = t • s)) := by
  intro S
  have hS : ∀ y, y ∈ S ↔ f y ≤ f x := fun y => EReal.coe_le_coe_iff
  have hsub := FCA_D135.mem_dirSub_iff hf_convex x
  have h0 : ¬ ∀ h, 0 ≤ FCA_D135.dd f x h := by
    intro H
    apply hf_subdiff
    rw [hsub]
    intro h
    simpa using H h
  constructor
  · intro hd
    have hd' : ∀ y, f y ≤ f x → inner ℝ d (y - x) ≤ 0 := fun y hy => hd y ((hS y).2 hy)
    by_cases hd0 : d = 0
    · obtain ⟨s, hs, -⟩ := FCA_D135.exists_subgrad hf_convex x ⊥ (by
        intro m hm
        rw [Submodule.mem_bot] at hm
        subst hm
        have := FCA_D135.dd_smul hf_convex x (0 : E) (two_pos)
        rw [smul_zero] at this
        linarith)
      exact ⟨0, s, le_rfl, (hsub s).2 hs, by simp [hd0]⟩
    · -- for `h` with `⟪d, h⟫ > 0`, `f x < f (x + h)`
      have pos : ∀ h, 0 < inner ℝ d h → f x < f (x + h) := by
        intro h hh
        by_contra hle
        push_neg at hle
        have := hd' (x + h) hle
        rw [add_sub_cancel_left] at this
        linarith
      have pos' : ∀ h, 0 < inner ℝ d h → 0 ≤ FCA_D135.dd f x h := by
        intro h hh
        apply FCA_D135.le_dd hf_convex x h
        intro t ht
        unfold FCA_D135.dq
        apply div_nonneg _ ht.le
        have := pos (t • h) (by rw [real_inner_smul_right]; positivity)
        linarith
      have hdd : 0 < inner ℝ d d := real_inner_self_pos.2 hd0
      -- for `w ⊥ d`, `0 ≤ dd f x w`
      have orth : ∀ w, inner ℝ d w = 0 → 0 ≤ FCA_D135.dd f x w := by
        intro w hw
        have hlim : Filter.Tendsto (fun ε : ℝ => -(ε * FCA_D135.dd f x d)) (𝓝[>] 0) (𝓝 0) := by
          have : Filter.Tendsto (fun ε : ℝ => -(ε * FCA_D135.dd f x d)) (𝓝 0)
              (𝓝 (-((0:ℝ) * FCA_D135.dd f x d))) :=
            ((continuous_id.mul continuous_const).neg).tendsto 0
          simpa using this.mono_left nhdsWithin_le_nhds
        apply le_of_tendsto hlim
        filter_upwards [self_mem_nhdsWithin] with ε hε
        have hε' : (0:ℝ) < ε := hε
        have h1 : 0 ≤ FCA_D135.dd f x (w + ε • d) := by
          apply pos'
          rw [inner_add_right, hw, real_inner_smul_right]
          positivity
        have h2 := FCA_D135.dd_add hf_convex x w (ε • d)
        have h3 := FCA_D135.dd_smul hf_convex x d hε'
        linarith
      obtain ⟨s, hs, hsM⟩ := FCA_D135.exists_subgrad hf_convex x (ℝ ∙ d)ᗮ (fun m hm =>
        orth m ((Submodule.mem_orthogonal_singleton_iff_inner_right).1 hm))
      -- `s` is a multiple of `d`
      have hs_mem : s ∈ (ℝ ∙ d)ᗮᗮ := by
        rw [Submodule.mem_orthogonal]
        intro u hu
        rw [real_inner_comm]
        exact hsM u hu
      rw [Submodule.orthogonal_orthogonal, Submodule.mem_span_singleton] at hs_mem
      obtain ⟨c, hc_eq⟩ := hs_mem
      have hc : 0 < c := by
        by_contra hc
        push_neg at hc
        apply h0
        intro h
        by_cases hh : 0 < inner ℝ d h
        · exact pos' h hh
        · push_neg at hh
          calc 0 ≤ c * inner ℝ d h := mul_nonneg_of_nonpos_of_nonpos hc hh
            _ = inner ℝ s h := by rw [← hc_eq, real_inner_smul_left]
            _ ≤ FCA_D135.dd f x h := hs h
      refine ⟨c⁻¹, s, inv_nonneg.2 hc.le, (hsub s).2 hs, ?_⟩
      rw [← hc_eq, smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
  · rintro ⟨t, s, ht, hs, rfl⟩
    intro y hy
    rw [hS] at hy
    have h1 := (hsub s).1 hs (y - x)
    have h2 := FCA_D135.dd_le hf_convex x (y - x) one_pos
    have h3 : FCA_D135.dq f x (y - x) 1 = f y - f x := by
      simp [FCA_D135.dq]
    have : inner ℝ s (y - x) ≤ 0 := by linarith
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos ht this

end FCA_chap_D_1_3_5
