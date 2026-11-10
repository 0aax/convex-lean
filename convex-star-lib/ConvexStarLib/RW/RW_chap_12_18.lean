import ConvexStarLib.Defs

/-!
# `RW_chap_12_18`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_18` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_18`, so the main result is `RW_chap_12_18.RW_chap_12_18`.
-/

namespace RW_chap_12_18

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem RW_chap_12_18
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C) :
  IsMaximalMonotone (normalCone C) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  -- Regular normals of a convex set satisfy the global variational inequality.
  have hreg : ∀ x_bar v : E, v ∈ regularNormalCone C x_bar →
      x_bar ∈ C ∧ ∀ x ∈ C, inner ℝ v (x - x_bar) ≤ 0 := by
    intro x_bar v h
    obtain ⟨hx, r, hr, V, hV, hVC⟩ := h
    refine ⟨hx, fun x hxC => ?_⟩
    by_contra hcon
    push_neg at hcon
    have hd : x - x_bar ≠ 0 := by
      intro h0
      rw [h0, inner_zero_right] at hcon
      exact lt_irrefl _ hcon
    have hdpos : 0 < ‖x - x_bar‖ := norm_pos_iff.mpr hd
    set c := inner ℝ v (x - x_bar) with hc
    have hεpos : 0 < c / (2 * ‖x - x_bar‖) := by positivity
    have h1 := hr.def hεpos
    have htend : Filter.Tendsto (fun t : ℝ => x_bar + t • (x - x_bar)) (𝓝[>] 0) (𝓝 x_bar) := by
      have : Filter.Tendsto (fun t : ℝ => x_bar + t • (x - x_bar)) (𝓝 0)
          (𝓝 (x_bar + (0:ℝ) • (x - x_bar))) :=
        tendsto_const_nhds.add (Filter.tendsto_id.smul_const _)
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
    obtain ⟨t, ht1, ht2, ht3⟩ :=
      ((htend.eventually h1).and ((htend.eventually hV).and h3)).exists
    have ht0 : 0 < t := ht3.1
    have hyC : x_bar + t • (x - x_bar) ∈ C := by
      have := hC_convex hx hxC (by linarith [ht3.2] : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
      convert this using 1
      rw [smul_sub, sub_smul, one_smul]
      abel
    have key := hVC _ ht2 hyC
    simp only [add_sub_cancel_left, inner_smul_right] at key
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos ht0] at ht1
    rw [abs_of_nonneg (by positivity : (0:ℝ) ≤ t * ‖x - x_bar‖)] at ht1
    have hle : r (x_bar + t • (x - x_bar)) ≤ |r (x_bar + t • (x - x_bar))| := le_abs_self _
    have : t * c ≤ c / (2 * ‖x - x_bar‖) * (t * ‖x - x_bar‖) := le_trans key (le_trans hle ht1)
    have heq : c / (2 * ‖x - x_bar‖) * (t * ‖x - x_bar‖) = t * c / 2 := by
      field_simp
    rw [heq] at this
    nlinarith
  -- Limiting normals of a closed convex set satisfy the same inequality.
  have key1 : ∀ x_bar v : E, v ∈ normalCone C x_bar →
      x_bar ∈ C ∧ ∀ x ∈ C, inner ℝ v (x - x_bar) ≤ 0 := by
    intro x_bar v h
    obtain ⟨xs, vs, hxs, hvs, hmem⟩ := h
    have hxsC : ∀ n, xs n ∈ C := fun n => (hreg _ _ (hmem n)).1
    have hxbar : x_bar ∈ C := hC_closed.mem_of_tendsto hxs (Filter.Eventually.of_forall hxsC)
    refine ⟨hxbar, fun x hxC => ?_⟩
    have hlim : Filter.Tendsto (fun n => inner ℝ (vs n) (x - xs n)) Filter.atTop
        (𝓝 (inner ℝ v (x - x_bar))) :=
      hvs.inner (tendsto_const_nhds.sub hxs)
    exact le_of_tendsto' hlim (fun n => (hreg _ _ (hmem n)).2 x hxC)
  -- Conversely, the variational inequality gives a (constant-sequence) normal.
  have key2 : ∀ x_bar v : E, x_bar ∈ C → (∀ x ∈ C, inner ℝ v (x - x_bar) ≤ 0) →
      v ∈ normalCone C x_bar := by
    intro x_bar v hx hv
    refine ⟨fun _ => x_bar, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_⟩
    refine ⟨hx, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem,
      fun y _ hy => hv y hy⟩
  refine ⟨?_, ?_⟩
  · intro x₀ x₁ v₀ v₁ h₀ h₁
    obtain ⟨hx₀, h₀'⟩ := key1 _ _ h₀
    obtain ⟨hx₁, h₁'⟩ := key1 _ _ h₁
    have a := h₀' x₁ hx₁
    have b := h₁' x₀ hx₀
    have hb : inner ℝ v₁ (x₁ - x₀) = - inner ℝ v₁ (x₀ - x₁) := by
      rw [← inner_neg_right, neg_sub]
    rw [inner_sub_left]
    linarith
  · intro x_hat v_hat hnot
    obtain ⟨p, hpC, hp⟩ := exists_norm_eq_iInf_of_complete_convex hC_nonempty
      hC_closed.isComplete hC_convex (x_hat + v_hat)
    have hp' := (norm_eq_iInf_iff_real_inner_le_zero hC_convex hpC).mp hp
    refine ⟨p, x_hat + v_hat - p, key2 _ _ hpC hp', ?_⟩
    have hrw : v_hat - (x_hat + v_hat - p) = -(x_hat - p) := by abel
    rw [hrw, inner_neg_left, real_inner_self_eq_norm_sq]
    have hne : x_hat - p ≠ 0 := by
      intro h
      have hpx : x_hat = p := sub_eq_zero.mp h
      subst hpx
      apply hnot
      refine key2 _ _ hpC (fun w hw => ?_)
      have := hp' w hw
      rwa [add_sub_cancel_left] at this
    have := norm_pos_iff.mpr hne
    nlinarith

end RW_chap_12_18
