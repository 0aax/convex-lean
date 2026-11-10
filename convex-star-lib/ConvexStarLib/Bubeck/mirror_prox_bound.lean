import ConvexStarLib.Defs

/-!
# `mirror_prox_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/mirror_prox_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace mirror_prox_bound`, so the main result is `mirror_prox_bound.mirror_prox_bound`.
-/

namespace mirror_prox_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem mirror_prox_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (x_prime : ℕ → E)
  (y_prime : ℕ → E)
  (ρ β R : ℝ)
  (x_star : E)
  (hR : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v})
  (hR_pos : R > 0)
  (ht : t ≥ 1) (hρ : ρ > 0)
  (hβ : β > 0)
  (hx_0 : x 0 ∈ 𝓧 ∩ 𝓓)
  (h_mirror_seq : IsMirrorProxSequence 𝓧 𝓓 f phi x y x_prime y_prime (ρ / β))
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓_convex : Convex ℝ 𝓓)
  (h𝓓_open : IsOpen 𝓓)
  (h𝓓_contains : 𝓧 ⊆ closure 𝓓)
  (h_inter_nonempty : Set.Nonempty (𝓧 ∩ 𝓓))
  (hphi_differentiable : DifferentiableOn ℝ phi 𝓓)
  (hphi_mirror_map : IsMirrorMap 𝓓 phi)
  (hphi_strong_convex : StrongConvexOn (𝓧 ∩ 𝓓) ρ phi)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_smooth : IsSmoothOn 𝓧 f β)
  (hf_grad : ∀ z ∈ 𝓧, DifferentiableAt ℝ f z)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, (y (s + 1))) - f x_star ≤
  β * (R ^ 2) / (ρ * t) := by
  obtain ⟨hx0min, hxproj, hyproj, hyp_mem, hxp_mem, hyp_eq, hxp_eq⟩ := h_mirror_seq
  set η : ℝ := ρ / β with hη_def
  have hη : 0 < η := div_pos hρ hβ
  have hηβ : η * β = ρ := by rw [hη_def]; field_simp
  have hS : Convex ℝ (𝓧 ∩ 𝓓) := h𝓧_convex.inter h𝓓_convex
  have hx_mem : ∀ s, x s ∈ 𝓧 ∩ 𝓓 := by
    intro s
    cases s with
    | zero => exact hx_0
    | succ n => exact (hxproj n).1
  have hy_mem : ∀ s, y (s + 1) ∈ 𝓧 ∩ 𝓓 := fun s => (hyproj s).1
  have hphi_diff : ∀ z ∈ 𝓓, DifferentiableAt ℝ phi z := fun z hz =>
    hphi_differentiable.differentiableAt (h𝓓_open.mem_nhds hz)
  -- first-order optimality condition on a convex set
  have first_order : ∀ (g : E → ℝ) (g' : E →L[ℝ] ℝ) (s : Set E) (a : E), Convex ℝ s → a ∈ s →
      IsMinOn g s a → HasFDerivAt g g' a → ∀ u ∈ s, 0 ≤ g' (u - a) := by
    intro g g' s a hs ha hmin hg u hu
    exact hmin.localize.hasFDerivWithinAt_nonneg hg.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hs.segment_subset ha hu))
  -- first-order characterization of strong convexity
  have strong_first_order : ∀ (g : E → ℝ) (m : ℝ) (s : Set E), StrongConvexOn s m g →
      ∀ a ∈ s, ∀ b ∈ s, DifferentiableAt ℝ g b →
      fderiv ℝ g b (a - b) ≤ g a - g b - m / 2 * ‖a - b‖ ^ 2 := by
    intro g m s hg a ha b hb hgb
    have hderiv : HasDerivAt (fun r : ℝ => g (b + r • (a - b))) (fderiv ℝ g b (a - b)) 0 := by
      have h1 : HasDerivAt (fun r : ℝ => b + r • (a - b)) (a - b) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (a - b)).const_add b
      have h2 : HasFDerivAt g (fderiv ℝ g b) (b + (0:ℝ) • (a - b)) := by
        simpa using hgb.hasFDerivAt
      exact h2.comp_hasDerivAt (0:ℝ) h1
    have hslope := hderiv.tendsto_slope_zero_right
    have hlim : Filter.Tendsto (fun r : ℝ => g a - g b - (1 - r) * (m / 2 * ‖a - b‖ ^ 2))
        (𝓝[>] 0) (𝓝 (g a - g b - m / 2 * ‖a - b‖ ^ 2)) := by
      have : Filter.Tendsto (fun r : ℝ => g a - g b - (1 - r) * (m / 2 * ‖a - b‖ ^ 2)) (𝓝 0)
          (𝓝 (g a - g b - (1 - 0) * (m / 2 * ‖a - b‖ ^ 2))) :=
        (continuous_const.sub ((continuous_const.sub continuous_id).mul
          continuous_const)).tendsto 0
      simpa using this.mono_left nhdsWithin_le_nhds
    apply le_of_tendsto_of_tendsto hslope hlim
    filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
    obtain ⟨hr0, hr1⟩ := hr
    obtain ⟨_, hg2⟩ := hg
    have hconv := hg2 hb ha (show (0:ℝ) ≤ 1 - r by linarith) hr0.le (show 1 - r + r = 1 by ring)
    have heq : (1 - r) • b + r • a = b + r • (a - b) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [heq, norm_sub_rev, smul_eq_mul, smul_eq_mul] at hconv
    simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
    rw [inv_mul_le_iff₀ hr0]
    nlinarith
  -- Bregman projection inequality
  have proj_ineq : ∀ yp p, p ∈ bregmanDivergenceProjSet 𝓧 𝓓 phi yp →
      ∀ u ∈ 𝓧 ∩ 𝓓, 0 ≤ (fderiv ℝ phi p - fderiv ℝ phi yp) (u - p) := by
    intro yp p hp u hu
    have hpD : DifferentiableAt ℝ phi p := hphi_diff p hp.1.2
    have hmin : IsMinOn (fun z => bregmanDivergence phi z yp) (𝓧 ∩ 𝓓) p :=
      isMinOn_iff.2 (fun z hz => hp.2 z hz)
    have hder : HasFDerivAt (fun z => bregmanDivergence phi z yp)
        (fderiv ℝ phi p - fderiv ℝ phi yp) p := by
      have h1 : HasFDerivAt (fun z => phi z - phi yp - ((fderiv ℝ phi yp) z - (fderiv ℝ phi yp) yp))
          (fderiv ℝ phi p - fderiv ℝ phi yp) p :=
        (hpD.hasFDerivAt.sub_const (phi yp)).sub
          ((fderiv ℝ phi yp).hasFDerivAt.sub_const ((fderiv ℝ phi yp) yp))
      refine h1.congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
      simp only [bregmanDivergence, map_sub]
    exact first_order _ _ _ _ hS hp.1 hmin hder u hu
  -- one step of mirror prox
  have step : ∀ u ∈ 𝓧 ∩ 𝓓, ∀ s : ℕ, η * (f (y (s + 1)) - f u) ≤
      bregmanDivergence phi u (x s) - bregmanDivergence phi u (x (s + 1)) := by
    intro u hu s
    have hxs := hx_mem s
    have hxs1 := hx_mem (s + 1)
    have hys := hy_mem s
    have p1 := proj_ineq (x_prime (s + 1)) (x (s + 1)) (hxproj s) u hu
    rw [hxp_eq s] at p1
    have p2 := proj_ineq (y_prime (s + 1)) (y (s + 1)) (hyproj s) (x (s + 1)) hxs1
    rw [hyp_eq s] at p2
    have cf : fderiv ℝ f (y (s + 1)) (u - y (s + 1)) ≤ f u - f (y (s + 1)) := by
      have := strong_first_order f 0 𝓧 (strongConvexOn_zero.2 hf_convex) u hu.1 (y (s + 1))
        hys.1 (hf_grad _ hys.1)
      simpa using this
    have sc1 := strong_first_order phi ρ (𝓧 ∩ 𝓓) hphi_strong_convex (y (s + 1)) hys (x s) hxs
      (hphi_diff _ hxs.2)
    have sc2 := strong_first_order phi ρ (𝓧 ∩ 𝓓) hphi_strong_convex (x (s + 1)) hxs1 (y (s + 1))
      hys (hphi_diff _ hys.2)
    have sm : (fderiv ℝ f (y (s + 1)) - fderiv ℝ f (x s)) (y (s + 1) - x (s + 1)) ≤
        β * (‖y (s + 1) - x s‖ * ‖y (s + 1) - x (s + 1)‖) := by
      calc _ ≤ ‖(fderiv ℝ f (y (s + 1)) - fderiv ℝ f (x s)) (y (s + 1) - x (s + 1))‖ :=
            Real.le_norm_self _
        _ ≤ ‖fderiv ℝ f (y (s + 1)) - fderiv ℝ f (x s)‖ * ‖y (s + 1) - x (s + 1)‖ :=
            ContinuousLinearMap.le_opNorm _ _
        _ ≤ (β * ‖y (s + 1) - x s‖) * ‖y (s + 1) - x (s + 1)‖ := by
            gcongr
            exact hf_smooth _ hys.1 _ hxs.1
        _ = β * (‖y (s + 1) - x s‖ * ‖y (s + 1) - x (s + 1)‖) := by ring
    have amgm : ‖y (s + 1) - x s‖ * ‖y (s + 1) - x (s + 1)‖ ≤
        (‖y (s + 1) - x s‖ ^ 2 + ‖x (s + 1) - y (s + 1)‖ ^ 2) / 2 := by
      rw [norm_sub_rev (x (s + 1))]
      nlinarith [sq_nonneg (‖y (s + 1) - x s‖ - ‖y (s + 1) - x (s + 1)‖)]
    have sm' := mul_le_mul_of_nonneg_left sm hη.le
    rw [← mul_assoc, hηβ] at sm'
    have amgm' := mul_le_mul_of_nonneg_left amgm hρ.le
    have cf' := mul_le_mul_of_nonneg_left cf hη.le
    unfold bregmanDivergence
    simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul] at p1 p2 cf' sc1 sc2 sm' ⊢
    linarith
  -- bound on the initial divergence
  have hbdd : BddAbove {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v} := by
    by_contra hnb
    rw [Real.sSup_of_not_bddAbove hnb] at hR
    have : R ^ 2 > 0 := by positivity
    linarith
  have hD0 : ∀ u ∈ 𝓧 ∩ 𝓓, bregmanDivergence phi u (x 0) ≤ R ^ 2 := by
    intro u hu
    have h1 : 0 ≤ fderiv ℝ phi (x 0) (u - x 0) :=
      first_order phi (fderiv ℝ phi (x 0)) (𝓧 ∩ 𝓓) (x 0) hS hx_0 hx0min
        (hphi_diff _ hx_0.2).hasFDerivAt u hu
    have h2 : phi u - phi (x 0) ≤ R ^ 2 := by
      rw [hR]
      exact le_csSup hbdd ⟨u, hu, rfl⟩
    unfold bregmanDivergence
    linarith
  have hDt : ∀ u ∈ 𝓧 ∩ 𝓓, ∀ s, 0 ≤ bregmanDivergence phi u (x s) := by
    intro u hu s
    have h1 := strong_first_order phi ρ (𝓧 ∩ 𝓓) hphi_strong_convex u hu (x s) (hx_mem s)
      (hphi_diff _ (hx_mem s).2)
    have h2 : 0 ≤ ρ / 2 * ‖u - x s‖ ^ 2 := by positivity
    unfold bregmanDivergence
    linarith
  have sum_bound : ∀ u ∈ 𝓧 ∩ 𝓓,
      ∑ s ∈ Finset.range t, (f (y (s + 1)) - f u) ≤ β * R ^ 2 / ρ := by
    intro u hu
    have h1 : η * ∑ s ∈ Finset.range t, (f (y (s + 1)) - f u) ≤
        bregmanDivergence phi u (x 0) - bregmanDivergence phi u (x t) := by
      rw [Finset.mul_sum]
      calc ∑ s ∈ Finset.range t, η * (f (y (s + 1)) - f u)
          ≤ ∑ s ∈ Finset.range t,
              (bregmanDivergence phi u (x s) - bregmanDivergence phi u (x (s + 1))) :=
            Finset.sum_le_sum (fun s _ => step u hu s)
        _ = bregmanDivergence phi u (x 0) - bregmanDivergence phi u (x t) :=
            Finset.sum_range_sub' _ t
    have h2 := hD0 u hu
    have h3 := hDt u hu t
    have h4 : η * ∑ s ∈ Finset.range t, (f (y (s + 1)) - f u) ≤ R ^ 2 := by linarith
    have h5 : β * (η * ∑ s ∈ Finset.range t, (f (y (s + 1)) - f u)) =
        ρ * ∑ s ∈ Finset.range t, (f (y (s + 1)) - f u) := by
      rw [← mul_assoc, mul_comm β η, hηβ]
    have h6 := mul_le_mul_of_nonneg_left h4 hβ.le
    rw [h5] at h6
    rw [le_div_iff₀ hρ]
    linarith
  have ht_pos : (0 : ℝ) < t := Nat.cast_pos.mpr (by omega)
  have ht_ne : (t : ℝ) ≠ 0 := ht_pos.ne'
  have jensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y (s + 1)) ≤
      (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (y (s + 1)) := by
    rw [Finset.smul_sum, Finset.mul_sum]
    have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t : ℝ))
      (p := fun s => y (s + 1)) (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
      (fun i _ => (hy_mem i).1)
    simpa [smul_eq_mul] using this
  have main : ∀ u ∈ 𝓧 ∩ 𝓓, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, y (s + 1)) - f u ≤
      β * R ^ 2 / (ρ * t) := by
    intro u hu
    have h1 := sum_bound u hu
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    have h3 : (1 / (t : ℝ)) * (∑ s ∈ Finset.range t, f (y (s + 1)) - t * f u) ≤
        (1 / (t : ℝ)) * (β * R ^ 2 / ρ) := mul_le_mul_of_nonneg_left h1 (by positivity)
    have h4 : (1 / (t : ℝ)) * (∑ s ∈ Finset.range t, f (y (s + 1)) - t * f u) =
        (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (y (s + 1)) - f u := by
      field_simp
    have h5 : (1 / (t : ℝ)) * (β * R ^ 2 / ρ) = β * R ^ 2 / (ρ * t) := by
      field_simp
    linarith [jensen]
  -- pass from points of 𝓧 ∩ 𝓓 to x_star ∈ 𝓧 ⊆ closure 𝓓
  have hlim : Filter.Tendsto (fun r : ℝ => β * R ^ 2 / (ρ * t) + r * (f (x 0) - f x_star))
      (𝓝[>] 0) (𝓝 (β * R ^ 2 / (ρ * t))) := by
    have : Filter.Tendsto (fun r : ℝ => β * R ^ 2 / (ρ * t) + r * (f (x 0) - f x_star)) (𝓝 0)
        (𝓝 (β * R ^ 2 / (ρ * t) + 0 * (f (x 0) - f x_star))) :=
      (continuous_const.add (continuous_id.mul continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  apply ge_of_tendsto hlim
  filter_upwards [Ioo_mem_nhdsGT one_pos] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have hzD : (1 - r) • x_star + r • x 0 ∈ 𝓓 := by
    have := h𝓓_convex.combo_closure_interior_mem_interior (h𝓓_contains hx_star_mem)
      (by rw [h𝓓_open.interior_eq]; exact hx_0.2) (show (0:ℝ) ≤ 1 - r by linarith) hr0
      (show 1 - r + r = 1 by ring)
    rwa [h𝓓_open.interior_eq] at this
  have hzX : (1 - r) • x_star + r • x 0 ∈ 𝓧 :=
    h𝓧_convex hx_star_mem hx_0.1 (show (0:ℝ) ≤ 1 - r by linarith) hr0.le
      (show 1 - r + r = 1 by ring)
  have h1 := main _ ⟨hzX, hzD⟩
  have h2 := hf_convex.2 hx_star_mem hx_0.1 (show (0:ℝ) ≤ 1 - r by linarith) hr0.le
    (show 1 - r + r = 1 by ring)
  simp only [smul_eq_mul] at h2
  linarith

end mirror_prox_bound
