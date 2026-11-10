import ConvexStarLib.Defs

/-!
# `mirror_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/mirror_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace mirror_descent_bound`, so the main result is `mirror_descent_bound.mirror_descent_bound`.
-/

namespace mirror_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem mirror_descent_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E)
  (𝓓 : Set E)
  (f : E → ℝ)
  (phi : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (g : ℕ → E →L[ℝ] ℝ)
  (ρ L R : ℝ)
  (x_star : E)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧 ∩ 𝓓, phi a - phi (x 0) = v})
  (hR_pos : R > 0)
  (ht : t ≥ 1) (hρ : ρ > 0) (hL : L > 0)
  (hx_0 : x 0 ∈ 𝓧 ∩ 𝓓)
  (h_mirror_seq : IsMirrorDescentSequence 𝓧 𝓓 f phi x y g ((R / L) * Real.sqrt (2 * ρ / t)))
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
  (hg_bounded : ∀ s, ‖g s‖ ≤ L)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, (x s)) - f x_star ≤
  R * L * Real.sqrt (2 / (ρ * t)) := by
  obtain ⟨h0min, hproj, hyD, hgrad, hsub⟩ := h_mirror_seq
  have ht_pos : (0 : ℝ) < t := by
    have : (1 : ℝ) ≤ t := by exact_mod_cast ht
    linarith
  set u : ℝ := Real.sqrt (2 * ρ / t) with hu_def
  have hu_pos : 0 < u := Real.sqrt_pos.mpr (by positivity)
  have hu_sq : u ^ 2 = 2 * ρ / t := Real.sq_sqrt (by positivity)
  set η : ℝ := (R / L) * u with hη_def
  have hη_pos : 0 < η := by positivity
  set S := 𝓧 ∩ 𝓓 with hS_def
  have hS_convex : Convex ℝ S := h𝓧_convex.inter h𝓓_convex
  have hxS : ∀ s, x s ∈ S := by
    intro s
    cases s with
    | zero => exact hx_0
    | succ n => exact (hproj n).1
  have hdiff : ∀ z ∈ 𝓓, HasFDerivAt phi (fderiv ℝ phi z) z := fun z hz =>
    (hphi_differentiable.differentiableAt (h𝓓_open.mem_nhds hz)).hasFDerivAt
  -- first-order optimality over a convex set
  have hopt : ∀ (F : E → ℝ) (F' : E →L[ℝ] ℝ) (a : E), a ∈ S → HasFDerivAt F F' a →
      (∀ z ∈ S, F a ≤ F z) → ∀ z ∈ S, 0 ≤ F' (z - a) := by
    intro F F' a ha hF hmin z hz
    have hloc : IsLocalMinOn F S a := IsMinOn.localize (fun w hw => hmin w hw)
    exact hloc.hasFDerivWithinAt_nonneg hF.hasFDerivWithinAt
      (sub_mem_posTangentConeAt_of_segment_subset (hS_convex.segment_subset ha hz))
  -- strong convexity, first order
  have hsc : ∀ a ∈ S, ∀ b ∈ S,
      phi a + fderiv ℝ phi a (b - a) + ρ / 2 * ‖b - a‖ ^ 2 ≤ phi b := by
    intro a ha b hb
    set c := ρ / 2 * ‖b - a‖ ^ 2 with hc
    have hk : HasDerivAt (fun τ : ℝ => phi (a + τ • (b - a))) (fderiv ℝ phi a (b - a)) 0 := by
      have h1 : HasDerivAt (fun τ : ℝ => a + τ • (b - a)) (b - a) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (b - a)).const_add a
      have h2 : HasFDerivAt phi (fderiv ℝ phi a) (a + (0:ℝ) • (b - a)) := by
        simpa using hdiff a ha.2
      exact h2.comp_hasDerivAt (0:ℝ) h1
    have hslope := hk.tendsto_slope_zero_right
    simp only [zero_add, zero_smul, add_zero] at hslope
    have hlim : Filter.Tendsto (fun τ : ℝ => phi b - phi a - (1 - τ) * c) (𝓝[>] 0)
        (𝓝 (phi b - phi a - c)) := by
      have : Filter.Tendsto (fun τ : ℝ => phi b - phi a - (1 - τ) * c) (𝓝 0)
          (𝓝 (phi b - phi a - (1 - 0) * c)) :=
        ((continuous_const.sub ((continuous_const.sub continuous_id).mul continuous_const)).tendsto 0)
      simpa using this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ),
        τ⁻¹ • (phi (a + τ • (b - a)) - phi a) ≤ phi b - phi a - (1 - τ) * c := by
      filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with τ hτ
      obtain ⟨hτ0, hτ1⟩ := hτ
      have hconv := hphi_strong_convex.2 ha hb (show (0:ℝ) ≤ 1 - τ by linarith) hτ0.le (show 1 - τ + τ = 1 by ring)
      have heq : (1 - τ) • a + τ • b = a + τ • (b - a) := by
        rw [smul_sub, sub_smul, one_smul]; abel
      rw [heq, norm_sub_rev] at hconv
      simp only [smul_eq_mul] at hconv ⊢
      rw [← hc] at hconv
      rw [inv_mul_le_iff₀ hτ0]
      linarith
    have := le_of_tendsto_of_tendsto hslope hlim hev
    linarith
  -- optimality of the Bregman projection
  have hpyth : ∀ s, ∀ z ∈ S,
      0 ≤ (fderiv ℝ phi (x (s+1)) - fderiv ℝ phi (y (s+1))) (z - x (s+1)) := by
    intro s z hz
    have hmem := (hproj s).1
    have hmin : ∀ w ∈ S, phi (x (s+1)) - fderiv ℝ phi (y (s+1)) (x (s+1)) ≤
        phi w - fderiv ℝ phi (y (s+1)) w := by
      intro w hw
      have := (hproj s).2 w hw
      unfold bregmanDivergence at this
      simp only [map_sub] at this
      linarith
    have hF : HasFDerivAt (fun w => phi w - fderiv ℝ phi (y (s+1)) w)
        (fderiv ℝ phi (x (s+1)) - fderiv ℝ phi (y (s+1))) (x (s+1)) :=
      (hdiff _ hmem.2).sub (fderiv ℝ phi (y (s+1))).hasFDerivAt
    exact hopt _ _ _ hmem hF hmin z hz
  -- optimality of x 0
  have hx0opt : ∀ z ∈ S, 0 ≤ fderiv ℝ phi (x 0) (z - x 0) :=
    hopt phi _ (x 0) hx_0 (hdiff _ hx_0.2) (fun w hw => h0min hw)
  -- the R² bound
  have hbdd : BddAbove {v | ∃ a ∈ S, phi a - phi (x 0) = v} := by
    by_contra hnb
    rw [Real.sSup_of_not_bddAbove hnb] at hR_sq
    have : 0 < R ^ 2 := by positivity
    linarith
  have hR : ∀ z ∈ S, phi z - phi (x 0) ≤ R ^ 2 := by
    intro z hz
    rw [hR_sq]
    exact le_csSup hbdd ⟨z, hz, rfl⟩
  -- one step
  have hstep : ∀ z ∈ S, ∀ s, η * (f (x s) - f z) ≤
      bregmanDivergence phi z (x s) - bregmanDivergence phi z (x (s+1)) +
        η ^ 2 * L ^ 2 / (2 * ρ) := by
    intro z hz s
    have h1 := hsub s z hz.1
    have h1' := mul_le_mul_of_nonneg_left h1 hη_pos.le
    have h2 := hpyth s z hz
    have h3 := hsc (x s) (hxS s) (x (s+1)) (hxS (s+1))
    set r := ‖x (s+1) - x s‖ with hr
    have h4 : g s (x s - x (s+1)) ≤ L * r := by
      calc g s (x s - x (s+1)) ≤ ‖g s (x s - x (s+1))‖ := Real.le_norm_self _
        _ ≤ ‖g s‖ * ‖x s - x (s+1)‖ := (g s).le_opNorm _
        _ ≤ L * ‖x s - x (s+1)‖ := by gcongr; exact hg_bounded s
        _ = L * r := by rw [hr, norm_sub_rev]
    have h4' := mul_le_mul_of_nonneg_left h4 hη_pos.le
    have h5 : η * (L * r) ≤ ρ / 2 * r ^ 2 + η ^ 2 * L ^ 2 / (2 * ρ) := by
      have key : ρ / 2 * r ^ 2 + η ^ 2 * L ^ 2 / (2 * ρ) - η * (L * r) =
          (ρ * r - η * L) ^ 2 / (2 * ρ) := by
        field_simp
        ring
      have : 0 ≤ (ρ * r - η * L) ^ 2 / (2 * ρ) := by positivity
      linarith
    rw [hgrad s] at h2
    unfold bregmanDivergence
    simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      smul_eq_mul, mul_add, mul_sub] at h1' h2 h3 h4' ⊢
    linarith
  -- telescoping
  have hsum : ∀ z ∈ S, η * (∑ s ∈ Finset.range t, f (x s) - t * f z) ≤
      R ^ 2 + t * (η ^ 2 * L ^ 2 / (2 * ρ)) := by
    intro z hz
    have h1 : ∑ s ∈ Finset.range t, η * (f (x s) - f z) ≤ ∑ s ∈ Finset.range t,
        (bregmanDivergence phi z (x s) - bregmanDivergence phi z (x (s+1)) +
          η ^ 2 * L ^ 2 / (2 * ρ)) :=
      Finset.sum_le_sum (fun s _ => hstep z hz s)
    rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => bregmanDivergence phi z (x i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul] at h1
    have h2 : bregmanDivergence phi z (x 0) ≤ R ^ 2 := by
      have := hx0opt z hz
      have := hR z hz
      unfold bregmanDivergence
      linarith
    have h3 : 0 ≤ bregmanDivergence phi z (x t) := by
      have := hsc (x t) (hxS t) z hz
      have : 0 ≤ ρ / 2 * ‖z - x t‖ ^ 2 := by positivity
      unfold bregmanDivergence
      linarith
    linarith
  -- the bound for comparators in S
  have hsqrt : Real.sqrt (2 / (ρ * t)) = u / ρ := by
    rw [show (2:ℝ) / (ρ * t) = (u / ρ) ^ 2 by rw [div_pow, hu_sq]; field_simp]
    exact Real.sqrt_sq (by positivity)
  have htu : (t:ℝ) * u ^ 2 = 2 * ρ := by rw [hu_sq]; field_simp
  have hB : ∀ z ∈ S, (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s) - f z ≤
      R * L * Real.sqrt (2 / (ρ * t)) := by
    intro z hz
    have h := hsum z hz
    set A := ∑ s ∈ Finset.range t, f (x s) - t * f z with hA
    have e1 : (t:ℝ) * (η ^ 2 * L ^ 2 / (2 * ρ)) = R ^ 2 := by
      rw [hη_def]
      field_simp
      linear_combination htu
    rw [e1] at h
    have h' : u * A ≤ 2 * R * L := by
      have e2 : η * A = R / L * (u * A) := by rw [hη_def]; ring
      rw [e2] at h
      have hLR : 0 ≤ L / R := by positivity
      calc u * A = (L / R) * (R / L * (u * A)) := by field_simp
        _ ≤ (L / R) * (R ^ 2 + R ^ 2) := by gcongr
        _ = 2 * R * L := by field_simp; ring
    have e3 : (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s) - f z = A / t := by
      rw [hA]; field_simp
    rw [e3, hsqrt, div_le_iff₀ ht_pos]
    have e4 : R * L * (u / ρ) * t = 2 * R * L / u := by
      field_simp
      linear_combination htu
    rw [e4, le_div_iff₀ hu_pos]
    linarith
  -- Jensen
  have hjensen : f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s) ≤
      (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s) := by
    have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t:ℝ)) (p := x)
      (fun _ _ => by positivity) (by simp [Finset.sum_const, Finset.card_range]; field_simp)
      (fun s _ => (hxS s).1)
    simpa [Finset.smul_sum, Finset.mul_sum] using this
  -- limiting argument
  set avg := (1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s with havg
  set B := R * L * Real.sqrt (2 / (ρ * t)) with hB_def
  have hzS : ∀ τ ∈ Set.Ioc (0:ℝ) 1, (1 - τ) • x_star + τ • x 0 ∈ S := by
    intro τ hτ
    constructor
    · exact h𝓧_convex hx_star_mem hx_0.1 (by linarith [hτ.2]) hτ.1.le (by ring)
    · have := h𝓓_convex.combo_closure_interior_mem_interior (h𝓓_contains hx_star_mem)
        (by rw [h𝓓_open.interior_eq]; exact hx_0.2) (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ)
        hτ.1 (by ring)
      rwa [h𝓓_open.interior_eq] at this
  have hfz : ∀ τ ∈ Set.Ioc (0:ℝ) 1, f avg - B ≤ (1 - τ) * f x_star + τ * f (x 0) := by
    intro τ hτ
    have h1 := hB _ (hzS τ hτ)
    have h2 := hf_convex.2 hx_star_mem hx_0.1 (by linarith [hτ.2] : (0:ℝ) ≤ 1 - τ) hτ.1.le
      (by ring)
    simp only [smul_eq_mul] at h2
    linarith
  have htend : Filter.Tendsto (fun τ : ℝ => (1 - τ) * f x_star + τ * f (x 0)) (𝓝[>] 0)
      (𝓝 (f x_star)) := by
    have hc : Continuous (fun τ : ℝ => (1 - τ) * f x_star + τ * f (x 0)) := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_mul, zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), f avg - B ≤ (1 - τ) * f x_star + τ * f (x 0) := by
    filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with τ hτ
    exact hfz τ hτ
  have := ge_of_tendsto htend hev
  linarith

end mirror_descent_bound
