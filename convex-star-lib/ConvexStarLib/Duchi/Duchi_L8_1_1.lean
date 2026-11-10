import ConvexStarLib.Defs

/-!
# `Duchi_L8_1_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_L8_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_L8_1_1`, so the main result is `Duchi_L8_1_1.Duchi_L8_1_1`.
-/

namespace Duchi_L8_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem Duchi_L8_1_1 {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (hf_diff : ContDiffOn ℝ 3 f (interior 𝓧))
  (hf_sc : IsSelfConcordant 𝓧 f 2)
  (hf_strict_convex : HasPosDefHessianOn 𝓧 f)
  (hf_boundary : BlowsUpOnBoundary 𝓧 f)
  (h𝓧_int : Set.Nonempty (interior 𝓧))
  (hf_bdd_below : BddBelow (f '' interior 𝓧)) :
  ∃ x₀ ∈ interior 𝓧, IsMinOn f (interior 𝓧) x₀ := by
  have key_1d : ∀ (phi u g j : ℝ → ℝ) (m : ℝ),
      (∀ t, 0 ≤ t → HasDerivAt phi (u t) t) →
      (∀ t, 0 ≤ t → HasDerivAt u (g t) t) →
      (∀ t, 0 ≤ t → HasDerivAt g (j t) t) →
      (∀ t, 0 ≤ t → 0 < g t) →
      (∀ t, 0 ≤ t → |j t| ≤ 2 * (Real.sqrt (g t))^3) →
      (∀ t, 0 ≤ t → m ≤ phi t) →
      (∀ t, 0 ≤ t → phi t ≤ phi 0) → False := by
    intro phi u g j m hphi hu hg hgpos hj hlow hup
    set c := (Real.sqrt (g 0))⁻¹ with hc
    have hsq0 : 0 < Real.sqrt (g 0) := Real.sqrt_pos.mpr (hgpos 0 le_rfl)
    have hcpos : 0 < c := inv_pos.mpr hsq0
    -- Step 1: sq t = (sqrt (g t))⁻¹ satisfies sq t ≤ c + t
    have hsq : ∀ t, 0 ≤ t → (Real.sqrt (g t))⁻¹ ≤ c + t := by
      intro t ht
      have hderiv : ∀ s ∈ Set.Ici (0:ℝ), HasDerivWithinAt (fun s => (Real.sqrt (g s))⁻¹)
          (-(j s / (2 * Real.sqrt (g s))) / (Real.sqrt (g s))^2) (Set.Ici 0) s := by
        intro s hs
        have h1 := (hg s hs).sqrt (hgpos s hs).ne'
        have h2 := h1.inv (Real.sqrt_pos.mpr (hgpos s hs)).ne'
        exact h2.hasDerivWithinAt
      have hbound : ∀ s ∈ Set.Ici (0:ℝ),
          ‖-(j s / (2 * Real.sqrt (g s))) / (Real.sqrt (g s))^2‖ ≤ 1 := by
        intro s hs
        have hsq := Real.sqrt_pos.mpr (hgpos s hs)
        rw [Real.norm_eq_abs, abs_div, abs_neg, abs_div,
          abs_of_pos (by positivity : (0:ℝ) < 2 * Real.sqrt (g s)),
          abs_of_pos (by positivity : (0:ℝ) < Real.sqrt (g s) ^ 2)]
        rw [div_div, div_le_one (by positivity)]
        calc |j s| ≤ 2 * Real.sqrt (g s) ^ 3 := hj s hs
          _ = 2 * Real.sqrt (g s) * Real.sqrt (g s) ^ 2 := by ring
      have := (convex_Ici (0:ℝ)).norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
        Set.self_mem_Ici ht
      simp only [Real.norm_eq_abs, sub_zero, one_mul] at this
      have h3 := (abs_le.mp this).2
      rw [abs_of_nonneg ht] at h3
      linarith
    -- Step 2: g t ≥ 1/(c+t)^2
    have hglow : ∀ t, 0 ≤ t → 1 / (c + t)^2 ≤ g t := by
      intro t ht
      have h1 := hsq t ht
      have hsq := Real.sqrt_pos.mpr (hgpos t ht)
      have hct : 0 < c + t := by linarith
      have h2 : 1 / (c + t) ≤ Real.sqrt (g t) := by
        rw [div_le_iff₀ hct]
        have := mul_le_mul_of_nonneg_left h1 hsq.le
        rw [mul_inv_cancel₀ hsq.ne'] at this
        linarith
      calc 1 / (c+t)^2 = (1/(c+t))^2 := (one_div_pow (c+t) 2).symm
        _ ≤ (Real.sqrt (g t))^2 := by gcongr
        _ = g t := Real.sq_sqrt (hgpos t ht).le
    -- Step 3: u monotone on [0, ∞)
    have humono : MonotoneOn u (Set.Ici 0) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := g)
      · intro t ht; exact (hu t ht).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Ici] at ht; exact (hu t (le_of_lt ht)).hasDerivWithinAt
      · intro t ht; rw [interior_Ici] at ht; exact (hgpos t ht.le).le
    -- Step 4: u t ≤ 0 for t ≥ 0
    have hunonpos : ∀ t, 0 ≤ t → u t ≤ 0 := by
      intro t₀ ht₀
      by_contra hpos
      push_neg at hpos
      have hphit₀ := hup t₀ ht₀
      set T := t₀ + (phi 0 - phi t₀ + 1) / u t₀ with hTdef
      have hdpos : 0 < (phi 0 - phi t₀ + 1) / u t₀ := div_pos (by linarith) hpos
      have hT : t₀ < T := by linarith
      obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope phi u hT
        (fun x hx => (hphi x (le_trans ht₀ hx.1)).continuousAt.continuousWithinAt)
        (fun x hx => hphi x (le_trans ht₀ hx.1.le))
      have hmono : u t₀ ≤ u ξ := humono ht₀ (le_trans ht₀ hξ.1.le) hξ.1.le
      have hTt : 0 < T - t₀ := by linarith
      rw [eq_div_iff hTt.ne'] at hξeq
      have h1 : u t₀ * (T - t₀) ≤ phi T - phi t₀ := by
        rw [← hξeq]; exact mul_le_mul_of_nonneg_right hmono hTt.le
      have h2 : u t₀ * (T - t₀) = phi 0 - phi t₀ + 1 := by
        rw [hTdef]; field_simp; ring
      have h3 := hup T (by linarith)
      linarith
    -- Step 5: w t = u t + 1/(c+t) is monotone on [0,∞)
    have hwmono : MonotoneOn (fun t => u t + 1/(c+t)) (Set.Ici 0) := by
      have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => u t + 1/(c+t)) (g t - 1/(c+t)^2) t := by
        intro t ht
        have hct : c + t ≠ 0 := by linarith
        have h1 : HasDerivAt (fun t => c + t) 1 t := (hasDerivAt_id t).const_add c
        have h2 : HasDerivAt (fun s => 1/(c+s)) (-1/(c+t)^2) t := by
          have := (hasDerivAt_const t (1:ℝ)).div h1 hct
          convert this using 1; ring
        have h3 := (hu t ht).add h2
        convert h3 using 1; ring
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) (f' := fun t => g t - 1/(c+t)^2)
      · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).hasDerivWithinAt
      · intro t ht; rw [interior_Ici] at ht; have := hglow t ht.le; linarith
    -- Step 6: w t ≤ 0
    have hwnonpos : ∀ t, 0 ≤ t → u t + 1/(c+t) ≤ 0 := by
      intro t₁ ht₁
      by_contra hpos; push_neg at hpos
      set w₁ := u t₁ + 1/(c+t₁) with hw₁
      set T := t₁ + 1/w₁ with hTdef
      have hT0 : 0 < 1 / w₁ := by positivity
      have hTt : t₁ ≤ T := by linarith
      have h1 : w₁ ≤ u T + 1/(c+T) := hwmono ht₁ (le_trans ht₁ hTt) hTt
      have h2 : 1/(c+T) < w₁ := by
        rw [div_lt_iff₀ (by linarith)]
        have : 1 = w₁ * (1 / w₁) := by field_simp
        nlinarith
      have := hunonpos T (by linarith)
      linarith
    -- Step 7: F t = phi t + log (c + t) antitone on [0,∞)
    have hFanti : AntitoneOn (fun t => phi t + Real.log (c + t)) (Set.Ici 0) := by
      have hd : ∀ t, 0 ≤ t → HasDerivAt (fun t => phi t + Real.log (c + t)) (u t + 1/(c+t)) t := by
        intro t ht
        have hct : c + t ≠ 0 := by linarith
        have h1 : HasDerivAt (fun t => c + t) 1 t := (hasDerivAt_id t).const_add c
        have h2 := h1.log hct
        exact (hphi t ht).add h2
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := fun t => u t + 1/(c+t))
      · intro t ht; exact (hd t ht).continuousAt.continuousWithinAt
      · intro t ht; rw [interior_Ici] at ht; exact (hd t (le_of_lt ht)).hasDerivWithinAt
      · intro t ht; rw [interior_Ici] at ht; exact hwnonpos t ht.le
    -- Step 8: contradiction
    have hm0 := hlow 0 le_rfl
    set T := c * Real.exp (phi 0 - m + 1) - c with hTdef
    have hexp : 1 ≤ Real.exp (phi 0 - m + 1) := by
      exact Real.one_le_exp (by linarith)
    have hT : 0 ≤ T := by
      rw [hTdef]; nlinarith
    have h1 := hFanti (Set.self_mem_Ici) hT hT
    simp only [add_zero] at h1
    have hcT : c + T = c * Real.exp (phi 0 - m + 1) := by rw [hTdef]; ring
    rw [hcT, Real.log_mul hcpos.ne' (Real.exp_pos _).ne', Real.log_exp] at h1
    have h2 := hlow T hT
    linarith
  classical
  set U := interior 𝓧 with hU_def
  have hUo : IsOpen U := isOpen_interior
  obtain ⟨x₀, hx₀⟩ := h𝓧_int
  obtain ⟨m, hm⟩ := hf_bdd_below
  have hm' : ∀ y ∈ U, m ≤ f y := fun y hy => hm ⟨y, hy, rfl⟩
  have hcont : ContinuousOn f U := hf_diff.continuousOn
  -- differentiability facts
  have hdf : ∀ x ∈ U, HasFDerivAt f (fderiv ℝ f x) x := fun x hx =>
    ((hf_diff.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hx)).hasFDerivAt
  have hgradC : ContDiffOn ℝ 2 (gradient f) U := by
    have h1 : ContDiffOn ℝ 2 (fderiv ℝ f) U := hf_diff.fderiv_of_isOpen hUo (by norm_num)
    exact (InnerProductSpace.toDual ℝ _).symm.contDiff.comp_contDiffOn h1
  have hdgrad : ∀ x ∈ U, HasFDerivAt (gradient f) (hessianOperator f x) x := fun x hx =>
    ((hgradC.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hx)).hasFDerivAt
  have hhessC : ContDiffOn ℝ 1 (hessianOperator f) U := hgradC.fderiv_of_isOpen hUo (by norm_num)
  have hdhess : ∀ x ∈ U, HasFDerivAt (hessianOperator f) (jerkOperator f x) x := fun x hx =>
    ((hhessC.differentiableOn (by norm_num)).differentiableAt (hUo.mem_nhds hx)).hasFDerivAt
  -- the sublevel set
  set L : Set (EuclideanSpace ℝ (Fin n)) := {x | x ∈ U ∧ f x ≤ f x₀} with hL_def
  have hLU : L ⊆ U := fun x hx => hx.1
  have hx₀L : x₀ ∈ L := ⟨hx₀, le_rfl⟩
  have hLconv : Convex ℝ L := hf_sc.1.convex_le (f x₀)
  have hLclosed : IsClosed L := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    have hne : (𝓝[L] y).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hy
    by_cases hyU : y ∈ U
    · refine ⟨hyU, ?_⟩
      have hca : ContinuousAt f y := hcont.continuousAt (hUo.mem_nhds hyU)
      have h1 : Filter.Tendsto f (𝓝[L] y) (𝓝 (f y)) := hca.tendsto.mono_left nhdsWithin_le_nhds
      exact le_of_tendsto h1 (eventually_nhdsWithin_of_forall (fun x hx => hx.2))
    · exfalso
      have hyfr : y ∈ frontier 𝓧 := ⟨closure_mono interior_subset (closure_mono hLU hy), hyU⟩
      have h2 : ∀ᶠ z in 𝓝[L] y, f x₀ + 1 ≤ f z :=
        Filter.Eventually.filter_mono (nhdsWithin_mono y hLU) (hf_boundary y hyfr (f x₀ + 1))
      have h3 : ∀ᶠ z in 𝓝[L] y, z ∈ L := self_mem_nhdsWithin
      obtain ⟨z, hz1, hz2⟩ := (h2.and h3).exists
      linarith [hz2.2]
  have hLbdd : Bornology.IsBounded L := by
    by_contra hnb
    have hfar : ∀ k : ℕ, ∃ x ∈ L, (k:ℝ) < ‖x - x₀‖ := by
      intro k
      by_contra hcon
      push_neg at hcon
      apply hnb
      rw [Metric.isBounded_iff_subset_closedBall x₀]
      exact ⟨k, fun x hx => by rw [Metric.mem_closedBall, dist_eq_norm]; exact hcon x hx⟩
    choose xs hxsL hxsfar using hfar
    set ds : ℕ → EuclideanSpace ℝ (Fin n) := fun k => ‖xs k - x₀‖⁻¹ • (xs k - x₀) with hds
    have hds_mem : ∀ k, ds k ∈ Metric.sphere (0:EuclideanSpace ℝ (Fin n)) 1 := by
      intro k
      have hpos : 0 < ‖xs k - x₀‖ := lt_of_le_of_lt (Nat.cast_nonneg k) (hxsfar k)
      simp [hds, norm_smul, hpos.ne']
    obtain ⟨d, hd_mem, sq, hsqmono, hsqlim⟩ := (isCompact_sphere (0:EuclideanSpace ℝ (Fin n)) 1).tendsto_subseq hds_mem
    have hd0 : d ≠ 0 := by
      intro h; rw [h] at hd_mem; simp at hd_mem
    have hray : ∀ t : ℝ, 0 ≤ t → x₀ + t • d ∈ L := by
      intro t ht
      apply hLclosed.mem_of_tendsto ((hsqlim.const_smul t).const_add x₀)
      rw [Filter.eventually_atTop]
      refine ⟨⌈t⌉₊, fun k hk => ?_⟩
      have h1 : t ≤ (sq k : ℝ) := le_trans (Nat.le_ceil t) (by exact_mod_cast le_trans hk (hsqmono.id_le k))
      have h2 : t < ‖xs (sq k) - x₀‖ := lt_of_le_of_lt h1 (hxsfar (sq k))
      have hpos : 0 < ‖xs (sq k) - x₀‖ := lt_of_le_of_lt ht h2
      have hmem := hLconv.add_smul_sub_mem hx₀L (hxsL (sq k)) (t := t / ‖xs (sq k) - x₀‖)
        ⟨div_nonneg ht hpos.le, (div_le_one hpos).mpr h2.le⟩
      convert hmem using 2
      simp [hds, smul_smul, div_eq_mul_inv]
    have hp : ∀ t : ℝ, 0 ≤ t → x₀ + t • d ∈ U := fun t ht => (hray t ht).1
    have hpd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => x₀ + t • d) d t := by
      intro t
      simpa using ((hasDerivAt_id t).smul_const d).const_add x₀
    apply key_1d (fun t => f (x₀ + t • d)) (fun t => inner ℝ d (gradient f (x₀ + t • d)))
      (fun t => inner ℝ d (hessianOperator f (x₀ + t • d) d))
      (fun t => inner ℝ d (jerkOperator f (x₀ + t • d) d d)) m
    · intro t ht
      have h := (hdf _ (hp t ht)).comp_hasDerivAt t (hpd t)
      have heq : (fderiv ℝ f (x₀ + t • d)) d = inner ℝ d (gradient f (x₀ + t • d)) := by
        rw [real_inner_comm]; simp [gradient]
      rw [← heq]; exact h
    · intro t ht
      have h1 := (hdgrad _ (hp t ht)).comp_hasDerivAt t (hpd t)
      have h3 := (innerSL ℝ d).hasFDerivAt.comp_hasDerivAt t h1
      simpa using h3
    · intro t ht
      have h1 := (hdhess _ (hp t ht)).comp_hasDerivAt t (hpd t)
      have h2 : HasDerivAt (fun s => hessianOperator f (x₀ + s • d) d)
          (jerkOperator f (x₀ + t • d) d d) t := by
        have := h1.clm_apply (hasDerivAt_const t d)
        simpa using this
      have h3 := (innerSL ℝ d).hasFDerivAt.comp_hasDerivAt t h2
      simpa using h3
    · intro t ht
      exact hf_strict_convex _ (hp t ht) d hd0
    · intro t ht
      exact hf_sc.2.2.1 _ (hp t ht) d
    · intro t ht
      exact hm' _ (hp t ht)
    · intro t ht
      simpa using (hray t ht).2
  have hLcpt : IsCompact L := Metric.isCompact_of_isClosed_isBounded hLclosed hLbdd
  obtain ⟨x, hxL, hxmin⟩ := hLcpt.exists_isMinOn ⟨x₀, hx₀L⟩ (hcont.mono hLU)
  refine ⟨x, hxL.1, isMinOn_iff.mpr fun y hy => ?_⟩
  by_cases hyL : f y ≤ f x₀
  · exact isMinOn_iff.mp hxmin y ⟨hy, hyL⟩
  · push_neg at hyL
    linarith [hxL.2]

end Duchi_L8_1_1
