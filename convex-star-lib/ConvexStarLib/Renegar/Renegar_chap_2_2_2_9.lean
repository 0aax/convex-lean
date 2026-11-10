import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_2_9`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_2_9` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_2_9`, so the main result is `Renegar_chap_2_2_2_9.Renegar_chap_2_2_2_9`.
-/

namespace Renegar_chap_2_2_2_9

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Renegar_chap_2_2_2_9 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x : ℕ → E)
  (x_tilde : E)
  (hf_sc : IsSelfConcordantLocalNorm f Df)
  (hx : ∀ i, x i ∈ Df)
  (hx_tilde : x_tilde ∈ frontier Df) :
  Filter.Tendsto x Filter.atTop (𝓝 x_tilde) →
  (Filter.Tendsto (fun i => f (x i)) Filter.atTop Filter.atTop ∧
  Filter.Tendsto (fun i => ‖gradient f (x i)‖) Filter.atTop Filter.atTop) := by
  intro hlim
  -- regularity
  have hfd : ∀ y ∈ Df, DifferentiableAt ℝ f y := fun y hy =>
    (hf_C2.differentiableOn (by norm_num)).differentiableAt (h_Df_open.mem_nhds hy)
  have hgd : ∀ y ∈ Df, DifferentiableAt ℝ (fun z => gradient f z) y := by
    intro y hy
    by_contra hnd
    obtain ⟨v, hv⟩ := exists_ne (0 : E)
    have h := h_Df_pd y hy v hv
    simp only [localInnerProd, hessianOperator, fderiv_zero_of_not_differentiableAt hnd,
      ContinuousLinearMap.zero_apply, inner_zero_right, lt_self_iff_false] at h
  -- Dikin
  have hdikin : ∀ y ∈ Df, ∀ z, z ∉ Df → 1 ≤ localInnerProd f y (z - y) (z - y) := by
    intro y hy z hz
    by_contra hlt
    push_neg at hlt
    apply hz
    apply (hf_sc y hy).1
    show localNorm f y (z - y) < 1
    unfold localNorm
    rw [Real.sqrt_lt' one_pos]
    simpa using hlt
  -- bilinearity
  have hscale : ∀ y d : E, ∀ c : ℝ,
      localInnerProd f y (c • d) (c • d) = c ^ 2 * localInnerProd f y d d := by
    intro y d c
    simp only [localInnerProd, map_smul, inner_smul_left, inner_smul_right, RCLike.conj_to_real]
    ring
  -- derivative of φ
  have hderiv_f : ∀ y d : E, ∀ t : ℝ, y + t • d ∈ Df →
      HasDerivAt (fun t : ℝ => f (y + t • d)) (inner ℝ (gradient f (y + t • d)) d) t := by
    intro y d t ht
    have h1 : HasDerivAt (fun t : ℝ => y + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    have h2 := (hfd _ ht).hasGradientAt.hasFDerivAt.comp_hasDerivAt t h1
    simpa [Function.comp_def, InnerProductSpace.toDual_apply_apply] using h2
  have hderiv_g : ∀ y d : E, ∀ t : ℝ, y + t • d ∈ Df →
      HasDerivAt (fun t : ℝ => inner ℝ (gradient f (y + t • d)) d)
        (localInnerProd f (y + t • d) d d) t := by
    intro y d t ht
    have h1 : HasDerivAt (fun t : ℝ => y + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add y
    have h2 := (hgd _ ht).hasFDerivAt.comp_hasDerivAt t h1
    have h3 := h2.inner ℝ (hasDerivAt_const t d)
    simp only [inner_zero_right, zero_add, Function.comp_def] at h3
    convert h3 using 1
    simp only [localInnerProd, hessianOperator]
    rw [real_inner_comm]
  have key : ∀ y d : E, ∀ s : ℝ, 1 < s → y ∈ Df → y + d ∈ Df → y + s • d ∉ Df →
      inner ℝ (gradient f y) d + 1 / (s - 1) - 1 / s ≤ inner ℝ (gradient f (y + d)) d ∧
      f y + inner ℝ (gradient f y) d + (Real.log s - Real.log (s - 1) - 1 / s) ≤ f (y + d) := by
    intro y d s hs hy hyd hsd
    have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, y + t • d ∈ Df := fun t ht =>
      h_Df_convex.add_smul_mem hy hyd ht
    have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < s - t := fun t ht => by linarith [ht.2]
    have hhess : ∀ t ∈ Set.Icc (0:ℝ) 1, 1 / (s - t) ^ 2 ≤ localInnerProd f (y + t • d) d d := by
      intro t ht
      have h1 := hdikin (y + t • d) (hseg t ht) (y + s • d) hsd
      have h2 : y + s • d - (y + t • d) = (s - t) • d := by rw [sub_smul]; abel
      rw [h2, hscale] at h1
      rw [div_le_iff₀ (pow_pos (hpos t ht) 2)]
      linarith [h1]
    set ψ : ℝ → ℝ := fun t => inner ℝ (gradient f (y + t • d)) d with hψ
    set u : ℝ → ℝ := fun t => ψ t - (s - t)⁻¹ with hu
    have hu_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt u (localInnerProd f (y + t • d) d d - 1 / (s - t) ^ 2) t := by
      intro t ht
      have h1 := hderiv_g y d t (hseg t ht)
      have h2 : HasDerivAt (fun t : ℝ => s - t) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub s
      have h3 := h2.inv (ne_of_gt (hpos t ht))
      have h4 := h1.sub h3
      convert h4 using 1
      ring
    have hu_mono : MonotoneOn u (Set.Icc 0 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      · intro t ht; exact (hu_deriv t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hu_deriv t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have := hhess t (Set.Ioo_subset_Icc_self ht)
        linarith
    set w : ℝ → ℝ := fun t => f (y + t • d) - (ψ 0 - 1 / s) * t + Real.log (s - t) with hw
    have hw_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt w (ψ t - (ψ 0 - 1 / s) - 1 / (s - t)) t := by
      intro t ht
      have h1 := hderiv_f y d t (hseg t ht)
      have h2 : HasDerivAt (fun t : ℝ => s - t) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub s
      have h3 := h2.log (ne_of_gt (hpos t ht))
      have h4 : HasDerivAt (fun t : ℝ => (ψ 0 - 1 / s) * t) (ψ 0 - 1 / s) t := by
        simpa using (hasDerivAt_id t).const_mul (ψ 0 - 1 / s)
      have h5 := (h1.sub h4).add h3
      convert h5 using 1
      ring
    have hw_mono : MonotoneOn w (Set.Icc 0 1) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      · intro t ht; exact (hw_deriv t ht).continuousAt.continuousWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        exact (hw_deriv t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
      · intro t ht
        rw [interior_Icc] at ht
        have h := hu_mono ⟨le_refl 0, zero_le_one⟩ (Set.Ioo_subset_Icc_self ht) ht.1.le
        simp only [hu, sub_zero] at h
        have e1 : 1 / s = s⁻¹ := one_div s
        have e2 : 1 / (s - t) = (s - t)⁻¹ := one_div (s - t)
        rw [e1, e2]
        linarith
    have h01 := hu_mono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
    have hw01 := hw_mono ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
    simp only [hu, hψ, hw, zero_smul, add_zero, one_smul, sub_zero, mul_zero, mul_one] at h01 hw01
    constructor
    · rw [one_div, one_div]; linarith
    · linarith
  set x0 := x 0 with hx0def
  have hx0 : x0 ∈ Df := hx 0
  have hxt_not_int : x_tilde ∉ interior Df := hx_tilde.2
  have hev : ∀ s : ℝ, 1 < s → ∀ᶠ i in Filter.atTop, x0 + s • (x i - x0) ∉ Df := by
    intro s hs
    have hs0 : s ≠ 0 := by positivity
    have hnot : x0 + s • (x_tilde - x0) ∉ closure Df := by
      intro hmem
      apply hxt_not_int
      have hx0i : x0 ∈ interior Df := by rw [h_Df_open.interior_eq]; exact hx0
      have ha : (0:ℝ) < 1 - 1 / s := by
        have : 1 / s < 1 := by rw [div_lt_one (by linarith)]; exact hs
        linarith
      have h := h_Df_convex.combo_interior_closure_mem_interior hx0i hmem
        (a := 1 - 1 / s) (b := 1 / s) ha (by positivity) (by ring)
      convert h using 1
      rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ hs0, one_smul, sub_smul, one_smul]
      abel
    have hcont : Filter.Tendsto (fun i => x0 + s • (x i - x0)) Filter.atTop
        (𝓝 (x0 + s • (x_tilde - x0))) :=
      tendsto_const_nhds.add ((hlim.sub tendsto_const_nhds).const_smul s)
    have := hcont.eventually (isClosed_closure.isOpen_compl.mem_nhds hnot)
    exact this.mono fun i hi hmem => hi (subset_closure hmem)
  have hbound : ∀ᶠ i in Filter.atTop, ‖x i - x0‖ ≤ ‖x_tilde - x0‖ + 1 := by
    have h1 : Filter.Tendsto (fun i => ‖x i - x0‖) Filter.atTop (𝓝 ‖x_tilde - x0‖) :=
      (hlim.sub tendsto_const_nhds).norm
    exact h1.eventually (eventually_le_nhds (by linarith))
  set R := ‖x_tilde - x0‖ + 1 with hR
  have hR0 : 0 < R := by positivity
  set G := ‖gradient f x0‖ with hG
  have hinner_lb : ∀ i, ‖x i - x0‖ ≤ R → -(G * R) ≤ inner ℝ (gradient f x0) (x i - x0) := by
    intro i hi
    have h1 := abs_real_inner_le_norm (gradient f x0) (x i - x0)
    have h2 : ‖gradient f x0‖ * ‖x i - x0‖ ≤ G * R := mul_le_mul_of_nonneg_left hi (norm_nonneg _)
    have h3 := neg_abs_le (inner ℝ (gradient f x0) (x i - x0))
    linarith
  constructor
  · rw [Filter.tendsto_atTop]
    intro M
    set K := max 0 (M - f x0 + G * R + 1) with hK
    set s := 1 + Real.exp (-K) with hs_def
    have hs : 1 < s := by have := Real.exp_pos (-K); linarith
    filter_upwards [hev s hs, hbound] with i hi hb
    have hxi : x0 + (x i - x0) = x i := by abel
    have h := (key x0 (x i - x0) s hs hx0 (by rw [hxi]; exact hx i) hi).2
    rw [hxi] at h
    have hlog1 : 0 ≤ Real.log s := Real.log_nonneg hs.le
    have hlog2 : Real.log (s - 1) = -K := by
      rw [hs_def, add_sub_cancel_left, Real.log_exp]
    have hinv : 1 / s ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hK1 : M - f x0 + G * R + 1 ≤ K := le_max_right _ _
    have := hinner_lb i hb
    linarith
  · rw [Filter.tendsto_atTop]
    intro M
    set K := max 1 (M * R + G * R + 1) with hK
    have hK0 : 0 < K := lt_of_lt_of_le one_pos (le_max_left _ _)
    set s := 1 + 1 / K with hs_def
    have hs : 1 < s := by have : 0 < 1 / K := by positivity
                          linarith
    filter_upwards [hev s hs, hbound] with i hi hb
    have hxi : x0 + (x i - x0) = x i := by abel
    have h := (key x0 (x i - x0) s hs hx0 (by rw [hxi]; exact hx i) hi).1
    rw [hxi] at h
    have h1 : 1 / (s - 1) = K := by
      rw [hs_def, add_sub_cancel_left, one_div_one_div]
    have hinv : 1 / s ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    have hK1 : M * R + G * R + 1 ≤ K := le_max_right _ _
    have := hinner_lb i hb
    have h2 := real_inner_le_norm (gradient f (x i)) (x i - x0)
    have h3 : ‖gradient f (x i)‖ * ‖x i - x0‖ ≤ ‖gradient f (x i)‖ * R :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    by_contra hcon
    push_neg at hcon
    have h4 : ‖gradient f (x i)‖ * R < M * R := mul_lt_mul_of_pos_right hcon hR0
    linarith

end Renegar_chap_2_2_2_9
