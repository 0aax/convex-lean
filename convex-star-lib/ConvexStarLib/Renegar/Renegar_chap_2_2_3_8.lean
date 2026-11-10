import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_8`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_8`, so the main result is `Renegar_chap_2_2_3_8.Renegar_chap_2_2_3_8`.
-/

namespace Renegar_chap_2_2_3_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Renegar_chap_2_2_3_8 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x y : E)
  (hf_sc : IsSCBarrier f Df h_Df_pd)
  (hx : x ∈ Df)
  (hy : y ∈ closure Df) :
  ∀ (t : ℝ), 0 < t → t ≤ 1 →
    f (y + t • (x - y)) ≤ f x - (barrierParameter f Df h_Df_pd) * (Real.log t) := by
  intro t ht0 ht1
  set θ := barrierParameter f Df h_Df_pd with hθ_def
  -- smoothness facts on `Df`
  have hCDA : ∀ z ∈ Df, ContDiffAt ℝ 2 f z := fun z hz =>
    hf_C2.contDiffAt (h_Df_open.mem_nhds hz)
  have hDA : ∀ z ∈ Df, DifferentiableAt ℝ f z := fun z hz =>
    (hCDA z hz).differentiableAt (by norm_num)
  have hDDA : ∀ z ∈ Df, DifferentiableAt ℝ (fderiv ℝ f) z := fun z hz =>
    ((hCDA z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hgrad_eq : (fun w => gradient f w) =
      (InnerProductSpace.toDual ℝ E).symm ∘ (fderiv ℝ f) := rfl
  have hH : ∀ z ∈ Df, HasFDerivAt (fun w => gradient f w) (hessianOperator f z) z := by
    intro z hz
    have : DifferentiableAt ℝ (fun w => gradient f w) z := by
      rw [hgrad_eq]
      exact (InnerProductSpace.toDual ℝ E).symm.differentiableAt.comp z (hDDA z hz)
    exact this.hasFDerivAt
  have hH_apply : ∀ z u w, inner ℝ (hessianOperator f z u) w = fderiv ℝ (fderiv ℝ f) z u w := by
    intro z u w
    show inner ℝ (fderiv ℝ ((InnerProductSpace.toDual ℝ E).symm ∘ (fderiv ℝ f)) z u) w = _
    rw [LinearIsometryEquiv.comp_fderiv]
    exact InnerProductSpace.toDual_symm_apply
  have hH_symm : ∀ z ∈ Df, ∀ u w,
      inner ℝ (hessianOperator f z u) w = inner ℝ (hessianOperator f z w) u := by
    intro z hz u w
    rw [hH_apply, hH_apply]
    exact (hCDA z hz).isSymmSndFDerivAt (by simp) u w
  have hpsd : ∀ z ∈ Df, ∀ v, 0 ≤ inner ℝ (hessianOperator f z v) v := by
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · have := h_Df_pd z hz v hv
      simp only [localInnerProd] at this
      rw [real_inner_comm]; exact this.le
  -- bounds on the barrier parameter
  have hbdd := hf_sc.2
  have hθ_ge : ∀ z (hz : z ∈ Df), barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ ≤ θ := fun z hz =>
    le_csSup hbdd ⟨⟨z, hz⟩, rfl⟩
  have hθ_nonneg : 0 ≤ θ := le_trans (by simp only [barrierIntegrand]; positivity) (hθ_ge x hx)
  -- key inequality: `⟪∇f z, v⟫² ≤ θ ⟪H z v, v⟫`
  have hkey : ∀ z ∈ Df, ∀ v,
      (inner ℝ (gradient f z) v) ^ 2 ≤ θ * inner ℝ (hessianOperator f z v) v := by
    intro z hz v
    set g := localGradient f Df h_Df_pd z z hz with hg
    have hHg : hessianOperator f z g = gradient f z := by
      simp [g, localGradient, hessianLinearEquiv]
    have hgg : barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ = inner ℝ (hessianOperator f z g) g := by
      simp only [barrierIntegrand, localNorm]
      rw [Real.sq_sqrt (by simpa [localInnerProd, real_inner_comm] using hpsd z hz g)]
      simp [localInnerProd, real_inner_comm, g]
    have hCS : (inner ℝ (hessianOperator f z g) v) ^ 2 ≤
        inner ℝ (hessianOperator f z g) g * inner ℝ (hessianOperator f z v) v := by
      have hd := discrim_le_zero (a := inner ℝ (hessianOperator f z v) v)
        (b := 2 * inner ℝ (hessianOperator f z g) v) (c := inner ℝ (hessianOperator f z g) g) ?_
      · unfold discrim at hd; nlinarith
      · intro s
        have := hpsd z hz (g + s • v)
        simp only [map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left,
          inner_smul_right] at this
        rw [hH_symm z hz v g] at this
        simp only [conj_trivial] at this
        nlinarith
    rw [← hHg]
    calc _ ≤ _ := hCS
      _ ≤ θ * _ := by
        rw [← hgg]; exact mul_le_mul_of_nonneg_right (hθ_ge z hz) (hpsd z hz v)
  -- the line through `y` and `x`
  set d := x - y with hd
  have hmem : ∀ s ∈ Set.Ioc (0:ℝ) 1, y + s • d ∈ Df := by
    intro s hs
    have := h_Df_convex.add_smul_sub_mem_interior' hy (h_Df_open.interior_eq.symm ▸ hx) hs
    rwa [h_Df_open.interior_eq] at this
  have hline : ∀ s : ℝ, HasDerivAt (fun s : ℝ => y + s • d) d s := by
    intro s
    simpa using ((hasDerivAt_id s).smul_const d).const_add y
  set q0 : ℝ → ℝ := fun s => f (y + s • d) with hq0
  set q1 : ℝ → ℝ := fun s => inner ℝ (gradient f (y + s • d)) d with hq1
  set q2 : ℝ → ℝ := fun s => inner ℝ (hessianOperator f (y + s • d) d) d with hq2
  have hq0' : ∀ s ∈ Set.Ioc (0:ℝ) 1, HasDerivAt q0 (q1 s) s := by
    intro s hs
    have h1 := (hDA _ (hmem s hs)).hasFDerivAt.comp_hasDerivAt s (hline s)
    convert h1 using 1
    simp [q1, gradient, InnerProductSpace.toDual_symm_apply]
  have hq0'' : ∀ s ∈ Set.Ioc (0:ℝ) 1, HasDerivAt q1 (q2 s) s := by
    intro s hs
    have h1 := (hH _ (hmem s hs)).comp_hasDerivAt s (hline s)
    have h2 := h1.inner ℝ (hasDerivAt_const s d)
    convert h2 using 1
    simp [q2]
  have hq2_nonneg : ∀ s ∈ Set.Ioc (0:ℝ) 1, 0 ≤ q2 s := fun s hs => hpsd _ (hmem s hs) d
  have hq0_key : ∀ s ∈ Set.Ioc (0:ℝ) 1, (q1 s) ^ 2 ≤ θ * q2 s := fun s hs => hkey _ (hmem s hs) d
  -- `q1` is monotone on `(0, 1]`
  have hq1_mono : MonotoneOn q1 (Set.Ioc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 1)
    · intro s hs; exact (hq0'' s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      exact (hq0'' s (Set.Ioo_subset_Ioc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Ioc] at hs
      exact hq2_nonneg s (Set.Ioo_subset_Ioc_self hs)
  -- Claim A: `-θ ≤ s q1 s`
  have hA : ∀ s ∈ Set.Ioc (0:ℝ) 1, -θ ≤ s * q1 s := by
    intro s₀ hs₀
    by_contra hlt
    push_neg at hlt
    have hneg0 : q1 s₀ < 0 := by
      by_contra h
      push_neg at h
      have := mul_nonneg hs₀.1.le h
      linarith
    have hneg : ∀ s ∈ Set.Ioc 0 s₀, q1 s < 0 := by
      intro s hs
      have := hq1_mono ⟨hs.1, hs.2.trans hs₀.2⟩ hs₀ hs.2
      linarith
    set h : ℝ → ℝ := fun s => s + θ / q1 s with hh
    have hderiv : ∀ s ∈ Set.Ioc 0 s₀,
        HasDerivAt h (1 + (0 * q1 s - θ * q2 s) / (q1 s) ^ 2) s := by
      intro s hs
      have hs1 : s ∈ Set.Ioc (0:ℝ) 1 := ⟨hs.1, hs.2.trans hs₀.2⟩
      exact (hasDerivAt_id s).add ((hasDerivAt_const s θ).fun_div (hq0'' s hs1) (hneg s hs).ne)
    have hderiv_nonpos : ∀ s ∈ Set.Ioc 0 s₀, 1 + (0 * q1 s - θ * q2 s) / (q1 s) ^ 2 ≤ 0 := by
      intro s hs
      have hs1 : s ∈ Set.Ioc (0:ℝ) 1 := ⟨hs.1, hs.2.trans hs₀.2⟩
      have hpos : 0 < (q1 s) ^ 2 := by
        rw [sq]; exact mul_pos_of_neg_of_neg (hneg s hs) (hneg s hs)
      rw [zero_mul, zero_sub, neg_div, ← sub_eq_add_neg, sub_nonpos, le_div_iff₀ hpos, one_mul]
      exact hq0_key s hs1
    have hh0 : 0 < h s₀ := by
      simp only [hh]
      have : -s₀ < θ / q1 s₀ := by
        rw [lt_div_iff_of_neg hneg0]; linarith
      linarith
    set s₁ := min s₀ (h s₀) / 2 with hs₁
    have hs₁_pos : 0 < s₁ := by
      have := lt_min hs₀.1 hh0
      positivity
    have hs₁_le : s₁ ≤ s₀ := by
      have := min_le_left s₀ (h s₀)
      linarith
    have hs₁_lt : s₁ < h s₀ := by
      have := min_le_right s₀ (h s₀)
      linarith
    have hanti : AntitoneOn h (Set.Icc s₁ s₀) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc s₁ s₀)
      · intro s hs
        exact (hderiv s ⟨hs₁_pos.trans_le hs.1, hs.2⟩).continuousAt.continuousWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact (hderiv s ⟨hs₁_pos.trans hs.1, hs.2.le⟩).hasDerivWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        exact hderiv_nonpos s ⟨hs₁_pos.trans hs.1, hs.2.le⟩
    have h1 : h s₀ ≤ h s₁ :=
      hanti ⟨le_rfl, hs₁_le⟩ ⟨hs₁_le, le_rfl⟩ hs₁_le
    have h2 : h s₁ ≤ s₁ := by
      simp only [hh]
      have : θ / q1 s₁ ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos hθ_nonneg (hneg s₁ ⟨hs₁_pos, hs₁_le⟩).le
      linarith
    linarith
  -- Claim B: `q0 s + θ log s` is monotone on `[t, 1]`
  have hB : MonotoneOn (fun s => q0 s + θ * Real.log s) (Set.Icc t 1) := by
    have hderiv : ∀ s ∈ Set.Icc t 1,
        HasDerivAt (fun s => q0 s + θ * Real.log s) (q1 s + θ * s⁻¹) s := by
      intro s hs
      have hs1 : s ∈ Set.Ioc (0:ℝ) 1 := ⟨ht0.trans_le hs.1, hs.2⟩
      exact (hq0' s hs1).add ((Real.hasDerivAt_log hs1.1.ne').const_mul θ)
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc t 1)
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs1 : s ∈ Set.Ioc (0:ℝ) 1 := ⟨ht0.trans hs.1, hs.2.le⟩
      have hA' := hA s hs1
      have hspos := hs1.1
      have : q1 s + θ * s⁻¹ = (s * q1 s + θ) * s⁻¹ := by field_simp
      rw [this]
      exact mul_nonneg (by linarith) (inv_nonneg.mpr hspos.le)
  have := hB ⟨le_rfl, ht1⟩ ⟨ht1, le_rfl⟩ ht1
  simp only [hq0, Real.log_one, mul_zero, add_zero, one_smul, hd, add_sub_cancel] at this
  linarith

end Renegar_chap_2_2_3_8
