import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_3`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_3`, so the main result is `Renegar_chap_2_2_3_3.Renegar_chap_2_2_3_3`.
-/

namespace Renegar_chap_2_2_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Renegar_chap_2_2_3_3 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x y : E)
  (hf_sc : IsSCBarrier f Df h_Df_pd)
  (hx : x ∈ Df)
  (hy : y ∈ Df) :
  inner ℝ (gradient f x) (y - x) < barrierParameter f Df h_Df_pd := by
  classical
  set ϑ := barrierParameter f Df h_Df_pd with hϑ_def
  -- positive semidefiniteness
  have h_psd : ∀ z ∈ Df, ∀ v, 0 ≤ inner ℝ v (hessianOperator f z v) := by
    intro z hz v
    by_cases hv : v = 0
    · simp [hv]
    · exact le_of_lt (h_Df_pd z hz v hv)
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : E)
  -- the gradient is differentiable on Df
  have h_diff : ∀ z ∈ Df, DifferentiableAt ℝ (fun y => gradient f y) z := by
    intro z hz
    by_contra hnd
    have h0 : hessianOperator f z = 0 := by
      unfold hessianOperator
      exact fderiv_zero_of_not_differentiableAt hnd
    have := h_Df_pd z hz v₀ hv₀
    simp [localInnerProd, h0] at this
  have h_hasDeriv : ∀ z ∈ Df,
      HasFDerivAt (fun y => gradient f y) (hessianOperator f z) z := by
    intro z hz
    exact (h_diff z hz).hasFDerivAt
  -- symmetry of the Hessian
  have h_symm : ∀ z ∈ Df, ∀ u v,
      inner ℝ u (hessianOperator f z v) = inner ℝ v (hessianOperator f z u) := by
    intro z hz
    have hfz : ContDiffAt ℝ 2 f z := hf_C2.contDiffAt (h_Df_open.mem_nhds hz)
    have hS : IsSymmSndFDerivAt ℝ f z := hfz.isSymmSndFDerivAt (by simp)
    have hdf : DifferentiableAt ℝ (fderiv ℝ f) z :=
      (hfz.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have key : ∀ u v, inner ℝ u (hessianOperator f z v) = fderiv ℝ (fderiv ℝ f) z v u := by
      intro u v
      have h1 : HasFDerivAt (fun y => inner ℝ u (gradient f y))
          ((innerSL ℝ u).comp (hessianOperator f z)) z :=
        (innerSL ℝ u).hasFDerivAt.comp z (h_hasDeriv z hz)
      have h2 : HasFDerivAt (fun y => fderiv ℝ f y u)
          ((fderiv ℝ f z).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) z).flip u) z :=
        hdf.hasFDerivAt.clm_apply (hasFDerivAt_const u z)
      have heq : (fun y => inner ℝ u (gradient f y)) = (fun y => fderiv ℝ f y u) := by
        funext y
        rw [real_inner_comm]
        simp [gradient, InnerProductSpace.toDual_symm_apply]
      rw [heq] at h1
      have h3 := h1.unique h2
      have h4 := congrArg (fun L => L v) h3
      simpa using h4
    intro u v
    rw [key, key]
    exact hS v u
  -- the local gradient
  have h_lg : ∀ z (hz : z ∈ Df),
      hessianOperator f z (localGradient f Df h_Df_pd z z hz) = gradient f z := by
    intro z hz
    unfold localGradient hessianLinearEquiv
    exact ContinuousLinearEquiv.ofBijective_apply_symm_apply _ _ _ _
  have h_bi : ∀ z (hz : z ∈ Df), barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ =
      inner ℝ (localGradient f Df h_Df_pd z z hz)
        (hessianOperator f z (localGradient f Df h_Df_pd z z hz)) := by
    intro z hz
    unfold barrierIntegrand localNorm localInnerProd
    exact Real.sq_sqrt (h_psd z hz _)
  have h_le : ∀ z (hz : z ∈ Df), barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ ≤ ϑ :=
    fun z hz => le_csSup hf_sc.2 (Set.mem_range_self (⟨z, hz⟩ : Df))
  -- key inequality
  have h_key : ∀ z ∈ Df, ∀ d : E,
      (inner ℝ (gradient f z) d) ^ 2 ≤ ϑ * inner ℝ d (hessianOperator f z d) := by
    intro z hz d
    set w := localGradient f Df h_Df_pd z z hz with hw_def
    have hw : hessianOperator f z w = gradient f z := h_lg z hz
    have hbi : barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ =
        inner ℝ w (hessianOperator f z w) := h_bi z hz
    have hle := h_le z hz
    have hCS : (inner ℝ d (hessianOperator f z w)) ^ 2 ≤
        inner ℝ d (hessianOperator f z d) * inner ℝ w (hessianOperator f z w) := by
      have hq : ∀ s : ℝ, 0 ≤ inner ℝ w (hessianOperator f z w) * (s * s) +
          (-2 * inner ℝ d (hessianOperator f z w)) * s +
          inner ℝ d (hessianOperator f z d) := by
        intro s
        have h0 := h_psd z hz (d - s • w)
        simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, inner_smul_left,
          inner_smul_right] at h0
        rw [h_symm z hz w d] at h0
        simp only [RCLike.conj_to_real] at h0
        nlinarith
      have h5 := discrim_le_zero hq
      unfold discrim at h5
      nlinarith
    rw [← hw, real_inner_comm]
    have hdd := h_psd z hz d
    nlinarith
  -- positivity of the barrier parameter
  have hϑ_pos : 0 < ϑ := by
    by_contra hneg
    push_neg at hneg
    have hg0 : ∀ z ∈ Df, gradient f z = 0 := by
      intro z hz
      have hw := h_lg z hz
      have hbi := h_bi z hz
      have h6 : inner ℝ (localGradient f Df h_Df_pd z z hz)
          (hessianOperator f z (localGradient f Df h_Df_pd z z hz)) ≤ 0 := by
        linarith [h_le z hz]
      by_contra hne
      have hw0 : localGradient f Df h_Df_pd z z hz ≠ 0 := by
        intro h
        rw [h, map_zero] at hw
        exact hne hw.symm
      have h7 := h_Df_pd z hz _ hw0
      unfold localInnerProd at h7
      linarith
    have hev : (fun y => gradient f y) =ᶠ[𝓝 x] (fun _ => (0 : E)) := by
      filter_upwards [h_Df_open.mem_nhds hx] with z hz
      exact hg0 z hz
    have hH0 : hessianOperator f x = 0 := by
      unfold hessianOperator
      rw [hev.fderiv_eq]
      simp
    have h8 := h_Df_pd x hx v₀ hv₀
    simp [localInnerProd, hH0] at h8
  -- main argument
  set d := y - x with hd
  by_cases hp0 : inner ℝ (gradient f x) d ≤ 0
  · linarith
  push_neg at hp0
  have hpath : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • d ∈ Df :=
    fun t ht => h_Df_convex.add_smul_sub_mem hx hy ht
  set p : ℝ → ℝ := fun t => inner ℝ (gradient f (x + t • d)) d with hp_def
  set p' : ℝ → ℝ := fun t => inner ℝ d (hessianOperator f (x + t • d) d) with hp'_def
  have hp_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt p (p' t) t := by
    intro t ht
    have hz : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have hg := (h_hasDeriv _ (hpath t ht)).comp_hasDerivAt t hz
    have h9 := hg.inner ℝ (hasDerivAt_const t d)
    simp only [inner_zero_right, zero_add] at h9
    convert h9 using 1
    simp [p', real_inner_comm]
  have hp'_nonneg : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ p' t := fun t ht => h_psd _ (hpath t ht) d
  have hp_mono : MonotoneOn p (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
    · intro t ht; exact (hp_deriv t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hp_deriv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht; exact hp'_nonneg t (interior_subset ht)
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.left_mem_Icc.mpr zero_le_one
  have h1mem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := Set.right_mem_Icc.mpr zero_le_one
  have hp0' : p 0 = inner ℝ (gradient f x) d := by simp [p]
  have hp_pos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < p t := by
    intro t ht
    have := hp_mono h0mem ht ht.1
    linarith
  set h : ℝ → ℝ := fun t => ϑ / p t + t with hh_def
  have hh_deriv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt h ((0 * p t - ϑ * p' t) / (p t) ^ 2 + 1) t := by
    intro t ht
    exact ((hasDerivAt_const t ϑ).div (hp_deriv t ht) (ne_of_gt (hp_pos t ht))).add
      (hasDerivAt_id' t)
  have hh_anti : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
    · intro t ht; exact (hh_deriv t ht).continuousAt.continuousWithinAt
    · intro t ht; exact (hh_deriv t (interior_subset ht)).hasDerivWithinAt
    · intro t ht
      have ht' := interior_subset ht
      have hpt := hp_pos t ht'
      have hk : (p t) ^ 2 ≤ ϑ * p' t := h_key _ (hpath t ht') d
      have h10 : 1 ≤ ϑ * p' t / p t ^ 2 := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h11 : (0 * p t - ϑ * p' t) / p t ^ 2 = -(ϑ * p' t / p t ^ 2) := by ring
      rw [h11]
      linarith
  have h12 := hh_anti h0mem h1mem zero_le_one
  simp only [h] at h12
  have h13 : 0 < ϑ / p 1 := div_pos hϑ_pos (hp_pos 1 h1mem)
  have h14 : 1 < ϑ / p 0 := by linarith
  rw [lt_div_iff₀ (hp_pos 0 h0mem)] at h14
  linarith

end Renegar_chap_2_2_3_3
