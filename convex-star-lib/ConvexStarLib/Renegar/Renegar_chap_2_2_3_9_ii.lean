import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_9_ii`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_9_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_9_ii`, so the main result is `Renegar_chap_2_2_3_9_ii.Renegar_chap_2_2_3_9_ii`.
-/

namespace Renegar_chap_2_2_3_9_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem Renegar_chap_2_2_3_9_ii [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x : E)
  (hx : x ∈ Df)
  (hf_log_homo_barrier : IsLogarithmicallyHomogeneousBarrier f Df h_Df_pd) :
  (∀ t : ℝ, 0 < t →
    hessianOperator f (t • x) = (t ^ 2)⁻¹ • hessianOperator f x) ∧
  (localGradient f Df h_Df_pd x x hx = (-1 : ℝ) • x) ∧
  (localNorm f x (localGradient f Df h_Df_pd x x hx) =
    Real.sqrt (barrierParameter f Df h_Df_pd)) := by
  obtain ⟨_, K, hDfK, hKcone, hhom⟩ := hf_log_homo_barrier
  set ν := barrierParameter f Df h_Df_pd with hν
  -- homogeneity on Df
  have hhom' : ∀ y ∈ Df, ∀ t : ℝ, 0 < t → f (t • y) = f y - ν * Real.log t := by
    intro y hy t ht
    rw [hDfK] at hy
    exact hhom y hy t ht
  -- Df is closed under positive scaling
  have hcone : ∀ y ∈ Df, ∀ t : ℝ, 0 < t → t • y ∈ Df := by
    intro y hy t ht
    rw [hDfK] at hy ⊢
    have hU : IsOpen {z : E | t⁻¹ • z ∈ interior K} :=
      isOpen_interior.preimage (continuous_const_smul t⁻¹)
    have hUK : {z : E | t⁻¹ • z ∈ interior K} ⊆ K := by
      intro z hz
      have := hKcone _ (interior_subset hz) t ht
      rwa [smul_smul, mul_inv_cancel₀ ht.ne', one_smul] at this
    apply interior_maximal hUK hU
    show t⁻¹ • t • y ∈ interior K
    rwa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
  -- regularity
  have hCD : ∀ y ∈ Df, ContDiffAt ℝ 2 f y := fun y hy =>
    hf_C2.contDiffAt (h_Df_open.mem_nhds hy)
  have hDiff : ∀ y ∈ Df, DifferentiableAt ℝ f y := fun y hy =>
    (hCD y hy).differentiableAt (by norm_num)
  have hgradDiff : ∀ y ∈ Df, DifferentiableAt ℝ (gradient f) y := by
    intro y hy
    have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := (hCD y hy).fderiv_right (by norm_num)
    have h2 : ContDiffAt ℝ 1
        (fun z => (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv (fderiv ℝ f z)) y :=
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.contDiff.contDiffAt.comp y h1
    exact h2.differentiableAt (by norm_num)
  -- gradient scaling
  have hfderiv_scale : ∀ y ∈ Df, ∀ t : ℝ, 0 < t →
      ∀ v : E, t * fderiv ℝ f (t • y) v = fderiv ℝ f y v := by
    intro y hy t ht v
    have heq : (fun z => f z - ν * Real.log t) =ᶠ[𝓝 y] (fun z => f (t • z)) := by
      filter_upwards [h_Df_open.mem_nhds hy] with z hz
      exact (hhom' z hz t ht).symm
    have hA : HasFDerivAt (fun z => f (t • z))
        ((fderiv ℝ f (t • y)).comp (t • ContinuousLinearMap.id ℝ E)) y :=
      (hDiff _ (hcone y hy t ht)).hasFDerivAt.comp y ((hasFDerivAt_id y).const_smul t)
    have hB : HasFDerivAt (fun z => f z - ν * Real.log t) (fderiv ℝ f y) y :=
      (hDiff y hy).hasFDerivAt.sub_const _
    have := (hA.congr_of_eventuallyEq heq).unique hB
    have := congrArg (fun L => L v) this
    simpa using this
  have hgrad_scale : ∀ y ∈ Df, ∀ t : ℝ, 0 < t → gradient f (t • y) = t⁻¹ • gradient f y := by
    intro y hy t ht
    have hL : fderiv ℝ f (t • y) = t⁻¹ • fderiv ℝ f y := by
      ext v
      rw [ContinuousLinearMap.smul_apply, ← hfderiv_scale y hy t ht v, smul_eq_mul,
        ← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul]
    simp only [gradient, hL, map_smul]
  -- Hessian scaling
  have hHess : ∀ t : ℝ, 0 < t →
      hessianOperator f (t • x) = (t ^ 2)⁻¹ • hessianOperator f x := by
    intro t ht
    have heq : (fun z => t⁻¹ • gradient f z) =ᶠ[𝓝 x] (fun z => gradient f (t • z)) := by
      filter_upwards [h_Df_open.mem_nhds hx] with z hz
      exact (hgrad_scale z hz t ht).symm
    have hA : HasFDerivAt (fun z => gradient f (t • z))
        ((fderiv ℝ (gradient f) (t • x)).comp (t • ContinuousLinearMap.id ℝ E)) x :=
      (hgradDiff _ (hcone x hx t ht)).hasFDerivAt.comp x ((hasFDerivAt_id x).const_smul t)
    have hB : HasFDerivAt (fun z => t⁻¹ • gradient f z) (t⁻¹ • fderiv ℝ (gradient f) x) x :=
      (hgradDiff x hx).hasFDerivAt.const_smul t⁻¹
    have hU := (hA.congr_of_eventuallyEq heq).unique hB
    ext v
    have := congrArg (fun L => L (t⁻¹ • v)) hU
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, smul_smul, inv_mul_cancel₀ ht.ne', one_smul, map_smul] at this
    show fderiv ℝ (gradient f) (t • x) v = ((t ^ 2)⁻¹ • fderiv ℝ (gradient f) x) v
    rw [this, ContinuousLinearMap.smul_apply, pow_two, mul_inv]
  -- H(x) x = - ∇f(x)
  have hHx : hessianOperator f x x = -gradient f x := by
    have heq : (fun s : ℝ => s⁻¹ • gradient f x) =ᶠ[𝓝 (1 : ℝ)]
        (fun s : ℝ => gradient f (s • x)) := by
      filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with s hs
      exact (hgrad_scale x hx s hs).symm
    have hA : HasDerivAt (fun s : ℝ => gradient f (s • x)) (hessianOperator f x ((1 : ℝ) • x)) 1 :=
      (hgradDiff x hx).hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ)
        ((hasDerivAt_id (1 : ℝ)).smul_const x) (one_smul ℝ x).symm
    have hB : HasDerivAt (fun s : ℝ => s⁻¹ • gradient f x) ((-((1 : ℝ) ^ 2)⁻¹) • gradient f x) 1 :=
      (hasDerivAt_inv one_ne_zero).smul_const (gradient f x)
    have := (hA.congr_of_eventuallyEq heq).unique hB
    simpa using this
  -- ⟪∇f(x), x⟫ = -ν
  have hfx : fderiv ℝ f x x = -ν := by
    have heq : (fun s : ℝ => f x - ν * Real.log s) =ᶠ[𝓝 (1 : ℝ)]
        (fun s : ℝ => f (s • x)) := by
      filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with s hs
      exact (hhom' x hx s hs).symm
    have hA : HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f x ((1 : ℝ) • x)) 1 :=
      (hDiff x hx).hasFDerivAt.comp_hasDerivAt_of_eq (1 : ℝ)
        ((hasDerivAt_id (1 : ℝ)).smul_const x) (one_smul ℝ x).symm
    have hB : HasDerivAt (fun s : ℝ => f x - ν * Real.log s) (-(ν * (1 : ℝ)⁻¹)) 1 :=
      ((Real.hasDerivAt_log one_ne_zero).const_mul ν).const_sub (f x)
    have := (hA.congr_of_eventuallyEq heq).unique hB
    simpa using this
  have hinner : inner ℝ x (gradient f x) = -ν := by
    rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply, hfx]
  -- local gradient
  have hLG : localGradient f Df h_Df_pd x x hx = (-1 : ℝ) • x := by
    unfold localGradient
    rw [ContinuousLinearEquiv.symm_apply_eq]
    show gradient f x = hessianOperator f x ((-1 : ℝ) • x)
    rw [map_smul, hHx, neg_one_smul, neg_neg]
  refine ⟨hHess, hLG, ?_⟩
  rw [hLG]
  unfold localNorm localInnerProd
  congr 1
  rw [map_smul, hHx, inner_smul_left, inner_smul_right, inner_neg_right, hinner]
  simp

end Renegar_chap_2_2_3_9_ii
