import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_6`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_6`, so the main result is `Renegar_chap_2_2_3_6.Renegar_chap_2_2_3_6`.
-/

namespace Renegar_chap_2_2_3_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Helper lemmas -/

/-- The inverse Riesz map as a continuous ℝ-linear map. -/
noncomputable def rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E :=
  { toFun := fun ℓ => (InnerProductSpace.toDual ℝ E).symm ℓ
    map_add' := fun a b => by simp
    map_smul' := fun c a => by simp
    cont := (InnerProductSpace.toDual ℝ E).symm.continuous }

lemma rieszCLM'_apply (ℓ : E →L[ℝ] ℝ) :
    (rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E) ℓ = (InnerProductSpace.toDual ℝ E).symm ℓ := rfl

lemma hasFDerivAt_gradient' (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) :
    HasFDerivAt (fun y => gradient f y)
      ((rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E).comp (fderiv ℝ (fderiv ℝ f) y)) y := by
  have h1 : DifferentiableAt ℝ (fderiv ℝ f) y := by
    have := hf.fderiv_right (m := 1) (by norm_num)
    exact this.differentiableAt (by norm_num)
  have h2 : (fun y => gradient f y) = fun y => (rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E) (fderiv ℝ f y) := rfl
  rw [h2]
  exact (rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E).hasFDerivAt.comp y h1.hasFDerivAt

lemma hessianOperator_eq' (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) :
    hessianOperator f y = (rieszCLM' : (E →L[ℝ] ℝ) →L[ℝ] E).comp (fderiv ℝ (fderiv ℝ f) y) :=
  (hasFDerivAt_gradient' f y hf).fderiv

lemma localInnerProd_eq' (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) (u v : E) :
    localInnerProd f y u v = fderiv ℝ (fderiv ℝ f) y v u := by
  rw [localInnerProd, hessianOperator_eq' f y hf, real_inner_comm]
  simp [rieszCLM'_apply, InnerProductSpace.toDual_symm_apply]

lemma localInnerProd_symm' (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) (u v : E) :
    localInnerProd f y u v = localInnerProd f y v u := by
  rw [localInnerProd_eq' f y hf, localInnerProd_eq' f y hf]
  exact (hf.isSymmSndFDerivAt (by simp)) v u

lemma hasDerivAt_line_f' (f : E → ℝ) (x d : E) (s : ℝ) (hf : ContDiffAt ℝ 2 f (x + s • d)) :
    HasDerivAt (fun t : ℝ => f (x + t • d)) (inner ℝ (gradient f (x + s • d)) d) s := by
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hfd : HasFDerivAt f (fderiv ℝ f (x + s • d)) (x + s • d) :=
    (hf.differentiableAt (by norm_num)).hasFDerivAt
  have := hfd.comp_hasDerivAt s hline
  convert this using 1
  simp [gradient, InnerProductSpace.toDual_symm_apply]

lemma hasDerivAt_line_grad' (f : E → ℝ) (x d : E) (s : ℝ) (hf : ContDiffAt ℝ 2 f (x + s • d)) :
    HasDerivAt (fun t : ℝ => inner ℝ (gradient f (x + t • d)) d)
      (localInnerProd f (x + s • d) d d) s := by
  have hline : HasDerivAt (fun t : ℝ => x + t • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have hg : HasFDerivAt (fun y => gradient f y) (hessianOperator f (x + s • d)) (x + s • d) := by
    rw [hessianOperator_eq' f _ hf]; exact hasFDerivAt_gradient' f _ hf
  have h2 := hg.comp_hasDerivAt s hline
  have h3 := HasDerivAt.inner ℝ h2 (hasDerivAt_const s d)
  convert h3 using 1
  simp [localInnerProd, real_inner_comm]

lemma localInnerProd_self_nonneg' (f : E → ℝ) (Df : Set E)
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (x : E) (hx : x ∈ Df) (v : E) :
    0 ≤ localInnerProd f x v v := by
  by_cases hv : v = 0
  · simp [hv, localInnerProd]
  · exact (h_pd x hx v hv).le

lemma localInnerProd_smul' (f : E → ℝ) (x d : E) (s : ℝ) :
    localInnerProd f x (s • d) (s • d) = s ^ 2 * localInnerProd f x d d := by
  simp only [localInnerProd, map_smul, real_inner_smul_left, real_inner_smul_right]; ring

lemma localNorm_smul' (f : E → ℝ) (x d : E) (s : ℝ) :
    localNorm f x (s • d) = |s| * localNorm f x d := by
  unfold localNorm
  rw [localInnerProd_smul', Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq_eq_abs]

lemma hessian_localGradient' (f : E → ℝ) (Df : Set E)
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (x : E) (hx : x ∈ Df) :
    hessianOperator f x (localGradient f Df h_pd x x hx) = gradient f x := by
  have : ∀ v, hessianLinearEquiv f Df x hx h_pd v = hessianOperator f x v := fun v => rfl
  rw [localGradient, ← this, ContinuousLinearEquiv.apply_symm_apply]

lemma inner_grad_sq_le' (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df) (hDf : IsOpen Df)
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (x : E) (hx : x ∈ Df) (d : E) :
    (inner ℝ (gradient f x) d) ^ 2 ≤ barrierIntegrand f Df h_pd ⟨x, hx⟩ * localInnerProd f x d d := by
  have hfx : ContDiffAt ℝ 2 f x := hf.contDiffAt (hDf.mem_nhds hx)
  have hHu := hessian_localGradient' f Df h_pd x hx
  set u := localGradient f Df h_pd x x hx with hu
  have hB : barrierIntegrand f Df h_pd ⟨x, hx⟩ = localInnerProd f x u u := by
    simp only [barrierIntegrand, localNorm]
    rw [Real.sq_sqrt (localInnerProd_self_nonneg' f Df h_pd x hx u)]
  have hg : inner ℝ (gradient f x) d = localInnerProd f x u d := by
    rw [← hHu, real_inner_comm, localInnerProd_symm' f x hfx u d]; rfl
  rw [hB, hg]
  have key : ∀ t : ℝ, 0 ≤ localInnerProd f x d d * (t * t) + (-2 * localInnerProd f x u d) * t
      + localInnerProd f x u u := by
    intro t
    have h0 := localInnerProd_self_nonneg' f Df h_pd x hx (u - t • d)
    have hsym := localInnerProd_symm' f x hfx d u
    have e : localInnerProd f x (u - t • d) (u - t • d) = localInnerProd f x u u
        - 2 * t * localInnerProd f x u d + t ^ 2 * localInnerProd f x d d := by
      simp only [localInnerProd, map_sub, map_smul, inner_sub_left, inner_sub_right,
        real_inner_smul_left, real_inner_smul_right] at hsym ⊢
      rw [hsym]; ring
    rw [e] at h0
    nlinarith
  have := discrim_le_zero key
  simp only [discrim] at this
  nlinarith [localInnerProd_self_nonneg' f Df h_pd x hx u, localInnerProd_self_nonneg' f Df h_pd x hx d]

lemma theta_bound' (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df) (hDf : IsOpen Df)
    (hconv : Convex ℝ Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (θ : ℝ) (hθ : 0 < θ) (hbound : ∀ x (hx : x ∈ Df), barrierIntegrand f Df h_pd ⟨x, hx⟩ ≤ θ)
    (x y : E) (hx : x ∈ Df) (hy : y ∈ Df) : inner ℝ (gradient f x) (y - x) ≤ θ := by
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, x + s • (y - x) ∈ Df :=
    fun s hs => hconv.add_smul_sub_mem hx hy hs
  let ψ : ℝ → ℝ := fun s => inner ℝ (gradient f (x + s • (y - x))) (y - x)
  let q : ℝ → ℝ := fun s => localInnerProd f (x + s • (y - x)) (y - x) (y - x)
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (q s) s := fun s hs =>
    hasDerivAt_line_grad' f x (y - x) s (hf.contDiffAt (hDf.mem_nhds (hmem s hs)))
  have hq_nonneg : ∀ s ∈ Set.Icc (0:ℝ) 1, 0 ≤ q s := fun s hs =>
    localInnerProd_self_nonneg' f Df h_pd _ (hmem s hs) (y - x)
  have hCS : ∀ s ∈ Set.Icc (0:ℝ) 1, ψ s ^ 2 ≤ θ * q s := by
    intro s hs
    have h1 := inner_grad_sq_le' f Df hf hDf h_pd _ (hmem s hs) (y - x)
    have h2 := hbound _ (hmem s hs)
    calc ψ s ^ 2 ≤ barrierIntegrand f Df h_pd ⟨_, hmem s hs⟩ * q s := h1
      _ ≤ θ * q s := mul_le_mul_of_nonneg_right h2 (hq_nonneg s hs)
  have hcont : ContinuousOn ψ (Set.Icc 0 1) := fun s hs =>
    (hderiv s hs).continuousAt.continuousWithinAt
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont (f' := q)
    · intro s hs; rw [interior_Icc] at hs
      exact (hderiv s (Set.Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs; rw [interior_Icc] at hs; exact hq_nonneg s (Set.Ioo_subset_Icc_self hs)
  by_contra hcon
  push_neg at hcon
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_refl 0, zero_le_one⟩
  have h1mem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have hψ0 : θ < ψ 0 := by simpa [ψ] using hcon
  have hpos : ∀ s ∈ Set.Icc (0:ℝ) 1, θ < ψ s := fun s hs =>
    lt_of_lt_of_le hψ0 (hmono h0mem hs hs.1)
  have hanti : AntitoneOn (fun s => (ψ s)⁻¹ + s / θ) (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (f' := fun s => -(q s) / (ψ s) ^ 2 + 1 / θ)
    · intro s hs
      exact (((hderiv s hs).continuousAt.inv₀ (ne_of_gt (hθ.trans (hpos s hs)))).add
        (continuousAt_id.div_const θ)).continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      exact (((hderiv s hs').inv (ne_of_gt (hθ.trans (hpos s hs')))).add
        ((hasDerivAt_id' s).div_const θ)).hasDerivWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      have hψpos := hθ.trans (hpos s hs')
      have h1 := hCS s hs'
      have h2 : 1 / θ ≤ q s / ψ s ^ 2 := by
        rw [div_le_div_iff₀ hθ (by positivity)]; linarith
      simp only [neg_div]
      linarith
  have := hanti h0mem h1mem zero_le_one
  simp only at this
  have hψ1 := hθ.trans (hpos 1 h1mem)
  have h3 : (ψ 0)⁻¹ < 1 / θ := by rw [one_div]; exact inv_strictAnti₀ hθ hψ0
  have h4 : 0 < (ψ 1)⁻¹ := inv_pos.mpr hψ1
  simp only [zero_div, add_zero] at this
  linarith

lemma first_order' (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df) (hDf : IsOpen Df)
    (hconv : Convex ℝ Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (w y : E) (hw : w ∈ Df) (hy : y ∈ Df) : f w + inner ℝ (gradient f w) (y - w) ≤ f y := by
  have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, w + s • (y - w) ∈ Df :=
    fun s hs => hconv.add_smul_sub_mem hw hy hs
  have hcd : ∀ s ∈ Set.Icc (0:ℝ) 1, ContDiffAt ℝ 2 f (w + s • (y - w)) :=
    fun s hs => hf.contDiffAt (hDf.mem_nhds (hmem s hs))
  let ψ : ℝ → ℝ := fun s => inner ℝ (gradient f (w + s • (y - w))) (y - w)
  have hmono : MonotoneOn ψ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun s => localInnerProd f (w + s • (y - w)) (y - w) (y - w))
    · intro s hs
      exact (hasDerivAt_line_grad' f w (y - w) s (hcd s hs)).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      exact (hasDerivAt_line_grad' f w (y - w) s
        (hcd s (Set.Ioo_subset_Icc_self hs))).hasDerivWithinAt
    · intro s hs; rw [interior_Icc] at hs
      exact localInnerProd_self_nonneg' f Df h_pd _ (hmem s (Set.Ioo_subset_Icc_self hs)) (y - w)
  have hmono2 : MonotoneOn (fun s => f (w + s • (y - w)) - s * ψ 0) (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) (f' := fun s => ψ s - ψ 0)
    · intro s hs
      exact ((hasDerivAt_line_f' f w (y - w) s (hcd s hs)).sub
        ((hasDerivAt_id' s).mul_const (ψ 0))).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Icc] at hs
      have := ((hasDerivAt_line_f' f w (y - w) s (hcd s (Set.Ioo_subset_Icc_self hs))).sub
        ((hasDerivAt_id' s).mul_const (ψ 0)))
      convert this.hasDerivWithinAt using 1; simp [ψ]
    · intro s hs; rw [interior_Icc] at hs
      have hs' := Set.Ioo_subset_Icc_self hs
      exact sub_nonneg.mpr (hmono ⟨le_refl 0, zero_le_one⟩ hs' hs'.1)
  have := hmono2 ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp [ψ] at this
  linarith

lemma blowup_bound' (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df) (hDf : IsOpen Df)
    (h_ball : ∀ x ∈ Df, localBall f x x 1 ⊆ Df)
    (x₀ p : E) (hp : p ∉ Df) (hseg : ∀ s ∈ Set.Ico (0:ℝ) 1, x₀ + s • (p - x₀) ∈ Df)
    (t : ℝ) (ht : t ∈ Set.Ico (0:ℝ) 1) :
    f x₀ + t * (inner ℝ (gradient f x₀) (p - x₀) - 1) - Real.log (1 - t)
      ≤ f (x₀ + t • (p - x₀)) := by
  let ψ : ℝ → ℝ := fun s => inner ℝ (gradient f (x₀ + s • (p - x₀))) (p - x₀)
  let q : ℝ → ℝ := fun s => localInnerProd f (x₀ + s • (p - x₀)) (p - x₀) (p - x₀)
  have hcd : ∀ s ∈ Set.Ico (0:ℝ) 1, ContDiffAt ℝ 2 f (x₀ + s • (p - x₀)) :=
    fun s hs => hf.contDiffAt (hDf.mem_nhds (hseg s hs))
  have hq1 : ∀ s ∈ Set.Ico (0:ℝ) 1, 1 ≤ (1 - s) ^ 2 * q s := by
    intro s hs
    by_contra hlt; push_neg at hlt
    apply hp
    have hpd : p - (x₀ + s • (p - x₀)) = (1 - s) • (p - x₀) := by module
    have : p ∈ localBall f (x₀ + s • (p - x₀)) (x₀ + s • (p - x₀)) 1 := by
      show localNorm f (x₀ + s • (p - x₀)) (p - (x₀ + s • (p - x₀))) < 1
      rw [hpd, localNorm, Real.sqrt_lt' one_pos, one_pow, localInnerProd_smul']
      exact hlt
    exact h_ball _ (hseg s hs) this
  have hk : MonotoneOn (fun s => ψ s - (1 - s)⁻¹) (Set.Ico 0 1) := by
    have hderiv : ∀ s ∈ Set.Ico (0:ℝ) 1,
        HasDerivAt (fun s => ψ s - (1 - s)⁻¹) (q s - 1 / (1 - s) ^ 2) s := by
      intro s hs
      have h1 := hasDerivAt_line_grad' f x₀ (p - x₀) s (hcd s hs)
      have hne : (1 - s) ≠ 0 := by linarith [hs.2]
      have h2 := ((hasDerivAt_id' s).const_sub 1).inv hne
      convert h1.sub h2 using 1
      ring
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun s => q s - 1 / (1 - s) ^ 2)
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Ico] at hs
      exact (hderiv s (Set.Ioo_subset_Ico_self hs)).hasDerivWithinAt
    · intro s hs; rw [interior_Ico] at hs
      have hs' := Set.Ioo_subset_Ico_self hs
      have h1 := hq1 s hs'
      have hpos : 0 < (1 - s) ^ 2 := by have := hs.2; nlinarith
      show 0 ≤ q s - 1 / (1 - s) ^ 2
      rw [sub_nonneg, div_le_iff₀ hpos]; linarith
  have hh : MonotoneOn (fun s => f (x₀ + s • (p - x₀)) + Real.log (1 - s) - s * (ψ 0 - 1))
      (Set.Ico 0 1) := by
    have hderiv : ∀ s ∈ Set.Ico (0:ℝ) 1,
        HasDerivAt (fun s => f (x₀ + s • (p - x₀)) + Real.log (1 - s) - s * (ψ 0 - 1))
          (ψ s - (1 - s)⁻¹ - (ψ 0 - 1)) s := by
      intro s hs
      have h1 := hasDerivAt_line_f' f x₀ (p - x₀) s (hcd s hs)
      have hne : (1 - s) ≠ 0 := by linarith [hs.2]
      have h2 := ((hasDerivAt_id' s).const_sub 1).log hne
      have h3 := (hasDerivAt_id' s).mul_const (ψ 0 - 1)
      convert (h1.add h2).sub h3 using 1
      simp only [ψ]
      field_simp
      ring
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ico 0 1)
      (f' := fun s => ψ s - (1 - s)⁻¹ - (ψ 0 - 1))
    · intro s hs; exact (hderiv s hs).continuousAt.continuousWithinAt
    · intro s hs; rw [interior_Ico] at hs
      exact (hderiv s (Set.Ioo_subset_Ico_self hs)).hasDerivWithinAt
    · intro s hs; rw [interior_Ico] at hs
      have hs' := Set.Ioo_subset_Ico_self hs
      have := hk ⟨le_refl 0, zero_lt_one⟩ hs' hs'.1
      simp only [sub_zero, inv_one] at this
      show 0 ≤ ψ s - (1 - s)⁻¹ - (ψ 0 - 1)
      linarith
  have := hh ⟨le_refl 0, zero_lt_one⟩ ht ht.1
  simp only [ψ, zero_smul, add_zero, sub_zero, Real.log_one, zero_mul] at this
  linarith

lemma coercive_of_pos' [Nontrivial E] (A : E →L[ℝ] E) (hA : ∀ v ≠ 0, 0 < inner ℝ v (A v)) :
    ∃ c > 0, ∀ v, c * ‖v‖ ^ 2 ≤ inner ℝ v (A v) := by
  have hcpt : IsCompact (Metric.sphere (0:E) 1) := isCompact_sphere 0 1
  have hne : (Metric.sphere (0:E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
  have hcont : ContinuousOn (fun v => inner ℝ v (A v)) (Metric.sphere (0:E) 1) :=
    (continuous_id.inner A.continuous).continuousOn
  obtain ⟨v₀, hv₀, hmin⟩ := hcpt.exists_isMinOn hne hcont
  have hv₀ne : v₀ ≠ 0 := by
    intro h; rw [h] at hv₀; simp at hv₀
  refine ⟨inner ℝ v₀ (A v₀), hA v₀ hv₀ne, fun v => ?_⟩
  by_cases hv : v = 0
  · simp [hv]
  · have hnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
    have hu : ‖v‖⁻¹ • v ∈ Metric.sphere (0:E) 1 := by
      simp [norm_smul, hnorm.ne']
    have h1 := (isMinOn_iff.mp hmin) _ hu
    have hvu : v = ‖v‖ • (‖v‖⁻¹ • v) := by simp [smul_smul, hnorm.ne']
    have h2 : inner ℝ v (A v) = ‖v‖ ^ 2 * inner ℝ (‖v‖⁻¹ • v) (A (‖v‖⁻¹ • v)) := by
      conv_lhs => rw [hvu]
      simp only [map_smul, real_inner_smul_left, real_inner_smul_right]; ring
    rw [h2]
    have h3 : 0 ≤ ‖v‖ ^ 2 := by positivity
    simp only at h1
    nlinarith

lemma bounded_of_center' [Nontrivial E] (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df)
    (hDf : IsOpen Df) (hconv : Convex ℝ Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hSC : IsSelfConcordantLocalNorm f Df)
    (θ : ℝ) (hθ : 0 < θ) (hbound : ∀ x (hx : x ∈ Df), barrierIntegrand f Df h_pd ⟨x, hx⟩ ≤ θ)
    (z : E) (hz : z ∈ Df) (hgz : gradient f z = 0) : Bornology.IsBounded Df := by
  have key : ∀ y ∈ Df, localInnerProd f z (y - z) (y - z) ≤ 1 + (16 * θ) ^ 2 := by
    intro y hy
    have hr_nonneg : 0 ≤ localNorm f z (y - z) := Real.sqrt_nonneg _
    have hr2 : localNorm f z (y - z) ^ 2 = localInnerProd f z (y - z) (y - z) :=
      Real.sq_sqrt (localInnerProd_self_nonneg' f Df h_pd z hz (y - z))
    set r := localNorm f z (y - z) with hr
    by_cases hr1 : r ≤ 1
    · nlinarith
    push_neg at hr1
    have hd0 : y - z ≠ 0 := by
      intro h
      rw [h] at hr
      simp [localNorm, localInnerProd] at hr
      linarith
    have hmem : ∀ s ∈ Set.Icc (0:ℝ) 1, z + s • (y - z) ∈ Df :=
      fun s hs => hconv.add_smul_sub_mem hz hy hs
    let ψ : ℝ → ℝ := fun s => inner ℝ (gradient f (z + s • (y - z))) (y - z)
    let q : ℝ → ℝ := fun s => localInnerProd f (z + s • (y - z)) (y - z) (y - z)
    have hderiv : ∀ s ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (q s) s := fun s hs =>
      hasDerivAt_line_grad' f z (y - z) s (hf.contDiffAt (hDf.mem_nhds (hmem s hs)))
    set t₁ := 1 / (2 * r) with ht₁
    have ht₁pos : 0 < t₁ := by positivity
    have ht₁r : t₁ * r = 1 / 2 := by rw [ht₁]; field_simp
    have ht₁half : t₁ ≤ 1 / 2 := by nlinarith
    have hIcc : ∀ s ∈ Set.Icc (0:ℝ) t₁, s ∈ Set.Icc (0:ℝ) 1 :=
      fun s hs => ⟨hs.1, by linarith [hs.2]⟩
    have hqlow : ∀ s ∈ Set.Icc (0:ℝ) t₁, r ^ 2 / 4 ≤ q s := by
      intro s hs
      have hs1 := hIcc s hs
      have hy'D := hmem s hs1
      have hsub : z + s • (y - z) - z = s • (y - z) := by abel
      have hnorm_s : localNorm f z (z + s • (y - z) - z) = s * r := by
        rw [hsub, localNorm_smul', abs_of_nonneg hs.1]
      have hsr : s * r ≤ 1 / 2 := by
        rw [← ht₁r]; exact mul_le_mul_of_nonneg_right hs.2 hr_nonneg
      have hball : z + s • (y - z) ∈ localBall f z z 1 := by
        show localNorm f z (z + s • (y - z) - z) < 1
        rw [hnorm_s]; linarith
      have hsc := ((hSC z hz).2 _ hball (y - z) hd0).1
      rw [hnorm_s, ← hr] at hsc
      have hrpos : 0 < r := by linarith
      have hnn : 0 ≤ localNorm f (z + s • (y - z)) (y - z) := Real.sqrt_nonneg _
      have hq2 : localNorm f (z + s • (y - z)) (y - z) ^ 2 = q s :=
        Real.sq_sqrt (localInnerProd_self_nonneg' f Df h_pd _ hy'D (y - z))
      have h3 : r * (1 - s * r) ≤ localNorm f (z + s • (y - z)) (y - z) := by
        have := mul_le_mul_of_nonneg_left hsc hrpos.le
        rwa [← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul] at this
      have h4 : r / 2 ≤ localNorm f (z + s • (y - z)) (y - z) := by nlinarith
      rw [← hq2]
      nlinarith
    have hmono : MonotoneOn (fun s => ψ s - s * (r ^ 2 / 4)) (Set.Icc 0 t₁) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 t₁)
        (f' := fun s => q s - r ^ 2 / 4)
      · intro s hs
        exact ((hderiv s (hIcc s hs)).sub
          ((hasDerivAt_id' s).mul_const _)).continuousAt.continuousWithinAt
      · intro s hs; rw [interior_Icc] at hs
        have := (hderiv s (hIcc s (Set.Ioo_subset_Icc_self hs))).sub
          ((hasDerivAt_id' s).mul_const (r ^ 2 / 4))
        convert this.hasDerivWithinAt using 1; ring
      · intro s hs; rw [interior_Icc] at hs
        exact sub_nonneg.mpr (hqlow s (Set.Ioo_subset_Icc_self hs))
    have hψ0 : ψ 0 = 0 := by simp [ψ, hgz]
    have hmt := hmono ⟨le_refl 0, ht₁pos.le⟩ ⟨ht₁pos.le, le_refl t₁⟩ ht₁pos.le
    simp only [hψ0, zero_mul, sub_zero] at hmt
    have hψt : r / 8 ≤ ψ t₁ := by
      have : t₁ * (r ^ 2 / 4) = r / 8 := by
        have : t₁ * (r ^ 2 / 4) = (t₁ * r) * r / 4 := by ring
        rw [this, ht₁r]; ring
      linarith
    have hθb := theta_bound' f Df hf hDf hconv h_pd θ hθ hbound (z + t₁ • (y - z)) y
      (hmem t₁ (hIcc t₁ ⟨ht₁pos.le, le_refl t₁⟩)) hy
    have hyx : y - (z + t₁ • (y - z)) = (1 - t₁) • (y - z) := by module
    rw [hyx, real_inner_smul_right] at hθb
    have hψtpos : 0 < ψ t₁ := by linarith
    have h5 : r ≤ 16 * θ := by
      have : (1 / 2) * ψ t₁ ≤ (1 - t₁) * ψ t₁ :=
        mul_le_mul_of_nonneg_right (by linarith) hψtpos.le
      have : (1 - t₁) * ψ t₁ ≤ θ := hθb
      linarith
    nlinarith
  obtain ⟨c, hc, hcoer⟩ := coercive_of_pos' (hessianOperator f z) (fun v hv => h_pd z hz v hv)
  rw [Metric.isBounded_iff_subset_closedBall z]
  refine ⟨Real.sqrt ((1 + (16 * θ) ^ 2) / c), fun y hy => ?_⟩
  rw [Metric.mem_closedBall, dist_eq_norm]
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ hc]
  have h1 := hcoer (y - z)
  have h2 := key y hy
  unfold localInnerProd at h2
  linarith

lemma center_of_bounded' (f : E → ℝ) (Df : Set E) (hf : ContDiffOn ℝ 2 f Df) (hDf : IsOpen Df)
    (hconv : Convex ℝ Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (h_ball : ∀ x ∈ Df, localBall f x x 1 ⊆ Df)
    (hne : Df.Nonempty) (hbdd : Bornology.IsBounded Df) : ∃ z, IsAnalyticCenter f Df z := by
  obtain ⟨x₀, hx₀⟩ := hne
  have blowup : ∀ p ∈ closure Df, p ∉ Df → ∀ M : ℝ, ∃ δ > 0, ∀ x ∈ Df, dist x p < δ → M < f x := by
    intro p hpcl hpD M
    obtain ⟨ρ, hρ, hball⟩ := Metric.isOpen_iff.mp hDf x₀ hx₀
    have hcb : Metric.closedBall x₀ (ρ / 2) ⊆ Df :=
      (Metric.closedBall_subset_ball (by linarith)).trans hball
    obtain ⟨C, hC⟩ : ∃ C, ∀ u ∈ Metric.closedBall x₀ (ρ / 2), f u ≤ C := by
      obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ (ρ / 2)).bddAbove_image (hf.continuousOn.mono hcb)
      exact ⟨C, fun u hu => hC ⟨u, hu, rfl⟩⟩
    have hx₀int : x₀ ∈ interior Df := by rw [hDf.interior_eq]; exact hx₀
    have hseg : ∀ s ∈ Set.Ico (0:ℝ) 1, x₀ + s • (p - x₀) ∈ Df := by
      intro s hs
      have := hconv.combo_interior_closure_mem_interior hx₀int hpcl (sub_pos.mpr hs.2) hs.1
        (by ring : (1 - s) + s = 1)
      rw [hDf.interior_eq] at this
      convert this using 1
      module
    set ψ₀ := inner ℝ (gradient f x₀) (p - x₀) with hψ₀
    set K := |M| + |C| + |f x₀| + |ψ₀ - 1| + 1 with hK
    have hKpos : 0 < K := by positivity
    set t := 1 - Real.exp (-K) with ht
    have ht0 : 0 < t := by
      have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hKpos); linarith
    have ht1 : t < 1 := by have := Real.exp_pos (-K); linarith
    have hlog : Real.log (1 - t) = -K := by rw [ht, _root_.sub_sub_cancel, Real.log_exp]
    have hw := blowup_bound' f Df hf hDf h_ball x₀ p hpD hseg t ⟨ht0.le, ht1⟩
    rw [hlog, ← hψ₀] at hw
    refine ⟨(ρ / 2) * (1 - t) / t, by have := sub_pos.mpr ht1; positivity, fun x hx hxp => ?_⟩
    have h1t : 0 < 1 - t := sub_pos.mpr ht1
    set u := x₀ + (t / (1 - t)) • (p - x) with hu
    have huball : u ∈ Metric.closedBall x₀ (ρ / 2) := by
      rw [Metric.mem_closedBall, dist_eq_norm, hu, add_sub_cancel_left, norm_smul,
        Real.norm_eq_abs, abs_of_pos (div_pos ht0 h1t), ← dist_eq_norm, _root_.dist_comm]
      rw [lt_div_iff₀ ht0] at hxp
      rw [div_mul_eq_mul_div, div_le_iff₀ h1t]
      nlinarith
    have huD : u ∈ Df := hcb huball
    have hfu : f u ≤ C := hC u huball
    set w := x₀ + t • (p - x₀) with hw_def
    have hwD : w ∈ Df := hseg t ⟨ht0.le, ht1⟩
    have hw_eq : w = t • x + (1 - t) • u := by
      rw [hw_def, hu, smul_add, smul_smul, mul_div_cancel₀ _ h1t.ne']
      module
    have hc1 := first_order' f Df hf hDf hconv h_pd w x hwD hx
    have hc2 := first_order' f Df hf hDf hconv h_pd w u hwD huD
    have hzero : t * inner ℝ (gradient f w) (x - w) + (1 - t) * inner ℝ (gradient f w) (u - w)
        = 0 := by
      rw [← real_inner_smul_right, ← real_inner_smul_right, ← inner_add_right]
      have : t • (x - w) + (1 - t) • (u - w) = 0 := by
        rw [hw_eq]; module
      rw [this, inner_zero_right]
    have hconvex : f w ≤ t * f x + (1 - t) * f u := by
      nlinarith [mul_le_mul_of_nonneg_left hc1 ht0.le, mul_le_mul_of_nonneg_left hc2 h1t.le]
    have hA : -|ψ₀ - 1| ≤ t * (ψ₀ - 1) := by
      nlinarith [mul_nonneg ht0.le (by linarith [neg_abs_le (ψ₀ - 1)] : 0 ≤ ψ₀ - 1 + |ψ₀ - 1|),
        mul_nonneg h1t.le (abs_nonneg (ψ₀ - 1))]
    have hB : (1 - t) * f u ≤ |C| := by
      nlinarith [mul_le_mul_of_nonneg_left hfu h1t.le, le_abs_self C, abs_nonneg C,
        mul_nonneg ht0.le (abs_nonneg C), mul_nonneg h1t.le (sub_nonneg.mpr (le_abs_self C))]
    have hM' : t * M ≤ |M| := by
      nlinarith [le_abs_self M, abs_nonneg M, mul_nonneg ht0.le (sub_nonneg.mpr (le_abs_self M)),
        mul_nonneg h1t.le (abs_nonneg M)]
    have hfx0 : -|f x₀| ≤ f x₀ := neg_abs_le _
    have htfx : t * M < t * f x := by linarith
    exact lt_of_mul_lt_mul_left htfx ht0.le
  set S := {x ∈ Df | f x ≤ f x₀} with hS
  have hSsub : S ⊆ Df := fun x hx => hx.1
  have hSclosed : IsClosed S := by
    apply isClosed_of_closure_subset
    intro x hx
    have hxD : x ∈ closure Df := closure_mono hSsub hx
    by_cases hxin : x ∈ Df
    · refine ⟨hxin, ?_⟩
      have hcont : ContinuousAt f x := hf.continuousOn.continuousAt (hDf.mem_nhds hxin)
      exact ContinuousWithinAt.closure_le hx hcont.continuousWithinAt continuousWithinAt_const
        (fun y hy => hy.2)
    · obtain ⟨δ, hδ, hδ'⟩ := blowup x hxD hxin (f x₀)
      obtain ⟨y, hyS, hyx⟩ := Metric.mem_closure_iff.mp hx δ hδ
      exact absurd hyS.2 (not_le.mpr (hδ' y hyS.1 (by rw [_root_.dist_comm]; exact hyx)))
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSclosed (hbdd.subset hSsub)
  obtain ⟨z, hzS, hzmin⟩ := hScpt.exists_isMinOn ⟨x₀, hx₀, le_refl _⟩
    (hf.continuousOn.mono hSsub)
  refine ⟨z, hzS.1, ?_⟩
  have hmin : IsMinOn f Df z := by
    rw [isMinOn_iff]
    intro x hx
    by_cases hxS : f x ≤ f x₀
    · exact (isMinOn_iff.mp hzmin) x ⟨hx, hxS⟩
    · push_neg at hxS; exact le_trans hzS.2 hxS.le
  have hloc : IsLocalMin f z := hmin.isLocalMin (hDf.mem_nhds hzS.1)
  have := hloc.fderiv_eq_zero
  simp [gradient, this]

theorem Renegar_chap_2_2_3_6 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (hDf_nonempty : Set.Nonempty Df)
  (hf_sc : IsSCBarrier f Df h_Df_pd) :
  (∃ x, IsAnalyticCenter f Df x) ↔ (Bornology.IsBounded Df) := by
  obtain ⟨hSC, hBdd⟩ := hf_sc
  obtain ⟨M, hM⟩ := hBdd
  have hθpos : 0 < max M 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hbound : ∀ x (hx : x ∈ Df), barrierIntegrand f Df h_Df_pd ⟨x, hx⟩ ≤ max M 1 :=
    fun x hx => le_trans (hM ⟨⟨x, hx⟩, rfl⟩) (le_max_left _ _)
  constructor
  · rintro ⟨z, hzD, hgz⟩
    exact bounded_of_center' f Df hf_C2 h_Df_open h_Df_convex h_Df_pd hSC (max M 1) hθpos hbound
      z hzD hgz
  · intro hbdd
    exact center_of_bounded' f Df hf_C2 h_Df_open h_Df_convex h_Df_pd
      (fun x hx => (hSC x hx).1) hDf_nonempty hbdd

end Renegar_chap_2_2_3_6
