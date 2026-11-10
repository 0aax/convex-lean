import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_1`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_1`, so the main result is `Renegar_chap_2_2_3_1.Renegar_chap_2_2_3_1`.
-/

namespace Renegar_chap_2_2_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

open InnerProductSpace in
lemma aux_gradient_differentiableAt {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) :
    DifferentiableAt ℝ (gradient f) x := by
  have hL : IsBoundedLinearMap ℝ (fun p : StrongDual ℝ E => (toDual ℝ E).symm p) :=
    { map_add := fun p q => map_add _ p q
      map_smul := fun c p => by simp
      bound := ⟨1, one_pos, fun p => by simp⟩ }
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  exact hL.differentiableAt.comp x hdf

lemma aux_inner_hessian {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    inner ℝ u (hessianOperator f x v) = fderiv ℝ (fderiv ℝ f) x v u := by
  have hdg := aux_gradient_differentiableAt hf
  have hdf : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have h1 : HasFDerivAt (fun y => inner ℝ u (gradient f y))
      ((innerSL ℝ u).comp (hessianOperator f x)) x :=
    (innerSL ℝ u).hasFDerivAt.comp x hdg.hasFDerivAt
  have h2 : HasFDerivAt (fun y => fderiv ℝ f y u)
      ((fderiv ℝ f x).comp (0 : E →L[ℝ] E) + (fderiv ℝ (fderiv ℝ f) x).flip u) x :=
    hdf.hasFDerivAt.clm_apply (hasFDerivAt_const u x)
  have h3 : (fun y => inner ℝ u (gradient f y)) = fun y => fderiv ℝ f y u := by
    funext y
    rw [real_inner_comm]
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  rw [h3] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simpa using this

lemma aux_hessian_symm {f : E → ℝ} {x : E} (hf : ContDiffAt ℝ 2 f x) (u v : E) :
    inner ℝ u (hessianOperator f x v) = inner ℝ v (hessianOperator f x u) := by
  rw [aux_inner_hessian hf, aux_inner_hessian hf]
  exact (hf.isSymmSndFDerivAt (by simp)).eq v u

lemma aux_gradient_add {f₁ f₂ : E → ℝ} {y : E} (h₁ : DifferentiableAt ℝ f₁ y)
    (h₂ : DifferentiableAt ℝ f₂ y) :
    gradient (f₁ + f₂) y = gradient f₁ y + gradient f₂ y := by
  simp only [gradient]
  rw [fderiv_add h₁ h₂, map_add]

lemma aux_hessian_add {f₁ f₂ : E → ℝ} {S : Set E} (hS : IsOpen S) (hf₁ : ContDiffOn ℝ 2 f₁ S)
    (hf₂ : ContDiffOn ℝ 2 f₂ S) {x : E} (hx : x ∈ S) :
    hessianOperator (f₁ + f₂) x = hessianOperator f₁ x + hessianOperator f₂ x := by
  have hev : gradient (f₁ + f₂) =ᶠ[𝓝 x] fun y => gradient f₁ y + gradient f₂ y := by
    filter_upwards [hS.mem_nhds hx] with y hy
    exact aux_gradient_add ((hf₁.contDiffAt (hS.mem_nhds hy)).differentiableAt two_ne_zero)
      ((hf₂.contDiffAt (hS.mem_nhds hy)).differentiableAt two_ne_zero)
  unfold hessianOperator
  rw [hev.fderiv_eq]
  exact fderiv_fun_add (aux_gradient_differentiableAt (hf₁.contDiffAt (hS.mem_nhds hx)))
    (aux_gradient_differentiableAt (hf₂.contDiffAt (hS.mem_nhds hx)))

lemma aux_hessian_localGradient (f : E → ℝ) (Df : Set E)
    (h : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (x y : E) (hx : x ∈ Df) :
    hessianOperator f x (localGradient f Df h x y hx) = gradient f y := by
  unfold localGradient
  exact (hessianLinearEquiv f Df x hx h).apply_symm_apply (gradient f y)

lemma aux_localInnerProd_nonneg (f : E → ℝ) (Df : Set E)
    (h : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) {x : E} (hx : x ∈ Df) (v : E) :
    0 ≤ localInnerProd f x v v := by
  by_cases hv : v = 0
  · subst hv; simp [localInnerProd]
  · exact (h x hx v hv).le

lemma aux_barrierIntegrand_eq (f : E → ℝ) (Df : Set E)
    (h : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (x : Df) :
    barrierIntegrand f Df h x = localInnerProd f x.1 (localGradient f Df h x.1 x.1 x.2)
      (localGradient f Df h x.1 x.1 x.2) := by
  unfold barrierIntegrand localNorm
  rw [Real.sq_sqrt (aux_localInnerProd_nonneg f Df h x.2 _)]

lemma aux_real_sc (a₁ a₂ b₁ b₂ q₁ q₂ : ℝ) (ha₁ : 0 < a₁) (ha₂ : 0 < a₂) (hb₁ : 0 ≤ b₁)
    (hb₂ : 0 ≤ b₂) (hq₁ : 0 ≤ q₁) (hq₂ : 0 ≤ q₂) (hr : √(q₁ + q₂) < 1)
    (h₁ : 1 - √q₁ ≤ (√a₁)⁻¹ * √b₁ ∧ (√a₁)⁻¹ * √b₁ ≤ (1 - √q₁)⁻¹)
    (h₂ : 1 - √q₂ ≤ (√a₂)⁻¹ * √b₂ ∧ (√a₂)⁻¹ * √b₂ ≤ (1 - √q₂)⁻¹) :
    1 - √(q₁ + q₂) ≤ (√(a₁ + a₂))⁻¹ * √(b₁ + b₂) ∧
      (√(a₁ + a₂))⁻¹ * √(b₁ + b₂) ≤ (1 - √(q₁ + q₂))⁻¹ := by
  have hρ₁ : √q₁ ≤ √(q₁ + q₂) := Real.sqrt_le_sqrt (by linarith)
  have hρ₂ : √q₂ ≤ √(q₁ + q₂) := Real.sqrt_le_sqrt (by linarith)
  set c := 1 - √(q₁ + q₂) with hc
  have hc0 : 0 < c := by linarith
  have hc₁ : c ≤ 1 - √q₁ := by linarith
  have hc₂ : c ≤ 1 - √q₂ := by linarith
  have hd₁ : 0 < 1 - √q₁ := by linarith
  have hd₂ : 0 < 1 - √q₂ := by linarith
  have hs₁ : 0 < √a₁ := Real.sqrt_pos.mpr ha₁
  have hs₂ : 0 < √a₂ := Real.sqrt_pos.mpr ha₂
  have ht₁ : 0 ≤ √b₁ := Real.sqrt_nonneg _
  have ht₂ : 0 ≤ √b₂ := Real.sqrt_nonneg _
  -- lower bounds: c * √aᵢ ≤ √bᵢ
  have l₁ : c * √a₁ ≤ √b₁ := by
    have h := h₁.1
    rw [le_inv_mul_iff₀ hs₁] at h
    nlinarith
  have l₂ : c * √a₂ ≤ √b₂ := by
    have h := h₂.1
    rw [le_inv_mul_iff₀ hs₂] at h
    nlinarith
  -- upper bounds: c * √bᵢ ≤ √aᵢ
  have u₁ : c * √b₁ ≤ √a₁ := by
    have h := h₁.2
    rw [inv_mul_le_iff₀ hs₁, le_mul_inv_iff₀ hd₁] at h
    nlinarith
  have u₂ : c * √b₂ ≤ √a₂ := by
    have h := h₂.2
    rw [inv_mul_le_iff₀ hs₂, le_mul_inv_iff₀ hd₂] at h
    nlinarith
  -- squares
  have sa₁ := Real.sq_sqrt ha₁.le
  have sa₂ := Real.sq_sqrt ha₂.le
  have sb₁ := Real.sq_sqrt hb₁
  have sb₂ := Real.sq_sqrt hb₂
  have L₁ : c ^ 2 * a₁ ≤ b₁ := by
    have := pow_le_pow_left₀ (by positivity) l₁ 2
    rw [mul_pow, sa₁, sb₁] at this
    exact this
  have L₂ : c ^ 2 * a₂ ≤ b₂ := by
    have := pow_le_pow_left₀ (by positivity) l₂ 2
    rw [mul_pow, sa₂, sb₂] at this
    exact this
  have U₁ : c ^ 2 * b₁ ≤ a₁ := by
    have := pow_le_pow_left₀ (by positivity) u₁ 2
    rw [mul_pow, sa₁, sb₁] at this
    exact this
  have U₂ : c ^ 2 * b₂ ≤ a₂ := by
    have := pow_le_pow_left₀ (by positivity) u₂ 2
    rw [mul_pow, sa₂, sb₂] at this
    exact this
  have hsA : 0 < √(a₁ + a₂) := Real.sqrt_pos.mpr (by linarith)
  have hcA : c * √(a₁ + a₂) ≤ √(b₁ + b₂) := by
    rw [← Real.sqrt_sq hc0.le, ← Real.sqrt_mul (sq_nonneg c)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hcB : c * √(b₁ + b₂) ≤ √(a₁ + a₂) := by
    rw [← Real.sqrt_sq hc0.le, ← Real.sqrt_mul (sq_nonneg c)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  constructor
  · rw [le_inv_mul_iff₀ hsA]
    linarith [mul_comm c (√(a₁ + a₂))]
  · rw [inv_mul_le_iff₀ hsA, le_mul_inv_iff₀ hc0]
    linarith [mul_comm c (√(b₁ + b₂))]

lemma aux_barrier_le (f₁ f₂ : E → ℝ) (Df₁ Df₂ : Set E)
    (h_Df₁_open : IsOpen Df₁) (h_Df₂_open : IsOpen Df₂)
    (hf₁_C2 : ContDiffOn ℝ 2 f₁ Df₁) (hf₂_C2 : ContDiffOn ℝ 2 f₂ Df₂)
    (h_Df₁_pd : ∀ x ∈ Df₁, ∀ v ≠ 0, 0 < localInnerProd (f := f₁) x v v)
    (h_Df₂_pd : ∀ x ∈ Df₂, ∀ v ≠ 0, 0 < localInnerProd (f := f₂) x v v)
    (h_Df₁f₂_pd : ∀ x ∈ Df₁ ∩ Df₂, ∀ v ≠ 0, 0 < localInnerProd (f := f₁ + f₂) x v v)
    (x : E) (hx : x ∈ Df₁ ∩ Df₂) :
    barrierIntegrand (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd ⟨x, hx⟩ ≤
      barrierIntegrand f₁ Df₁ h_Df₁_pd ⟨x, hx.1⟩ + barrierIntegrand f₂ Df₂ h_Df₂_pd ⟨x, hx.2⟩ := by
  rw [aux_barrierIntegrand_eq, aux_barrierIntegrand_eq, aux_barrierIntegrand_eq]
  have hc₁ : ContDiffAt ℝ 2 f₁ x := hf₁_C2.contDiffAt (h_Df₁_open.mem_nhds hx.1)
  have hc₂ : ContDiffAt ℝ 2 f₂ x := hf₂_C2.contDiffAt (h_Df₂_open.mem_nhds hx.2)
  have hS : IsOpen (Df₁ ∩ Df₂) := h_Df₁_open.inter h_Df₂_open
  have hH : hessianOperator (f₁ + f₂) x = hessianOperator f₁ x + hessianOperator f₂ x :=
    aux_hessian_add hS (hf₁_C2.mono Set.inter_subset_left) (hf₂_C2.mono Set.inter_subset_right) hx
  have hg : gradient (f₁ + f₂) x = gradient f₁ x + gradient f₂ x :=
    aux_gradient_add (hc₁.differentiableAt two_ne_zero) (hc₂.differentiableAt two_ne_zero)
  have hw := aux_hessian_localGradient (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd x x hx
  have hw₁ := aux_hessian_localGradient f₁ Df₁ h_Df₁_pd x x hx.1
  have hw₂ := aux_hessian_localGradient f₂ Df₂ h_Df₂_pd x x hx.2
  set w := localGradient (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd x x hx
  set w₁ := localGradient f₁ Df₁ h_Df₁_pd x x hx.1
  set w₂ := localGradient f₂ Df₂ h_Df₂_pd x x hx.2
  have hs₁ := aux_hessian_symm hc₁ w₁ w
  have hs₂ := aux_hessian_symm hc₂ w₂ w
  have hp₁ := aux_localInnerProd_nonneg f₁ Df₁ h_Df₁_pd hx.1 (w₁ - w)
  have hp₂ := aux_localInnerProd_nonneg f₂ Df₂ h_Df₂_pd hx.2 (w₂ - w)
  simp only [localInnerProd] at hp₁ hp₂ ⊢
  have e1 : inner ℝ w (hessianOperator (f₁ + f₂) x w) =
      inner ℝ w (hessianOperator f₁ x w) + inner ℝ w (hessianOperator f₂ x w) := by
    rw [hH, ContinuousLinearMap.add_apply, inner_add_right]
  have e2 : inner ℝ w (hessianOperator (f₁ + f₂) x w) =
      inner ℝ w (hessianOperator f₁ x w₁) + inner ℝ w (hessianOperator f₂ x w₂) := by
    rw [hw, hg, inner_add_right, hw₁, hw₂]
  rw [map_sub, inner_sub_left, inner_sub_right, inner_sub_right] at hp₁ hp₂
  linarith

set_option linter.unusedVariables false in
theorem Renegar_chap_2_2_3_1 [Nontrivial E]
  (f₁ f₂ : E → ℝ)
  (Df₁ Df₂ : Set E)
  (h_Df₁_open : IsOpen Df₁) (h_Df₁_convex : Convex ℝ Df₁)
  (h_Df₂_open : IsOpen Df₂) (h_Df₂_convex : Convex ℝ Df₂)
  (hf₁_C2 : ContDiffOn ℝ 2 f₁ Df₁) (hf₂_C2 : ContDiffOn ℝ 2 f₂ Df₂)
  (h_Df₁_pd : ∀ x ∈ Df₁, ∀ v ≠ 0, 0 < localInnerProd (f := f₁) x v v)
  (h_Df₂_pd : ∀ x ∈ Df₂, ∀ v ≠ 0, 0 < localInnerProd (f := f₂) x v v)
  (h_Df₁f₂_pd : ∀ x ∈ Df₁ ∩ Df₂, ∀ v ≠ 0, 0 < localInnerProd (f := f₁ + f₂) x v v)
  (hf₁_sc : IsSCBarrier f₁ Df₁ h_Df₁_pd)
  (hf₂_sc : IsSCBarrier f₂ Df₂ h_Df₂_pd)
  (h_Df : Set.Nonempty (Df₁ ∩ Df₂)) :
  (IsSCBarrier (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd) ∧
  (barrierParameter (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd ≤
    barrierParameter f₁ Df₁ h_Df₁_pd +
    barrierParameter f₂ Df₂ h_Df₂_pd) := by
  obtain ⟨hsc₁, hbdd₁⟩ := hf₁_sc
  obtain ⟨hsc₂, hbdd₂⟩ := hf₂_sc
  have hS : IsOpen (Df₁ ∩ Df₂) := h_Df₁_open.inter h_Df₂_open
  -- the local inner product of the sum splits on the common domain
  have hIP : ∀ z ∈ Df₁ ∩ Df₂, ∀ u v, localInnerProd (f₁ + f₂) z u v =
      localInnerProd f₁ z u v + localInnerProd f₂ z u v := by
    intro z hz u v
    simp only [localInnerProd, aux_hessian_add hS (hf₁_C2.mono Set.inter_subset_left)
      (hf₂_C2.mono Set.inter_subset_right) hz, ContinuousLinearMap.add_apply, inner_add_right]
  have hN : ∀ z ∈ Df₁ ∩ Df₂, ∀ v, localNorm (f₁ + f₂) z v =
      √(localInnerProd f₁ z v v + localInnerProd f₂ z v v) := by
    intro z hz v
    simp only [localNorm, hIP z hz]
  have hnn₁ : ∀ {z : E}, z ∈ Df₁ → ∀ v, 0 ≤ localInnerProd f₁ z v v :=
    fun hz v => aux_localInnerProd_nonneg f₁ Df₁ h_Df₁_pd hz v
  have hnn₂ : ∀ {z : E}, z ∈ Df₂ → ∀ v, 0 ≤ localInnerProd f₂ z v v :=
    fun hz v => aux_localInnerProd_nonneg f₂ Df₂ h_Df₂_pd hz v
  -- self-concordance of the sum
  have hSC : IsSelfConcordantLocalNorm (f₁ + f₂) (Df₁ ∩ Df₂) := by
    intro x hx
    have hx₁ := hx.1
    have hx₂ := hx.2
    have hball₁ : ∀ y, y ∈ localBall (f₁ + f₂) x x 1 → y ∈ localBall f₁ x x 1 := by
      intro y hy
      simp only [localBall, Set.mem_setOf_eq, hN x hx] at hy ⊢
      unfold localNorm
      calc √(localInnerProd f₁ x (y - x) (y - x))
          ≤ √(localInnerProd f₁ x (y - x) (y - x) + localInnerProd f₂ x (y - x) (y - x)) :=
            Real.sqrt_le_sqrt (by linarith [hnn₂ hx₂ (y - x)])
        _ < 1 := hy
    have hball₂ : ∀ y, y ∈ localBall (f₁ + f₂) x x 1 → y ∈ localBall f₂ x x 1 := by
      intro y hy
      simp only [localBall, Set.mem_setOf_eq, hN x hx] at hy ⊢
      unfold localNorm
      calc √(localInnerProd f₂ x (y - x) (y - x))
          ≤ √(localInnerProd f₁ x (y - x) (y - x) + localInnerProd f₂ x (y - x) (y - x)) :=
            Real.sqrt_le_sqrt (by linarith [hnn₁ hx₁ (y - x)])
        _ < 1 := hy
    have hball : localBall (f₁ + f₂) x x 1 ⊆ Df₁ ∩ Df₂ := fun y hy =>
      ⟨(hsc₁ x hx₁).1 (hball₁ y hy), (hsc₂ x hx₂).1 (hball₂ y hy)⟩
    refine ⟨hball, ?_⟩
    intro y hy v hv
    have hyD := hball hy
    have k₁ := (hsc₁ x hx₁).2 y (hball₁ y hy) v hv
    have k₂ := (hsc₂ x hx₂).2 y (hball₂ y hy) v hv
    have hr : localNorm (f₁ + f₂) x (y - x) < 1 := hy
    rw [hN x hx] at hr ⊢
    rw [hN x hx, hN y hyD]
    unfold localNorm at k₁ k₂
    exact aux_real_sc _ _ _ _ _ _ (h_Df₁_pd x hx₁ v hv) (h_Df₂_pd x hx₂ v hv)
      (hnn₁ hyD.1 v) (hnn₂ hyD.2 v) (hnn₁ hx₁ _) (hnn₂ hx₂ _) hr k₁ k₂
  -- pointwise bound on the barrier integrand
  have key : ∀ x : ↥(Df₁ ∩ Df₂), barrierIntegrand (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd x ≤
      barrierParameter f₁ Df₁ h_Df₁_pd + barrierParameter f₂ Df₂ h_Df₂_pd := by
    rintro ⟨x, hx⟩
    calc _ ≤ barrierIntegrand f₁ Df₁ h_Df₁_pd ⟨x, hx.1⟩ +
          barrierIntegrand f₂ Df₂ h_Df₂_pd ⟨x, hx.2⟩ :=
        aux_barrier_le f₁ f₂ Df₁ Df₂ h_Df₁_open h_Df₂_open hf₁_C2 hf₂_C2 h_Df₁_pd h_Df₂_pd
          h_Df₁f₂_pd x hx
      _ ≤ _ := add_le_add (le_csSup hbdd₁ ⟨⟨x, hx.1⟩, rfl⟩) (le_csSup hbdd₂ ⟨⟨x, hx.2⟩, rfl⟩)
  have hub : ∀ b ∈ Set.range (fun x : ↥(Df₁ ∩ Df₂) =>
      barrierIntegrand (f₁ + f₂) (Df₁ ∩ Df₂) h_Df₁f₂_pd x),
      b ≤ barrierParameter f₁ Df₁ h_Df₁_pd + barrierParameter f₂ Df₂ h_Df₂_pd := by
    rintro _ ⟨x, rfl⟩
    exact key x
  haveI : Nonempty ↥(Df₁ ∩ Df₂) := h_Df.to_subtype
  refine ⟨⟨hSC, ⟨_, hub⟩⟩, ?_⟩
  exact csSup_le (Set.range_nonempty _) hub

end Renegar_chap_2_2_3_1
