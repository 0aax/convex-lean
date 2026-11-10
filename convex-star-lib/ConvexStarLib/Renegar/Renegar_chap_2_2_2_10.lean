import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_2_10`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_2_10` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_2_10`, so the main result is `Renegar_chap_2_2_2_10.Renegar_chap_2_2_2_10`.
-/

namespace Renegar_chap_2_2_2_10

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma aux_localInnerProd_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y c d : E) (α β : ℝ) :
    localInnerProd f y (α • c + β • d) (α • c + β • d) =
      α ^ 2 * localInnerProd f y c c + α * β * (localInnerProd f y c d + localInnerProd f y d c)
        + β ^ 2 * localInnerProd f y d d := by
  simp only [localInnerProd, map_add, map_smul, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right]
  ring

lemma aux_localInnerProd_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y c : E) (α : ℝ) :
    localInnerProd f y (α • c) (α • c) = α ^ 2 * localInnerProd f y c c := by
  simp only [localInnerProd, map_smul, real_inner_smul_left, real_inner_smul_right]
  ring

lemma aux_localNorm_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y c : E) (α : ℝ) :
    localNorm f y (α • c) = |α| * localNorm f y c := by
  unfold localNorm
  rw [aux_localInnerProd_smul, Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq_eq_abs]

lemma aux_localNorm_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y c : E) : 0 ≤ localNorm f y c :=
  Real.sqrt_nonneg _

lemma aux_Q_nonneg {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (y : E) (hy : y ∈ Df) (c : E) :
    0 ≤ localInnerProd f y c c := by
  by_cases hc : c = 0
  · simp [hc, localInnerProd]
  · exact (h_Df_pd y hy c hc).le

lemma aux_norm_sq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) (y : E) (hy : y ∈ Df) (c : E) :
    localNorm f y c ^ 2 = localInnerProd f y c c :=
  Real.sq_sqrt (aux_Q_nonneg f Df h_Df_pd y hy c)

lemma aux_hessian_inner {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y a b : E) :
    localInnerProd f y a b = fderiv ℝ (fderiv ℝ f) y b a := by
  unfold localInnerProd hessianOperator
  have : (fun z => gradient f z) = (InnerProductSpace.toDual ℝ E).symm ∘ (fderiv ℝ f) := by
    funext z; rfl
  rw [this, LinearIsometryEquiv.comp_fderiv]
  rw [real_inner_comm]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply]
  exact InnerProductSpace.toDual_symm_apply

lemma aux_hessian_symm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) (a b : E) :
    localInnerProd f y a b = localInnerProd f y b a := by
  rw [aux_hessian_inner, aux_hessian_inner]
  exact (hf.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField])) b a

lemma aux_hasFDerivAt_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y : E) (hf : ContDiffAt ℝ 2 f y) :
    HasFDerivAt (fun z => gradient f z) (hessianOperator f y) y := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) y := hf.fderiv_right (by norm_num)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) y := h1.differentiableAt (by norm_num)
  have h3 : DifferentiableAt ℝ (fun z => gradient f z) y := by
    have : (fun z => gradient f z) = (InnerProductSpace.toDual ℝ E).symm ∘ (fderiv ℝ f) := by
      funext z; rfl
    rw [this]
    exact (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.differentiableAt.comp y h2
  exact h3.hasFDerivAt

lemma aux_inner_gradient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (y w : E) : inner ℝ (gradient f y) w = fderiv ℝ f y w := by
  unfold gradient; exact InnerProductSpace.toDual_symm_apply

lemma aux_mono01 {gg gd : ℝ → ℝ} (hgg : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt gg (gd t) t)
    (hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ gd t) : gg 0 ≤ gg 1 := by
  have hcont : ContinuousOn gg (Set.Icc 0 1) :=
    fun t ht => (hgg t ht).continuousAt.continuousWithinAt
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) 1) hcont
    (fun t ht => (hgg t (interior_subset ht)).hasDerivWithinAt)
    (fun t ht => hpos t (interior_subset ht))
  exact hmono (Set.left_mem_Icc.mpr zero_le_one) (Set.right_mem_Icc.mpr zero_le_one) zero_le_one

lemma aux_deriv_line {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (q d e : E) (t : ℝ)
    (hg : HasFDerivAt (fun z => gradient f z) (hessianOperator f (q + t • d)) (q + t • d)) :
    HasDerivAt (fun t : ℝ => inner ℝ e (gradient f (q + t • d)))
      (localInnerProd f (q + t • d) e d) t := by
  have hline : HasDerivAt (fun t : ℝ => q + t • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add q
  have h2 := hg.comp_hasDerivAt t hline
  have h3 := ((innerSL ℝ e).hasFDerivAt).comp_hasDerivAt t h2
  simpa [localInnerProd, Function.comp_def] using h3

/-- Self-concordance, quadratic-form version. -/
lemma aux_SC_quad {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hf_sc : IsSelfConcordantLocalNorm f Df) (q : E) (hq : q ∈ Df) (y : E)
    (hy : localNorm f q (y - q) < 1) :
    y ∈ Df ∧ ∀ c, (1 - localNorm f q (y - q)) ^ 2 * localInnerProd f q c c ≤ localInnerProd f y c c ∧
      (1 - localNorm f q (y - q)) ^ 2 * localInnerProd f y c c ≤ localInnerProd f q c c := by
  obtain ⟨hball, hsc⟩ := hf_sc q hq
  have hyD : y ∈ Df := hball hy
  refine ⟨hyD, fun c => ?_⟩
  by_cases hc : c = 0
  · subst hc; simp [localInnerProd]
  obtain ⟨h1, h2⟩ := hsc y hy c hc
  generalize localNorm f q (y - q) = δ at hy h1 h2 ⊢
  have hδ1 : 0 < 1 - δ := by linarith
  have hqpos : 0 < localNorm f q c := Real.sqrt_pos.mpr (h_Df_pd q hq c hc)
  have hny : 0 ≤ localNorm f y c := aux_localNorm_nonneg f y c
  rw [← aux_norm_sq f Df h_Df_pd q hq c, ← aux_norm_sq f Df h_Df_pd y hyD c]
  generalize localNorm f q c = nq at hqpos h1 h2 ⊢
  generalize localNorm f y c = ny at hny h1 h2 ⊢
  have e1 : (1 - δ) * nq ≤ ny := by
    rw [le_inv_mul_iff₀ hqpos] at h1
    linarith
  have e2 : (1 - δ) * ny ≤ nq := by
    rw [inv_mul_le_iff₀ hqpos] at h2
    have := mul_le_mul_of_nonneg_left h2 hδ1.le
    rw [mul_left_comm, mul_inv_cancel₀ hδ1.ne', mul_one] at this
    linarith
  have e1' : 0 ≤ (1 - δ) * nq := by positivity
  have e2' : 0 ≤ (1 - δ) * ny := by positivity
  constructor
  · have := mul_le_mul e1 e1 e1' hny
    linarith
  · have := mul_le_mul e2 e2 e2' hqpos.le
    linarith

/-- Pure algebra for the polarization (bilinear) bound. -/
lemma aux_bilin_alg (a ρ μ By Bx Qyw Qyv : ℝ) (ha : 0 < a) (hρ : 0 < ρ) (hμ : 0 < μ)
    (hYp : μ * (a ^ 2 * ρ ^ 2 + a * ρ * (Bx + Bx) + ρ ^ 2 * a ^ 2) ≤
      a ^ 2 * Qyw + a * ρ * (By + By) + ρ ^ 2 * Qyv)
    (hYm : μ * (a ^ 2 * Qyw + a * (-ρ) * (By + By) + (-ρ) ^ 2 * Qyv) ≤
      a ^ 2 * ρ ^ 2 + a * (-ρ) * (Bx + Bx) + (-ρ) ^ 2 * a ^ 2)
    (hXp : 0 ≤ a ^ 2 * ρ ^ 2 + a * ρ * (Bx + Bx) + ρ ^ 2 * a ^ 2) :
    0 ≤ By - Bx + (a / μ - a) * ρ := by
  have key : 0 ≤ 4 * a * ρ * (μ * (By - Bx) + (1 - μ) * a * ρ) := by
    linarith [mul_le_mul_of_nonneg_left hYp hμ.le, mul_nonneg (sq_nonneg (1 - μ)) hXp]
  have key2 : 0 ≤ μ * (By - Bx) + (1 - μ) * a * ρ := by
    have h4 : 0 < 4 * a * ρ := by positivity
    exact (mul_nonneg_iff_of_pos_left h4).mp key
  have : By - Bx + (a / μ - a) * ρ = (μ * (By - Bx) + (1 - μ) * a * ρ) / μ := by
    field_simp
  rw [this]
  positivity

/-- Pure algebra: final numerical inequality. -/
lemma aux_final_ineq (a ρ s : ℝ) (ha : 0 < a) (ha4 : a ≤ 1 / 4) (hρ : 0 < ρ)
    (hρa : 3 * a ^ 2 ≤ (1 - a) ^ 3 * ρ) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hs_lo : (1 - a) ^ 2 * ρ ^ 2 ≤ s ^ 2) :
    a ^ 2 / (1 - a) * ρ < s ^ 2 - s ^ 3 + s ^ 4 / 3 := by
  have h1a : 0 < 1 - a := by linarith
  have hs_pos : 0 < s := by
    have : 0 < (1 - a) ^ 2 * ρ ^ 2 := by positivity
    rcases hs0.lt_or_eq with h | h
    · exact h
    · rw [← h] at hs_lo; linarith
  have hf1 : s ^ 2 / 3 < s ^ 2 - s ^ 3 + s ^ 4 / 3 := by
    have : 0 < s ^ 2 * (1 - s) * (2 - s) := by
      apply _root_.mul_pos (_root_.mul_pos (by positivity) (by linarith)) (by linarith)
    linarith
  have hf2 : a ^ 2 / (1 - a) * ρ ≤ (1 - a) ^ 2 * ρ ^ 2 / 3 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ h1a (by norm_num)]
    have := mul_le_mul_of_nonneg_right hρa hρ.le
    linarith
  linarith

lemma aux_rho_le (r : ℝ) (hr_pos : 0 < r) (hr : r ≤ 1 / 4) :
    3 * r ^ 2 / (1 - r) ^ 3 ≤ 4 / 9 := by
  have hr1 : 0 < 1 - r := by linarith
  rw [div_le_iff₀ (by positivity)]
  linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - 4 * r) (sq_nonneg (2 + r))]

/-- First-order estimate along the segment `[q, q + w]`. -/
lemma aux_e1 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hf_sc : IsSelfConcordantLocalNorm f Df)
    (hgrad : ∀ y ∈ Df, HasFDerivAt (fun z => gradient f z) (hessianOperator f y) y)
    (q w : E) (hq : q ∈ Df) (s : ℝ) (hs_def : localNorm f q w = s) (hs1 : s < 1) :
    s ^ 2 - s ^ 3 + s ^ 4 / 3 ≤ inner ℝ w (gradient f (q + w)) - inner ℝ w (gradient f q) := by
  have hs0 : 0 ≤ s := hs_def ▸ aux_localNorm_nonneg f q w
  have hs_sq : localInnerProd f q w w = s ^ 2 := by
    rw [← hs_def, aux_norm_sq f Df h_Df_pd q hq w]
  have hpt : ∀ t ∈ Set.Icc (0:ℝ) 1, localNorm f q ((q + t • w) - q) < 1 := by
    intro t ht
    rw [add_sub_cancel_left, aux_localNorm_smul, abs_of_nonneg ht.1, hs_def]
    have : t * s ≤ s := mul_le_of_le_one_left hs0 ht.2
    linarith
  have key := aux_mono01
    (gg := fun t => inner ℝ w (gradient f (q + t • w)) + s / 3 * (1 - t * s) ^ 3)
    (gd := fun t => localInnerProd f (q + t • w) w w - s ^ 2 * (1 - t * s) ^ 2) ?_ ?_
  · simp only [zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_pow, mul_one,
      one_mul] at key
    linarith
  · intro t ht
    have hD : q + t • w ∈ Df := (aux_SC_quad f Df h_Df_pd hf_sc q hq _ (hpt t ht)).1
    have h1 := aux_deriv_line f q w w t (hgrad _ hD)
    have h2 : HasDerivAt (fun t : ℝ => s / 3 * (1 - t * s) ^ 3) (-(s ^ 2 * (1 - t * s) ^ 2)) t := by
      have := ((((hasDerivAt_id t).mul_const s).const_sub 1).pow 3).const_mul (s / 3)
      convert this using 1
      simp; ring
    convert h1.add h2 using 1
  · intro t ht
    have h := ((aux_SC_quad f Df h_Df_pd hf_sc q hq _ (hpt t ht)).2 w).1
    rw [add_sub_cancel_left, aux_localNorm_smul, abs_of_nonneg ht.1, hs_def, hs_sq] at h
    show 0 ≤ localInnerProd f (q + t • w) w w - s ^ 2 * (1 - t * s) ^ 2
    linarith

/-- Estimate of the gradient increment along `[x, x + v]` against the Hessian at `x`. -/
lemma aux_e2 {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hf_sc : IsSelfConcordantLocalNorm f Df)
    (hgrad : ∀ y ∈ Df, HasFDerivAt (fun z => gradient f z) (hessianOperator f y) y)
    (hsymm : ∀ y ∈ Df, ∀ c d, localInnerProd f y c d = localInnerProd f y d c)
    (x v w : E) (hx : x ∈ Df) (a ρ : ℝ) (ha_def : localNorm f x v = a)
    (hw : localNorm f x w = ρ) (ha_pos : 0 < a) (ha1 : a < 1) (hρ_pos : 0 < ρ) :
    -(a ^ 2 / (1 - a)) * ρ ≤
      inner ℝ w (gradient f (x + v)) - inner ℝ w (gradient f x) - localInnerProd f x w v := by
  have hvQ : localInnerProd f x v v = a ^ 2 := by rw [← ha_def, aux_norm_sq f Df h_Df_pd x hx v]
  have hwQ : localInnerProd f x w w = ρ ^ 2 := by rw [← hw, aux_norm_sq f Df h_Df_pd x hx w]
  have hta : ∀ t ∈ Set.Icc (0:ℝ) 1, t * a < 1 := by
    intro t ht
    have : t * a ≤ a := mul_le_of_le_one_left ha_pos.le ht.2
    linarith
  have hxt : ∀ t ∈ Set.Icc (0:ℝ) 1, localNorm f x ((x + t • v) - x) < 1 := by
    intro t ht
    rw [add_sub_cancel_left, aux_localNorm_smul, abs_of_nonneg ht.1, ha_def]
    exact hta t ht
  have key := aux_mono01 (gg := fun t => inner ℝ w (gradient f (x + t • v))
      - t * localInnerProd f x w v + ((1 - t * a)⁻¹ - t * a) * ρ)
    (gd := fun t => localInnerProd f (x + t • v) w v - localInnerProd f x w v
      + (a / (1 - t * a) ^ 2 - a) * ρ) ?_ ?_
  · simp only [zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul, inv_one] at key
    have h1a : (1 - a)⁻¹ = 1 + a + a ^ 2 / (1 - a) := by
      have : (1 - a) ≠ 0 := by linarith
      field_simp; ring
    rw [h1a] at key
    linarith
  · intro t ht
    have hD : x + t • v ∈ Df := (aux_SC_quad f Df h_Df_pd hf_sc x hx _ (hxt t ht)).1
    have h1 := aux_deriv_line f x v w t (hgrad _ hD)
    have h2 : HasDerivAt (fun t : ℝ => t * localInnerProd f x w v) (localInnerProd f x w v) t := by
      simpa using (hasDerivAt_id t).mul_const (localInnerProd f x w v)
    have h3 : HasDerivAt (fun t : ℝ => ((1 - t * a)⁻¹ - t * a) * ρ)
        ((a / (1 - t * a) ^ 2 - a) * ρ) t := by
      have hne : (1 - t * a) ≠ 0 := by linarith [hta t ht]
      have := (((((hasDerivAt_id t).mul_const a).const_sub 1).inv (by simpa using hne)).sub
        ((hasDerivAt_id t).mul_const a)).mul_const ρ
      convert this using 1
      simp only [id]
      field_simp
    exact (h1.sub h2).add h3
  · intro t ht
    obtain ⟨hD, hq⟩ := aux_SC_quad f Df h_Df_pd hf_sc x hx _ (hxt t ht)
    rw [add_sub_cancel_left, aux_localNorm_smul, abs_of_nonneg ht.1, ha_def] at hq
    have hμ : 0 < (1 - t * a) ^ 2 := by
      have : 0 < 1 - t * a := by linarith [hta t ht]
      positivity
    have hYp := (hq (a • w + ρ • v)).1
    have hYm := (hq (a • w + (-ρ) • v)).2
    have hXp := aux_Q_nonneg f Df h_Df_pd x hx (a • w + ρ • v)
    simp only [aux_localInnerProd_expand] at hYp hYm hXp
    rw [hsymm _ hD v w] at hYp hYm
    rw [hsymm x hx v w, hwQ, hvQ] at hYp hYm hXp
    show 0 ≤ localInnerProd f (x + t • v) w v - localInnerProd f x w v
      + (a / (1 - t * a) ^ 2 - a) * ρ
    exact aux_bilin_alg a ρ _ _ _ _ _ ha_pos hρ_pos hμ hYp hYm hXp

/-- Boundary estimate: on the sphere `‖w‖_x = ρ` the directional derivative points outward. -/
lemma aux_bdry {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (f : E → ℝ) (Df : Set E)
    (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hf_sc : IsSelfConcordantLocalNorm f Df)
    (hgrad : ∀ y ∈ Df, HasFDerivAt (fun z => gradient f z) (hessianOperator f y) y)
    (hsymm : ∀ y ∈ Df, ∀ c d, localInnerProd f y c d = localInnerProd f y d c)
    (x v w : E) (hx : x ∈ Df) (a ρ : ℝ) (ha_def : localNorm f x v = a)
    (hw : localNorm f x w = ρ) (ha_pos : 0 < a) (ha4 : a ≤ 1 / 4) (hρ_pos : 0 < ρ)
    (hρ_le : ρ ≤ 4 / 9) (hρa : 3 * a ^ 2 ≤ (1 - a) ^ 3 * ρ) :
    0 < inner ℝ w (gradient f (x + v + w)) - inner ℝ w (gradient f x)
      - localInnerProd f x w v := by
  have hpx : localNorm f x ((x + v) - x) = a := by rw [add_sub_cancel_left, ha_def]
  obtain ⟨hp, hxp⟩ := aux_SC_quad f Df h_Df_pd hf_sc x hx (x + v) (by rw [hpx]; linarith)
  rw [hpx] at hxp
  have hwQ : localInnerProd f x w w = ρ ^ 2 := by rw [← hw, aux_norm_sq f Df h_Df_pd x hx w]
  obtain ⟨s, hs_def⟩ : ∃ s, localNorm f (x + v) w = s := ⟨_, rfl⟩
  have hs0 : 0 ≤ s := hs_def ▸ aux_localNorm_nonneg f (x + v) w
  have hs_sq : localInnerProd f (x + v) w w = s ^ 2 := by
    rw [← hs_def, aux_norm_sq f Df h_Df_pd (x + v) hp w]
  have hs_lo : (1 - a) ^ 2 * ρ ^ 2 ≤ s ^ 2 := by rw [← hs_sq, ← hwQ]; exact (hxp w).1
  have hs_hi : (1 - a) ^ 2 * s ^ 2 ≤ ρ ^ 2 := by rw [← hs_sq, ← hwQ]; exact (hxp w).2
  have hs1 : s < 1 := by
    by_contra hcon
    push_neg at hcon
    have h4 : 1 ≤ s ^ 2 := one_le_pow₀ hcon
    have h5 : (3 / 4 : ℝ) ^ 2 ≤ (1 - a) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have h6 : ρ ^ 2 ≤ (4 / 9 : ℝ) ^ 2 := pow_le_pow_left₀ hρ_pos.le hρ_le 2
    have h7 : (3 / 4 : ℝ) ^ 2 * 1 ≤ (1 - a) ^ 2 * s ^ 2 :=
      mul_le_mul h5 h4 (by norm_num) (by positivity)
    linarith
  have he1 := aux_e1 f Df h_Df_pd hf_sc hgrad (x + v) w hp s hs_def hs1
  have he2 := aux_e2 f Df h_Df_pd hf_sc hgrad hsymm x v w hx a ρ ha_def hw ha_pos
    (by linarith) hρ_pos
  have hfin := aux_final_ineq a ρ s ha_pos ha4 hρ_pos hρa hs0 hs1 hs_lo
  have : -(a ^ 2 / (1 - a)) * ρ = -(a ^ 2 / (1 - a) * ρ) := by ring
  linarith

/-- Closed local balls are compact (finite dimension, positive definite Hessian). -/
lemma aux_compact {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [Nontrivial E] (f : E → ℝ) (x : E)
    (hpd : ∀ c ≠ 0, 0 < localInnerProd f x c c) (v : E) (ρ : ℝ) :
    IsCompact (closedLocalBall f x v ρ) := by
  have hcQ : Continuous (fun c => localInnerProd f x c c) := by
    unfold localInnerProd
    exact continuous_id.inner (hessianOperator f x).continuous
  have hcontK : Continuous (fun u => localNorm f x (u - v)) := by
    unfold localNorm
    exact Real.continuous_sqrt.comp (hcQ.comp (continuous_id.sub continuous_const))
  have hK_closed : IsClosed (closedLocalBall f x v ρ) := isClosed_le hcontK continuous_const
  obtain ⟨m, hm_pos, hm⟩ : ∃ m > 0, ∀ c, m * ‖c‖ ^ 2 ≤ localInnerProd f x c c := by
    have hsph : IsCompact (Metric.sphere (0:E) 1) := isCompact_sphere 0 1
    have hne : (Metric.sphere (0:E) 1).Nonempty := NormedSpace.sphere_nonempty.mpr zero_le_one
    obtain ⟨c0, hc0, hmin⟩ := hsph.exists_isMinOn hne hcQ.continuousOn
    have hc0' : c0 ≠ 0 := by
      intro h; rw [h] at hc0; simp at hc0
    refine ⟨localInnerProd f x c0 c0, hpd c0 hc0', fun c => ?_⟩
    by_cases hc : c = 0
    · simp [hc, localInnerProd]
    · have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
      have hmem : ‖c‖⁻¹ • c ∈ Metric.sphere (0:E) 1 := by
        simp [norm_smul, hcn.ne']
      have h1 := isMinOn_iff.mp hmin _ hmem
      simp only at h1
      rw [aux_localInnerProd_smul] at h1
      have h2 : ‖c‖ ^ 2 * (‖c‖⁻¹ ^ 2 * localInnerProd f x c c) = localInnerProd f x c c := by
        field_simp
      calc localInnerProd f x c0 c0 * ‖c‖ ^ 2
          ≤ (‖c‖⁻¹ ^ 2 * localInnerProd f x c c) * ‖c‖ ^ 2 := by gcongr
        _ = localInnerProd f x c c := by rw [mul_comm]; exact h2
  have hK_bdd : Bornology.IsBounded (closedLocalBall f x v ρ) := by
    rw [Metric.isBounded_iff_subset_closedBall v]
    refine ⟨Real.sqrt (ρ ^ 2 / m), fun u hu => ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have h1 : localNorm f x (u - v) ≤ ρ := hu
    have h2 := hm (u - v)
    have hQ : 0 ≤ localInnerProd f x (u - v) (u - v) := by
      by_cases hc : u - v = 0
      · simp [hc, localInnerProd]
      · exact (hpd _ hc).le
    have h3 : localNorm f x (u - v) ^ 2 = localInnerProd f x (u - v) (u - v) := Real.sq_sqrt hQ
    have h4 : localNorm f x (u - v) ^ 2 ≤ ρ ^ 2 :=
      pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
    have h5 : ‖u - v‖ ^ 2 ≤ ρ ^ 2 / m := by
      rw [le_div_iff₀ hm_pos]; linarith
    exact le_trans (le_abs_self _) (Real.abs_le_sqrt h5)
  exact Metric.isCompact_of_isClosed_isBounded hK_closed hK_bdd

set_option linter.unusedVariables false in
theorem Renegar_chap_2_2_2_10 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x v : E)
  (r : ℝ)
  (hf_sc : IsSelfConcordantLocalNorm f Df)
  (hx : x ∈ Df)
  (hr : r ≤ 1 / 4) :
  localNorm (f := f) x v ≤ r →
    ∃ u ∈ closedLocalBall (f := f) x v ((3 * r ^ 2) / ((1 - r) ^ 3)),
      localGradient f Df h_Df_pd x (x + u) hx =
      (localGradient f Df h_Df_pd x x hx) + v := by
  intro hvr
  have hC2 : ∀ y ∈ Df, ContDiffAt ℝ 2 f y :=
    fun y hy => hf_C2.contDiffAt (h_Df_open.mem_nhds hy)
  have hsymm : ∀ y ∈ Df, ∀ c d, localInnerProd f y c d = localInnerProd f y d c :=
    fun y hy c d => aux_hessian_symm f y (hC2 y hy) c d
  have hgrad : ∀ y ∈ Df, HasFDerivAt (fun z => gradient f z) (hessianOperator f y) y :=
    fun y hy => aux_hasFDerivAt_gradient f y (hC2 y hy)
  obtain ⟨a, ha_def⟩ : ∃ a, localNorm f x v = a := ⟨_, rfl⟩
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ, 3 * r ^ 2 / (1 - r) ^ 3 = ρ := ⟨_, rfl⟩
  rw [ha_def] at hvr
  rw [hρ_def]
  have ha0 : 0 ≤ a := ha_def ▸ aux_localNorm_nonneg f x v
  have hr1 : 0 < 1 - r := by linarith
  have hρ0 : 0 ≤ ρ := by rw [← hρ_def]; positivity
  by_cases hv0 : v = 0
  · refine ⟨0, ?_, ?_⟩
    · show localNorm f x (0 - v) ≤ ρ
      rw [hv0, sub_zero]
      simp only [localNorm, localInnerProd, map_zero, inner_zero_left, Real.sqrt_zero]
      exact hρ0
    · simp [hv0]
  have ha_pos : 0 < a := by rw [← ha_def]; exact Real.sqrt_pos.mpr (h_Df_pd x hx v hv0)
  have hr_pos : 0 < r := lt_of_lt_of_le ha_pos hvr
  have hρ_pos : 0 < ρ := by rw [← hρ_def]; positivity
  have hρ_le : ρ ≤ 4 / 9 := hρ_def ▸ aux_rho_le r hr_pos hr
  have hρa : 3 * a ^ 2 ≤ (1 - a) ^ 3 * ρ := by
    have h1 : (1 - r) ^ 3 * ρ = 3 * r ^ 2 := by
      rw [← hρ_def]; field_simp
    have h2 : (1 - r) ^ 3 ≤ (1 - a) ^ 3 := pow_le_pow_left₀ hr1.le (by linarith) 3
    have h3 : (1 - r) ^ 3 * ρ ≤ (1 - a) ^ 3 * ρ := mul_le_mul_of_nonneg_right h2 hρ_pos.le
    have h4 : a ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ ha0 hvr 2
    linarith
  -- the point `x + v` lies in `Df`, and the closed local ball around `v` is mapped into `Df`
  have hpx : localNorm f x ((x + v) - x) = a := by rw [add_sub_cancel_left, ha_def]
  obtain ⟨hp, hxp⟩ := aux_SC_quad f Df h_Df_pd hf_sc x hx (x + v) (by rw [hpx]; linarith)
  rw [hpx] at hxp
  have hKD : ∀ u ∈ closedLocalBall f x v ρ, x + u ∈ Df := by
    intro u hu
    have h1 : localNorm f x (u - v) ≤ ρ := hu
    have h2 : localInnerProd f x (u - v) (u - v) ≤ ρ ^ 2 := by
      rw [← aux_norm_sq f Df h_Df_pd x hx]
      exact pow_le_pow_left₀ (aux_localNorm_nonneg _ _ _) h1 2
    have h3 := (hxp (u - v)).2
    have h4 : localNorm f (x + v) ((x + u) - (x + v)) < 1 := by
      rw [add_sub_add_left_eq_sub]
      have hn := aux_norm_sq f Df h_Df_pd (x + v) hp (u - v)
      by_contra hcon
      push_neg at hcon
      have h5 : 1 ≤ localNorm f (x + v) (u - v) ^ 2 := one_le_pow₀ hcon
      have h6 : (3 / 4 : ℝ) ^ 2 ≤ (1 - a) ^ 2 := pow_le_pow_left₀ (by norm_num) (by linarith) 2
      have h7 : ρ ^ 2 ≤ (4 / 9 : ℝ) ^ 2 := pow_le_pow_left₀ hρ_pos.le hρ_le 2
      have h8 : (3 / 4 : ℝ) ^ 2 * 1 ≤ (1 - a) ^ 2 * localNorm f (x + v) (u - v) ^ 2 :=
        mul_le_mul h6 h5 (by norm_num) (by positivity)
      rw [hn] at h8
      linarith
    exact (aux_SC_quad f Df h_Df_pd hf_sc (x + v) hp _ h4).1
  -- the function to minimize
  obtain ⟨cc, hcc_def⟩ : ∃ cc, gradient f x + hessianOperator f x v = cc := ⟨_, rfl⟩
  have hFderiv : ∀ u, x + u ∈ Df →
      HasFDerivAt (fun u => f (x + u) - inner ℝ cc u) (fderiv ℝ f (x + u) - innerSL ℝ cc) u := by
    intro u hu
    have hfd : HasFDerivAt f (fderiv ℝ f (x + u)) (x + u) :=
      ((hC2 _ hu).differentiableAt (by norm_num)).hasFDerivAt
    have h1 : HasFDerivAt (fun u => f (x + u)) (fderiv ℝ f (x + u)) u := by
      have := hfd.comp u ((hasFDerivAt_id u).const_add x)
      simpa using this
    exact h1.sub (innerSL ℝ cc).hasFDerivAt
  have hFcont : ContinuousOn (fun u => f (x + u) - inner ℝ cc u) (closedLocalBall f x v ρ) := by
    have h1 : ContinuousOn (fun u => f (x + u)) (closedLocalBall f x v ρ) :=
      (hf_C2.continuousOn).comp (continuous_const.add continuous_id).continuousOn
        (fun u hu => hKD u hu)
    exact h1.sub (continuous_const.inner continuous_id).continuousOn
  have hvK : v ∈ closedLocalBall f x v ρ := by
    show localNorm f x (v - v) ≤ ρ
    rw [sub_self]
    simp only [localNorm, localInnerProd, map_zero, inner_zero_left, Real.sqrt_zero]
    exact hρ0
  have hK_compact : IsCompact (closedLocalBall f x v ρ) :=
    aux_compact f x (fun c hc => h_Df_pd x hx c hc) v ρ
  obtain ⟨u0, hu0K, hu0min⟩ := hK_compact.exists_isMinOn ⟨v, hvK⟩ hFcont
  have hu0D : x + u0 ∈ Df := hKD u0 hu0K
  have hcontK : Continuous (fun u => localNorm f x (u - v)) := by
    unfold localNorm localInnerProd
    exact Real.continuous_sqrt.comp ((continuous_id.sub continuous_const).inner
      ((hessianOperator f x).continuous.comp (continuous_id.sub continuous_const)))
  -- the minimizer is an interior point
  have hint : localNorm f x (u0 - v) < ρ := by
    by_contra hcon
    have heq : localNorm f x (u0 - v) = ρ := le_antisymm hu0K (not_lt.mp hcon)
    have hb := aux_bdry f Df h_Df_pd hf_sc hgrad hsymm x v (u0 - v) hx a ρ ha_def heq ha_pos
      (by linarith) hρ_pos hρ_le hρa
    rw [show x + v + (u0 - v) = x + u0 by abel] at hb
    have hseg : segment ℝ u0 (u0 + -(u0 - v)) ⊆ closedLocalBall f x v ρ := by
      intro z hz
      rw [segment_eq_image'] at hz
      obtain ⟨θ, hθ, rfl⟩ := hz
      show localNorm f x (u0 + θ • (u0 + -(u0 - v) - u0) - v) ≤ ρ
      have : u0 + θ • (u0 + -(u0 - v) - u0) - v = (1 - θ) • (u0 - v) := by
        module
      rw [this, aux_localNorm_smul, heq, abs_of_nonneg (by linarith [hθ.2])]
      nlinarith [hθ.1]
    have htc := mem_posTangentConeAt_of_segment_subset hseg
    have h0 := hu0min.localize.hasFDerivWithinAt_nonneg (hFderiv u0 hu0D).hasFDerivWithinAt htc
    simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply, map_neg] at h0
    rw [← aux_inner_gradient, ← hcc_def, inner_add_left] at h0
    simp only [localInnerProd] at hb
    rw [real_inner_comm (u0 - v) (gradient f (x + u0)), real_inner_comm (u0 - v) (gradient f x),
      real_inner_comm (u0 - v) (hessianOperator f x v)] at h0
    linarith
  have hKnhds : closedLocalBall f x v ρ ∈ 𝓝 u0 := by
    have hopen : IsOpen {u | localNorm f x (u - v) < ρ} := isOpen_lt hcontK continuous_const
    exact Filter.mem_of_superset (hopen.mem_nhds hint)
      (fun u hu => show localNorm f x (u - v) ≤ ρ from le_of_lt hu)
  have hzero := (hu0min.isLocalMin hKnhds).hasFDerivAt_eq_zero (hFderiv u0 hu0D)
  have hgradeq : gradient f (x + u0) = cc := by
    apply ext_inner_right ℝ
    intro h
    have := congrArg (fun L => L h) hzero
    simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply,
      ContinuousLinearMap.zero_apply] at this
    rw [aux_inner_gradient]; linarith
  refine ⟨u0, hu0K, ?_⟩
  unfold localGradient
  rw [hgradeq, ← hcc_def, map_add]
  congr 1
  have : hessianOperator f x v = hessianLinearEquiv f Df x hx h_Df_pd v := rfl
  rw [this, ContinuousLinearEquiv.symm_apply_apply]

end Renegar_chap_2_2_2_10
