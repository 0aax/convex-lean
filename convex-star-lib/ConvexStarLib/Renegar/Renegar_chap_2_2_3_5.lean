import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_5`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_5`, so the main result is `Renegar_chap_2_2_3_5.Renegar_chap_2_2_3_5`.
-/

namespace Renegar_chap_2_2_3_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section RenegarAux

omit [FiniteDimensional ℝ E] in
lemma renegarAux_hasFDerivAt_fderiv {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x : E} (hx : x ∈ Df) :
    HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) x) x := by
  have h1 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hopen.mem_nhds hx)
  have h2 : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (h1.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact h2.hasFDerivAt

lemma renegarAux_hasFDerivAt_gradient' {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x : E} (hx : x ∈ Df) :
    HasFDerivAt (fun y => gradient f y)
      (((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap :
        StrongDual ℝ E →L[ℝ] E).comp (fderiv ℝ (fderiv ℝ f) x)) x :=
  ((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap :
      StrongDual ℝ E →L[ℝ] E).hasFDerivAt.comp x (renegarAux_hasFDerivAt_fderiv hf hopen hx)

lemma renegarAux_hessian_eq {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x : E} (hx : x ∈ Df) :
    hessianOperator f x = ((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap :
        StrongDual ℝ E →L[ℝ] E).comp (fderiv ℝ (fderiv ℝ f) x) :=
  (renegarAux_hasFDerivAt_gradient' hf hopen hx).fderiv

lemma renegarAux_hasFDerivAt_gradient {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x : E} (hx : x ∈ Df) :
    HasFDerivAt (fun y => gradient f y) (hessianOperator f x) x := by
  rw [renegarAux_hessian_eq hf hopen hx]
  exact renegarAux_hasFDerivAt_gradient' hf hopen hx

lemma renegarAux_hessian_symm {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x : E} (hx : x ∈ Df) (u v : E) :
    inner ℝ u (hessianOperator f x v) = inner ℝ v (hessianOperator f x u) := by
  have h1 : ContDiffAt ℝ 2 f x := hf.contDiffAt (hopen.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ f x := h1.isSymmSndFDerivAt (by simp)
  rw [renegarAux_hessian_eq hf hopen hx]
  have key : ∀ a b : E, inner ℝ a (((InnerProductSpace.toDual ℝ E).symm.toLinearIsometry.toContinuousLinearMap :
        StrongDual ℝ E →L[ℝ] E).comp (fderiv ℝ (fderiv ℝ f) x) b) = fderiv ℝ (fderiv ℝ f) x b a := by
    intro a b
    rw [real_inner_comm]
    exact InnerProductSpace.toDual_symm_apply
  rw [key, key]
  exact hsymm v u

end RenegarAux

section RenegarAux2

lemma renegarAux_localInnerProd_nonneg {f : E → ℝ} {Df : Set E}
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) {x : E} (hx : x ∈ Df) (v : E) :
    0 ≤ localInnerProd f x v v := by
  by_cases hv : v = 0
  · subst hv; simp [localInnerProd]
  · exact (h_pd x hx v hv).le

lemma renegarAux_cs {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    {x : E} (hx : x ∈ Df) (u w : E) :
    (localInnerProd f x u w) ^ 2 ≤ localInnerProd f x u u * localInnerProd f x w w := by
  have hsym := renegarAux_hessian_symm hf hopen hx w u
  have hq : ∀ t : ℝ, 0 ≤ localInnerProd f x w w * (t * t) + 2 * localInnerProd f x u w * t
      + localInnerProd f x u u := by
    intro t
    have h0 := renegarAux_localInnerProd_nonneg h_pd hx (u + t • w)
    have expand : localInnerProd f x (u + t • w) (u + t • w) = localInnerProd f x w w * (t * t)
        + 2 * localInnerProd f x u w * t + localInnerProd f x u u := by
      simp only [localInnerProd, map_add, map_smul, inner_add_left, inner_add_right,
        inner_smul_left, inner_smul_right, RCLike.conj_to_real]
      rw [hsym]
      ring
    linarith [expand]
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith [hd]

lemma renegarAux_hessian_localGradient {f : E → ℝ} {Df : Set E}
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) {x : E} (hx : x ∈ Df) :
    hessianOperator f x (localGradient f Df h_pd x x hx) = gradient f x := by
  show hessianOperator f x ((hessianLinearEquiv f Df x hx h_pd).symm (gradient f x)) = gradient f x
  rw [← (show ∀ v, hessianLinearEquiv f Df x hx h_pd v = hessianOperator f x v from fun v => rfl)]
  exact ContinuousLinearEquiv.apply_symm_apply _ _

lemma renegarAux_barrierIntegrand_eq {f : E → ℝ} {Df : Set E}
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v) {x : E} (hx : x ∈ Df) :
    barrierIntegrand f Df h_pd ⟨x, hx⟩ = localInnerProd f x (localGradient f Df h_pd x x hx)
      (localGradient f Df h_pd x x hx) := by
  unfold barrierIntegrand localNorm
  exact Real.sq_sqrt (renegarAux_localInnerProd_nonneg h_pd hx _)

lemma renegarAux_barrierIntegrand_le {f : E → ℝ} {Df : Set E}
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hbdd : BddAbove (Set.range fun x : Df => barrierIntegrand f Df h_pd x))
    {x : E} (hx : x ∈ Df) :
    barrierIntegrand f Df h_pd ⟨x, hx⟩ ≤ barrierParameter f Df h_pd :=
  le_csSup hbdd ⟨⟨x, hx⟩, rfl⟩

lemma renegarAux_barrierParameter_nonneg {f : E → ℝ} {Df : Set E}
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hbdd : BddAbove (Set.range fun x : Df => barrierIntegrand f Df h_pd x))
    {x : E} (hx : x ∈ Df) :
    0 ≤ barrierParameter f Df h_pd :=
  le_trans (by unfold barrierIntegrand; positivity) (renegarAux_barrierIntegrand_le h_pd hbdd hx)

lemma renegarAux_grad_bound {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hbdd : BddAbove (Set.range fun x : Df => barrierIntegrand f Df h_pd x))
    {x : E} (hx : x ∈ Df) (d : E) :
    (inner ℝ (gradient f x) d) ^ 2 ≤ barrierParameter f Df h_pd * localInnerProd f x d d := by
  have h1 : inner ℝ (gradient f x) d = localInnerProd f x d (localGradient f Df h_pd x x hx) := by
    rw [← renegarAux_hessian_localGradient h_pd hx, real_inner_comm]
    rfl
  have h2 := renegarAux_cs hf hopen h_pd hx d (localGradient f Df h_pd x x hx)
  have h3 : localInnerProd f x (localGradient f Df h_pd x x hx) (localGradient f Df h_pd x x hx)
      ≤ barrierParameter f Df h_pd := by
    rw [← renegarAux_barrierIntegrand_eq h_pd hx]
    exact renegarAux_barrierIntegrand_le h_pd hbdd hx
  have h4 := renegarAux_localInnerProd_nonneg h_pd hx d
  rw [h1]
  calc _ ≤ localInnerProd f x d d * localInnerProd f x (localGradient f Df h_pd x x hx)
          (localGradient f Df h_pd x x hx) := h2
    _ ≤ localInnerProd f x d d * barrierParameter f Df h_pd := mul_le_mul_of_nonneg_left h3 h4
    _ = _ := mul_comm _ _

end RenegarAux2

section RenegarAux3

lemma renegarAux_hasDerivAt_line {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) {x d : E} {t : ℝ} (ht : x + t • d ∈ Df) :
    HasDerivAt (fun s : ℝ => inner ℝ (gradient f (x + s • d)) d)
      (localInnerProd f (x + t • d) d d) t := by
  have hG := renegarAux_hasFDerivAt_gradient hf hopen ht
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d t := by
    simpa using ((hasDerivAt_id t).smul_const d).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => gradient f (x + s • d))
      (hessianOperator f (x + t • d) d) t :=
    HasFDerivAt.comp_hasDerivAt (l := fun y => gradient f y) t hG hline
  have hinner := hcomp.inner ℝ (hasDerivAt_const t d)
  convert hinner using 1
  simp [localInnerProd, real_inner_comm]

lemma renegarAux_main_ineq {f : E → ℝ} {Df : Set E} (hf : ContDiffOn ℝ 2 f Df)
    (hopen : IsOpen Df) (hconv : Convex ℝ Df)
    (h_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
    (hbdd : BddAbove (Set.range fun x : Df => barrierIntegrand f Df h_pd x))
    {x y : E} (hx : x ∈ Df) (hy : y ∈ Df) :
    inner ℝ (gradient f x) (y - x) ≤ barrierParameter f Df h_pd := by
  have hϑ0 : 0 ≤ barrierParameter f Df h_pd := renegarAux_barrierParameter_nonneg h_pd hbdd hx
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • (y - x) ∈ Df :=
    fun t ht => hconv.add_smul_sub_mem hx hy ht
  have hderiv : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun s : ℝ => inner ℝ (gradient f (x + s • (y - x))) (y - x))
        (localInnerProd f (x + t • (y - x)) (y - x) (y - x)) t :=
    fun t ht => renegarAux_hasDerivAt_line hf hopen (hseg t ht)
  set ϑ := barrierParameter f Df h_pd with hϑ
  set d := y - x with hd
  set gφ : ℝ → ℝ := fun s => inner ℝ (gradient f (x + s • d)) d with hgφ
  have hgφ0 : gφ 0 = inner ℝ (gradient f x) d := by simp [hgφ]
  rw [← hgφ0]
  by_contra hcon
  push_neg at hcon
  have hmono : MonotoneOn gφ (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    exact renegarAux_localInnerProd_nonneg h_pd (hseg t (interior_subset ht)) d
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < gφ t := by
    intro t ht
    have := hmono ⟨le_refl 0, zero_le_one⟩ ht ht.1
    linarith
  have hd2 : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt (fun t => ϑ / gφ t + t)
      (ϑ * (-(localInnerProd f (x + t • d) d d) / (gφ t) ^ 2) + 1) t := by
    intro t ht
    have h1 := ((hderiv t ht).inv (hpos t ht).ne').const_mul ϑ
    have h2 := h1.add (hasDerivAt_id t)
    convert h2 using 1
  have hanti : AntitoneOn (fun t => ϑ / gφ t + t) (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (fun t ht => (hd2 t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hd2 t (interior_subset ht)).hasDerivWithinAt)
    intro t ht
    have ht' := interior_subset ht
    have hb := renegarAux_grad_bound hf hopen h_pd hbdd (hseg t ht') d
    have hpt := hpos t ht'
    have hsq : 0 < (gφ t) ^ 2 := by positivity
    have h1 : 1 ≤ ϑ * localInnerProd f (x + t • d) d d / (gφ t) ^ 2 := by
      rw [le_div_iff₀ hsq]
      simpa [hgφ] using hb
    have h2 : ϑ * (-(localInnerProd f (x + t • d) d d) / (gφ t) ^ 2)
        = -(ϑ * localInnerProd f (x + t • d) d d / (gφ t) ^ 2) := by ring
    rw [h2]
    linarith
  have hfin := hanti ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only at hfin
  have h1pos := hpos 1 ⟨zero_le_one, le_refl 1⟩
  have h0pos := hpos 0 ⟨le_refl 0, zero_le_one⟩
  have h3 : 0 ≤ ϑ / gφ 1 := div_nonneg hϑ0 h1pos.le
  have h4 : 1 ≤ ϑ / gφ 0 := by linarith
  rw [le_div_iff₀ h0pos] at h4
  linarith

end RenegarAux3
theorem Renegar_chap_2_2_3_5 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (z : E)
  (hf_sc : IsSCBarrier f Df h_Df_pd)
  (hz : IsAnalyticCenter f Df z) :
  localBall f z z 1 ⊆ Df ∧
  Df ⊆ localBall f z z (4 * (barrierParameter f Df h_Df_pd) + 1) := by
  obtain ⟨hz_mem, hz_grad⟩ := hz
  obtain ⟨hsc, hbdd⟩ := hf_sc
  refine ⟨(hsc z hz_mem).1, ?_⟩
  intro y hy
  have hϑ0 : 0 ≤ barrierParameter f Df h_Df_pd :=
    renegarAux_barrierParameter_nonneg h_Df_pd hbdd hz_mem
  show localNorm f z (y - z) < 4 * barrierParameter f Df h_Df_pd + 1
  set ϑ := barrierParameter f Df h_Df_pd with hϑ
  set d := y - z with hd
  set T := localNorm f z d with hT
  have hT0 : 0 ≤ T := Real.sqrt_nonneg _
  by_cases hT1 : T < 1
  · linarith
  push_neg at hT1
  have hTpos : 0 < T := by linarith
  have hd0 : d ≠ 0 := by
    intro h
    have : T = 0 := by
      rw [hT, h]
      simp [localNorm, localInnerProd]
    linarith
  have hnorm_smul : ∀ s : ℝ, 0 ≤ s → localNorm f z (s • d) = s * T := by
    intro s hs
    simp only [hT, localNorm, localInnerProd, map_smul, inner_smul_left, inner_smul_right,
      RCLike.conj_to_real]
    rw [← mul_assoc, Real.sqrt_mul (mul_self_nonneg s), Real.sqrt_mul_self hs]
  set s₀ : ℝ := 1 / (2 * T) with hs₀
  have hs₀pos : 0 < s₀ := by positivity
  have hs₀T : s₀ * T = 1 / 2 := by
    rw [hs₀]
    field_simp
  have hs₀le : s₀ ≤ 1 / 2 := by nlinarith
  have hball : ∀ s ∈ Set.Icc (0:ℝ) s₀, z + s • d ∈ localBall f z z 1 := by
    intro s hs
    show localNorm f z (z + s • d - z) < 1
    rw [add_sub_cancel_left, hnorm_smul s hs.1]
    nlinarith [hs.2]
  have hmemDf : ∀ s ∈ Set.Icc (0:ℝ) s₀, z + s • d ∈ Df :=
    fun s hs => (hsc z hz_mem).1 (hball s hs)
  have hlow : ∀ s ∈ Set.Icc (0:ℝ) s₀,
      T ^ 2 * (1 - s * T) ^ 2 ≤ localInnerProd f (z + s • d) d d := by
    intro s hs
    have hsc' := ((hsc z hz_mem).2 (z + s • d) (hball s hs) d hd0).1
    rw [add_sub_cancel_left, hnorm_smul s hs.1] at hsc'
    have h1 : T * (1 - s * T) ≤ localNorm f (z + s • d) d := by
      have := mul_le_mul_of_nonneg_left hsc' hTpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hTpos.ne', one_mul] at this
    have h2 : 0 ≤ T * (1 - s * T) := by
      apply mul_nonneg hTpos.le
      nlinarith [hs.2]
    have h3 : (localNorm f (z + s • d) d) ^ 2 = localInnerProd f (z + s • d) d d :=
      Real.sq_sqrt (renegarAux_localInnerProd_nonneg h_Df_pd (hmemDf s hs) d)
    calc T ^ 2 * (1 - s * T) ^ 2 = (T * (1 - s * T)) ^ 2 := by ring
      _ ≤ (localNorm f (z + s • d) d) ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = _ := h3
  have hderiv : ∀ s ∈ Set.Icc (0:ℝ) s₀,
      HasDerivAt (fun s : ℝ => inner ℝ (gradient f (z + s • d)) d
          - T ^ 2 * (s - s ^ 2 * T + s ^ 3 * T ^ 2 / 3))
        (localInnerProd f (z + s • d) d d - T ^ 2 * (1 - 2 * s * T + s ^ 2 * T ^ 2)) s := by
    intro s hs
    have h1 := renegarAux_hasDerivAt_line hf_C2 h_Df_open (hmemDf s hs)
    have h2 : HasDerivAt (fun s : ℝ => T ^ 2 * (s - s ^ 2 * T + s ^ 3 * T ^ 2 / 3))
        (T ^ 2 * (1 - 2 * s * T + s ^ 2 * T ^ 2)) s := by
      have ha := hasDerivAt_id' s
      have hb := (hasDerivAt_pow 2 s).mul_const T
      have hc := ((hasDerivAt_pow 3 s).mul_const (T ^ 2)).div_const 3
      have := ((ha.sub hb).add hc).const_mul (T ^ 2)
      convert this using 1
      rw [show (2:ℕ) - 1 = 1 from rfl, show (3:ℕ) - 1 = 2 from rfl]
      push_cast
      ring
    exact h1.sub h2
  have hmono : MonotoneOn (fun s : ℝ => inner ℝ (gradient f (z + s • d)) d
          - T ^ 2 * (s - s ^ 2 * T + s ^ 3 * T ^ 2 / 3)) (Set.Icc 0 s₀) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 s₀)
      (fun t ht => (hderiv t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hderiv t (interior_subset ht)).hasDerivWithinAt)
    intro s hs
    have := hlow s (interior_subset hs)
    nlinarith
  have hval := hmono ⟨le_refl 0, hs₀pos.le⟩ ⟨hs₀pos.le, le_refl s₀⟩ hs₀pos.le
  simp only [zero_smul, add_zero, hz_grad, inner_zero_left] at hval
  have hmain := renegarAux_main_ineq hf_C2 h_Df_open h_Df_convex h_Df_pd hbdd
    (hmemDf s₀ ⟨hs₀pos.le, le_refl _⟩) hy
  have hyx : y - (z + s₀ • d) = (1 - s₀) • d := by
    rw [hd, sub_smul, one_smul]
    abel
  rw [hyx, inner_smul_right] at hmain
  have h7 : T ^ 2 * (s₀ - s₀ ^ 2 * T + s₀ ^ 3 * T ^ 2 / 3) = 7 * T / 24 := by
    have : T ^ 2 * (s₀ - s₀ ^ 2 * T + s₀ ^ 3 * T ^ 2 / 3)
        = T * ((s₀ * T) - (s₀ * T) ^ 2 + (s₀ * T) ^ 3 / 3) := by ring
    rw [this, hs₀T]
    ring
  rw [h7] at hval
  set P := inner ℝ (gradient f (z + s₀ • d)) d with hP
  have hP7 : 7 * T / 24 ≤ P := by linarith
  have h1s : 0 ≤ 1 - s₀ := by linarith
  have hprod : (1 - s₀) * (7 * T / 24) ≤ (1 - s₀) * P := mul_le_mul_of_nonneg_left hP7 h1s
  have hexp : (1 - s₀) * (7 * T / 24) = 7 * T / 24 - 7 / 48 := by
    have : (1 - s₀) * (7 * T / 24) = 7 * T / 24 - 7 * (s₀ * T) / 24 := by ring
    rw [this, hs₀T]
    ring
  linarith

end Renegar_chap_2_2_3_5
