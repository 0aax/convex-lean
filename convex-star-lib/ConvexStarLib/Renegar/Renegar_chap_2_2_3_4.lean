import ConvexStarLib.Defs

/-!
# `Renegar_chap_2_2_3_4`

Source: Renegar, A Mathematical View of Interior-Point Methods (chap. 2).

Statement from the `convex-eval-v28-2h/Renegar_chap_2_2_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Renegar_chap_2_2_3_4`, so the main result is `Renegar_chap_2_2_3_4.Renegar_chap_2_2_3_4`.
-/

namespace Renegar_chap_2_2_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Renegar_chap_2_2_3_4 [Nontrivial E]
  (f : E → ℝ)
  (Df : Set E)
  (hf_C2 : ContDiffOn ℝ 2 f Df)
  (h_Df_open : IsOpen Df) (h_Df_convex : Convex ℝ Df)
  (h_Df_pd : ∀ x ∈ Df, ∀ v ≠ 0, 0 < localInnerProd f x v v)
  (x y : E)
  (hf_sc : IsSCBarrier f Df h_Df_pd)
  (hx : x ∈ Df)
  (hy : y ∈ Df) :
  inner ℝ (gradient f x) (y - x) ≥ 0 →
    y ∈ localBall f x x (4 * (barrierParameter f Df h_Df_pd) + 1) := by
  intro hgrad
  obtain ⟨hsc, hbdd⟩ := hf_sc
  -- generic monotonicity lemma from MVT
  have mono : ∀ (F F' : ℝ → ℝ) (a b : ℝ), a ≤ b →
      (∀ t ∈ Set.Icc a b, HasDerivAt F (F' t) t) →
      (∀ t ∈ Set.Icc a b, 0 ≤ F' t) → F a ≤ F b := by
    intro F F' a b hab hF hF'
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · obtain ⟨c, hc, hc'⟩ := exists_hasDerivAt_eq_slope F F' h
        (fun t ht => (hF t ht).continuousAt.continuousWithinAt)
        (fun t ht => hF t (Set.Ioo_subset_Icc_self ht))
      have h1 := hF' c (Set.Ioo_subset_Icc_self hc)
      rw [hc', le_div_iff₀ (sub_pos.mpr h)] at h1
      linarith
  -- basic differentiability facts
  have hCD : ∀ z ∈ Df, ContDiffAt ℝ 2 f z := fun z hz =>
    hf_C2.contDiffAt (h_Df_open.mem_nhds hz)
  have hgrad_eq : gradient f = (InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ f := by
    funext w; rfl
  have hHasF : ∀ z ∈ Df, HasFDerivAt (gradient f) (hessianOperator f z) z := by
    intro z hz
    have h1 : DifferentiableAt ℝ (fderiv ℝ f) z :=
      ((hCD z hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
    have h2 : DifferentiableAt ℝ (gradient f) z := by
      rw [hgrad_eq]
      exact ((InnerProductSpace.toDual ℝ E).symm.toContinuousLinearEquiv.differentiableAt).comp z h1
    exact h2.hasFDerivAt
  have hH : ∀ z, ∀ u v, inner ℝ u (hessianOperator f z v) = fderiv ℝ (fderiv ℝ f) z v u := by
    intro z u v
    rw [hessianOperator, hgrad_eq, LinearIsometryEquiv.comp_fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      LinearIsometryEquiv.coe_toContinuousLinearEquiv]
    rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]
  have hsymm : ∀ z ∈ Df, ∀ u v, localInnerProd f z u v = localInnerProd f z v u := by
    intro z hz u v
    simp only [localInnerProd, hH]
    exact ((hCD z hz).isSymmSndFDerivAt (by simp)) v u
  have hpos : ∀ z ∈ Df, ∀ v, 0 ≤ localInnerProd f z v v := by
    intro z hz v
    by_cases hv : v = 0
    · simp [hv, localInnerProd]
    · exact (h_Df_pd z hz v hv).le
  -- the barrier parameter bound
  set θ := barrierParameter f Df h_Df_pd with hθ_def
  have hbi_le : ∀ z (hz : z ∈ Df), barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ ≤ θ := by
    intro z hz
    exact le_csSup hbdd (Set.mem_range_self (⟨z, hz⟩ : Df))
  have hθ0 : 0 ≤ θ := by
    refine le_trans ?_ (hbi_le x hx)
    unfold barrierIntegrand
    exact sq_nonneg _
  -- Cauchy-Schwarz
  have hCS : ∀ z ∈ Df, ∀ e, (inner ℝ (gradient f z) e) ^ 2 ≤ θ * localInnerProd f z e e := by
    intro z hz e
    set w := (hessianLinearEquiv f Df z hz h_Df_pd).symm (gradient f z) with hw_def
    have hw : hessianOperator f z w = gradient f z := by
      have := ContinuousLinearEquiv.apply_symm_apply (hessianLinearEquiv f Df z hz h_Df_pd) (gradient f z)
      exact this
    have hbi : barrierIntegrand f Df h_Df_pd ⟨z, hz⟩ = localInnerProd f z w w := by
      unfold barrierIntegrand localNorm localGradient
      exact Real.sq_sqrt (hpos z hz w)
    have hinner : inner ℝ (gradient f z) e = localInnerProd f z w e := by
      rw [← hw, real_inner_comm]
      rw [hsymm z hz]
      rfl
    have hquad : ∀ l : ℝ, 0 ≤ localInnerProd f z e e * (l * l) + (2 * localInnerProd f z w e) * l + localInnerProd f z w w := by
      intro l
      have h := hpos z hz (w + l • e)
      have hs := hsymm z hz e w
      simp only [localInnerProd, map_add, map_smul, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right] at h hs ⊢
      simp at h
      rw [hs] at h
      nlinarith [h]
    have hd := discrim_le_zero hquad
    unfold discrim at hd
    have h1 := hbi_le z hz
    rw [hbi] at h1
    have h2 := hpos z hz e
    rw [hinner]
    nlinarith [mul_le_mul_of_nonneg_right h1 h2]
  -- the line from x to y
  set d := y - x with hd_def
  have hzmem : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • d ∈ Df := fun t ht =>
    h_Df_convex.add_smul_sub_mem hx hy ht
  set ψ : ℝ → ℝ := fun t => inner ℝ (gradient f (x + t • d)) d with hψ_def
  set q : ℝ → ℝ := fun t => localInnerProd f (x + t • d) d d with hq_def
  have hψ' : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt ψ (q t) t := by
    intro t ht
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 : HasDerivAt (gradient f ∘ fun t : ℝ => x + t • d)
        (hessianOperator f (x + t • d) d) t :=
      (hHasF _ (hzmem t ht)).comp_hasDerivAt t h1
    have h3 := h2.inner ℝ (hasDerivAt_const t d)
    simp only [inner_zero_right, zero_add] at h3
    convert h3 using 1
    simp only [hq_def, localInnerProd]
    rw [real_inner_comm]
  have hq0 : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ q t := fun t ht => hpos _ (hzmem t ht) d
  have hψq : ∀ t ∈ Set.Icc (0:ℝ) 1, ψ t ^ 2 ≤ θ * q t := fun t ht => hCS _ (hzmem t ht) d
  have hψ0 : 0 ≤ ψ 0 := by simpa [hψ_def] using hgrad
  -- ψ is monotone
  have hψmono : ∀ a b, 0 ≤ a → a ≤ b → b ≤ 1 → ψ a ≤ ψ b := by
    intro a b ha hab hb
    exact mono ψ q a b hab (fun t ht => hψ' t ⟨ha.trans ht.1, ht.2.trans hb⟩)
      (fun t ht => hq0 t ⟨ha.trans ht.1, ht.2.trans hb⟩)
  -- the local norm
  set s := localNorm f x d with hs_def
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  show s < 4 * θ + 1
  rcases lt_or_ge s 1 with hs1 | hs1
  · linarith
  -- now s ≥ 1
  have hd0 : d ≠ 0 := by
    intro h
    have : s = 0 := by simp [hs_def, h, localNorm, localInnerProd]
    linarith
  have hnorm_smul : ∀ t : ℝ, 0 ≤ t → localNorm f x (t • d) = t * s := by
    intro t ht
    have : localInnerProd f x (t • d) (t • d) = t ^ 2 * localInnerProd f x d d := by
      simp only [localInnerProd, map_smul, inner_smul_left, inner_smul_right]
      simp; ring
    rw [localNorm, this, Real.sqrt_mul (sq_nonneg t), Real.sqrt_sq ht]
    rfl
  set t1 := 1 / (2 * s) with ht1_def
  have hs_pos : 0 < s := by linarith
  have ht1_pos : 0 < t1 := by positivity
  have ht1s : t1 * s = 1 / 2 := by rw [ht1_def]; field_simp
  have ht1_le : t1 ≤ 1 / 2 := by nlinarith
  -- lower bound on q from self-concordance
  have hq_lower : ∀ t ∈ Set.Icc 0 t1, s ^ 2 * (1 - t * s) ^ 2 ≤ q t := by
    intro t ht
    have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
    have hts : t * s ≤ 1 / 2 := by nlinarith [ht.2]
    have hmem : x + t • d ∈ localBall f x x 1 := by
      show localNorm f x (x + t • d - x) < 1
      rw [add_sub_cancel_left, hnorm_smul t ht.1]
      linarith
    have hsc' := ((hsc x hx).2 (x + t • d) hmem d hd0).1
    rw [add_sub_cancel_left, hnorm_smul t ht.1] at hsc'
    have h1 : s * (1 - t * s) ≤ localNorm f (x + t • d) d := by
      have := mul_le_mul_of_nonneg_left hsc' hs0
      rwa [← mul_assoc, mul_inv_cancel₀ hs_pos.ne', one_mul] at this
    have h2 : 0 ≤ s * (1 - t * s) := by nlinarith
    have h3 : (localNorm f (x + t • d) d) ^ 2 = q t := Real.sq_sqrt (hq0 t htI)
    calc s ^ 2 * (1 - t * s) ^ 2 = (s * (1 - t * s)) ^ 2 := by ring
      _ ≤ (localNorm f (x + t • d) d) ^ 2 := pow_le_pow_left₀ h2 h1 2
      _ = q t := h3
  -- Claim A
  have hA : s / 4 ≤ ψ t1 := by
    have := mono (fun t => ψ t - s ^ 2 * t + s ^ 3 * t ^ 2)
      (fun t => q t - s ^ 2 + s ^ 3 * (2 * t)) 0 t1 ht1_pos.le
      (fun t ht => by
        have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨ht.1, by linarith [ht.2]⟩
        have := (((hψ' t htI).sub ((hasDerivAt_id t).const_mul (s ^ 2))).add
          (((hasDerivAt_pow 2 t).const_mul (s ^ 3))))
        convert this using 1
        simp)
      (fun t ht => by
        have := hq_lower t ht
        nlinarith [sq_nonneg (t * s ^ 2)])
    simp only at this
    have e1 : s ^ 2 * t1 = s / 2 := by linear_combination s * ht1s
    have e2 : s ^ 3 * t1 ^ 2 = s / 4 := by linear_combination (s * (t1 * s + 1 / 2)) * ht1s
    linarith
  -- Claim B
  have hψpos : ∀ t ∈ Set.Icc t1 1, 0 < ψ t := by
    intro t ht
    have := hψmono t1 t ht1_pos.le ht.1 ht.2
    linarith
  have hB : (1 - t1) * ψ t1 ≤ θ := by
    have hm := mono (fun t => -θ * (ψ t)⁻¹ - t) (fun t => -θ * (-(q t) / (ψ t) ^ 2) - 1) t1 1
      (by linarith)
      (fun t ht => by
        have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
        exact (((hψ' t htI).inv (hψpos t ht).ne').const_mul (-θ)).sub (hasDerivAt_id t))
      (fun t ht => by
        have htI : t ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith [ht.1], ht.2⟩
        have hp := hψpos t ht
        have hpq := hψq t htI
        have : 1 ≤ θ * q t / ψ t ^ 2 := by rw [le_div_iff₀ (by positivity)]; linarith
        have : -θ * (-(q t) / (ψ t) ^ 2) - 1 = θ * q t / ψ t ^ 2 - 1 := by ring
        linarith)
    simp only at hm
    have hp1 := hψpos 1 ⟨by linarith, le_refl _⟩
    have hpt1 := hψpos t1 ⟨le_refl _, by linarith⟩
    have h1 : 0 ≤ θ * (ψ 1)⁻¹ := by positivity
    have h2 : 1 - t1 ≤ θ * (ψ t1)⁻¹ := by linarith
    have h3 := mul_le_mul_of_nonneg_right h2 hpt1.le
    rw [mul_assoc, inv_mul_cancel₀ hpt1.ne', mul_one] at h3
    exact h3
  have e3 : (1 - t1) * (s / 4) = s / 4 - 1 / 8 := by linear_combination (-1 / 4) * ht1s
  have e4 := mul_le_mul_of_nonneg_left hA (by linarith : (0:ℝ) ≤ 1 - t1)
  linarith

end Renegar_chap_2_2_3_4
