import ConvexStarLib.Defs

/-!
# `FCA_chap_E_4_1_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_4_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_4_1_3`, so the main result is `FCA_chap_E_4_1_3.FCA_chap_E_4_1_3`.
-/

namespace FCA_chap_E_4_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Subgradient inequality for a convex differentiable function. -/
lemma aux_subgrad {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) {x : E}
    (hx : DifferentiableAt ℝ f x) (y : E) :
    f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
  set d := y - x with hd
  let g1 : ℝ → ℝ := fun t => f (x + t • d)
  have hgc : ConvexOn ℝ Set.univ g1 := by
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have := hconv.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
    simp only [g1, smul_eq_mul]
    convert this using 2
    have : x = μ • x + ν • x := by rw [← add_smul, hμν, one_smul]
    conv_lhs => rw [this]
    module
  have hgd : HasDerivAt g1 (inner ℝ (gradient f x) d) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
    have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • d) := by
      simpa using hx.hasFDerivAt
    have := h2.comp_hasDerivAt (0:ℝ) h1
    rw [inner_gradient_left hx]
    exact this
  have := hgc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hgd
  simp only [slope, g1, hd] at this
  simp at this
  linarith

/-- Strict subgradient inequality for a strictly convex differentiable function. -/
lemma aux_subgrad_strict {f : E → ℝ} (hsc : StrictConvexOn ℝ Set.univ f) {x : E}
    (hx : DifferentiableAt ℝ f x) {y : E} (hxy : x ≠ y) :
    f x + inner ℝ (gradient f x) (y - x) < f y := by
  have h1 := hsc.2 (Set.mem_univ x) (Set.mem_univ y) hxy (by norm_num : (0:ℝ) < 1/2)
    (by norm_num : (0:ℝ) < 1/2) (by norm_num)
  have h2 := aux_subgrad hsc.convexOn hx ((1/2 : ℝ) • x + (1/2 : ℝ) • y)
  have h3 : (1/2 : ℝ) • x + (1/2 : ℝ) • y - x = (1/2 : ℝ) • (y - x) := by
    module
  rw [h3, inner_smul_right] at h2
  simp only [smul_eq_mul] at h1
  linarith

/-- Fermat's rule: at a minimizer of `f - ⟪s, ·⟫`, the gradient of `f` is `s`. -/
lemma aux_grad_eq_of_min {f : E → ℝ} {x s : E} (hx : DifferentiableAt ℝ f x)
    (hmin : ∀ y, f x - inner ℝ s x ≤ f y - inner ℝ s y) : gradient f x = s := by
  have hF : HasFDerivAt (fun y => f y - inner ℝ s y) (fderiv ℝ f x - innerSL ℝ s) x :=
    hx.hasFDerivAt.sub (innerSL ℝ s).hasFDerivAt
  have hloc : IsLocalMin (fun y => f y - inner ℝ s y) x :=
    Filter.Eventually.of_forall hmin
  have h0 := hloc.hasFDerivAt_eq_zero hF
  apply ext_inner_right ℝ
  intro v
  rw [inner_gradient_left hx]
  have := congrArg (fun L : E →L[ℝ] ℝ => L v) h0
  simp only [ContinuousLinearMap.sub_apply, innerSL_apply_apply,
    ContinuousLinearMap.zero_apply] at this
  linarith

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Real form of 1-coercivity. -/
lemma aux_coercive_real {f : E → ℝ} (h : IsOneCoerciveFun (liftRealtoEReal f)) (C : ℝ) :
    ∀ᶠ x in Bornology.cobounded E, C * ‖x‖ ≤ f x := by
  have h1 := h C
  rw [comap_norm_atTop] at h1
  filter_upwards [h1, eventually_cobounded_le_norm 1] with x hx hx1
  have hpos : 0 < ‖x‖ := by linarith
  simp only [liftRealtoEReal] at hx
  rw [← EReal.coe_mul, EReal.coe_le_coe_iff, le_inv_mul_iff₀ hpos] at hx
  linarith [mul_comm C ‖x‖]

/-- Existence of a minimizer of `f - ⟪s, ·⟫`. -/
lemma aux_exists_min {f : E → ℝ} (hcont : Continuous f)
    (h : IsOneCoerciveFun (liftRealtoEReal f)) (s : E) :
    ∃ x, ∀ y, f x - inner ℝ s x ≤ f y - inner ℝ s y := by
  have hc : Continuous (fun y => f y - inner ℝ s y) := hcont.sub (continuous_const.inner continuous_id)
  apply hc.exists_forall_le
  rw [← Metric.cobounded_eq_cocompact, Filter.tendsto_atTop]
  intro M
  filter_upwards [aux_coercive_real h (‖s‖ + 1), eventually_cobounded_le_norm M] with y hy hyM
  have := real_inner_le_norm s y
  nlinarith

/-- The gradient of a convex differentiable function is continuous. -/
lemma aux_grad_cont {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) :
    Continuous (gradient f) := by
  rw [Metric.continuous_iff]
  intro x ε hε
  have hg : HasGradientAt f (gradient f x) x := (hd x).hasGradientAt
  rw [hasGradientAt_iff_isLittleO] at hg
  have hη : (0:ℝ) < ε / 4 := by positivity
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 (hg.def hη)
  refine ⟨δ / 2, by positivity, fun x' hx' => ?_⟩
  rw [dist_eq_norm] at hx' ⊢
  set v := gradient f x' - gradient f x with hv
  by_cases hv0 : v = 0
  · rw [hv0, norm_zero]; exact hε
  have hvpos : 0 < ‖v‖ := norm_pos_iff.2 hv0
  set t := δ / 2 with ht
  have htpos : 0 < t := by positivity
  set w := (t / ‖v‖) • v with hw
  have hwn : ‖w‖ = t := by
    rw [hw, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hvpos.ne']
  have hvw : inner ℝ v w = t * ‖v‖ := by
    rw [hw, real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
  have hsub := aux_subgrad hconv (hd x') (x' + w)
  rw [add_sub_cancel_left] at hsub
  have n1 : ‖x' + w - x‖ ≤ ‖x' - x‖ + t := by
    calc ‖x' + w - x‖ = ‖(x' - x) + w‖ := by congr 1; abel
      _ ≤ ‖x' - x‖ + ‖w‖ := norm_add_le _ _
      _ = ‖x' - x‖ + t := by rw [hwn]
  have hb1 := hball (show dist (x' + w) x < δ by rw [dist_eq_norm]; linarith)
  have hb2 := hball (show dist x' x < δ by rw [dist_eq_norm]; linarith)
  simp only [Real.norm_eq_abs] at hb1 hb2
  have e1 : inner ℝ (gradient f x) (x' + w - x) =
      inner ℝ (gradient f x) (x' - x) + inner ℝ (gradient f x) w := by
    rw [← inner_add_right]; congr 1; abel
  have e2 : inner ℝ v w = inner ℝ (gradient f x') w - inner ℝ (gradient f x) w := by
    rw [hv, inner_sub_left]
  have a1 := (abs_le.1 hb1).2
  have a2 := (abs_le.1 hb2).1
  have m1 : ε / 4 * ‖x' + w - x‖ ≤ ε / 4 * (2 * t) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have m2 : ε / 4 * ‖x' - x‖ ≤ ε / 4 * t :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have key : t * ‖v‖ ≤ t * (3 * (ε / 4)) := by nlinarith
  have := le_of_mul_le_mul_left key htpos
  linarith

/-- The gradient tends to infinity at infinity. -/
lemma aux_grad_tendsto {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f)
    (h : IsOneCoerciveFun (liftRealtoEReal f)) :
    Filter.Tendsto (gradient f) (Filter.cocompact E) (Filter.cocompact E) := by
  rw [← Metric.cobounded_eq_cocompact, ← tendsto_norm_atTop_iff_cobounded, Filter.tendsto_atTop]
  intro M
  filter_upwards [aux_coercive_real h (M + |f 0|), eventually_cobounded_le_norm 1] with y hy hy1
  have hsub := aux_subgrad hconv (hd y) 0
  rw [zero_sub, inner_neg_right] at hsub
  have hcs := real_inner_le_norm (gradient f y) y
  have habs := le_abs_self (f 0)
  have h1 : |f 0| ≤ |f 0| * ‖y‖ := le_mul_of_one_le_right (abs_nonneg _) hy1
  have h2 : M * ‖y‖ ≤ ‖gradient f y‖ * ‖y‖ := by nlinarith
  exact le_of_mul_le_mul_right h2 (by linarith)

/-- Value of the conjugate. -/
lemma aux_conj_eq {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hd : Differentiable ℝ f) {s x : E}
    (hx : gradient f x = s) :
    conjugate (liftRealtoEReal f) s = ((inner ℝ s x - f x : ℝ) : EReal) := by
  unfold conjugate
  apply IsGreatest.csSup_eq
  refine ⟨⟨x, Set.mem_univ _, ?_⟩, ?_⟩
  · simp [liftRealtoEReal, EReal.coe_sub]
  · rintro _ ⟨y, -, rfl⟩
    simp only [liftRealtoEReal]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := aux_subgrad hconv (hd x) y
    rw [hx, inner_sub_right] at this
    linarith

set_option linter.unusedVariables false in
theorem FCA_chap_E_4_1_3
  (f : E → ℝ)
  (hf_convex : InConvRn (liftRealtoEReal f))
  (hf_strict : StrictConvexOn ℝ Set.univ f)
  (hf_diff : Differentiable ℝ f)
  (hf_coercive : IsOneCoerciveFun (liftRealtoEReal f)) :
  (∀ s, conjugate (liftRealtoEReal f) s < ⊤) ∧
  (∃ (g : E → ℝ),
    (∀ s, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
    (StrictConvexOn ℝ Set.univ g) ∧
    (Differentiable ℝ g) ∧
    (IsOneCoerciveFun (liftRealtoEReal g))) ∧
  ((Function.Bijective (gradient f)) ∧
    (Continuous (gradient f)) ∧
    (Continuous (Function.invFun (gradient f)))) ∧
  (∀ s, (conjugate (liftRealtoEReal f) s) =
  (inner ℝ s (Function.invFun (gradient f) s) -
  f (Function.invFun (gradient f) s) : ℝ)) := by
  have hconv : ConvexOn ℝ Set.univ f := hf_strict.convexOn
  have hcont : Continuous f := hf_diff.continuous
  -- surjectivity of the gradient
  have hsurj : Function.Surjective (gradient f) := by
    intro s
    obtain ⟨x, hx⟩ := aux_exists_min hcont hf_coercive s
    exact ⟨x, aux_grad_eq_of_min (hf_diff x) hx⟩
  -- injectivity of the gradient
  have hinj : Function.Injective (gradient f) := by
    intro x y hxy
    by_contra hne
    have k1 := aux_subgrad_strict hf_strict (hf_diff x) hne
    have k2 := aux_subgrad_strict hf_strict (hf_diff y) (Ne.symm hne)
    rw [hxy, inner_sub_right] at k1
    rw [inner_sub_right] at k2
    linarith
  have hbij : Function.Bijective (gradient f) := ⟨hinj, hsurj⟩
  have hgc : Continuous (gradient f) := aux_grad_cont hconv hf_diff
  -- continuity of the inverse
  have hclosed : IsClosedMap (gradient f) :=
    (isProperMap_iff_tendsto_cocompact.2
      ⟨hgc, aux_grad_tendsto hconv hf_diff hf_coercive⟩).isClosedMap
  have hXc : Continuous (Function.invFun (gradient f)) := by
    let e := Equiv.ofBijective (gradient f) hbij
    let hm := e.toHomeomorphOfContinuousClosed hgc hclosed
    have : Function.invFun (gradient f) = hm.symm := by
      funext s
      apply hinj
      rw [Function.invFun_eq (hsurj s)]
      simp only [hm, e, Equiv.toHomeomorphOfContinuousClosed_symm_apply]
      exact (Equiv.ofBijective_apply_symm_apply _ hbij s).symm
    rw [this]
    exact hm.symm.continuous
  set X := Function.invFun (gradient f) with hX
  have hXinv : ∀ s, gradient f (X s) = s := fun s => Function.invFun_eq (hsurj s)
  have hconj : ∀ s, conjugate (liftRealtoEReal f) s = ((inner ℝ s (X s) - f (X s) : ℝ) : EReal) :=
    fun s => aux_conj_eq hconv hf_diff (hXinv s)
  -- the conjugate as a real function
  set g : E → ℝ := fun s => inner ℝ s (X s) - f (X s) with hg
  -- `g s` dominates every affine minorant `⟪s, y⟫ - f y`
  have hgy : ∀ s y, inner ℝ s y - f y ≤ g s := by
    intro s y
    have := aux_subgrad hconv (hf_diff (X s)) y
    rw [hXinv s, inner_sub_right] at this
    simp only [hg]
    linarith
  refine ⟨fun s => by rw [hconj s]; exact EReal.coe_lt_top _, ⟨g, hconj, ?_, ?_, ?_⟩,
    ⟨hbij, hgc, hXc⟩, hconj⟩
  · -- strict convexity of g
    refine ⟨convex_univ, fun s1 _ s2 _ hne a b ha hb hab => ?_⟩
    have hne' : ∀ s', s' ≠ a • s1 + b • s2 → X (a • s1 + b • s2) ≠ X s' := by
      intro s' hs' h
      apply hs'
      rw [← hXinv s', ← h, hXinv]
    have hs1 : s1 ≠ a • s1 + b • s2 := by
      intro h
      apply hne
      have h1 : b • (s2 - s1) = 0 := by
        have ha' : a = 1 - b := by linarith
        rw [ha'] at h
        calc b • (s2 - s1) = s1 - ((1 - b) • s1 + b • s2) + b • (s2 - s1) - s1 + s1 := by
              rw [← h]; abel
          _ = 0 := by module
      rcases smul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact (sub_eq_zero.1 h2).symm
    have hs2 : s2 ≠ a • s1 + b • s2 := by
      intro h
      apply hne
      have h1 : a • (s1 - s2) = 0 := by
        have hb' : b = 1 - a := by linarith
        rw [hb'] at h
        calc a • (s1 - s2) = s2 - (a • s1 + (1 - a) • s2) + a • (s1 - s2) - s2 + s2 := by
              rw [← h]; abel
          _ = 0 := by module
      rcases smul_eq_zero.1 h1 with h2 | h2
      · linarith
      · exact sub_eq_zero.1 h2
    have k1 := aux_subgrad_strict hf_strict (hf_diff (X s1)) (hne' s1 hs1).symm
    have k2 := aux_subgrad_strict hf_strict (hf_diff (X s2)) (hne' s2 hs2).symm
    rw [hXinv, inner_sub_right] at k1 k2
    have e : inner ℝ (a • s1 + b • s2) (X (a • s1 + b • s2)) =
        a * inner ℝ s1 (X (a • s1 + b • s2)) + b * inner ℝ s2 (X (a • s1 + b • s2)) := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have m1 := mul_lt_mul_of_pos_left (show inner ℝ s1 (X (a • s1 + b • s2)) -
      f (X (a • s1 + b • s2)) < inner ℝ s1 (X s1) - f (X s1) by linarith) ha
    have m2 := mul_lt_mul_of_pos_left (show inner ℝ s2 (X (a • s1 + b • s2)) -
      f (X (a • s1 + b • s2)) < inner ℝ s2 (X s2) - f (X s2) by linarith) hb
    have hfab : f (X (a • s1 + b • s2)) =
        a * f (X (a • s1 + b • s2)) + b * f (X (a • s1 + b • s2)) := by
      rw [← add_mul, hab, one_mul]
    simp only [hg, smul_eq_mul]
    rw [e]
    linarith
  · -- differentiability of g
    intro s
    have : HasGradientAt g (X s) s := by
      rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
      intro c hc
      have hev : ∀ᶠ s' in 𝓝 s, dist (X s') (X s) < c :=
        Metric.tendsto_nhds.1 (hXc.tendsto s) c hc
      filter_upwards [hev] with s' hs'
      rw [dist_eq_norm] at hs'
      have l1 := aux_subgrad hconv (hf_diff (X s')) (X s)
      rw [hXinv s', inner_sub_right] at l1
      have l2 := aux_subgrad hconv (hf_diff (X s)) (X s')
      rw [hXinv s, inner_sub_right] at l2
      have key : 0 ≤ g s' - g s - inner ℝ (X s) (s' - s) ∧
          g s' - g s - inner ℝ (X s) (s' - s) ≤ inner ℝ (s' - s) (X s' - X s) := by
        simp only [hg]
        rw [real_inner_comm (s' - s) (X s)]
        simp only [inner_sub_left, inner_sub_right]
        constructor <;> linarith
      have cs := real_inner_le_norm (s' - s) (X s' - X s)
      rw [Real.norm_eq_abs, abs_of_nonneg key.1]
      calc _ ≤ inner ℝ (s' - s) (X s' - X s) := key.2
        _ ≤ ‖s' - s‖ * ‖X s' - X s‖ := cs
        _ ≤ ‖s' - s‖ * c := by gcongr
        _ = c * ‖s' - s‖ := mul_comm _ _
    exact this.differentiableAt
  · -- 1-coercivity of g
    intro C
    rw [comap_norm_atTop]
    have hRpos : 0 < |C| + 1 := by positivity
    obtain ⟨M, hM⟩ :=
      (isCompact_closedBall (0:E) (|C| + 1)).exists_bound_of_continuousOn hcont.continuousOn
    filter_upwards [eventually_cobounded_le_norm (max M 1)] with s hs
    have hs1 : 1 ≤ ‖s‖ := le_trans (le_max_right _ _) hs
    have hsM : M ≤ ‖s‖ := le_trans (le_max_left _ _) hs
    have hspos : 0 < ‖s‖ := by linarith
    have hyn : ‖((|C| + 1) / ‖s‖) • s‖ = |C| + 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), div_mul_cancel₀ _ hspos.ne']
    have hsy : inner ℝ s (((|C| + 1) / ‖s‖) • s) = (|C| + 1) * ‖s‖ := by
      rw [real_inner_smul_right, real_inner_self_eq_norm_sq]; field_simp
    have hfy : f (((|C| + 1) / ‖s‖) • s) ≤ M := by
      have := hM (((|C| + 1) / ‖s‖) • s) (by rw [mem_closedBall_zero_iff, hyn])
      rw [Real.norm_eq_abs] at this
      exact le_trans (le_abs_self _) this
    have hgs := hgy s (((|C| + 1) / ‖s‖) • s)
    simp only [liftRealtoEReal]
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff, le_inv_mul_iff₀ hspos]
    have hC : C * ‖s‖ ≤ |C| * ‖s‖ := mul_le_mul_of_nonneg_right (le_abs_self C) hspos.le
    have : (|C| + 1) * ‖s‖ = |C| * ‖s‖ + ‖s‖ := by ring
    nlinarith

end FCA_chap_E_4_1_3
