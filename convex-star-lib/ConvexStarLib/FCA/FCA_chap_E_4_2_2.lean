import ConvexStarLib.Defs

/-!
# `FCA_chap_E_4_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_4_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_4_2_2`, so the main result is `FCA_chap_E_4_2_2.FCA_chap_E_4_2_2`.
-/

namespace FCA_chap_E_4_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open InnerProductSpace Filter Asymptotics

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_4_2_2
  (f : E → ℝ)
  (L : ℝ)
  (hL : L > 0)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lip_grad : ∀ (x₁ x₂ : E),
                 ‖gradient f x₁ - gradient f x₂‖ ≤ L * ‖x₁ - x₂‖) :
  (∀ (C : Set E),
  (C ⊆ effDom ((conjugate (liftRealtoEReal f)))) →
  (Convex ℝ C) →
  (∃ (g : E → ℝ),
  (∀ s ∈ C, (conjugate (liftRealtoEReal f) s) = (g s : EReal)) ∧
  (StrongConvexOn C (1 / L) g)) ∧
  (∀ (x₁ x₂ : E),
  inner ℝ (gradient f x₁ - gradient f x₂) (x₁ - x₂) ≥
  (1 / L) * ‖gradient f x₁ - gradient f x₂‖ ^ 2)) := by
  set G : E → E := gradient f with hG_def
  have hG_cont : Continuous G := by
    refine (LipschitzWith.of_dist_le' (K := L) fun x y => ?_).continuous
    rw [dist_eq_norm, dist_eq_norm]
    exact hf_lip_grad x y
  have hf_cont : Continuous f := hf_convex.locallyLipschitz.continuous
  -- Step 1: density of differentiability points
  have hD : Dense {x | DifferentiableAt ℝ f x} := by
    letI : MeasurableSpace E := borel E
    haveI : BorelSpace E := ⟨rfl⟩
    rw [dense_iff_inter_open]
    rintro U hU ⟨x, hxU⟩
    obtain ⟨K, t, ht, hKt⟩ := hf_convex.locallyLipschitz x
    set V := interior t ∩ U with hV_def
    have hVo : IsOpen V := isOpen_interior.inter hU
    have hxV : x ∈ V := ⟨mem_interior_iff_mem_nhds.2 ht, hxU⟩
    have hKV : LipschitzOnWith K f V := hKt.mono (Set.inter_subset_left.trans interior_subset)
    have hae := hKV.ae_differentiableWithinAt_of_mem
      (μ := (Module.Basis.ofVectorSpace ℝ E).addHaar)
    obtain ⟨y, hyV, hy⟩ :=
      (MeasureTheory.Measure.dense_of_ae hae).inter_open_nonempty V hVo ⟨x, hxV⟩
    exact ⟨y, hyV.2, (hy hyV).differentiableAt (hVo.mem_nhds hyV)⟩
  -- Step 2: subgradient inequality at differentiability points
  have hA0 : ∀ x, DifferentiableAt ℝ f x → ∀ y, f x + inner ℝ (G x) (y - x) ≤ f y := by
    intro x hx y
    set phi : ℝ → ℝ := fun t => f (x + t • (y - x)) with hphi
    have hphic : ConvexOn ℝ Set.univ phi := by
      refine ⟨convex_univ, fun a _ b _ m n hm hn hmn => ?_⟩
      have := hf_convex.2 (Set.mem_univ (x + a • (y - x))) (Set.mem_univ (x + b • (y - x)))
        hm hn hmn
      have e : x + (m • a + n • b) • (y - x) = m • (x + a • (y - x)) + n • (x + b • (y - x)) := by
        have hn' : n = 1 - m := by linarith
        subst hn'
        simp only [smul_eq_mul]
        module
      simp only [hphi, e]
      exact this
    have hphid : HasDerivAt phi (inner ℝ (G x) (y - x)) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
      have h2 : HasFDerivAt f (fderiv ℝ f x) (x + (0:ℝ) • (y - x)) := by
        simpa using hx.hasFDerivAt
      have h3 := h2.comp_hasDerivAt (0:ℝ) h1
      rw [hx.hasGradientAt.fderiv_apply] at h3
      exact h3
    have := hphic.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hphid
    rw [slope_def_field] at this
    simp [hphi] at this
    linarith
  -- Step 3: subgradient inequality everywhere
  have hA : ∀ x y, f x + inner ℝ (G x) (y - x) ≤ f y := by
    intro x y
    have hclosed : IsClosed {x | f x + inner ℝ (G x) (y - x) ≤ f y} :=
      isClosed_le (hf_cont.add (hG_cont.inner (continuous_const.sub continuous_id)))
        continuous_const
    have hsub : {x | DifferentiableAt ℝ f x} ⊆ {x | f x + inner ℝ (G x) (y - x) ≤ f y} :=
      fun x hx => hA0 x hx y
    have h1 := closure_minimal hsub hclosed
    rw [hD.closure_eq] at h1
    exact h1 (Set.mem_univ x)
  -- Step 4: f has gradient G x at every x
  have hgrad : ∀ x, HasGradientAt f (G x) x := by
    intro x
    rw [hasGradientAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro c hc
    have hball : Metric.ball x (c / L) ∈ 𝓝 x := Metric.ball_mem_nhds x (div_pos hc hL)
    filter_upwards [hball] with y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have h1 := hA x y
    have h2 := hA y x
    have h3 : inner ℝ (G y - G x) (y - x) ≤ L * ‖y - x‖ ^ 2 := by
      calc inner ℝ (G y - G x) (y - x) ≤ ‖G y - G x‖ * ‖y - x‖ := real_inner_le_norm _ _
        _ ≤ L * ‖y - x‖ * ‖y - x‖ := by gcongr; exact hf_lip_grad y x
        _ = L * ‖y - x‖ ^ 2 := by ring
    have h4 : inner ℝ (G y) (x - y) = - inner ℝ (G y) (y - x) := by
      rw [← inner_neg_right, neg_sub]
    have h5 : inner ℝ (G y - G x) (y - x) = inner ℝ (G y) (y - x) - inner ℝ (G x) (y - x) :=
      inner_sub_left _ _ _
    rw [Real.norm_eq_abs, abs_le]
    have h6 : L * ‖y - x‖ ^ 2 ≤ c * ‖y - x‖ := by
      have : L * ‖y - x‖ ≤ c := by rw [lt_div_iff₀ hL] at hy; linarith
      nlinarith [norm_nonneg (y - x)]
    constructor <;> nlinarith
  -- Step 5: descent lemma
  have hB : ∀ x y, f y ≤ f x + inner ℝ (G x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
    intro x y
    set d := y - x with hd
    set psi : ℝ → ℝ := fun t => f (x + t • d) - f x - t * inner ℝ (G x) d with hpsi
    have hpsid : ∀ t, HasDerivAt psi (inner ℝ (G (x + t • d)) d - inner ℝ (G x) d) t := by
      intro t
      have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
        simpa using ((hasDerivAt_id t).smul_const d).const_add x
      have h2 := (hgrad (x + t • d)).hasFDerivAt.comp_hasDerivAt t h1
      rw [InnerProductSpace.toDual_apply_apply] at h2
      have h3 := (h2.sub_const (f x)).sub ((hasDerivAt_id t).mul_const (inner ℝ (G x) d))
      simpa using h3
    have key := image_le_of_deriv_right_le_deriv_boundary (a := 0) (b := 1) (f := psi)
      (f' := fun t => inner ℝ (G (x + t • d)) d - inner ℝ (G x) d)
      (B := fun t => L / 2 * t ^ 2 * ‖d‖ ^ 2) (B' := fun t => L * t * ‖d‖ ^ 2)
      (fun t _ => (hpsid t).continuousAt.continuousWithinAt)
      (fun t _ => (hpsid t).hasDerivWithinAt)
      (by simp [hpsi])
      (by fun_prop)
      (fun t _ => by
        have : HasDerivAt (fun t : ℝ => L / 2 * t ^ 2 * ‖d‖ ^ 2) (L * t * ‖d‖ ^ 2) t := by
          have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖d‖ ^ 2)
          convert this using 1; ring
        exact this.hasDerivWithinAt)
      (fun t ht => by
        show inner ℝ (G (x + t • d)) d - inner ℝ (G x) d ≤ L * t * ‖d‖ ^ 2
        rw [← inner_sub_left]
        calc inner ℝ (G (x + t • d) - G x) d ≤ ‖G (x + t • d) - G x‖ * ‖d‖ :=
              real_inner_le_norm _ _
          _ ≤ L * ‖x + t • d - x‖ * ‖d‖ := by gcongr; exact hf_lip_grad _ _
          _ = L * t * ‖d‖ ^ 2 := by
            rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]; ring)
      (Set.right_mem_Icc.2 zero_le_one)
    have hxd : x + d = y := by rw [hd]; abel
    simp [hpsi, hxd] at key
    linarith
  -- Step 6: key inequality
  have hK : ∀ x₁ x₂, f x₂ + inner ℝ (G x₂) (x₁ - x₂) + 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 ≤ f x₁ := by
    intro x₁ x₂
    set z := x₁ - (1 / L) • (G x₁ - G x₂) with hz
    have h1 := hA x₂ z
    have h2 := hB x₁ z
    have e1 : z - x₂ = (x₁ - x₂) - (1 / L) • (G x₁ - G x₂) := by rw [hz]; abel
    have e2 : z - x₁ = -((1 / L) • (G x₁ - G x₂)) := by rw [hz]; abel
    rw [e1, inner_sub_right, real_inner_smul_right] at h1
    rw [e2, inner_neg_right, real_inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at h2
    have e3 : inner ℝ (G x₁) (G x₁ - G x₂) - inner ℝ (G x₂) (G x₁ - G x₂) = ‖G x₁ - G x₂‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have e4 : L / 2 * (1 / L * ‖G x₁ - G x₂‖) ^ 2 = 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 := by
      field_simp
    have e5 : 1 / L * inner ℝ (G x₁) (G x₁ - G x₂) - 1 / L * inner ℝ (G x₂) (G x₁ - G x₂)
        = 1 / L * ‖G x₁ - G x₂‖ ^ 2 := by
      rw [← e3]; ring
    have e6 : 1 / L * ‖G x₁ - G x₂‖ ^ 2
        = 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 + 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 := by
      field_simp; ring
    linarith
  -- co-coercivity
  have hcoco : ∀ x₁ x₂, inner ℝ (G x₁ - G x₂) (x₁ - x₂) ≥ (1 / L) * ‖G x₁ - G x₂‖ ^ 2 := by
    intro x₁ x₂
    have h1 := hK x₁ x₂
    have h2 := hK x₂ x₁
    rw [norm_sub_rev (G x₂) (G x₁)] at h2
    have e : inner ℝ (G x₁ - G x₂) (x₁ - x₂)
        = - inner ℝ (G x₂) (x₁ - x₂) - inner ℝ (G x₁) (x₂ - x₁) := by
      rw [inner_sub_left, ← neg_sub x₁ x₂, inner_neg_right]; ring
    rw [ge_iff_le, e]
    have : 1 / L * ‖G x₁ - G x₂‖ ^ 2
        = 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 + 1 / (2 * L) * ‖G x₁ - G x₂‖ ^ 2 := by
      field_simp; ring
    linarith
  -- conjugate lower bound
  have hconj : ∀ s x, (((inner ℝ s x - f x + 1 / (2 * L) * ‖s - G x‖ ^ 2 : ℝ)) : EReal) ≤
      conjugate (liftRealtoEReal f) s := by
    intro s x
    set y := x + (1 / L) • (s - G x) with hy
    have h1 : (((inner ℝ s y - f y : ℝ)) : EReal) ≤ conjugate (liftRealtoEReal f) s := by
      apply le_sSup
      exact ⟨y, Set.mem_univ y, by simp [liftRealtoEReal, EReal.coe_sub]⟩
    refine le_trans ?_ h1
    rw [EReal.coe_le_coe_iff]
    have h2 := hB x y
    have e1 : y - x = (1 / L) • (s - G x) := by rw [hy]; abel
    rw [e1, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at h2
    have e2 : inner ℝ s y = inner ℝ s x + 1 / L * inner ℝ s (s - G x) := by
      rw [hy, inner_add_right, real_inner_smul_right]
    rw [e2]
    have e3 : inner ℝ s (s - G x) - inner ℝ (G x) (s - G x) = ‖s - G x‖ ^ 2 := by
      rw [← inner_sub_left, real_inner_self_eq_norm_sq]
    have e4 : L / 2 * (1 / L * ‖s - G x‖) ^ 2 = 1 / (2 * L) * ‖s - G x‖ ^ 2 := by
      field_simp
    have e5 : 1 / L * inner ℝ s (s - G x) - 1 / L * inner ℝ (G x) (s - G x)
        = 1 / L * ‖s - G x‖ ^ 2 := by
      rw [← e3]; ring
    have e6 : 1 / L * ‖s - G x‖ ^ 2 = 1 / (2 * L) * ‖s - G x‖ ^ 2 + 1 / (2 * L) * ‖s - G x‖ ^ 2 := by
      field_simp; ring
    linarith
  have hquad : ∀ (p q : E) (a b : ℝ), a + b = 1 →
      a * b * ‖p - q‖ ^ 2 ≤ a * ‖p‖ ^ 2 + b * ‖q‖ ^ 2 := by
    intro p q a b hab
    have h1 : ‖a • p + b • q‖ ^ 2
        = a ^ 2 * ‖p‖ ^ 2 + 2 * (a * b) * inner ℝ p q + b ^ 2 * ‖q‖ ^ 2 := by
      rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
        Real.norm_eq_abs, Real.norm_eq_abs, mul_pow, mul_pow, sq_abs, sq_abs]
      ring
    have h2 : ‖p - q‖ ^ 2 = ‖p‖ ^ 2 - 2 * inner ℝ p q + ‖q‖ ^ 2 := norm_sub_sq_real p q
    have h3 : 0 ≤ ‖a • p + b • q‖ ^ 2 := sq_nonneg _
    rw [h2]
    have hb : b = 1 - a := by linarith
    subst hb
    nlinarith [h1, h3]
  intro C hC hCconv
  refine ⟨?_, hcoco⟩
  set F := conjugate (liftRealtoEReal f) with hF
  have hFbot : ∀ s, F s ≠ ⊥ := by
    intro s h
    have := hconj s 0
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  refine ⟨fun s => (F s).toReal, fun s hs => ?_, hCconv, ?_⟩
  · exact (EReal.coe_toReal (hC hs).ne (hFbot s)).symm
  · intro s hs t ht a b ha hb hab
    have hu : a • s + b • t ∈ C := hCconv hs ht ha hb hab
    have hFs : F s = ((F s).toReal : EReal) := (EReal.coe_toReal (hC hs).ne (hFbot s)).symm
    have hFt : F t = ((F t).toReal : EReal) := (EReal.coe_toReal (hC ht).ne (hFbot t)).symm
    have hFu : F (a • s + b • t) = ((F (a • s + b • t)).toReal : EReal) :=
      (EReal.coe_toReal (hC hu).ne (hFbot _)).symm
    simp only [smul_eq_mul]
    rw [← EReal.coe_le_coe_iff, ← hFu]
    apply sSup_le
    rintro v ⟨x, -, rfl⟩
    simp only [liftRealtoEReal]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have h1 := hconj s x
    have h2 := hconj t x
    rw [hFs, EReal.coe_le_coe_iff] at h1
    rw [hFt, EReal.coe_le_coe_iff] at h2
    have h3 := hquad (s - G x) (t - G x) a b hab
    rw [sub_sub_sub_cancel_right] at h3
    have e1 : inner ℝ (a • s + b • t) x = a * inner ℝ s x + b * inner ℝ t x := by
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    rw [e1]
    have hk : (0:ℝ) ≤ 1 / (2 * L) := by positivity
    have i1 := mul_le_mul_of_nonneg_left h1 ha
    have i2 := mul_le_mul_of_nonneg_left h2 hb
    have i3 := mul_le_mul_of_nonneg_left h3 hk
    have e2 : 1 / L / 2 = 1 / (2 * L) := by ring
    rw [e2]
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [i1, i2, i3]

end FCA_chap_E_4_2_2
