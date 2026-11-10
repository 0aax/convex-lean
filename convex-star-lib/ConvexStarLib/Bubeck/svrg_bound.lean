import ConvexStarLib.Defs

/-!
# `svrg_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/svrg_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace svrg_bound`, so the main result is `svrg_bound.svrg_bound`.
-/

namespace svrg_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


section SVRGAux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- First-order condition for convexity. -/
lemma svrg_convex_first_order {g : E → ℝ} (hd : Differentiable ℝ g)
    (hc : ConvexOn ℝ Set.univ g) (x y : E) :
    g x + inner ℝ (gradient g x) (y - x) ≤ g y := by
  set phi : ℝ → ℝ := fun t => g (x + t • (y - x)) with hphi
  have hphic : ConvexOn ℝ Set.univ phi := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ μ ν hμ hν hμν
    have key : x + (μ • a + ν • b) • (y - x) = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
      have hx : x = μ • x + ν • x := by rw [← add_smul, hμν, one_smul]
      calc x + (μ • a + ν • b) • (y - x)
          = (μ • x + ν • x) + (μ • a + ν • b) • (y - x) := by rw [← hx]
        _ = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
          simp only [smul_add, add_smul, smul_eq_mul, mul_smul]
          abel
    show g (x + (μ • a + ν • b) • (y - x)) ≤ μ • g (x + a • (y - x)) + ν • g (x + b • (y - x))
    rw [key]
    exact hc.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν
  have hderiv : HasDerivAt phi (inner ℝ (gradient g x) (y - x)) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).const_add x
    have h2 := (hd (x + (0:ℝ) • (y - x))).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    simp only [zero_smul, add_zero] at h2
    rw [inner_gradient_left (hd x)]
    exact h2
  have := hphic.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hderiv
  rw [slope_def_field] at this
  simp [hphi] at this
  linarith

/-- Descent lemma for functions with Lipschitz gradient. -/
lemma svrg_descent {g : E → ℝ} {L : ℝ} (hL : 0 ≤ L) (hd : Differentiable ℝ g)
    (hlip : LipschitzWith (Real.toNNReal L) (gradient g)) (x y : E) :
    g y ≤ g x + inner ℝ (gradient g x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  set d := y - x with hd_def
  set c := inner ℝ (gradient g x) d with hc_def
  set ψ : ℝ → ℝ := fun t => g (x + t • d) - t * c - L / 2 * ‖d‖ ^ 2 * t ^ 2 with hψ
  set ψ' : ℝ → ℝ := fun t => inner ℝ (gradient g (x + t • d)) d - c - L * ‖d‖ ^ 2 * t with hψ'
  have hderiv : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • d) d t := by
      simpa using ((hasDerivAt_id t).smul_const d).const_add x
    have h2 := (hd (x + t • d)).hasFDerivAt.comp_hasDerivAt t h1
    have h3 : HasDerivAt (fun t : ℝ => t * c) c t := by
      simpa using (hasDerivAt_id t).mul_const c
    have h4 : HasDerivAt (fun t : ℝ => L / 2 * ‖d‖ ^ 2 * t ^ 2) (L * ‖d‖ ^ 2 * t) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2 * ‖d‖ ^ 2))
      convert this using 1
      push_cast
      ring
    have := (h2.sub h3).sub h4
    convert this using 1
    simp only [hψ']
    rw [inner_gradient_left (hd _)]
  have hψ'_nonpos : ∀ t, 0 ≤ t → ψ' t ≤ 0 := by
    intro t ht
    simp only [hψ']
    have hL' : ((Real.toNNReal L : ℝ≥0) : ℝ) = L := Real.coe_toNNReal L hL
    have hlip' : ‖gradient g (x + t • d) - gradient g x‖ ≤ L * ‖t • d‖ := by
      have := hlip.dist_le_mul (x + t • d) x
      rw [dist_eq_norm, dist_eq_norm, hL'] at this
      simpa using this
    have hin : inner ℝ (gradient g (x + t • d)) d - c
        = inner ℝ (gradient g (x + t • d) - gradient g x) d := by
      rw [inner_sub_left]
    have h5 := real_inner_le_norm (gradient g (x + t • d) - gradient g x) d
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg ht] at hlip'
    have h6 : ‖gradient g (x + t • d) - gradient g x‖ * ‖d‖ ≤ L * (t * ‖d‖) * ‖d‖ :=
      mul_le_mul_of_nonneg_right hlip' (norm_nonneg _)
    nlinarith [h5, h6, hin]
  have hcont : ContinuousOn ψ (Set.Icc 0 1) :=
    fun t _ => (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope ψ ψ' zero_lt_one hcont (fun t _ => hderiv t)
  have hle : ψ 1 ≤ ψ 0 := by
    have := hψ'_nonpos ξ hξ.1.le
    rw [hξeq] at this
    simp at this
    linarith
  simp only [hψ] at hle
  simp [hd_def] at hle
  linarith

/-- Co-coercivity. TO PROVE -/
lemma svrg_cocoercive {g : E → ℝ} {L : ℝ} (hL : 0 < L) (hd : Differentiable ℝ g)
    (hc : ConvexOn ℝ Set.univ g) (hlip : LipschitzWith (Real.toNNReal L) (gradient g))
    (x y : E) :
    ‖gradient g y - gradient g x‖ ^ 2 ≤ 2 * L * (g y - g x - inner ℝ (gradient g x) (y - x)) := by
  have h1 := svrg_convex_first_order hd hc x (y - (1 / L) • (gradient g y - gradient g x))
  have h2 := svrg_descent hL.le hd hlip y (y - (1 / L) • (gradient g y - gradient g x))
  have e1 : y - (1 / L) • (gradient g y - gradient g x) - x
      = (y - x) - (1 / L) • (gradient g y - gradient g x) := by abel
  have e2 : y - (1 / L) • (gradient g y - gradient g x) - y
      = -((1 / L) • (gradient g y - gradient g x)) := by abel
  rw [e1, inner_sub_right, inner_smul_right] at h1
  rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / L)] at h2
  have e3 : inner ℝ (gradient g y) (gradient g y - gradient g x)
      - inner ℝ (gradient g x) (gradient g y - gradient g x)
      = ‖gradient g y - gradient g x‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  set D := ‖gradient g y - gradient g x‖ ^ 2 with hD
  set a := inner ℝ (gradient g x) (gradient g y - gradient g x) with ha
  set b := inner ℝ (gradient g y) (gradient g y - gradient g x) with hb
  set P := inner ℝ (gradient g x) (y - x) with hP
  have e4 : L / 2 * (1 / L * ‖gradient g y - gradient g x‖) ^ 2 = (1 / (2 * L)) * D := by
    rw [hD]; field_simp
  have e5 : (1 / L) * b - (1 / L) * a = (1 / L) * D := by rw [← mul_sub, e3]
  have e6 : (1 / L) * D = 2 * ((1 / (2 * L)) * D) := by field_simp
  have k2 : (1 / (2 * L)) * D ≤ g y - g x - P := by linarith
  have k3 := mul_le_mul_of_nonneg_left k2 (by positivity : (0:ℝ) ≤ 2 * L)
  have e7 : 2 * L * ((1 / (2 * L)) * D) = D := by field_simp
  linarith

/-- TO PROVE -/
lemma svrg_gradient_avg {m : ℕ} (f : Fin m → E → ℝ) (hd : ∀ i, Differentiable ℝ (f i)) (z : E) :
    gradient (fun z => (1 / (m : ℝ)) • ∑ i, f i z) z = (1 / (m : ℝ)) • ∑ i, gradient (f i) z := by
  have h : HasGradientAt (fun z => (1 / (m : ℝ)) • ∑ i, f i z)
      ((1 / (m : ℝ)) • ∑ i, gradient (f i) z) z := by
    rw [hasGradientAt_iff_hasFDerivAt]
    have hs : HasFDerivAt (fun z => ∑ i, f i z) (∑ i, fderiv ℝ (f i) z) z :=
      HasFDerivAt.fun_sum (fun i _ => (hd i z).hasFDerivAt)
    have := hs.fun_const_smul (1 / (m : ℝ))
    convert this using 1
    simp [map_sum, gradient]
  exact h.gradient

/-- TO PROVE -/
lemma svrg_gradient_eq_zero_of_isMinOn {g : E → ℝ} {x : E} (hd : DifferentiableAt ℝ g x)
    (h : IsMinOn g Set.univ x) : gradient g x = 0 := by
  have hloc : IsLocalMin g x := h.isLocalMin Filter.univ_mem
  have h0 : fderiv ℝ g x = 0 := hloc.hasFDerivAt_eq_zero hd.hasFDerivAt
  unfold gradient
  rw [h0, map_zero]

/-- TO PROVE -/
lemma svrg_sc_bound {F : E → ℝ} {α : ℝ} (hsc : StrongConvexOn Set.univ α F) (xs : E)
    (hmin : IsMinOn F Set.univ xs) (z : E) :
    (99 / 100) * (α / 2) * ‖z - xs‖ ^ 2 ≤ F z - F xs := by
  have _hcs : CompleteSpace E := inferInstance
  have h1 := hsc.2 (Set.mem_univ z) (Set.mem_univ xs) (show (0:ℝ) ≤ 1 / 100 by norm_num)
    (show (0:ℝ) ≤ 99 / 100 by norm_num) (show (1 / 100 : ℝ) + 99 / 100 = 1 by norm_num)
  have h2 : F xs ≤ F ((1 / 100 : ℝ) • z + (99 / 100 : ℝ) • xs) :=
    isMinOn_iff.mp hmin _ (Set.mem_univ _)
  simp only [smul_eq_mul] at h1
  nlinarith


omit [CompleteSpace E] in
/-- Deterministic one-step bound. -/
lemma svrg_one_step {m : ℕ} (hm : 0 < m) (f : Fin m → E → ℝ) (g : Fin m → E → E) (G : E → E)
    (β η : ℝ) (_hβ : 0 < β) (hη : 0 ≤ η) (xs : E)
    (hG : ∀ z, G z = (1 / (m : ℝ)) • ∑ i, g i z)
    (hG0 : G xs = 0)
    (hconv : ∀ i z w, f i z + inner ℝ (g i z) (w - z) ≤ f i w)
    (hcoco : ∀ i z w, ‖g i w - g i z‖ ^ 2 ≤ 2 * β * (f i w - f i z - inner ℝ (g i z) (w - z)))
    (x yt : E) :
    (1 / (m : ℝ)) * ∑ i, ‖x - η • (g i x - g i yt + G yt) - xs‖ ^ 2 ≤
      ‖x - xs‖ ^ 2
        - 2 * η * (1 - 2 * β * η) * ((1 / (m : ℝ)) * ∑ i, f i x - (1 / (m : ℝ)) * ∑ i, f i xs)
        + 4 * β * η ^ 2 * ((1 / (m : ℝ)) * ∑ i, f i yt - (1 / (m : ℝ)) * ∑ i, f i xs) := by
  have hM : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hsumG : ∀ z, ∑ i, g i z = (m : ℝ) • G z := by
    intro z
    rw [hG z, smul_smul, mul_one_div_cancel hM.ne', one_smul]
  have hsum0 : ∑ i, g i xs = 0 := by rw [hsumG, hG0, smul_zero]
  -- Step 1
  have h1 : ∀ i, ‖x - η • (g i x - g i yt + G yt) - xs‖ ^ 2 = ‖x - xs‖ ^ 2
      - 2 * η * inner ℝ (x - xs) (g i x - g i yt + G yt) + η ^ 2 * ‖g i x - g i yt + G yt‖ ^ 2 := by
    intro i
    have e : x - η • (g i x - g i yt + G yt) - xs = (x - xs) - η • (g i x - g i yt + G yt) := by
      abel
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  -- Step 2
  have h2 : ∑ i, inner ℝ (x - xs) (g i x - g i yt + G yt) = inner ℝ (x - xs) (∑ i, g i x) := by
    rw [← inner_sum]
    congr 1
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, hsumG yt, ← Nat.cast_smul_eq_nsmul ℝ, sub_add_cancel]
  -- Step 3
  have h3 : ∑ i, f i x - ∑ i, f i xs ≤ inner ℝ (x - xs) (∑ i, g i x) := by
    have hi : ∀ i, f i x - f i xs ≤ inner ℝ (x - xs) (g i x) := by
      intro i
      have h := hconv i x xs
      have e : inner ℝ (g i x) (xs - x) = - inner ℝ (x - xs) (g i x) := by
        rw [real_inner_comm, ← neg_sub x xs, inner_neg_left]
      linarith
    rw [← Finset.sum_sub_distrib, inner_sum]
    exact Finset.sum_le_sum (fun i _ => hi i)
  -- Step 4
  have h4 : ∀ i, ‖g i x - g i yt + G yt‖ ^ 2 ≤
      2 * ‖g i x - g i xs‖ ^ 2 + 2 * ‖g i yt - g i xs - G yt‖ ^ 2 := by
    intro i
    have e : g i x - g i yt + G yt = (g i x - g i xs) - (g i yt - g i xs - G yt) := by abel
    rw [e]
    have h := norm_sub_sq_real (g i x - g i xs) (g i yt - g i xs - G yt)
    have h' := norm_add_sq_real (g i x - g i xs) (g i yt - g i xs - G yt)
    nlinarith [sq_nonneg ‖g i x - g i xs + (g i yt - g i xs - G yt)‖]
  -- Step 5
  have h5 : ∑ i, ‖g i yt - g i xs - G yt‖ ^ 2 ≤ ∑ i, ‖g i yt - g i xs‖ ^ 2 := by
    have e1 : ∑ i, ‖g i yt - g i xs - G yt‖ ^ 2 = ∑ i, (‖g i yt - g i xs‖ ^ 2
        - 2 * inner ℝ (g i yt - g i xs) (G yt) + ‖G yt‖ ^ 2) :=
      Finset.sum_congr rfl (fun i _ => norm_sub_sq_real _ _)
    have e2 : ∑ i, inner ℝ (g i yt - g i xs) (G yt) = (m : ℝ) * ‖G yt‖ ^ 2 := by
      rw [← sum_inner, Finset.sum_sub_distrib, hsumG yt, hsum0, sub_zero, real_inner_smul_left,
        real_inner_self_eq_norm_sq]
    rw [e1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e2, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    nlinarith [mul_nonneg hM.le (sq_nonneg ‖G yt‖)]
  -- Step 6
  have h6 : ∀ w, ∑ i, ‖g i w - g i xs‖ ^ 2 ≤ 2 * β * (∑ i, f i w - ∑ i, f i xs) := by
    intro w
    calc ∑ i, ‖g i w - g i xs‖ ^ 2
        ≤ ∑ i, 2 * β * (f i w - f i xs - inner ℝ (g i xs) (w - xs)) :=
          Finset.sum_le_sum (fun i _ => hcoco i xs w)
      _ = 2 * β * (∑ i, f i w - ∑ i, f i xs - inner ℝ (∑ i, g i xs) (w - xs)) := by
        rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_inner]
      _ = 2 * β * (∑ i, f i w - ∑ i, f i xs) := by rw [hsum0, inner_zero_left, sub_zero]
  -- Combine
  have hsum1 : ∑ i, ‖x - η • (g i x - g i yt + G yt) - xs‖ ^ 2 = (m : ℝ) * ‖x - xs‖ ^ 2
      - 2 * η * inner ℝ (x - xs) (∑ i, g i x) + η ^ 2 * ∑ i, ‖g i x - g i yt + G yt‖ ^ 2 := by
    have e : ∑ i, ‖x - η • (g i x - g i yt + G yt) - xs‖ ^ 2 = ∑ i, (‖x - xs‖ ^ 2
        - 2 * η * inner ℝ (x - xs) (g i x - g i yt + G yt)
        + η ^ 2 * ‖g i x - g i yt + G yt‖ ^ 2) := Finset.sum_congr rfl (fun i _ => h1 i)
    rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hv : ∑ i, ‖g i x - g i yt + G yt‖ ^ 2 ≤
      2 * ∑ i, ‖g i x - g i xs‖ ^ 2 + 2 * ∑ i, ‖g i yt - g i xs - G yt‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => h4 i)
  have hvv : ∑ i, ‖g i x - g i yt + G yt‖ ^ 2 ≤
      4 * β * (∑ i, f i x - ∑ i, f i xs) + 4 * β * (∑ i, f i yt - ∑ i, f i xs) := by
    have := h6 x
    have := h6 yt
    linarith
  have hmain : ∑ i, ‖x - η • (g i x - g i yt + G yt) - xs‖ ^ 2 ≤ (m : ℝ) * ‖x - xs‖ ^ 2
      - 2 * η * (∑ i, f i x - ∑ i, f i xs)
      + η ^ 2 * (4 * β * (∑ i, f i x - ∑ i, f i xs) + 4 * β * (∑ i, f i yt - ∑ i, f i xs)) := by
    rw [hsum1]
    nlinarith [mul_le_mul_of_nonneg_left hvv (sq_nonneg η), mul_le_mul_of_nonneg_left h3 hη]
  have hMinv : (1 / (m : ℝ)) * (m : ℝ) = 1 := one_div_mul_cancel hM.ne'
  have key := mul_le_mul_of_nonneg_left hmain (le_of_lt (one_div_pos.mpr hM))
  refine le_trans key (le_of_eq ?_)
  linear_combination ‖x - xs‖ ^ 2 * hMinv

end SVRGAux

lemma svrg_integral_uniform {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ]
    {m : ℕ} {B : Type*} [MeasurableSpace B] (I : Ω → Fin m) (X : Ω → B)
    (hI : Measurable I) (hX : Measurable X) (hind : ProbabilityTheory.IndepFun I X μ)
    (hunif : ∀ i, μ (I ⁻¹' {i}) = (m : ENNReal)⁻¹)
    (g : Fin m → B → ℝ) (hg : ∀ i, Measurable (g i))
    (hint : ∀ i, Integrable (fun ω => g i (X ω)) μ) :
    ∫ ω, g (I ω) (X ω) ∂μ = ∫ ω, (1 / (m : ℝ)) * ∑ i, g i (X ω) ∂μ := by
  have hpt : ∀ ω, g (I ω) (X ω) = ∑ i, (if I ω = i then (1:ℝ) else 0) * g i (X ω) := by
    intro ω
    simp [ite_mul, Finset.sum_ite_eq]
  have hfmeas : ∀ i : Fin m, Measurable (fun j : Fin m => if j = i then (1:ℝ) else 0) :=
    fun i => measurable_of_finite _
  have hterm_int : ∀ i, Integrable (fun ω => (if I ω = i then (1:ℝ) else 0) * g i (X ω)) μ := by
    intro i
    refine Integrable.bdd_mul (c := 1) (hint i) ?_ ?_
    · exact ((hfmeas i).comp hI).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      split_ifs <;> simp
  have hindic : ∀ i, ∫ ω, (if I ω = i then (1:ℝ) else 0) ∂μ = 1 / (m : ℝ) := by
    intro i
    have : (fun ω => if I ω = i then (1:ℝ) else 0) = (I ⁻¹' {i}).indicator 1 := by
      ext ω; simp [Set.indicator]
    rw [this, integral_indicator_one (hI (measurableSet_singleton i)), measureReal_def, hunif i]
    simp
  have hterm : ∀ i, ∫ ω, (if I ω = i then (1:ℝ) else 0) * g i (X ω) ∂μ
      = 1 / (m:ℝ) * ∫ ω, g i (X ω) ∂μ := by
    intro i
    have := hind.integral_fun_comp_mul_comp (f := fun j : Fin m => if j = i then (1:ℝ) else 0)
      (g := g i) hI.aemeasurable hX.aemeasurable (hfmeas i).aestronglyMeasurable
      (hg i).aestronglyMeasurable
    rw [this, hindic i]
  calc ∫ ω, g (I ω) (X ω) ∂μ
        = ∫ ω, ∑ i, (if I ω = i then (1:ℝ) else 0) * g i (X ω) ∂μ := by
          congr 1; ext ω; exact hpt ω
    _ = ∑ i, ∫ ω, (if I ω = i then (1:ℝ) else 0) * g i (X ω) ∂μ :=
          integral_finset_sum _ (fun i _ => hterm_int i)
    _ = ∑ i, 1 / (m:ℝ) * ∫ ω, g i (X ω) ∂μ := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = 1 / (m:ℝ) * ∑ i, ∫ ω, g i (X ω) ∂μ := by rw [Finset.mul_sum]
    _ = 1 / (m:ℝ) * ∫ ω, ∑ i, g i (X ω) ∂μ := by
          rw [integral_finset_sum _ (fun i _ => hint i)]
    _ = ∫ ω, (1 / (m : ℝ)) * ∑ i, g i (X ω) ∂μ := by rw [integral_const_mul]

theorem svrg_bound {k m n s : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (y : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → ℕ → Ω → Fin m)
  (α β : ℝ)
  (y0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hy0 : ∀ ω, y 0 ω = y0)
  (hβ_pos : β > 0) (hα_pos : α > 0) (hm_pos : m > 0)
  (hk : k > 0 ∧ k = Nat.ceil (20 * (β / α)))
  (h_mirror_seq : IsSVRGSequence μ k f x y I (1 / (10 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hf_strongly_convex :
    StrongConvexOn Set.univ α (fun z => (1 / (m : ℝ)) * ∑ i, f i z))
  (hx_star : IsMinOn (fun z => (1 / (m : ℝ)) • ∑ i, f i z) Set.univ x_star)
  (hf_sum_y_int : ∀ s, Integrable (fun ω => (1 / (m : ℝ)) • ∑ i, f i (y s ω)) μ)
  (hf_sum_x_int : ∀ s t, Integrable (fun ω => (1 / (m : ℝ)) • ∑ i, f i (x s t ω)) μ) :
  let f_sum := fun z => (1 / (m : ℝ)) • ∑ i, f i z
  ∫ ω, f_sum (y s ω) ∂μ - f_sum x_star ≤
    ((9 / 10) ^ s) * (f_sum y0 - f_sum x_star) := by
  intro f_sum
  obtain ⟨hxm, hym, hIm, hiter, _hiid, hind, hunif⟩ := h_mirror_seq
  obtain ⟨hx0, hstep, hyavg⟩ := hiter
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk.1
  have hk20 : 20 * (β / α) ≤ (k : ℝ) := by rw [hk.2]; exact Nat.le_ceil _
  have hFdiff : Differentiable ℝ f_sum := by
    simp only [f_sum]
    fun_prop
  have hgF : ∀ z, gradient f_sum z = (1 / (m : ℝ)) • ∑ i, gradient (f i) z :=
    svrg_gradient_avg f hf_differentiable
  have hgF0 : gradient f_sum x_star = 0 :=
    svrg_gradient_eq_zero_of_isMinOn (hFdiff x_star) hx_star
  have hgcont : ∀ i, Continuous (gradient (f i)) := fun i => (hf_smooth i).continuous
  have hgFcont : Continuous (gradient f_sum) := by
    have : gradient f_sum = fun z => (1 / (m : ℝ)) • ∑ i, gradient (f i) z := funext hgF
    rw [this]
    fun_prop
  have hmin : ∀ z, f_sum x_star ≤ f_sum z := fun z => hx_star (Set.mem_univ z)
  have hsc : ∀ z, ‖z - x_star‖ ^ 2 ≤ (200 / (99 * α)) * (f_sum z - f_sum x_star) := by
    intro z
    have h1 := svrg_sc_bound (F := f_sum) hf_strongly_convex x_star hx_star z
    calc ‖z - x_star‖ ^ 2 = (200 / (99 * α)) * ((99 / 100) * (α / 2) * ‖z - x_star‖ ^ 2) := by
          field_simp; ring
      _ ≤ (200 / (99 * α)) * (f_sum z - f_sum x_star) := by gcongr
  have hconv : ∀ i z w, f i z + inner ℝ (gradient (f i) z) (w - z) ≤ f i w :=
    fun i z w => svrg_convex_first_order (hf_differentiable i) (hf_convex i) z w
  have hcoco : ∀ i z w, ‖gradient (f i) w - gradient (f i) z‖ ^ 2 ≤
      2 * β * (f i w - f i z - inner ℝ (gradient (f i) z) (w - z)) :=
    fun i z w => svrg_cocoercive hβ_pos (hf_differentiable i) (hf_convex i) (hf_smooth i) z w
  -- integrability facts
  have hFx_int : ∀ s t, Integrable (fun ω => f_sum (x s t ω)) μ := hf_sum_x_int
  have hFy_int : ∀ s, Integrable (fun ω => f_sum (y s ω)) μ := hf_sum_y_int
  have hsqx_int : ∀ s t, Integrable (fun ω => ‖x s t ω - x_star‖ ^ 2) μ := by
    intro s t
    refine Integrable.mono'
      (((hf_sum_x_int s t).sub (integrable_const (f_sum x_star))).const_mul (200 / (99 * α)))
      (((hxm s t).sub_const x_star).norm.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsc _
  have hsqy_int : ∀ s, Integrable (fun ω => ‖y s ω - x_star‖ ^ 2) μ := by
    intro s
    refine Integrable.mono'
      (((hf_sum_y_int s).sub (integrable_const (f_sum x_star))).const_mul (200 / (99 * α)))
      (((hym s).sub_const x_star).norm.pow_const 2).aestronglyMeasurable ?_
    refine Filter.Eventually.of_forall (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hsc _
  -- one-step bound in expectation
  have hstepE : ∀ s t, t < k →
      ∫ ω, ‖x s (t+1) ω - x_star‖ ^ 2 ∂μ ≤
        ∫ ω, ‖x s t ω - x_star‖ ^ 2 ∂μ
          - 2 * (1 / (10 * β)) * (1 - 2 * β * (1 / (10 * β))) *
              (∫ ω, f_sum (x s t ω) ∂μ - f_sum x_star)
          + 4 * β * (1 / (10 * β)) ^ 2 * (∫ ω, f_sum (y s ω) ∂μ - f_sum x_star) := by
    intro s t ht
    set η : ℝ := 1 / (10 * β) with hη
    have hηpos : 0 < η := by positivity
    set Φ : Fin m → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) → ℝ :=
      fun i p => ‖p.1 - η • (gradient (f i) p.1 - gradient (f i) p.2 + gradient f_sum p.2)
        - x_star‖ ^ 2 with hΦ
    set X : Ω → (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) :=
      fun ω => (x s t ω, y s ω) with hX
    have hXm : Measurable X := (hxm s t).prodMk (hym s)
    have hΦm : ∀ i, Measurable (Φ i) := by
      intro i
      apply Continuous.measurable
      have h1 := hgcont i
      simp only [hΦ]
      fun_prop
    set R : Ω → ℝ := fun ω => ‖x s t ω - x_star‖ ^ 2
          - 2 * η * (1 - 2 * β * η) * (f_sum (x s t ω) - f_sum x_star)
          + 4 * β * η ^ 2 * (f_sum (y s ω) - f_sum x_star) with hR
    have hR_int : Integrable R μ := by
      refine ((hsqx_int s t).sub (((hf_sum_x_int s t).sub
        (integrable_const (f_sum x_star))).const_mul _)).add
        (((hf_sum_y_int s).sub (integrable_const (f_sum x_star))).const_mul _)
    have hpt : ∀ ω, (1 / (m : ℝ)) * ∑ i, Φ i (X ω) ≤ R ω := by
      intro ω
      exact svrg_one_step hm_pos f (fun i => gradient (f i)) (gradient f_sum) β η hβ_pos
        hηpos.le x_star hgF hgF0 hconv hcoco (x s t ω) (y s ω)
    have hΦ0 : ∀ i p, 0 ≤ Φ i p := fun i p => by positivity
    have hΦ_int : ∀ i, Integrable (fun ω => Φ i (X ω)) μ := by
      intro i
      refine Integrable.mono' (hR_int.const_mul (m : ℝ)) ((hΦm i).comp hXm).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall (fun ω => ?_)
      have h1 : Φ i (X ω) ≤ ∑ j, Φ j (X ω) :=
        Finset.single_le_sum (fun j _ => hΦ0 j (X ω)) (Finset.mem_univ i)
      have h2 := hpt ω
      rw [Real.norm_eq_abs, abs_of_nonneg (hΦ0 i _)]
      have h3 : ∑ j, Φ j (X ω) ≤ m * R ω := by
        have := mul_le_mul_of_nonneg_left h2 hmR.le
        rwa [← mul_assoc, mul_one_div_cancel hmR.ne', one_mul] at this
      linarith
    have hEq : (fun ω => ‖x s (t+1) ω - x_star‖ ^ 2) = fun ω => Φ (I s t ω) (X ω) := by
      funext ω
      rw [hstep s t ω ht]
    have hsum_int : Integrable (fun ω => (1 / (m : ℝ)) * ∑ i, Φ i (X ω)) μ :=
      (integrable_finset_sum _ (fun i _ => hΦ_int i)).const_mul _
    calc ∫ ω, ‖x s (t+1) ω - x_star‖ ^ 2 ∂μ = ∫ ω, Φ (I s t ω) (X ω) ∂μ := by rw [hEq]
      _ = ∫ ω, (1 / (m : ℝ)) * ∑ i, Φ i (X ω) ∂μ :=
          svrg_integral_uniform (I s t) X (hIm s t) hXm (hind s t) (hunif s t) Φ hΦm hΦ_int
      _ ≤ ∫ ω, R ω ∂μ := integral_mono hsum_int hR_int hpt
      _ = _ := by
          simp only [hR]
          rw [integral_add, integral_sub, integral_const_mul, integral_const_mul, integral_sub,
            integral_sub]
          · simp
          all_goals first
            | exact hsqx_int s t
            | exact hf_sum_x_int s t
            | exact hf_sum_y_int s
            | exact integrable_const _
            | exact ((hf_sum_x_int s t).sub (integrable_const _)).const_mul _
            | exact ((hf_sum_y_int s).sub (integrable_const _)).const_mul _
            | exact (hsqx_int s t).sub (((hf_sum_x_int s t).sub (integrable_const _)).const_mul _)
  -- per-epoch contraction
  have hepoch : ∀ s, ∫ ω, f_sum (y (s+1) ω) ∂μ - f_sum x_star ≤
      (9 / 10) * (∫ ω, f_sum (y s ω) ∂μ - f_sum x_star) := by
    intro s
    set D := ∫ ω, f_sum (y s ω) ∂μ - f_sum x_star with hD
    set a : ℕ → ℝ := fun t => ∫ ω, ‖x s t ω - x_star‖ ^ 2 ∂μ with ha
    set b : ℕ → ℝ := fun t => ∫ ω, f_sum (x s t ω) ∂μ - f_sum x_star with hb
    have hD0 : 0 ≤ D := by
      have h := integral_mono (integrable_const (f_sum x_star)) (hFy_int s)
          (fun ω => hmin (y s ω))
      rw [integral_const, probReal_univ, one_smul] at h
      linarith
    have hc1 : 2 * (1 / (10 * β)) * (1 - 2 * β * (1 / (10 * β))) = 4 / (25 * β) := by
      field_simp; ring
    have hc2 : 4 * β * (1 / (10 * β)) ^ 2 = 1 / (25 * β) := by
      field_simp; ring
    have hrec : ∀ t, t < k → a (t+1) ≤ a t - 4 / (25 * β) * b t + 1 / (25 * β) * D := by
      intro t ht
      have := hstepE s t ht
      rw [hc1, hc2] at this
      exact this
    have hsum : ∀ j, j ≤ k → a j + 4 / (25 * β) * ∑ t ∈ Finset.range j, b t ≤
        a 0 + j * (1 / (25 * β)) * D := by
      intro j
      induction j with
      | zero => intro _; simp
      | succ j ih =>
        intro hj
        have h1 := ih (by omega)
        have h2 := hrec j (by omega)
        rw [Finset.sum_range_succ]
        push_cast
        linarith
    have hak : 0 ≤ a k := integral_nonneg (fun ω => by positivity)
    have ha0 : a 0 ≤ (200 / (99 * α)) * D := by
      simp only [ha]
      have : (fun ω => ‖x s 0 ω - x_star‖ ^ 2) = fun ω => ‖y s ω - x_star‖ ^ 2 := by
        funext ω; rw [hx0 s ω]
      rw [this]
      calc ∫ ω, ‖y s ω - x_star‖ ^ 2 ∂μ
          ≤ ∫ ω, (200 / (99 * α)) * (f_sum (y s ω) - f_sum x_star) ∂μ :=
            integral_mono (hsqy_int s) (((hFy_int s).sub (integrable_const _)).const_mul _)
              (fun ω => hsc _)
        _ = (200 / (99 * α)) * D := by
            rw [integral_const_mul, integral_sub (hFy_int s) (integrable_const _), integral_const,
              probReal_univ, one_smul]
    have hjensen : ∫ ω, f_sum (y (s+1) ω) ∂μ - f_sum x_star ≤
        (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, b t := by
      have hconvF : ConvexOn ℝ Set.univ f_sum := hf_strongly_convex.convexOn (fun r => by show (0:ℝ) ≤ α / 2 * r ^ 2; positivity)
      have hpt : ∀ ω, f_sum (y (s+1) ω) ≤
          (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, f_sum (x s t ω) := by
        intro ω
        rw [hyavg s ω, Finset.smul_sum, Finset.mul_sum]
        have := hconvF.map_sum_le (t := Finset.range k) (w := fun _ => 1 / (k : ℝ))
          (p := fun t => x s t ω)
          (fun _ _ => by positivity) (by simp; field_simp) (fun _ _ => Set.mem_univ _)
        simpa [smul_eq_mul] using this
      have hint2 : Integrable
          (fun ω => (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, f_sum (x s t ω)) μ :=
        (integrable_finset_sum _ (fun t _ => hFx_int s t)).const_mul _
      have h1 := integral_mono (hFy_int (s+1)) hint2 hpt
      rw [integral_const_mul, integral_finset_sum _ (fun t _ => hFx_int s t)] at h1
      simp only [hb]
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_sub]
      have : (1 / (k:ℝ)) * (k * f_sum x_star) = f_sum x_star := by field_simp
      linarith
    have hS := hsum k le_rfl
    set S := ∑ t ∈ Finset.range k, b t with hS_def
    have h1 : 4 / (25 * β) * S ≤ (200 / (99 * α)) * D + k * (1 / (25 * β)) * D := by linarith
    have h2 : S ≤ (1250 / 99) * ((β / α) * D) + k / 4 * D := by
      have := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 25 * β / 4 by positivity)
      calc S = 25 * β / 4 * (4 / (25 * β) * S) := by field_simp
        _ ≤ 25 * β / 4 * ((200 / (99 * α)) * D + k * (1 / (25 * β)) * D) := this
        _ = (1250 / 99) * ((β / α) * D) + k / 4 * D := by field_simp; ring
    have h3 : (β / α) * D ≤ (k / 20) * D := mul_le_mul_of_nonneg_right (by linarith) hD0
    have h4 : S ≤ (349 / 396) * (k * D) := by linarith
    calc ∫ ω, f_sum (y (s+1) ω) ∂μ - f_sum x_star ≤ (1 / (k : ℝ)) * S := hjensen
      _ ≤ (1 / (k : ℝ)) * ((349 / 396) * (k * D)) := by gcongr
      _ = (349 / 396) * D := by field_simp
      _ ≤ (9 / 10) * D := by linarith
  have hfinal : ∀ s, ∫ ω, f_sum (y s ω) ∂μ - f_sum x_star ≤
      (9 / 10) ^ s * (f_sum y0 - f_sum x_star) := by
    intro s
    induction s with
    | zero =>
      simp only [pow_zero, one_mul]
      have : (fun ω => f_sum (y 0 ω)) = fun _ => f_sum y0 := by funext ω; rw [hy0 ω]
      rw [this, integral_const]
      simp
    | succ s ih =>
      calc _ ≤ (9 / 10) * (∫ ω, f_sum (y s ω) ∂μ - f_sum x_star) := hepoch s
        _ ≤ (9 / 10) * ((9 / 10) ^ s * (f_sum y0 - f_sum x_star)) := by gcongr
        _ = (9 / 10) ^ (s + 1) * (f_sum y0 - f_sum x_star) := by ring
  exact hfinal s

end svrg_bound
