import ConvexStarLib.Defs

/-!
# `randomized_coordinate_descent_gamma_stronglyconvex_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/randomized_coordinate_descent_gamma_stronglyconvex_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace randomized_coordinate_descent_gamma_stronglyconvex_bound`, so the main result is `randomized_coordinate_descent_gamma_stronglyconvex_bound.randomized_coordinate_descent_gamma_stronglyconvex_bound`.
-/

namespace randomized_coordinate_descent_gamma_stronglyconvex_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open MeasureTheory ProbabilityTheory


lemma rcd_coord_descent_aux {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (e : EuclideanSpace ℝ (Fin n))
    (hsmooth : ∀ (y : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      ‖(fderiv ℝ f (y + u • e)) e - (fderiv ℝ f y) e‖ ≤ L * |u|)
    (y : EuclideanSpace ℝ (Fin n)) (u : ℝ) :
    f (y + u • e) ≤ f y + u * (fderiv ℝ f y) e + L / 2 * u ^ 2 := by
  set g := (fderiv ℝ f y) e with hg
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f (y + (t * u) • e))
      ((fderiv ℝ f (y + (t * u) • e)) (u • e)) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => y + (t * u) • e) (u • e) t := by
      have := ((hasDerivAt_id t).mul_const u).smul_const e
      simpa using this.const_add y
    exact (hf _).hasFDerivAt.comp_hasDerivAt t h1
  have hB : ∀ t : ℝ, HasDerivAt (fun t : ℝ => f y + t * u * g + L / 2 * u ^ 2 * t ^ 2)
      (u * g + L * u ^ 2 * t) t := by
    intro t
    have := ((((hasDerivAt_id t).mul_const u).mul_const g).const_add (f y)).add
      (((hasDerivAt_id t).pow 2).const_mul (L / 2 * u ^ 2))
    convert this using 1
    simp; ring
  have key := image_le_of_deriv_right_le_deriv_boundary
    (f := fun t : ℝ => f (y + (t * u) • e)) (f' := fun t => (fderiv ℝ f (y + (t * u) • e)) (u • e))
    (a := 0) (b := 1)
    (B := fun t : ℝ => f y + t * u * g + L / 2 * u ^ 2 * t ^ 2)
    (B' := fun t => u * g + L * u ^ 2 * t)
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt)
    (fun t _ => (hderiv t).hasDerivWithinAt)
    (by simp)
    (fun t _ => (hB t).continuousAt.continuousWithinAt)
    (fun t _ => (hB t).hasDerivWithinAt)
    (by
      intro t ht
      simp only
      rw [map_smul, smul_eq_mul]
      have h := hsmooth y (t * u)
      rw [Real.norm_eq_abs] at h
      have ht0 : 0 ≤ t := ht.1
      have h2 : u * ((fderiv ℝ f (y + (t * u) • e)) e - g) ≤
          |u| * |(fderiv ℝ f (y + (t * u) • e)) e - g| := by
        rw [← abs_mul]; exact le_abs_self _
      have h3 : |u| * |(fderiv ℝ f (y + (t * u) • e)) e - g| ≤ |u| * (L * |t * u|) :=
        mul_le_mul_of_nonneg_left h (abs_nonneg u)
      have h4 : |u| * (L * |t * u|) = L * u ^ 2 * t := by
        rw [abs_mul, abs_of_nonneg ht0]
        have : |u| * |u| = u * u := abs_mul_abs_self u
        linear_combination (L * t) * this
      nlinarith)
  have := key (show (1:ℝ) ∈ Set.Icc 0 1 by simp)
  simpa using this

lemma rcd_step_eq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (y : EuclideanSpace ℝ (Fin n))
    (i : Fin n) (η : ℝ) :
    randomizedCoordDescentStep f y i η =
      y + (-(η * (fderiv ℝ f y) (EuclideanSpace.single i 1))) • EuclideanSpace.single i (1:ℝ) := by
  unfold randomizedCoordDescentStep
  ext j
  simp [EuclideanSpace.single_apply]
  split_ifs <;> ring

lemma rcd_step_descent {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (L : ℝ) (hL : 0 < L) (i : Fin n)
    (hsmooth : ∀ (y : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      ‖(fderiv ℝ f (y + u • EuclideanSpace.single i (1:ℝ))) (EuclideanSpace.single i (1:ℝ)) -
        (fderiv ℝ f y) (EuclideanSpace.single i (1:ℝ))‖ ≤ L * |u|)
    (y : EuclideanSpace ℝ (Fin n)) :
    f (randomizedCoordDescentStep f y i L⁻¹) ≤
      f y - ((fderiv ℝ f y) (EuclideanSpace.single i 1)) ^ 2 / (2 * L) := by
  rw [rcd_step_eq]
  have := rcd_coord_descent_aux f hf L _ hsmooth y
    (-(L⁻¹ * (fderiv ℝ f y) (EuclideanSpace.single i 1)))
  refine this.trans (le_of_eq ?_)
  field_simp
  ring

lemma rcd_fderiv_eq_inner_of_subgradient {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : Differentiable ℝ f)
    (y w : EuclideanSpace ℝ (Fin n)) (hw : InDomIsSubgradientAt Set.univ f y w)
    (v : EuclideanSpace ℝ (Fin n)) :
    (fderiv ℝ f y) v = inner ℝ v w := by
  have hmin : IsLocalMin (fun t : ℝ => f (y + t • v) - t * inner ℝ v w) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have := hw (y + t • v) (Set.mem_univ _)
    simp only [add_sub_cancel_left, real_inner_smul_left] at this
    simp only [zero_smul, add_zero, zero_mul, sub_zero]
    linarith
  have hd : HasDerivAt (fun t : ℝ => f (y + t • v) - t * inner ℝ v w)
      ((fderiv ℝ f y) v - inner ℝ v w) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    have h2 := (hf (y + (0:ℝ) • v)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
    simp only [zero_smul, add_zero] at h2
    have h3 := (hasDerivAt_id (0:ℝ)).mul_const (inner ℝ v w)
    simpa using h2.sub h3
  have := hmin.hasDerivAt_eq_zero hd
  linarith

lemma rcd_sc_bound {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (hf : Differentiable ℝ f)
    (b : Fin n → ℝ) (hb : ∀ i, 0 < b i) (α : ℝ) (hα : 0 < α)
    (hconv : IsAlphaStronglyConvex Set.univ f (fun v => Real.sqrt (∑ i, b i * (v i) ^ 2)) α)
    (y z : EuclideanSpace ℝ (Fin n)) :
    f y - f z ≤ (1 / (2 * α)) * ∑ i, ((fderiv ℝ f y) (EuclideanSpace.single i 1)) ^ 2 / b i := by
  obtain ⟨w, hw⟩ := hconv.1 y (Set.mem_univ _)
  have h := hconv.2 y (Set.mem_univ _) z (Set.mem_univ _) w hw
  have hg : ∀ i, (fderiv ℝ f y) (EuclideanSpace.single i 1) = w i := by
    intro i
    rw [rcd_fderiv_eq_inner_of_subgradient f hf y w hw, EuclideanSpace.inner_single_left]
    simp
  simp_rw [hg]
  rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_nonneg (hb i).le (sq_nonneg _)))] at h
  rw [PiLp.inner_apply] at h
  simp only [PiLp.sub_apply, RCLike.inner_apply, conj_trivial] at h
  have key : ∀ i, (y i - z i) * w i - α / 2 * (b i * (y i - z i) ^ 2) ≤
      (1 / (2 * α)) * (w i ^ 2 / b i) := by
    intro i
    have hbi := hb i
    have : (1 / (2 * α)) * (w i ^ 2 / b i) - ((y i - z i) * w i - α / 2 * (b i * (y i - z i) ^ 2))
        = (α * b i / 2) * ((y i - z i) - w i / (α * b i)) ^ 2 := by
      field_simp; ring
    nlinarith [this, mul_nonneg (mul_nonneg hα.le hbi.le) (sq_nonneg ((y i - z i) - w i / (α * b i)))]
  calc f y - f z ≤ ∑ i, (y i - z i) * w i - α / 2 * ∑ i, b i * (y i - z i) ^ 2 := h
    _ = ∑ i, ((y i - z i) * w i - α / 2 * (b i * (y i - z i) ^ 2)) := by
        rw [Finset.mul_sum, Finset.sum_sub_distrib]
    _ ≤ ∑ i, (1 / (2 * α)) * (w i ^ 2 / b i) := Finset.sum_le_sum (fun i _ => key i)
    _ = _ := by rw [Finset.mul_sum]

set_option linter.unusedVariables false in
theorem randomized_coordinate_descent_gamma_stronglyconvex_bound {n t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ α : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hβ_pos : ∀ i, β i > 0)
  (hα_pos : α > 0)
  (hγ_pos : γ ≥ 0)
  (ht_pos : t > 0)
  (h_rcd_gamma_seq : IsRandomizedCoordDescentGammaSequence μ f x I β γ)
  (hf_diff : Differentiable ℝ f)
  (hf_convex : IsAlphaStronglyConvex Set.univ f
    (fun v => Real.sqrt (∑ i, (Real.rpow (β i) (1 - γ)) * (v i) ^ 2)) α)
  (hf_smooth : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
    let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)
    ‖(fderiv ℝ f (x + u • ei)) (EuclideanSpace.single i (1:ℝ)) -
    (fderiv ℝ f x) (EuclideanSpace.single i (1:ℝ))‖ ≤ β i * |u|)
  (hx_star : IsMinOn f Set.univ x_star) :
  let k := (α)⁻¹ * (∑ i, Real.rpow (β i) γ)
  ∫ ω, f (x t ω) ∂μ - f x_star ≤
  (1 - ((n : ℝ) * k)⁻¹) ^ t * (f x0 - f x_star) := by
  intro k
  obtain ⟨hxm, hIm, hstep, hind, hprob⟩ := h_rcd_gamma_seq
  set S := ∑ j, Real.rpow (β j) γ with hS_def
  have hrpow_pos : ∀ i, 0 < Real.rpow (β i) γ := fun i => Real.rpow_pos_of_pos (hβ_pos i) γ
  have hS_pos : 0 < S :=
    Finset.sum_pos (fun i _ => hrpow_pos i) ⟨⟨0, hn_pos⟩, Finset.mem_univ _⟩
  have hk_pos : 0 < k := mul_pos (inv_pos.mpr hα_pos) hS_pos
  set p : Fin n → ℝ := fun i => Real.rpow (β i) γ / S with hp_def
  have hp_nonneg : ∀ i, 0 ≤ p i := fun i => div_nonneg (hrpow_pos i).le hS_pos.le
  have hp_sum : ∑ i, p i = 1 := by
    simp only [hp_def]
    rw [← Finset.sum_div, div_self hS_pos.ne']
  set Ψ : EuclideanSpace ℝ (Fin n) → Fin n → EuclideanSpace ℝ (Fin n) :=
    fun y i => randomizedCoordDescentStep f y i (β i)⁻¹ with hΨ_def
  -- pointwise bound
  have hpw : ∀ y, ∑ i, p i * f (Ψ y i) ≤ f y - k⁻¹ * (f y - f x_star) := by
    intro y
    set g : Fin n → ℝ := fun i => (fderiv ℝ f y) (EuclideanSpace.single i 1) with hg_def
    set b : Fin n → ℝ := fun i => Real.rpow (β i) (1 - γ) with hb_def
    have hb_pos : ∀ i, 0 < b i := fun i => Real.rpow_pos_of_pos (hβ_pos i) _
    have hdesc : ∀ i, f (Ψ y i) ≤ f y - g i ^ 2 / (2 * β i) := by
      intro i
      exact rcd_step_descent f hf_diff (β i) (hβ_pos i) i (fun y u => hf_smooth i y u) y
    have hsc := rcd_sc_bound f hf_diff b hb_pos α hα_pos hf_convex y x_star
    have hbβ : ∀ i, Real.rpow (β i) γ * b i = β i := by
      intro i
      simp only [hb_def]
      rw [Real.rpow_eq_pow, Real.rpow_eq_pow, ← Real.rpow_add (hβ_pos i), add_sub_cancel,
        Real.rpow_one]
    have hterm : ∀ i, p i * (g i ^ 2 / (2 * β i)) = (g i ^ 2 / b i) / (2 * S) := by
      intro i
      simp only [hp_def]
      have hβi := hβ_pos i
      have hbi := hb_pos i
      have hri := hrpow_pos i
      have h := hbβ i
      field_simp
      linear_combination (g i ^ 2) * h
    calc ∑ i, p i * f (Ψ y i) ≤ ∑ i, p i * (f y - g i ^ 2 / (2 * β i)) :=
          Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hdesc i) (hp_nonneg i))
      _ = f y - (∑ i, g i ^ 2 / b i) / (2 * S) := by
          simp_rw [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp_sum, one_mul, hterm,
            Finset.sum_div]
      _ ≤ f y - k⁻¹ * (f y - f x_star) := by
          have hk_inv : k⁻¹ = α / S := by simp only [k]; rw [mul_inv, inv_inv]; ring
          rw [hk_inv]
          have hQ : 2 * α * (f y - f x_star) ≤ ∑ i, g i ^ 2 / b i := by
            have := mul_le_mul_of_nonneg_left hsc (by positivity : (0:ℝ) ≤ 2 * α)
            rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
          rw [_root_.sub_le_sub_iff_left, div_mul_eq_mul_div, div_le_div_iff₀ hS_pos (by positivity)]
          nlinarith [hQ, hS_pos]
  -- measurability of Ψ
  have hΨ_meas_i : ∀ i, Measurable (fun y => Ψ y i) := by
    intro i
    have : (fun y => Ψ y i) = fun y => y + (-((β i)⁻¹ * (fderiv ℝ f y)
        (EuclideanSpace.single i 1))) • EuclideanSpace.single i (1:ℝ) :=
      funext (fun y => rcd_step_eq f y i _)
    rw [this]
    exact measurable_id.add
      (((measurable_fderiv_apply_const ℝ f _).const_mul _).neg.smul_const _)
  have hΨ_meas : Measurable (fun q : EuclideanSpace ℝ (Fin n) × Fin n => Ψ q.1 q.2) :=
    measurable_from_prod_countable_left (fun i => hΨ_meas_i i)
  have hf_meas : Measurable f := hf_diff.continuous.measurable
  have hfΨ_meas : ∀ i, Measurable (fun y => f (Ψ y i)) :=
    fun i => hf_meas.comp (hΨ_meas_i i)
  have hxs : ∀ s ω, x (s+1) ω = Ψ (x s ω) (I s ω) := hstep
  -- finite range
  have hfin : ∀ s, (Set.range (x s)).Finite := by
    intro s
    induction s with
    | zero =>
      refine (Set.finite_singleton x0).subset ?_
      rintro _ ⟨ω, rfl⟩
      simp [hx0]
    | succ s ih =>
      refine ((ih.prod (Set.finite_univ (α := Fin n))).image (fun q => Ψ q.1 q.2)).subset ?_
      rintro _ ⟨ω, rfl⟩
      exact ⟨(x s ω, I s ω), ⟨⟨ω, rfl⟩, Set.mem_univ _⟩, (hxs s ω).symm⟩
  -- integrability
  have hint : ∀ s (h : EuclideanSpace ℝ (Fin n) → ℝ), Measurable h →
      Integrable (fun ω => h (x s ω)) μ := by
    intro s h hh
    obtain ⟨C, hC⟩ := ((hfin s).image (fun y => ‖h y‖)).bddAbove
    refine Integrable.of_bound (hh.comp (hxm s)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => ?_))
    exact hC ⟨x s ω, ⟨ω, rfl⟩, rfl⟩
  -- independence
  set M : ℕ → MeasurableSpace Ω := fun s =>
    ⨆ j ∈ Set.Iio s, MeasurableSpace.comap (I j) inferInstance with hM_def
  have hxM : ∀ s, Measurable[M s] (x s) := by
    intro s
    induction s with
    | zero =>
      have : x 0 = fun _ => x0 := funext hx0
      rw [this]
      exact measurable_const
    | succ s ih =>
      have hle : M s ≤ M (s + 1) := by
        apply biSup_mono
        intro j hj
        simp only [Set.mem_Iio] at hj ⊢
        omega
      have hI_le : MeasurableSpace.comap (I s) inferInstance ≤ M (s + 1) :=
        le_iSup₂ (f := fun j (_ : j ∈ Set.Iio (s+1)) =>
          MeasurableSpace.comap (I j) inferInstance) s (by simp)
      have h1 : Measurable[M (s+1)] (x s) := ih.mono hle le_rfl
      have h2 : Measurable[M (s+1)] (I s) := (comap_measurable (I s)).mono hI_le le_rfl
      have : x (s + 1) = fun ω => Ψ (x s ω) (I s ω) := funext (hxs s)
      rw [this]
      exact hΨ_meas.comp (h1.prodMk h2)
  have hindep : ∀ s, IndepFun (x s) (I s) μ := by
    intro s
    have h1 := (iIndepFun_iff_iIndep _ _ _).mp hind
    have h2 := indep_iSup_of_disjoint (fun j => (hIm j).comap_le) h1
      (S := Set.Iio s) (T := {s}) (by simp)
    rw [iSup_singleton] at h2
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_left h2 (hxM s).comap_le
  -- one-step expectation identity
  have hE : ∀ s, ∫ ω, f (x (s+1) ω) ∂μ = ∑ i, p i * ∫ ω, f (Ψ (x s ω) i) ∂μ := by
    intro s
    have hpt : ∀ ω, f (x (s+1) ω) =
        ∑ i, f (Ψ (x s ω) i) * (if I s ω = i then (1:ℝ) else 0) := by
      intro ω
      rw [Finset.sum_mul_boole, if_pos (Finset.mem_univ _), hxs]
    simp_rw [hpt]
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      have h := (hindep s).integral_comp_mul_comp (f := fun y => f (Ψ y i))
        (g := fun j : Fin n => if j = i then (1:ℝ) else 0)
        (hxm s).aemeasurable (hIm s).aemeasurable (hfΨ_meas i).aestronglyMeasurable
        (measurable_of_finite _).aestronglyMeasurable
      have h' : ∫ ω, f (Ψ (x s ω) i) * (if I s ω = i then (1:ℝ) else 0) ∂μ =
          (∫ ω, f (Ψ (x s ω) i) ∂μ) * ∫ ω, (if I s ω = i then (1:ℝ) else 0) ∂μ := h
      rw [h']
      have hind_int : ∫ ω, (if I s ω = i then (1:ℝ) else 0) ∂μ = p i := by
        have : (fun ω => if I s ω = i then (1:ℝ) else 0) = (I s ⁻¹' {i}).indicator 1 := by
          funext ω
          by_cases h : I s ω = i
          · simp [h]
          · simp [h]
        rw [this, integral_indicator_one ((hIm s) (measurableSet_singleton i)), measureReal_def,
          hprob s i, ENNReal.toReal_ofReal (hp_nonneg i)]
      rw [hind_int, mul_comm]
    · intro i _
      exact (hint s _ (hfΨ_meas i)).mul_bdd
        ((measurable_of_finite (fun j : Fin n => if j = i then (1:ℝ) else 0)).comp
          (hIm s)).aestronglyMeasurable
        (c := 1) (Filter.Eventually.of_forall (fun ω => by split_ifs <;> simp))
  have hstep_bound : ∀ s, ∫ ω, f (x (s+1) ω) ∂μ ≤
      ∫ ω, f (x s ω) ∂μ - k⁻¹ * (∫ ω, f (x s ω) ∂μ - f x_star) := by
    intro s
    rw [hE s]
    have hFi : ∀ i, Integrable (fun ω => p i * f (Ψ (x s ω) i)) μ :=
      fun i => (hint s _ (hfΨ_meas i)).const_mul (p i)
    have hfx : Integrable (fun ω => f (x s ω)) μ := hint s f hf_meas
    have h1 : ∑ i, p i * ∫ ω, f (Ψ (x s ω) i) ∂μ = ∫ ω, ∑ i, p i * f (Ψ (x s ω) i) ∂μ := by
      rw [integral_finset_sum _ (fun i _ => hFi i)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [integral_const_mul]
    rw [h1]
    have h2 : ∫ ω, ∑ i, p i * f (Ψ (x s ω) i) ∂μ ≤
        ∫ ω, (f (x s ω) - k⁻¹ * (f (x s ω) - f x_star)) ∂μ := by
      apply integral_mono
      · exact integrable_finset_sum _ (fun i _ => hFi i)
      · exact hfx.sub ((hfx.sub (integrable_const _)).const_mul _)
      · intro ω; exact hpw (x s ω)
    refine h2.trans (le_of_eq ?_)
    have hg : Integrable (fun ω => k⁻¹ * (f (x s ω) - f x_star)) μ :=
      (hfx.sub (integrable_const _)).const_mul _
    rw [integral_sub hfx hg, integral_const_mul, integral_sub hfx (integrable_const _),
      integral_const]
    simp
  set a : ℕ → ℝ := fun s => ∫ ω, f (x s ω) ∂μ - f x_star with ha_def
  have ha_nonneg : ∀ s, 0 ≤ a s := by
    intro s
    simp only [ha_def]
    have : f x_star ≤ ∫ ω, f (x s ω) ∂μ := by
      have h := integral_mono (integrable_const (f x_star)) (hint s f hf_meas)
        (fun ω => hx_star (Set.mem_univ (x s ω)))
      simpa using h
    linarith
  set c := 1 - ((n : ℝ) * k)⁻¹ with hc_def
  have hrec : ∀ s, a (s + 1) ≤ c * a s := by
    intro s
    have h1 := hstep_bound s
    have h2 : (1 - k⁻¹) * a s ≤ c * a s := by
      apply mul_le_mul_of_nonneg_right _ (ha_nonneg s)
      simp only [hc_def]
      have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn_pos
      have : ((n:ℝ) * k)⁻¹ ≤ k⁻¹ := by
        rw [mul_inv]
        calc (n:ℝ)⁻¹ * k⁻¹ ≤ 1 * k⁻¹ :=
              mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hn1) (inv_nonneg.mpr hk_pos.le)
          _ = k⁻¹ := one_mul _
      linarith
    simp only [ha_def] at h2 ⊢
    nlinarith [h1, h2]
  have ha0 : a 0 = f x0 - f x_star := by
    simp [ha_def, hx0]
  have hfinal : a t ≤ c ^ t * a 0 := by
    rcases le_or_gt 0 c with hc | hc
    · have : ∀ s, a s ≤ c ^ s * a 0 := by
        intro s
        induction s with
        | zero => simp
        | succ s ih =>
          calc a (s+1) ≤ c * a s := hrec s
            _ ≤ c * (c ^ s * a 0) := mul_le_mul_of_nonneg_left ih hc
            _ = c ^ (s+1) * a 0 := by ring
      exact this t
    · have h0 : a 0 = 0 := by
        have := hrec 0
        have := ha_nonneg 1
        have := ha_nonneg 0
        nlinarith
      obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
      have := hrec t'
      have := ha_nonneg t'
      rw [h0, mul_zero]
      nlinarith
  rw [ha0] at hfinal
  exact hfinal

end randomized_coordinate_descent_gamma_stronglyconvex_bound
