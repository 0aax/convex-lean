import ConvexStarLib.Defs

/-!
# `randomized_coordinate_descent_gamma_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/randomized_coordinate_descent_gamma_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace randomized_coordinate_descent_gamma_bound`, so the main result is `randomized_coordinate_descent_gamma_bound.randomized_coordinate_descent_gamma_bound`.
-/

namespace randomized_coordinate_descent_gamma_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open ProbabilityTheory

variable {n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- One coordinate step decreases `f` by at least `g_i ^ 2 / (2 β_i)`. -/
lemma rcdgb_step_le {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (β : Fin n → ℝ)
    (hβ_pos : ∀ i, β i > 0) (hf_diff : Differentiable ℝ f)
    (hf_smooth : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)
      ‖(fderiv ℝ f (x + u • ei)) (EuclideanSpace.single i (1:ℝ)) -
      (fderiv ℝ f x) (EuclideanSpace.single i (1:ℝ))‖ ≤ β i * |u|)
    (y : EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    f (randomizedCoordDescentStep f y i (β i)⁻¹) ≤
      f y - (fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i) := by
  -- coordinate-wise descent lemma
  have hdesc0 : ∀ (u : ℝ),
      f (y + u • EuclideanSpace.single i (1:ℝ)) ≤
        f y + u * (fderiv ℝ f y (EuclideanSpace.single i (1:ℝ))) + β i / 2 * u ^ 2 := by
    intro u
    set e : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ) with he
    set g := fderiv ℝ f y e with hg
    let Φ : ℝ → ℝ := fun r => f (y + r • (u • e)) - f y - r * u * g - β i / 2 * r ^ 2 * u ^ 2
    have hΦd : ∀ r, HasDerivAt Φ
        (fderiv ℝ f (y + r • (u • e)) (u • e) - u * g - β i * r * u ^ 2) r := by
      intro r
      have h1 : HasDerivAt (fun r : ℝ => y + r • (u • e)) (u • e) r := by
        simpa using ((hasDerivAt_id r).smul_const (u • e)).const_add y
      have h2 := (hf_diff (y + r • (u • e))).hasFDerivAt.comp_hasDerivAt r h1
      have h3 : HasDerivAt (fun r : ℝ => r * u * g + β i / 2 * r ^ 2 * u ^ 2)
          (u * g + β i * r * u ^ 2) r := by
        have := (((hasDerivAt_id r).mul_const u).mul_const g).add
          ((((hasDerivAt_id r).pow 2).const_mul (β i / 2)).mul_const (u ^ 2))
        convert this using 1
        simp only [id]
        push_cast
        ring
      have h4 := (h2.sub_const (f y)).sub h3
      convert h4 using 1
      · ext r; simp [Φ]; ring
      · ring
    have hanti : AntitoneOn Φ (Set.Ici 0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0)
      · exact fun r _ => (hΦd r).continuousAt.continuousWithinAt
      · exact fun r _ => (hΦd r).hasDerivWithinAt
      · intro r hr
        rw [interior_Ici, Set.mem_Ioi] at hr
        have hs := hf_smooth i y (r * u)
        simp only at hs
        rw [smul_smul, map_smul, smul_eq_mul]
        rw [Real.norm_eq_abs] at hs
        have hb := hβ_pos i
        have : u * (fderiv ℝ f (y + (r * u) • e) e - g) ≤ |u| * (β i * |r * u|) := by
          calc u * (fderiv ℝ f (y + (r * u) • e) e - g)
              ≤ |u * (fderiv ℝ f (y + (r * u) • e) e - g)| := le_abs_self _
            _ = |u| * |fderiv ℝ f (y + (r * u) • e) e - g| := abs_mul _ _
            _ ≤ |u| * (β i * |r * u|) := by gcongr
        rw [abs_mul, abs_of_pos hr] at this
        have hu : |u| * (β i * (r * |u|)) = β i * r * u ^ 2 := by
          rw [show |u| * (β i * (r * |u|)) = β i * r * (|u| * |u|) by ring, abs_mul_abs_self]
          ring
        nlinarith
    have h01 := hanti (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 zero_le_one) zero_le_one
    simp [Φ] at h01
    linarith
  have hb := hβ_pos i
  have heq : randomizedCoordDescentStep f y i (β i)⁻¹ =
      y + (-((β i)⁻¹ * fderiv ℝ f y (EuclideanSpace.single i 1))) •
        EuclideanSpace.single i (1:ℝ) := by
    simp only [randomizedCoordDescentStep]
    ext j
    simp [EuclideanSpace.single_apply]
    split_ifs <;> ring
  rw [heq]
  refine (hdesc0 _).trans (le_of_eq ?_)
  field_simp
  ring

/-- First-order characterization of convexity, written in coordinates. -/
lemma rcdgb_first_order {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_diff : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f)
    (y z : EuclideanSpace ℝ (Fin n)) :
    f y - f z ≤ ∑ i, (y i - z i) * fderiv ℝ f y (EuclideanSpace.single i 1) := by
  have hfo : f y + fderiv ℝ f y (z - y) ≤ f z := by
    set d := z - y with hd
    let χ : ℝ → ℝ := fun t => f (y + t • d)
    have hχc : ConvexOn ℝ Set.univ χ := by
      refine ⟨convex_univ, fun a _ b _ p q hp hq hpq => ?_⟩
      have : y + (p • a + q • b) • d = p • (y + a • d) + q • (y + b • d) := by
        rw [smul_add, smul_add, smul_smul, smul_smul, add_add_add_comm, ← add_smul, hpq,
          one_smul, add_smul, smul_eq_mul, smul_eq_mul]
      simp only [χ, this]
      exact hf_convex.2 (Set.mem_univ _) (Set.mem_univ _) hp hq hpq
    have hχd : HasDerivAt χ (fderiv ℝ f y d) 0 := by
      have h1 : HasDerivAt (fun t : ℝ => y + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add y
      have h2 := (hf_diff (y + (0:ℝ) • d)).hasFDerivAt.comp_hasDerivAt (0:ℝ) h1
      simpa using h2
    have := hχc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hχd
    simp [χ, slope, hd] at this
    rw [hd, map_sub]
    linarith
  have h2 : fderiv ℝ f y (z - y) =
      ∑ i, (z - y) i * fderiv ℝ f y (EuclideanSpace.single i (1:ℝ)) := by
    conv_lhs => rw [show z - y = ∑ i, (z - y) i • EuclideanSpace.single i (1:ℝ) by
      ext j; simp [Pi.single_apply]]
    simp [map_sum, map_smul]
  have h3 : ∑ i, (z - y) i * fderiv ℝ f y (EuclideanSpace.single i (1:ℝ)) =
      - ∑ i, (y i - z i) * fderiv ℝ f y (EuclideanSpace.single i 1) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simp only [PiLp.sub_apply]
    ring
  rw [h2, h3] at hfo
  linarith

/-- A per-coordinate algebraic inequality (weighted AM-GM). -/
lemma rcdgb_alg (R S K c dd gg ww PP : ℝ) (hR : 0 < R) (hS : 0 < S)
    (hK : K = 2 * R ^ 2 * S) (hww : 0 < ww) (hPP : 0 < PP) :
    (2 * c * (dd * gg) - c ^ 2 / R ^ 2 * (ww * dd ^ 2)) / K ≤
      (PP / S) * (gg ^ 2 / (2 * (PP * ww))) := by
  have hK_pos : 0 < K := by rw [hK]; positivity
  have e1 : (PP / S) * (gg ^ 2 / (2 * (PP * ww))) = (R ^ 2 * gg ^ 2 / ww) / K := by
    rw [hK]; field_simp
  rw [e1]
  apply div_le_div_of_nonneg_right _ hK_pos.le
  have e2 : R ^ 2 * gg ^ 2 / ww - (2 * c * (dd * gg) - c ^ 2 / R ^ 2 * (ww * dd ^ 2)) =
      (R ^ 2 * gg - c * ww * dd) ^ 2 / (R ^ 2 * ww) := by
    field_simp; ring
  have : 0 ≤ (R ^ 2 * gg - c * ww * dd) ^ 2 / (R ^ 2 * ww) := by positivity
  linarith

/-- The coordinate descent step is measurable in the current point. -/
lemma rcdgb_step_measurable {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (β : Fin n → ℝ)
    (i : Fin n) : Measurable (fun y => randomizedCoordDescentStep f y i ((β i)⁻¹)) := by
  have hsingle : ∀ c : ℝ, EuclideanSpace.single i c = c • EuclideanSpace.single i (1:ℝ) := by
    intro c; ext j; simp [EuclideanSpace.single_apply]
  have : (fun y => randomizedCoordDescentStep f y i ((β i)⁻¹)) = fun y =>
      y - ((β i)⁻¹ * fderiv ℝ f y (EuclideanSpace.single i 1)) • EuclideanSpace.single i (1:ℝ) := by
    funext y
    simp only [randomizedCoordDescentStep]
    rw [hsingle]
  rw [this]
  have hm : Measurable fun y => fderiv ℝ f y (EuclideanSpace.single i 1) :=
    measurable_fderiv_apply_const ℝ f _
  exact measurable_id.sub ((hm.const_mul _).smul_const _)

/-- The coordinate chosen at step `s` is independent of the current iterate. -/
lemma rcdgb_indep {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
    (I : ℕ → Ω → Fin n) (β : Fin n → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    (hx0 : ∀ ω, x 0 ω = x0) (hIm : ∀ s, Measurable (I s))
    (hstep : ∀ s ω, x (s + 1) ω = randomizedCoordDescentStep f (x s ω) (I s ω) ((β (I s ω))⁻¹))
    (hind : iIndepFun (fun p => I p) μ) (s : ℕ) :
    IndepFun (I s) (x s) μ := by
  have hΦ : Measurable (fun p : EuclideanSpace ℝ (Fin n) × Fin n =>
      randomizedCoordDescentStep f p.1 p.2 ((β p.2)⁻¹)) := by
    apply measurable_from_prod_countable_left
    intro i
    exact rcdgb_step_measurable f β i
  let m : ℕ → MeasurableSpace Ω := fun j => MeasurableSpace.comap (I j) inferInstance
  have hm_le : ∀ j, m j ≤ ‹MeasurableSpace Ω› := fun j => (hIm j).comap_le
  have hiind : iIndep m μ := (iIndepFun_iff_iIndep _ _ _).1 hind
  let 𝓕 : ℕ → MeasurableSpace Ω := fun s => ⨆ j ∈ Set.Iio s, m j
  have hxF : ∀ s, Measurable[𝓕 s] (x s) := by
    intro s
    induction s with
    | zero =>
      have : x 0 = fun _ => x0 := funext hx0
      rw [this]; exact measurable_const
    | succ k ih =>
      have hfun : x (k+1) = (fun p : EuclideanSpace ℝ (Fin n) × Fin n =>
          randomizedCoordDescentStep f p.1 p.2 ((β p.2)⁻¹)) ∘ (fun ω => (x k ω, I k ω)) :=
        funext (hstep k)
      rw [hfun]
      apply hΦ.comp
      apply Measurable.prodMk
      · exact ih.mono (biSup_mono fun j hj => lt_trans hj (Nat.lt_succ_self k)) le_rfl
      · exact (comap_measurable (I k)).mono (le_biSup m (Nat.lt_succ_self k)) le_rfl
  have key := indep_iSup_of_disjoint hm_le hiind (S := {s}) (T := Set.Iio s) (by simp)
  rw [IndepFun_iff_Indep]
  refine indep_of_indep_of_le_right (indep_of_indep_of_le_left key ?_) (hxF s).comap_le
  exact le_biSup m (Set.mem_singleton s)

/-- Expectation of `h J X` for independent `J` (finite-valued) and `X`. -/
lemma rcdgb_expect {n : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → EuclideanSpace ℝ (Fin n)) (J : Ω → Fin n)
    (hX : Measurable X) (hJ : Measurable J) (hind : IndepFun J X μ)
    (h : Fin n → EuclideanSpace ℝ (Fin n) → ℝ) (hh : ∀ i, Measurable (h i))
    (C : ℝ) (hC : ∀ i ω, |h i (X ω)| ≤ C) :
    ∫ ω, h (J ω) (X ω) ∂μ = ∫ ω, ∑ i, μ.real (J ⁻¹' {i}) * h i (X ω) ∂μ := by
  have hC0 : 0 ≤ C := by
    rcases isEmpty_or_nonempty Ω with hΩ | ⟨⟨ω⟩⟩
    · exact absurd (measure_univ (μ := μ)) (by simp [Set.univ_eq_empty_iff.2 hΩ])
    · rcases isEmpty_or_nonempty (Fin n) with hn | ⟨⟨i⟩⟩
      · exact (hn.false (J ω)).elim
      · exact le_trans (abs_nonneg _) (hC i ω)
  have hbint : ∀ g : Ω → ℝ, Measurable g → (∀ ω, |g ω| ≤ C) → Integrable g μ :=
    fun g hg hC => Integrable.of_bound hg.aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by rw [Real.norm_eq_abs]; exact hC ω))
  have hint_i : ∀ i, Integrable (fun ω => h i (X ω)) μ := fun i =>
    hbint _ ((hh i).comp hX) (fun ω => hC i ω)
  have hpt : (fun ω => h (J ω) (X ω)) = fun ω => ∑ i, (if J ω = i then (1:ℝ) else 0) *
      h i (X ω) := by
    funext ω
    simp [ite_mul, Finset.sum_ite_eq]
  rw [hpt, integral_finset_sum, integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [integral_const_mul]
    have hind_i : ∫ ω, (if J ω = i then (1:ℝ) else 0) * h i (X ω) ∂μ =
        (∫ ω, (if J ω = i then (1:ℝ) else 0) ∂μ) * ∫ ω, h i (X ω) ∂μ :=
      hind.integral_fun_comp_mul_comp hJ.aemeasurable hX.aemeasurable
        (f := fun j => if j = i then (1:ℝ) else 0) (g := h i)
        (Measurable.of_discrete.aestronglyMeasurable) ((hh i).aestronglyMeasurable)
    rw [hind_i]
    congr 1
    have : (fun ω => if J ω = i then (1:ℝ) else 0) = (J ⁻¹' {i}).indicator 1 := by
      funext ω
      by_cases hω : J ω = i
      · rw [Set.indicator_of_mem (by simpa using hω)]; simp [hω]
      · rw [Set.indicator_of_notMem (by simpa using hω)]; simp [hω]
    rw [this, integral_indicator_one (hJ (measurableSet_singleton i))]
  · intro i _
    exact (hint_i i).const_mul _
  · intro i _
    refine hbint _ ?_ ?_
    · exact ((Measurable.of_discrete (f := fun j : Fin n => if j = i then (1:ℝ) else 0)).comp
        hJ).mul ((hh i).comp hX)
    · intro ω
      by_cases hω : J ω = i
      · simp only [hω, if_true, one_mul]
        exact hC i ω
      · simp only [hω, if_false, zero_mul, abs_zero]
        exact hC0

/-- Solving the recursion `K δ_{s+1} ≤ K δ_s - δ_s ^ 2`. -/
lemma rcdgb_seq (δ : ℕ → ℝ) (K : ℝ) (hK_pos : 0 < K) (hδ_nonneg : ∀ s, 0 ≤ δ s)
    (hrec : ∀ s, K * δ (s+1) ≤ K * δ s - δ s ^ 2) (s : ℕ) :
    δ (s+1) * ((s:ℝ)+1) ≤ K := by
  induction s with
  | zero =>
    have h1 := hrec 0
    have h2 := hδ_nonneg 0
    have h3 := hδ_nonneg 1
    simp only [Nat.cast_zero, zero_add, mul_one]
    nlinarith [sq_nonneg (δ 0 - K / 2)]
  | succ k ih =>
    have h1 := hrec (k+1)
    have h2 := hδ_nonneg (k+1)
    have h3 := hδ_nonneg (k+2)
    push_cast
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    have haK : δ (k+1) ≤ K := by nlinarith
    have key : K * (δ (k+1+1) * ((k:ℝ)+1+1)) ≤ K * K := by
      nlinarith [mul_nonneg (sub_nonneg.2 ih) (sub_nonneg.2 haK),
        mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ (k:ℝ)+1+1), sq_nonneg (δ (k+1))]
    exact le_of_mul_le_mul_left key hK_pos

set_option linter.unusedVariables false in
theorem randomized_coordinate_descent_gamma_bound {n t : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (β : Fin n → ℝ)
  (γ R : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hβ_pos : ∀ i, β i > 0)
  (hγ_pos : γ ≥ 0)
  (hR_pos : R > 0)
  (ht_pos : t > 0)
  (hR_sq : R ^ 2 = sSup {v | ∃ x', (f x' ≤ f x0) ∧
                                   (v = ∑ i, (Real.rpow (β i) (1 - γ)) * (x' i - x_star i) ^ 2)})
  (h_rcd_gamma_seq : IsRandomizedCoordDescentGammaSequence μ f x I β γ)
  (hf_diff : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_smooth : ∀ (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (u : ℝ),
    let ei : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i (1:ℝ)
    ‖(fderiv ℝ f (x + u • ei)) (EuclideanSpace.single i (1:ℝ)) -
    (fderiv ℝ f x) (EuclideanSpace.single i (1:ℝ))‖ ≤ β i * |u|)
  (hx_star : IsMinOn f Set.univ x_star) :
  ∫ ω, f (x t ω) ∂μ - f x_star ≤
  (2 * (R ^ 2) * (∑ i, Real.rpow (β i) γ)) / (t : ℝ) := by
  obtain ⟨hxm, hIm, hstep, hind, hdist⟩ := h_rcd_gamma_seq
  -- basic constants
  have hP_pos : ∀ i, 0 < Real.rpow (β i) γ := fun i => Real.rpow_pos_of_pos (hβ_pos i) γ
  set S : ℝ := ∑ j, Real.rpow (β j) γ with hS_def
  have hS_pos : 0 < S := by
    apply Finset.sum_pos (fun i _ => hP_pos i)
    exact Finset.univ_nonempty_iff.2 ⟨⟨0, hn_pos⟩⟩
  have hR2_pos : 0 < R ^ 2 := by positivity
  set K : ℝ := 2 * R ^ 2 * S with hK_def
  have hK_pos : 0 < K := by positivity
  set fs := f x_star with hfs_def
  have hlow : ∀ y, fs ≤ f y := fun y => hx_star (Set.mem_univ y)
  -- the weighted distance to the minimizer is bounded on the sublevel set
  have hbdd : ∀ y, f y ≤ f x0 →
      ∑ i, Real.rpow (β i) (1 - γ) * (y i - x_star i) ^ 2 ≤ R ^ 2 := by
    intro y hy
    have hTbdd : BddAbove {v | ∃ x', (f x' ≤ f x0) ∧
        (v = ∑ i, (Real.rpow (β i) (1 - γ)) * (x' i - x_star i) ^ 2)} := by
      by_contra hcon
      rw [Real.sSup_of_not_bddAbove hcon] at hR_sq
      linarith
    rw [hR_sq]
    exact le_csSup hTbdd ⟨y, hy, rfl⟩
  have hdesc := rcdgb_step_le f β hβ_pos hf_diff hf_smooth
  -- the key deterministic inequality for one expected step
  have hβPw : ∀ i, β i = Real.rpow (β i) γ * Real.rpow (β i) (1 - γ) := by
    intro i
    simp only [Real.rpow_eq_pow]
    rw [← Real.rpow_add (hβ_pos i)]
    simp
  have hPsum : ∑ i, Real.rpow (β i) γ / S = 1 := by
    rw [← Finset.sum_div]; exact div_self (ne_of_gt hS_pos)
  have hkey : ∀ y, f y ≤ f x0 → ∀ c : ℝ, 0 ≤ c →
      ∑ i, (Real.rpow (β i) γ / S) * f (randomizedCoordDescentStep f y i (β i)⁻¹) ≤
        f y - (2 * c * (f y - fs) - c ^ 2) / K := by
    intro y hy c hc
    have h1 : ∑ i, (Real.rpow (β i) γ / S) * f (randomizedCoordDescentStep f y i (β i)⁻¹) ≤
        ∑ i, (Real.rpow (β i) γ / S) *
          (f y - (fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i)) := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (hdesc y i) (div_nonneg (hP_pos i).le hS_pos.le)
    have h2 : ∑ i, (Real.rpow (β i) γ / S) *
          (f y - (fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i)) =
        f y - ∑ i, (Real.rpow (β i) γ / S) *
          ((fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i)) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hPsum, one_mul]
    have h3 : ∀ i, (2 * c * ((y i - x_star i) * fderiv ℝ f y (EuclideanSpace.single i 1)) -
          c ^ 2 / R ^ 2 * (Real.rpow (β i) (1 - γ) * (y i - x_star i) ^ 2)) / K ≤
        (Real.rpow (β i) γ / S) *
          ((fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i)) := by
      intro i
      have := rcdgb_alg R S K c (y i - x_star i) (fderiv ℝ f y (EuclideanSpace.single i 1))
        (Real.rpow (β i) (1 - γ)) (Real.rpow (β i) γ) hR_pos hS_pos hK_def
        (Real.rpow_pos_of_pos (hβ_pos i) _) (hP_pos i)
      rw [← hβPw i] at this
      exact this
    have h4 : (2 * c * (f y - fs) - c ^ 2) / K ≤
        ∑ i, (2 * c * ((y i - x_star i) * fderiv ℝ f y (EuclideanSpace.single i 1)) -
          c ^ 2 / R ^ 2 * (Real.rpow (β i) (1 - γ) * (y i - x_star i) ^ 2)) / K := by
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ hK_pos.le
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      have hc1 := rcdgb_first_order f hf_diff hf_convex y x_star
      have hc2 := hbdd y hy
      have h5 : c ^ 2 / R ^ 2 * ∑ i, Real.rpow (β i) (1 - γ) * (y i - x_star i) ^ 2 ≤ c ^ 2 := by
        calc c ^ 2 / R ^ 2 * ∑ i, Real.rpow (β i) (1 - γ) * (y i - x_star i) ^ 2
            ≤ c ^ 2 / R ^ 2 * R ^ 2 := by gcongr
          _ = c ^ 2 := by field_simp
      have h6 : 2 * c * (f y - fs) ≤
          2 * c * ∑ i, (y i - x_star i) * fderiv ℝ f y (EuclideanSpace.single i 1) := by
        apply mul_le_mul_of_nonneg_left hc1; positivity
      linarith
    have h5 := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h3 i)
    linarith
  -- the iterates stay in the initial sublevel set
  have hstep_le' : ∀ y i, f (randomizedCoordDescentStep f y i (β i)⁻¹) ≤ f y := by
    intro y i
    have h1 := hdesc y i
    have h2 : 0 ≤ (fderiv ℝ f y (EuclideanSpace.single i 1)) ^ 2 / (2 * β i) := by
      have := hβ_pos i; positivity
    linarith
  have hmono : ∀ s ω, f (x s ω) ≤ f x0 := by
    intro s
    induction s with
    | zero => intro ω; rw [hx0]
    | succ k ih =>
      intro ω
      rw [hstep k ω]
      exact (hstep_le' _ _).trans (ih ω)
  have hfm : Measurable f := hf_diff.continuous.measurable
  -- integrability
  set C : ℝ := max |fs| |f x0| with hC_def
  have hCb : ∀ v, fs ≤ v → v ≤ f x0 → |v| ≤ C := by
    intro v h1 h2
    rw [abs_le]
    constructor
    · have := neg_abs_le fs; have := le_max_left |fs| |f x0|; linarith
    · have := le_abs_self (f x0); have := le_max_right |fs| |f x0|; linarith
  have hint : ∀ s, Integrable (fun ω => f (x s ω)) μ := fun s =>
    Integrable.of_bound (hfm.comp (hxm s)).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]; exact hCb _ (hlow _) (hmono s ω)))
  have hint_i : ∀ s i,
      Integrable (fun ω => f (randomizedCoordDescentStep f (x s ω) i (β i)⁻¹)) μ := fun s i =>
    Integrable.of_bound (hfm.comp ((rcdgb_step_measurable f β i).comp (hxm s))).aestronglyMeasurable C
      (Filter.Eventually.of_forall (fun ω => by
        rw [Real.norm_eq_abs]
        exact hCb _ (hlow _) ((hstep_le' _ _).trans (hmono s ω))))
  -- one-step expectation
  have hp : ∀ s i, μ.real (I s ⁻¹' {i}) = Real.rpow (β i) γ / S := by
    intro s i
    rw [measureReal_def, hdist s i, ENNReal.toReal_ofReal (div_nonneg (hP_pos i).le hS_pos.le)]
  have hexp : ∀ s, ∫ ω, f (x (s+1) ω) ∂μ =
      ∫ ω, ∑ i, (Real.rpow (β i) γ / S) * f (randomizedCoordDescentStep f (x s ω) i (β i)⁻¹) ∂μ := by
    intro s
    have hpt : (fun ω => f (x (s+1) ω)) =
        fun ω => (fun i y => f (randomizedCoordDescentStep f y i (β i)⁻¹)) (I s ω) (x s ω) := by
      funext ω
      rw [hstep s ω]
    rw [hpt, rcdgb_expect μ (x s) (I s) (hxm s) (hIm s)
      (rcdgb_indep μ f x I β x0 hx0 hIm hstep hind s)
      (fun i y => f (randomizedCoordDescentStep f y i (β i)⁻¹))
      (fun i => hfm.comp (rcdgb_step_measurable f β i)) C
      (fun i ω => hCb _ (hlow _) ((hstep_le' _ _).trans (hmono s ω)))]
    simp only [hp]
  -- recursion for the expected suboptimality
  set δ : ℕ → ℝ := fun s => ∫ ω, f (x s ω) ∂μ - fs with hδ_def
  have hδ_nonneg : ∀ s, 0 ≤ δ s := by
    intro s
    have : fs ≤ ∫ ω, f (x s ω) ∂μ := by
      have := integral_mono (integrable_const fs) (hint s) (fun ω => hlow (x s ω))
      simpa using this
    simp only [hδ_def]; linarith
  have hrec : ∀ s, K * δ (s+1) ≤ K * δ s - δ s ^ 2 := by
    intro s
    have h1 := hexp s
    have haff : (fun ω => f (x s ω) - (2 * δ s * (f (x s ω) - fs) - δ s ^ 2) / K) =
        fun ω => (1 - 2 * δ s / K) * f (x s ω) + (2 * δ s * fs + δ s ^ 2) / K := by
      ext ω; field_simp; ring
    have h2 : ∫ ω, ∑ i, (Real.rpow (β i) γ / S) *
          f (randomizedCoordDescentStep f (x s ω) i (β i)⁻¹) ∂μ ≤
        ∫ ω, (f (x s ω) - (2 * δ s * (f (x s ω) - fs) - δ s ^ 2) / K) ∂μ := by
      apply integral_mono
      · exact integrable_finset_sum _ (fun i _ => (hint_i s i).const_mul _)
      · rw [haff]
        exact ((hint s).const_mul _).add (integrable_const _)
      · intro ω; exact hkey _ (hmono s ω) _ (hδ_nonneg s)
    have h3 : ∫ ω, (f (x s ω) - (2 * δ s * (f (x s ω) - fs) - δ s ^ 2) / K) ∂μ =
        (1 - 2 * δ s / K) * (∫ ω, f (x s ω) ∂μ) + (2 * δ s * fs + δ s ^ 2) / K := by
      rw [haff, integral_add ((hint s).const_mul _) (integrable_const _), integral_const_mul,
        integral_const]
      simp
    have hδs : δ s = ∫ ω, f (x s ω) ∂μ - fs := rfl
    have hδs1 : δ (s+1) = ∫ ω, f (x (s+1) ω) ∂μ - fs := rfl
    have h4 : δ (s+1) ≤
        (1 - 2 * δ s / K) * (∫ ω, f (x s ω) ∂μ) + (2 * δ s * fs + δ s ^ 2) / K - fs := by
      rw [hδs1, h1]; linarith
    have h5 : (1 - 2 * δ s / K) * (∫ ω, f (x s ω) ∂μ) + (2 * δ s * fs + δ s ^ 2) / K - fs =
        δ s - δ s ^ 2 / K := by
      rw [hδs]; field_simp; ring
    rw [h5] at h4
    have h6 : K * (δ s - δ s ^ 2 / K) = K * δ s - δ s ^ 2 := by field_simp
    calc K * δ (s+1) ≤ K * (δ s - δ s ^ 2 / K) := mul_le_mul_of_nonneg_left h4 hK_pos.le
      _ = K * δ s - δ s ^ 2 := h6
  -- solving the recursion
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  have h := rcdgb_seq δ K hK_pos hδ_nonneg hrec k
  simp only [hδ_def] at h
  rw [le_div_iff₀ (by positivity)]
  push_cast
  exact h

end randomized_coordinate_descent_gamma_bound
