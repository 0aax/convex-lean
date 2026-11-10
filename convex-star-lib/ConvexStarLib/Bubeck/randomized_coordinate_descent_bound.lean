import ConvexStarLib.Defs

/-!
# `randomized_coordinate_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/randomized_coordinate_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace randomized_coordinate_descent_bound`, so the main result is `randomized_coordinate_descent_bound.randomized_coordinate_descent_bound`.
-/

namespace randomized_coordinate_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


/-- First-order condition for a differentiable convex function. -/
lemma rcd_convex_grad_ineq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℝ}
    (hf_diff : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f) (x y : E) :
    f x + fderiv ℝ f x (y - x) ≤ f y := by
  have hφc : ConvexOn ℝ Set.univ (f ∘ AffineMap.lineMap (k := ℝ) x y) := by
    simpa using hf_convex.comp_affineMap (AffineMap.lineMap (k := ℝ) x y)
  have hline : HasDerivAt (fun τ : ℝ => τ • (y - x) + x) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).smul_const (y - x)).add_const x
  have hφd : HasDerivAt (f ∘ AffineMap.lineMap (k := ℝ) x y) (fderiv ℝ f x (y - x)) 0 := by
    have h1 : HasFDerivAt f (fderiv ℝ f x) ((fun τ : ℝ => τ • (y - x) + x) 0) := by
      simpa using (hf_diff x).hasFDerivAt
    have := h1.comp_hasDerivAt (0:ℝ) hline
    convert this using 1
  have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hφd
  simp [slope, AffineMap.lineMap_apply] at this
  rw [map_sub]
  linarith

/-- Coordinate expansion of a linear functional on Euclidean space, and the bound on the
sum of squares of its coordinates. -/
lemma rcd_euclid_dual_facts {n : ℕ} (ℓ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :
    (∀ v : EuclideanSpace ℝ (Fin n), ∑ i, ℓ (EuclideanSpace.single i 1) * v i = ℓ v) ∧
    ∑ i, (ℓ (EuclideanSpace.single i 1)) ^ 2 ≤ ‖ℓ‖ ^ 2 := by
  set w := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm ℓ with hw
  have hℓ : ∀ v, ℓ v = inner ℝ w v := by
    intro v
    rw [hw, InnerProductSpace.toDual_symm_apply]
  have he : ∀ i, ℓ (EuclideanSpace.single i 1) = w i := by
    intro i
    rw [hℓ, EuclideanSpace.inner_single_right]
    simp
  refine ⟨fun v => ?_, ?_⟩
  · rw [hℓ v, PiLp.inner_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [he]
    simp [mul_comm]
  · have hnorm : ‖w‖ = ‖ℓ‖ := by
      rw [hw, LinearIsometryEquiv.norm_map]
    rw [← hnorm, EuclideanSpace.norm_sq_eq]
    refine le_of_eq (Finset.sum_congr rfl (fun i _ => ?_))
    rw [he, Real.norm_eq_abs, sq_abs]

lemma rcd_step_norm_sq {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (e x_star : EuclideanSpace ℝ (Fin n)) (i : Fin n) (η : ℝ) :
    ‖randomizedCoordDescentStep f e i η - x_star‖ ^ 2 =
      ‖e - x_star‖ ^ 2 - 2 * η * (fderiv ℝ f e (EuclideanSpace.single i 1) * (e - x_star) i)
        + η ^ 2 * (fderiv ℝ f e (EuclideanSpace.single i 1)) ^ 2 := by
  unfold randomizedCoordDescentStep
  simp only []
  rw [sub_right_comm, norm_sub_sq_real, EuclideanSpace.inner_single_right,
    EuclideanSpace.norm_single]
  simp only [norm_mul, Real.norm_eq_abs, mul_pow, sq_abs, conj_trivial, PiLp.sub_apply]
  ring

/-- Averaged over the coordinate, one step decreases the squared distance to `x_star`. -/
lemma rcd_step_sum_bound {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf_diff : Differentiable ℝ f) (hf_convex : ConvexOn ℝ Set.univ f) {L : ℝ}
    (hL : ∀ e, ‖fderiv ℝ f e‖ ≤ L) (e x_star : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 ≤ η) :
    ∑ i, ‖randomizedCoordDescentStep f e i η - x_star‖ ^ 2 ≤
      n * ‖e - x_star‖ ^ 2 - 2 * η * (f e - f x_star) + η ^ 2 * L ^ 2 := by
  simp_rw [rcd_step_norm_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  obtain ⟨h1, h2⟩ := rcd_euclid_dual_facts (fderiv ℝ f e)
  rw [h1]
  have hg := rcd_convex_grad_ineq hf_diff hf_convex e x_star
  have hneg : (fderiv ℝ f e) (e - x_star) = - (fderiv ℝ f e) (x_star - e) := by
    rw [← map_neg, neg_sub]
  have h3 : ∑ i, (fderiv ℝ f e (EuclideanSpace.single i 1)) ^ 2 ≤ L ^ 2 := by
    refine h2.trans ?_
    exact pow_le_pow_left₀ (norm_nonneg _) (hL e) 2
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h4 : η ^ 2 * ∑ i, (fderiv ℝ f e (EuclideanSpace.single i 1)) ^ 2 ≤ η ^ 2 * L ^ 2 :=
    mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
  nlinarith

/-- The deterministic trajectory driven by a sequence of coordinates `a`. -/
noncomputable def rcdTraj {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (η : ℝ) (a : ℕ → Fin n) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => x0
  | s + 1 => randomizedCoordDescentStep f (rcdTraj f x0 η a s) (a s) η

lemma rcdTraj_congr {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ) (x0 : EuclideanSpace ℝ (Fin n))
    (η : ℝ) (a b : ℕ → Fin n) (s : ℕ) (h : ∀ j < s, a j = b j) :
    rcdTraj f x0 η a s = rcdTraj f x0 η b s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    simp only [rcdTraj]
    rw [ih (fun j hj => h j (by omega)), h s (by omega)]

/-- The trajectory driven by the coordinates indexed by a finset `T` (padded with `i0`). -/
noncomputable def rcdTrajFin {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x0 : EuclideanSpace ℝ (Fin n)) (η : ℝ) (i0 : Fin n) (T : Finset ℕ) (c : ↥T → Fin n)
    (s : ℕ) : EuclideanSpace ℝ (Fin n) :=
  rcdTraj f x0 η (fun j => if h : j ∈ T then c ⟨j, h⟩ else i0) s

lemma rcd_integrable_comp_finite {Ω β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] [MeasurableSpace β] [Finite β] [MeasurableSingletonClass β] {Y : Ω → β}
    (hY : Measurable Y) (h : β → ℝ) : Integrable (fun ω => h (Y ω)) μ :=
  (Integrable.of_finite (μ := μ.map Y) (f := h)).comp_measurable hY

lemma rcd_integral_comp_indep_uniform {Ω β : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] [MeasurableSpace β] [Finite β] [MeasurableSingletonClass β] {n : ℕ}
    {Y : Ω → β} {Z : Ω → Fin n} (hY : Measurable Y) (hZ : Measurable Z)
    (hYZ : ProbabilityTheory.IndepFun Y Z μ)
    (hZu : ∀ i, μ (Z ⁻¹' {i}) = (n : ℝ≥0∞)⁻¹) (G : β → Fin n → ℝ) :
    ∫ ω, G (Y ω) (Z ω) ∂μ = (1 / n) * ∑ i, ∫ ω, G (Y ω) i ∂μ := by
  have hsplit : ∀ ω, G (Y ω) (Z ω) = ∑ i, G (Y ω) i * (if Z ω = i then 1 else 0) := by
    intro ω
    simp
  simp_rw [hsplit]
  rw [integral_finset_sum _ (fun i _ => rcd_integrable_comp_finite (hY.prodMk hZ)
    (fun p => G p.1 i * if p.2 = i then 1 else 0))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hind : ProbabilityTheory.IndepFun (fun ω => G (Y ω) i)
      (fun ω => if Z ω = i then (1:ℝ) else 0) μ :=
    hYZ.comp (measurable_of_finite (fun b => G b i))
      (measurable_of_finite (fun j : Fin n => if j = i then (1:ℝ) else 0))
  rw [hind.integral_fun_mul_eq_mul_integral
    (rcd_integrable_comp_finite hY (fun b => G b i)).aestronglyMeasurable
    (rcd_integrable_comp_finite hZ (fun j => if j = i then (1:ℝ) else 0)).aestronglyMeasurable]
  have h1 : ∫ ω, (if Z ω = i then (1:ℝ) else 0) ∂μ = 1 / n := by
    have : (fun ω => if Z ω = i then (1:ℝ) else 0) = (Z ⁻¹' {i}).indicator 1 := by
      funext ω
      by_cases h : Z ω = i <;> simp [h]
    rw [this, integral_indicator_one (hZ (measurableSet_singleton i)), measureReal_def, hZu i]
    simp
  rw [h1, mul_comm]

set_option linter.unusedVariables false in
theorem randomized_coordinate_descent_bound {n t : ℕ} {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin n)
  (R L : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hn_pos : n > 0)
  (hR_pos : R > 0)
  (hL_pos : L > 0)
  (ht_pos : t > 0)
  (hR_sq : (1 / 2) * ‖x_star - x0‖ ^ 2 ≤ R ^ 2)
  (h_rcd_seq :
    IsRandomizedCoordDescentSequence μ f x I
      ((R / L) * (Real.sqrt (2 * n / t))))
  (hf_diff : Differentiable ℝ f)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_lipschitz : LipschitzWith (Real.toNNReal L) f)
  (hx_star : IsMinOn f Set.univ x_star) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f x_star ≤
    R * L * Real.sqrt (2 * n / t) := by
  obtain ⟨hx_meas, hI_meas, h_step, h_indep, h_unif⟩ := h_rcd_seq
  have hn : (0:ℝ) < n := by exact_mod_cast hn_pos
  have ht : (0:ℝ) < t := by exact_mod_cast ht_pos
  have hq_sq : Real.sqrt (2 * n / t) ^ 2 = 2 * n / t := Real.sq_sqrt (by positivity)
  have hq_pos : 0 < Real.sqrt (2 * n / t) := Real.sqrt_pos.mpr (by positivity)
  set q := Real.sqrt (2 * n / t) with hq_def
  set η : ℝ := (R / L) * q with hη_def
  have hη_pos : 0 < η := by positivity
  have hLfd : ∀ e, ‖fderiv ℝ f e‖ ≤ L := by
    intro e
    have := norm_fderiv_le_of_lipschitz ℝ (x₀ := e) hf_lipschitz
    rwa [Real.coe_toNNReal L hL_pos.le] at this
  -- the iterates as a deterministic function of the coordinates
  have hx_traj : ∀ s ω, x s ω = rcdTraj f x0 η (fun j => I j ω) s := by
    intro s ω
    induction s with
    | zero => simp [rcdTraj, hx0]
    | succ s ih => rw [h_step, ih]; rfl
  set i0 : Fin n := ⟨0, hn_pos⟩
  have hrep : ∀ (T : Finset ℕ) (s : ℕ), (∀ j < s, j ∈ T) → ∀ ω,
      x s ω = rcdTrajFin f x0 η i0 T (fun k : ↥T => I k ω) s := by
    intro T s hT ω
    rw [hx_traj, rcdTrajFin]
    apply rcdTraj_congr
    intro j hj
    simp [hT j hj]
  have hJ_meas : ∀ T : Finset ℕ, Measurable (fun ω (k : ↥T) => I k ω) := by
    intro T
    exact measurable_pi_lambda _ (fun k => hI_meas k)
  have hint : ∀ s (h : EuclideanSpace ℝ (Fin n) → ℝ), Integrable (fun ω => h (x s ω)) μ := by
    intro s h
    have e := hrep (Finset.range s) s (fun j hj => Finset.mem_range.mpr hj)
    simp_rw [e]
    exact rcd_integrable_comp_finite (hJ_meas (Finset.range s))
      (fun c => h (rcdTrajFin f x0 η i0 (Finset.range s) c s))
  have hJI : ∀ s, ProbabilityTheory.IndepFun (fun ω (k : ↥(Finset.range s)) => I k ω) (I s) μ := by
    intro s
    have h := h_indep.indepFun_finset (Finset.range s) {s}
      (Finset.disjoint_singleton_right.mpr Finset.notMem_range_self) hI_meas
    exact h.comp measurable_id (measurable_pi_apply ⟨s, Finset.mem_singleton_self s⟩)
  have hkey : ∀ s (G : EuclideanSpace ℝ (Fin n) → Fin n → ℝ),
      ∫ ω, G (x s ω) (I s ω) ∂μ = (1 / n) * ∑ i, ∫ ω, G (x s ω) i ∂μ := by
    intro s G
    have e := hrep (Finset.range s) s (fun j hj => Finset.mem_range.mpr hj)
    simp_rw [e]
    exact rcd_integral_comp_indep_uniform (hJ_meas (Finset.range s)) (hI_meas s) (hJI s)
      (h_unif s) (fun c i => G (rcdTrajFin f x0 η i0 (Finset.range s) c s) i)
  -- one-step inequality in expectation
  set a : ℕ → ℝ := fun s => ∫ ω, ‖x s ω - x_star‖ ^ 2 ∂μ with ha_def
  set b : ℕ → ℝ := fun s => ∫ ω, f (x s ω) ∂μ with hb_def
  have hstep1 : ∀ s, a (s + 1) ≤ a s - (2 * η / n) * (b s - f x_star) + η ^ 2 * L ^ 2 / n := by
    intro s
    have e1 : a (s + 1) = ∫ ω, ‖randomizedCoordDescentStep f (x s ω) (I s ω) η - x_star‖ ^ 2 ∂μ := by
      simp only [ha_def, h_step]
    have e2 : ∫ ω, ‖randomizedCoordDescentStep f (x s ω) (I s ω) η - x_star‖ ^ 2 ∂μ =
        1 / n * ∑ i, ∫ ω, ‖randomizedCoordDescentStep f (x s ω) i η - x_star‖ ^ 2 ∂μ :=
      hkey s (fun e i => ‖randomizedCoordDescentStep f e i η - x_star‖ ^ 2)
    rw [e1, e2]
    rw [← integral_finset_sum _ (fun i _ =>
      hint s (fun e => ‖randomizedCoordDescentStep f e i η - x_star‖ ^ 2))]
    have hmono : ∫ ω, ∑ i, ‖randomizedCoordDescentStep f (x s ω) i η - x_star‖ ^ 2 ∂μ ≤
        ∫ ω, ((n:ℝ) * ‖x s ω - x_star‖ ^ 2 - 2 * η * (f (x s ω) - f x_star) + η ^ 2 * L ^ 2) ∂μ :=
      integral_mono (hint s (fun e => ∑ i, ‖randomizedCoordDescentStep f e i η - x_star‖ ^ 2))
        (hint s (fun e => (n:ℝ) * ‖e - x_star‖ ^ 2 - 2 * η * (f e - f x_star) + η ^ 2 * L ^ 2))
        (fun ω => rcd_step_sum_bound hf_diff hf_convex hLfd (x s ω) x_star hη_pos.le)
    have hlin : ∫ ω, ((n:ℝ) * ‖x s ω - x_star‖ ^ 2 - 2 * η * (f (x s ω) - f x_star)
        + η ^ 2 * L ^ 2) ∂μ = n * a s - 2 * η * (b s - f x_star) + η ^ 2 * L ^ 2 := by
      rw [integral_add (hint s (fun e => (n:ℝ) * ‖e - x_star‖ ^ 2 - 2 * η * (f e - f x_star)))
        (integrable_const _)]
      rw [integral_sub (hint s (fun e => (n:ℝ) * ‖e - x_star‖ ^ 2))
        (hint s (fun e => 2 * η * (f e - f x_star)))]
      rw [integral_const_mul, integral_const_mul, integral_sub (hint s f) (integrable_const _)]
      simp [ha_def, hb_def]
    rw [hlin] at hmono
    calc 1 / (n:ℝ) * ∫ ω, ∑ i, ‖randomizedCoordDescentStep f (x s ω) i η - x_star‖ ^ 2 ∂μ
        ≤ 1 / (n:ℝ) * (n * a s - 2 * η * (b s - f x_star) + η ^ 2 * L ^ 2) :=
          mul_le_mul_of_nonneg_left hmono (by positivity)
      _ = a s - (2 * η / n) * (b s - f x_star) + η ^ 2 * L ^ 2 / n := by
          field_simp
  -- telescoping
  have htel : ∀ T : ℕ, (2 * η / n) * ∑ s ∈ Finset.range T, (b s - f x_star) ≤
      a 0 - a T + T * (η ^ 2 * L ^ 2 / n) := by
    intro T
    induction T with
    | zero => simp
    | succ T ih =>
      rw [Finset.sum_range_succ, mul_add]
      have := hstep1 T
      push_cast
      linarith
  have ha0 : a 0 = ‖x0 - x_star‖ ^ 2 := by
    simp [ha_def, hx0]
  have hat : 0 ≤ a t := integral_nonneg (fun ω => sq_nonneg _)
  -- Jensen
  have hjensen : ∀ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ≤
      (1 / t) * ∑ s ∈ Finset.range t, f (x s ω) := by
    intro ω
    have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t:ℝ))
      (p := fun s => x s ω) (fun _ _ => by positivity) (by simp; field_simp) (by simp)
    simpa [Finset.smul_sum, Finset.mul_sum] using this
  have hint_avg : Integrable (fun ω => f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω)) μ := by
    have e : ∀ s ∈ Finset.range t, ∀ ω, x s ω = rcdTrajFin f x0 η i0 (Finset.range t)
        (fun k : ↥(Finset.range t) => I k ω) s := by
      intro s hs ω
      exact hrep (Finset.range t) s (fun j hj => Finset.mem_range.mpr
        (lt_trans hj (Finset.mem_range.mp hs))) ω
    have e2 : (fun ω => f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω)) = fun ω =>
        (fun c => f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, rcdTrajFin f x0 η i0 (Finset.range t) c s))
          (fun k : ↥(Finset.range t) => I k ω) := by
      funext ω
      simp only []
      congr 2
      exact Finset.sum_congr rfl (fun s hs => e s hs ω)
    rw [e2]
    exact rcd_integrable_comp_finite (hJ_meas (Finset.range t))
      (fun c => f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, rcdTrajFin f x0 η i0 (Finset.range t) c s))
  have hint_sum : Integrable (fun ω => (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s ω)) μ :=
    (integrable_finset_sum _ (fun s _ => hint s f)).const_mul _
  have hJ : ∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ ≤
      (1 / t) * ∑ s ∈ Finset.range t, b s := by
    calc ∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ
        ≤ ∫ ω, (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, f (x s ω) ∂μ :=
          integral_mono hint_avg hint_sum hjensen
      _ = (1 / t) * ∑ s ∈ Finset.range t, b s := by
          rw [integral_const_mul, integral_finset_sum _ (fun s _ => hint s f)]
  -- final algebra
  set S := ∑ s ∈ Finset.range t, (b s - f x_star) with hS_def
  have hηL : η * L = R * q := by
    rw [hη_def]
    field_simp
  have h2n : 2 * (n:ℝ) = t * q ^ 2 := by
    rw [hq_sq]
    field_simp
  have hS : S ≤ t * (R * L * q) := by
    have h1 := htel t
    have h4 : a 0 - a t ≤ 2 * R ^ 2 := by
      rw [ha0, ← norm_neg, neg_sub]
      linarith
    have h3 : 2 * η * S ≤ n * (2 * R ^ 2) + t * (η * L) ^ 2 := by
      have h5 := mul_le_mul_of_nonneg_right h1 hn.le
      have h6 : (2 * η / n) * S * n = 2 * η * S := by
        field_simp
      have h7 : (a 0 - a t + t * (η ^ 2 * L ^ 2 / n)) * n = (a 0 - a t) * n + t * (η * L) ^ 2 := by
        field_simp
      rw [h6, h7] at h5
      nlinarith
    have key : 2 * η * S ≤ 2 * η * (t * (R * L * q)) := by
      calc 2 * η * S ≤ n * (2 * R ^ 2) + t * (η * L) ^ 2 := h3
        _ = 2 * η * (t * (R * L * q)) := by
          linear_combination R ^ 2 * h2n + t * (η * L - R * q) * hηL
    exact le_of_mul_le_mul_left key (by positivity)
  have hfinal : (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, b s - f x_star = S / t := by
    rw [hS_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  calc ∫ ω, f ((1 / (t:ℝ)) • ∑ s ∈ Finset.range t, x s ω) ∂μ - f x_star
      ≤ (1 / (t:ℝ)) * ∑ s ∈ Finset.range t, b s - f x_star := by linarith [hJ]
    _ = S / t := hfinal
    _ ≤ R * L * q := by
      rw [div_le_iff₀ ht]
      linarith [hS]

end randomized_coordinate_descent_bound
