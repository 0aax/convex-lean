import ConvexStarLib.Defs

/-!
# `minibatch_stochastic_gradient_descent_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/minibatch_stochastic_gradient_descent_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace minibatch_stochastic_gradient_descent_bound`, so the main result is `minibatch_stochastic_gradient_descent_bound.minibatch_stochastic_gradient_descent_bound`.
-/

namespace minibatch_stochastic_gradient_descent_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal RealInnerProductSpace

variable {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace MinibatchSGDAux

/-- Derivative of `f` along the line `τ ↦ x + τ • (y - x)`. -/
lemma hasDerivAt_along_line {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    {x y : EuclideanSpace ℝ (Fin n)} {t : ℝ}
    (hd : DifferentiableAt ℝ f (x + t • (y - x))) :
    HasDerivAt (fun τ : ℝ => f (x + τ • (y - x)))
      ⟪gradient f (x + t • (y - x)), y - x⟫ t := by
  have h1 : HasDerivAt (fun τ : ℝ => x + τ • (y - x)) (y - x) t := by
    simpa using ((hasDerivAt_id t).smul_const (y - x)).const_add x
  have h2 := hd.hasFDerivAt.comp_hasDerivAt t h1
  rw [inner_gradient_left hd]
  exact h2

/-- Lemma B: first-order condition for convex functions. -/
lemma convex_first_order {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hf : ConvexOn ℝ C f) {x y : EuclideanSpace ℝ (Fin n)} (hx : x ∈ C) (hy : y ∈ C)
    (hd : DifferentiableAt ℝ f x) :
    f x + ⟪gradient f x, y - x⟫ ≤ f y := by
  set phi : ℝ → ℝ := fun τ => f (x + τ • (y - x)) with hphi
  have hconv : ConvexOn ℝ (Set.Icc (0:ℝ) 1) phi := by
    refine ⟨convex_Icc 0 1, ?_⟩
    intro a ha b hb μ ν hμ hν hμν
    have hxa : x + a • (y - x) ∈ C := hf.1.add_smul_sub_mem hx hy ha
    have hxb : x + b • (y - x) ∈ C := hf.1.add_smul_sub_mem hx hy hb
    have key := hf.2 hxa hxb hμ hν hμν
    have heq : x + (μ • a + ν • b) • (y - x)
        = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
      obtain rfl : ν = 1 - μ := by linarith
      simp only [smul_eq_mul]
      module
    simp only [hphi, heq]
    exact key
  have hd0 : HasDerivAt phi ⟪gradient f x, y - x⟫ 0 := by
    have := hasDerivAt_along_line (f := f) (x := x) (y := y) (t := 0) (by simpa using hd)
    simpa using this
  have h := hconv.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
    (Set.right_mem_Icc.2 zero_le_one) zero_lt_one hd0
  rw [slope_def_field] at h
  simp [hphi] at h
  linarith

/-- Lemma C: descent lemma for functions with Lipschitz gradient on a convex set. -/
lemma smooth_descent {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : Convex ℝ C) {β : ℝ} (hβ : 0 ≤ β)
    (hL : LipschitzOnWith (Real.toNNReal β) (gradient f) C)
    (hd : ∀ z ∈ C, DifferentiableAt ℝ f z) {x y : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ C) (hy : y ∈ C) :
    f y ≤ f x + ⟪gradient f x, y - x⟫ + β / 2 * ‖y - x‖ ^ 2 := by
  set psi : ℝ → ℝ := fun τ => f (x + τ • (y - x)) - τ * ⟪gradient f x, y - x⟫
      - β / 2 * τ ^ 2 * ‖y - x‖ ^ 2 with hpsi
  set psi' : ℝ → ℝ := fun τ => ⟪gradient f (x + τ • (y - x)), y - x⟫ - ⟪gradient f x, y - x⟫
      - β * τ * ‖y - x‖ ^ 2 with hpsi'
  have hderiv : ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt psi (psi' τ) τ := by
    intro τ hτ
    have hmem : x + τ • (y - x) ∈ C := hC.add_smul_sub_mem hx hy hτ
    have h1 := hasDerivAt_along_line (hd _ hmem)
    have h2 : HasDerivAt (fun τ : ℝ => τ * ⟪gradient f x, y - x⟫) ⟪gradient f x, y - x⟫ τ := by
      simpa using (hasDerivAt_id τ).mul_const ⟪gradient f x, y - x⟫
    have h3 : HasDerivAt (fun τ : ℝ => β / 2 * τ ^ 2 * ‖y - x‖ ^ 2)
        (β * τ * ‖y - x‖ ^ 2) τ := by
      have := ((hasDerivAt_pow 2 τ).const_mul (β / 2)).mul_const (‖y - x‖ ^ 2)
      convert this using 1
      ring
    exact (h1.sub h2).sub h3
  have hnonpos : ∀ τ ∈ Set.Icc (0:ℝ) 1, psi' τ ≤ 0 := by
    intro τ hτ
    have hmem : x + τ • (y - x) ∈ C := hC.add_smul_sub_mem hx hy hτ
    have hlip : ‖gradient f (x + τ • (y - x)) - gradient f x‖ ≤ β * (τ * ‖y - x‖) := by
      have := hL.dist_le_mul _ hmem _ hx
      rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hβ] at this
      have e : x + τ • (y - x) - x = τ • (y - x) := by abel
      rw [e, norm_smul, Real.norm_of_nonneg hτ.1] at this
      exact this
    have hcs : ⟪gradient f (x + τ • (y - x)) - gradient f x, y - x⟫
        ≤ ‖gradient f (x + τ • (y - x)) - gradient f x‖ * ‖y - x‖ := real_inner_le_norm _ _
    rw [inner_sub_left] at hcs
    have hm := mul_le_mul_of_nonneg_right hlip (norm_nonneg (y - x))
    simp only [hpsi']
    nlinarith [norm_nonneg (y - x)]
  have hanti : AntitoneOn psi (Set.Icc (0:ℝ) 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) (f' := psi')
    · intro τ hτ
      exact (hderiv τ hτ).continuousAt.continuousWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact (hderiv τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
    · intro τ hτ
      rw [interior_Icc] at hτ
      exact hnonpos τ (Set.Ioo_subset_Icc_self hτ)
  have h01 := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
    zero_le_one
  simp only [hpsi] at h01
  simp at h01
  linarith

/-- Auxiliary: for a probability measure under which `X` and `Y` are independent bounded random
vectors, the expectation of the inner product is the inner product of the expectations. -/
lemma integral_inner_of_indepFun_aux {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {ν : Measure Ω} [IsProbabilityMeasure ν]
    {n : ℕ} {X Y : Ω → EuclideanSpace ℝ (Fin n)} (hX : Measurable X) (hY : Measurable Y)
    {B : ℝ} (hXB : ∀ ω, ‖X ω‖ ≤ B) (hYB : ∀ ω, ‖Y ω‖ ≤ B)
    (hXY : ProbabilityTheory.IndepFun X Y ν) :
    ∫ ω, ⟪X ω, Y ω⟫ ∂ν = ⟪∫ ω, X ω ∂ν, ∫ ω, Y ω ∂ν⟫ := by
  have hXi : Integrable X ν :=
    Integrable.of_bound hX.aestronglyMeasurable B (Filter.Eventually.of_forall hXB)
  have hYi : Integrable Y ν :=
    Integrable.of_bound hY.aestronglyMeasurable B (Filter.Eventually.of_forall hYB)
  have hXk : ∀ k, Integrable (fun ω => (X ω).ofLp k) ν := Integrable.eval_piLp hXi
  have hYk : ∀ k, Integrable (fun ω => (Y ω).ofLp k) ν := Integrable.eval_piLp hYi
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [eval_integral_piLp hXk, eval_integral_piLp hYk]
    exact hXY.symm.integral_fun_comp_mul_comp hY.aemeasurable hX.aemeasurable
      (f := fun y : EuclideanSpace ℝ (Fin n) => y.ofLp k)
      (g := fun x : EuclideanSpace ℝ (Fin n) => x.ofLp k)
      (by fun_prop) (by fun_prop)
  · intro k _
    refine (hXk k).bdd_mul (c := B) ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (hYk k).aestronglyMeasurable
    · exact (PiLp.norm_apply_le (Y ω) k).trans (hYB ω)

/-- Lemma P2: cross term for conditionally independent bounded random vectors. -/
lemma integral_inner_of_condIndepFun {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {n : ℕ} {X Y : Ω → EuclideanSpace ℝ (Fin n)} (hX : Measurable X) (hY : Measurable Y)
    {B : ℝ} (hXB : ∀ ω, ‖X ω‖ ≤ B) (hYB : ∀ ω, ‖Y ω‖ ≤ B)
    (hXY : ProbabilityTheory.CondIndepFun m hm X Y μ) :
    ∫ ω, ⟪X ω, Y ω⟫ ∂μ = ∫ ω, ⟪(μ[X|m]) ω, (μ[Y|m]) ω⟫ ∂μ := by
  -- conditional independence gives independence under `condExpKernel μ m ω` for a.e. `ω`
  have h_ae : ∀ᵐ ω ∂μ,
      ProbabilityTheory.IndepFun X Y (ProbabilityTheory.condExpKernel μ m ω) := by
    have h1 := (ProbabilityTheory.condIndepFun_iff_map_prod_eq_prod_map_map hX hY).1 hXY
    refine ae_of_ae_trim hm ?_
    filter_upwards [h1] with ω hω
    rw [ProbabilityTheory.Kernel.map_apply _ (hX.prodMk hY), ProbabilityTheory.Kernel.prod_apply,
      ProbabilityTheory.Kernel.map_apply _ hX, ProbabilityTheory.Kernel.map_apply _ hY] at hω
    exact (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable
      hY.aemeasurable).2 hω
  have hXi : Integrable X μ :=
    Integrable.of_bound hX.aestronglyMeasurable B (Filter.Eventually.of_forall hXB)
  have hYi : Integrable Y μ :=
    Integrable.of_bound hY.aestronglyMeasurable B (Filter.Eventually.of_forall hYB)
  have hXYi : Integrable (fun ω => ⟪X ω, Y ω⟫) μ := by
    refine Integrable.of_bound (hX.inner hY).aestronglyMeasurable (B * B)
      (Filter.Eventually.of_forall fun ω => ?_)
    calc ‖⟪X ω, Y ω⟫‖ ≤ ‖X ω‖ * ‖Y ω‖ := norm_inner_le_norm _ _
      _ ≤ B * B := mul_le_mul (hXB ω) (hYB ω) (norm_nonneg _) ((norm_nonneg _).trans (hXB ω))
  -- conditional expectations as integrals against the conditional expectation kernel
  have hcX := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hXi
  have hcY := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hYi
  have hcXY := ProbabilityTheory.condExp_ae_eq_integral_condExpKernel hm hXYi
  rw [← integral_condExp hm]
  refine integral_congr_ae ?_
  filter_upwards [h_ae, hcX, hcY, hcXY] with ω hω h1 h2 h3
  rw [h1, h2, h3]
  exact integral_inner_of_indepFun_aux hX hY hXB hYB hω

/-- Lemma A: variational inequality for projections onto convex sets. -/
lemma proj_inner_le {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} (hC : Convex ℝ C)
    {y w z : EuclideanSpace ℝ (Fin n)} (hw : w ∈ projectionMapping C y) (hz : z ∈ C) :
    ⟪y - w, z - w⟫ ≤ 0 := by
  have hwC : w ∈ C := hw.1
  haveI : Nonempty C := ⟨⟨w, hwC⟩⟩
  have heq : ‖y - w‖ = ⨅ v : C, ‖y - v‖ := by
    apply le_antisymm
    · apply le_ciInf
      intro v
      rw [norm_sub_rev y w, norm_sub_rev y v]
      exact hw.2 v v.2
    · have hbdd : BddBelow (Set.range fun v : C => ‖y - (v : EuclideanSpace ℝ (Fin n))‖) := by
        refine ⟨0, ?_⟩
        rintro _ ⟨v, rfl⟩
        exact norm_nonneg _
      exact ciInf_le hbdd ⟨w, hwC⟩
  exact (norm_eq_iInf_iff_real_inner_le_zero hC hwC).1 heq z hz

/-- Lemma D: one step of projected (stochastic) gradient descent. -/
lemma one_step {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))} {f : EuclideanSpace ℝ (Fin n) → ℝ}
    (hC : Convex ℝ C) (hfc : ConvexOn ℝ C f) {β η : ℝ} (hβ : 0 < β) (hη : 0 < η)
    (hL : LipschitzOnWith (Real.toNNReal β) (gradient f) C)
    (hd : ∀ z ∈ C, DifferentiableAt ℝ f z) {a b xs G : EuclideanSpace ℝ (Fin n)}
    (ha : a ∈ C) (hxs : xs ∈ C)
    (hb : b ∈ projectionMapping C (a - (1 / (β + 1 / η)) • G)) :
    f b - f xs ≤ (β + 1 / η) / 2 * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2)
      + η / 2 * ‖gradient f a - G‖ ^ 2 + ⟪gradient f a - G, a - xs⟫ := by
  have hbC : b ∈ C := hb.1
  have h1 := convex_first_order hfc ha hxs (hd a ha)
  have h2 := smooth_descent hC hβ.le hL hd ha hbC
  have h3 := proj_inner_le hC hb hxs
  set c := β + 1 / η with hc
  have hc_pos : 0 < c := by positivity
  set d := gradient f a - G with hd_def
  have hyoung : ⟪d, b - a⟫ ≤ η / 2 * ‖d‖ ^ 2 + 1 / (2 * η) * ‖b - a‖ ^ 2 := by
    have k1 := real_inner_le_norm d (b - a)
    have k2 : ‖d‖ * ‖b - a‖ ≤ η / 2 * ‖d‖ ^ 2 + 1 / (2 * η) * ‖b - a‖ ^ 2 := by
      rw [show η / 2 * ‖d‖ ^ 2 + 1 / (2 * η) * ‖b - a‖ ^ 2
          = ((η * ‖d‖) ^ 2 + ‖b - a‖ ^ 2) / (2 * η) by field_simp]
      rw [le_div_iff₀ (by positivity)]
      nlinarith [sq_nonneg (η * ‖d‖ - ‖b - a‖)]
    linarith
  -- expand the projection inequality
  have I1 : ⟪a - (1 / c) • G - b, xs - b⟫ = ⟪a - b, xs - b⟫ - (1 / c) * ⟪G, xs - b⟫ := by
    rw [show a - (1 / c) • G - b = (a - b) - (1 / c) • G by abel, inner_sub_left,
      real_inner_smul_left]
  have I2 : ⟪a - b, xs - b⟫ = -(1 / 2) * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2 - ‖b - a‖ ^ 2) := by
    have e1 : a - xs = (a - b) + (b - xs) := by abel
    have e2 : xs - b = -(b - xs) := by abel
    have e3 : ‖b - a‖ = ‖a - b‖ := norm_sub_rev b a
    rw [e1, norm_add_sq_real, e2, inner_neg_right, e3]
    ring
  have I3 : ⟪G, xs - b⟫ = -⟪G, b - xs⟫ := by
    rw [show xs - b = -(b - xs) by abel, inner_neg_right]
  have hG : ⟪G, b - xs⟫ ≤ c / 2 * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2 - ‖b - a‖ ^ 2) := by
    rw [I1, I2, I3] at h3
    have h4 : (1 / c) * ⟪G, b - xs⟫ ≤ (1 / 2) * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2 - ‖b - a‖ ^ 2) := by
      linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hc_pos.le
    rw [← mul_assoc, mul_one_div_cancel hc_pos.ne', one_mul] at h5
    linarith
  have I5 : ⟪gradient f a, b - a⟫ + ⟪gradient f a, a - xs⟫ = ⟪gradient f a, b - xs⟫ := by
    rw [← inner_add_right]; congr 1; abel
  have I4 : ⟪gradient f a, xs - a⟫ = -⟪gradient f a, a - xs⟫ := by
    rw [show xs - a = -(a - xs) by abel, inner_neg_right]
  have I6 : ⟪gradient f a, b - xs⟫ = ⟪G, b - xs⟫ + ⟪d, b - a⟫ + ⟪d, a - xs⟫ := by
    have : ⟪d, b - a⟫ + ⟪d, a - xs⟫ = ⟪d, b - xs⟫ := by
      rw [← inner_add_right]; congr 1; abel
    rw [add_assoc, this, hd_def, inner_sub_left]
    ring
  have I7 : c / 2 * ‖b - a‖ ^ 2 = β / 2 * ‖b - a‖ ^ 2 + 1 / (2 * η) * ‖b - a‖ ^ 2 := by
    rw [hc]; field_simp
  have I8 : c / 2 * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2 - ‖b - a‖ ^ 2)
      = c / 2 * (‖a - xs‖ ^ 2 - ‖b - xs‖ ^ 2) - c / 2 * ‖b - a‖ ^ 2 := by ring
  linarith

/-- Lemma P1: pull-out property, integrated. -/
lemma integral_inner_eq_of_condExp {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsFiniteMeasure μ] (hm : m ≤ mΩ) {n : ℕ}
    {W g h : Ω → EuclideanSpace ℝ (Fin n)}
    (hW : StronglyMeasurable[m] W) (hg : Integrable g μ)
    (hWg : Integrable (fun ω => ⟪g ω, W ω⟫) μ)
    (hgh : μ[g|m] =ᵐ[μ] h) :
    ∫ ω, ⟪g ω, W ω⟫ ∂μ = ∫ ω, ⟪h ω, W ω⟫ ∂μ := by
  have hWg' : Integrable (fun ω => innerSL ℝ (W ω) (g ω)) μ := by
    simpa [innerSL_apply_apply, real_inner_comm] using hWg
  have h1 := condExp_bilin_of_aestronglyMeasurable_left (innerSL ℝ) (m := m)
    hW.aestronglyMeasurable hWg' hg
  calc ∫ ω, ⟪g ω, W ω⟫ ∂μ = ∫ ω, innerSL ℝ (W ω) (g ω) ∂μ := by
        simp [innerSL_apply_apply, real_inner_comm]
    _ = ∫ ω, (μ[fun ω => innerSL ℝ (W ω) (g ω)|m]) ω ∂μ := (integral_condExp hm).symm
    _ = ∫ ω, innerSL ℝ (W ω) ((μ[g|m]) ω) ∂μ := integral_congr_ae h1
    _ = ∫ ω, ⟪h ω, W ω⟫ ∂μ := by
        refine integral_congr_ae ?_
        filter_upwards [hgh] with ω hω
        simp [innerSL_apply_apply, hω, real_inner_comm]

lemma integrable_inner_of_bound {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {n : ℕ} {u v : Ω → EuclideanSpace ℝ (Fin n)} {Cu Cv : ℝ}
    (hu : Measurable u) (hv : Measurable v) (hCu : ∀ ω, ‖u ω‖ ≤ Cu) (hCv : ∀ ω, ‖v ω‖ ≤ Cv) :
    Integrable (fun ω => ⟪u ω, v ω⟫) μ := by
  refine Integrable.of_bound (hu.inner hv).aestronglyMeasurable (Cu * Cv) (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs]
  calc |⟪u ω, v ω⟫| ≤ ‖u ω‖ * ‖v ω‖ := abs_real_inner_le_norm _ _
    _ ≤ Cu * Cv := mul_le_mul (hCu ω) (hCv ω) (norm_nonneg _) ((norm_nonneg _).trans (hCu ω))

/-- Lemma P3: variance bound for the minibatch average. -/
lemma variance_bound {Ω : Type*} {m : MeasurableSpace Ω} {mΩ : MeasurableSpace Ω}
    [StandardBorelSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ] (hm : m ≤ mΩ)
    {n M : ℕ} (hM : 0 < M) {g : Fin M → Ω → EuclideanSpace ℝ (Fin n)}
    {h : Ω → EuclideanSpace ℝ (Fin n)}
    (hg : ∀ i, Measurable (g i)) {B : ℝ} (hgB : ∀ i ω, ‖g i ω‖ ≤ B)
    (hh : StronglyMeasurable[m] h) {K : ℝ} (hhB : ∀ ω, ‖h ω‖ ≤ K)
    (hindep : ProbabilityTheory.iCondIndepFun m hm g μ)
    (hunb : ∀ i, μ[g i|m] =ᵐ[μ] h) :
    ∫ ω, ‖h ω - (1 / (M : ℝ)) • ∑ i, g i ω‖ ^ 2 ∂μ ≤ B ^ 2 / M := by
  have hhm : Measurable h := (hh.mono hm).measurable
  have hint_g : ∀ i, Integrable (g i) μ := fun i =>
    Integrable.of_bound (hg i).aestronglyMeasurable B (ae_of_all _ (hgB i))
  have hgh : ∀ i, ∫ ω, ⟪g i ω, h ω⟫ ∂μ = ∫ ω, ⟪h ω, h ω⟫ ∂μ := fun i =>
    integral_inner_eq_of_condExp hm hh (hint_g i)
      (integrable_inner_of_bound (hg i) hhm (hgB i) hhB) (hunb i)
  have hgg : ∀ i j, i ≠ j → ∫ ω, ⟪g i ω, g j ω⟫ ∂μ = ∫ ω, ⟪h ω, h ω⟫ ∂μ := by
    intro i j hij
    rw [integral_inner_of_condIndepFun hm (hg i) (hg j) (hgB i) (hgB j)
      (hindep.condIndepFun hij)]
    refine integral_congr_ae ?_
    filter_upwards [hunb i, hunb j] with ω hi hj
    rw [hi, hj]
  have hpair : ∀ i j, ∫ ω, ⟪h ω - g i ω, h ω - g j ω⟫ ∂μ ≤ if i = j then B ^ 2 else 0 := by
    intro i j
    have e : ∀ ω, ⟪h ω - g i ω, h ω - g j ω⟫
        = ⟪h ω, h ω⟫ - ⟪g j ω, h ω⟫ - ⟪g i ω, h ω⟫ + ⟪g i ω, g j ω⟫ := by
      intro ω
      simp only [inner_sub_left, inner_sub_right, real_inner_comm]
      ring
    simp_rw [e]
    have i1 := integrable_inner_of_bound (μ := μ) hhm hhm hhB hhB
    have i2 := integrable_inner_of_bound (μ := μ) (hg j) hhm (hgB j) hhB
    have i3 := integrable_inner_of_bound (μ := μ) (hg i) hhm (hgB i) hhB
    have i4 := integrable_inner_of_bound (μ := μ) (hg i) (hg j) (hgB i) (hgB j)
    have i12 : Integrable (fun ω => ⟪h ω, h ω⟫ - ⟪g j ω, h ω⟫) μ := i1.sub i2
    have i123 : Integrable (fun ω => ⟪h ω, h ω⟫ - ⟪g j ω, h ω⟫ - ⟪g i ω, h ω⟫) μ := i12.sub i3
    rw [integral_add i123 i4, integral_sub i12 i3, integral_sub i1 i2, hgh i, hgh j]
    split_ifs with hij
    · subst hij
      have k1 : ∫ ω, ⟪g i ω, g i ω⟫ ∂μ ≤ B ^ 2 := by
        have : ∫ ω, ⟪g i ω, g i ω⟫ ∂μ ≤ ∫ ω, B ^ 2 ∂μ := by
          refine integral_mono i4 (integrable_const _) (fun ω => ?_)
          simp only [real_inner_self_eq_norm_sq]
          have := hgB i ω
          have := norm_nonneg (g i ω)
          nlinarith
        simpa using this
      have k2 : 0 ≤ ∫ ω, ⟪h ω, h ω⟫ ∂μ :=
        integral_nonneg (fun ω => real_inner_self_nonneg)
      linarith
    · rw [hgg i j hij]
      linarith
  have hMpos : (0 : ℝ) < M := Nat.cast_pos.mpr hM
  have hsq : ∀ (v : Fin M → EuclideanSpace ℝ (Fin n)),
      ‖∑ i, v i‖ ^ 2 = ∑ i, ∑ j, ⟪v i, v j⟫ := by
    intro v
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hrepr : ∀ ω, ‖h ω - (1 / (M : ℝ)) • ∑ i, g i ω‖ ^ 2
      = (1 / (M : ℝ)) ^ 2 * ∑ i, ∑ j, ⟪h ω - g i ω, h ω - g j ω⟫ := by
    intro ω
    have e1 : h ω - (1 / (M : ℝ)) • ∑ i, g i ω = (1 / (M : ℝ)) • ∑ i, (h ω - g i ω) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_sub,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, one_div_mul_cancel hMpos.ne', one_smul]
    rw [e1, norm_smul, mul_pow, hsq, Real.norm_eq_abs, sq_abs]
  have hint_pair : ∀ i j, Integrable (fun ω => ⟪h ω - g i ω, h ω - g j ω⟫) μ := fun i j =>
    integrable_inner_of_bound (hhm.sub (hg i)) (hhm.sub (hg j))
      (fun ω => (norm_sub_le _ _).trans (add_le_add (hhB ω) (hgB i ω)))
      (fun ω => (norm_sub_le _ _).trans (add_le_add (hhB ω) (hgB j ω)))
  simp_rw [hrepr]
  rw [integral_const_mul, integral_finset_sum _ (fun i _ => integrable_finset_sum _
    (fun j _ => hint_pair i j))]
  simp_rw [integral_finset_sum _ (fun j _ => hint_pair _ j)]
  calc (1 / (M : ℝ)) ^ 2 * ∑ i, ∑ j, ∫ ω, ⟪h ω - g i ω, h ω - g j ω⟫ ∂μ
      ≤ (1 / (M : ℝ)) ^ 2 * ∑ i : Fin M, ∑ j : Fin M, (if i = j then B ^ 2 else 0) := by
        gcongr with i _ j _
        exact hpair i j
    _ = B ^ 2 / M := by
        simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp

end MinibatchSGDAux

set_option linter.unusedVariables false in
open MinibatchSGDAux in
theorem minibatch_stochastic_gradient_descent_bound
  {m n t : ℕ}
  {Ω : Type*}
  [MeasurableSpace Ω]
  [StandardBorelSpace Ω]
  (μ : Measure Ω)
  [IsProbabilityMeasure μ]
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (β B R : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (x0 : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hR_sq : R ^ 2 = sSup {v | ∃ a ∈ 𝓧, 1 / 2 * (‖a‖ ^ 2 - ‖x0‖ ^ 2) = v})
  (hR_pos : R > 0)
  (hB_pos : B > 0)
  (hβ_pos : β > 0)
  (ht_pos : t > 0)
  (hm_pos : m > 0)
  (h_minibatch_sgd_seq :
    let σ := Real.sqrt ((2 * B ^ 2) / (m : ℝ))
    let η := (R / σ) * Real.sqrt (2 / (t : ℝ))
    IsMinibatchStochasticGradientDescentSequence m 𝓧 x g (1 / (β + (1 / η))))
  (hx_meas : ∀ s, Measurable (x s))
  (hg_meas : ∀ s i, Measurable (g s i))
  (hg_bound : ∀ s i ω, ‖g s i ω‖ ≤ B)
  (hg_unbiased : ∀ s i,
    μ[g s i | MeasurableSpace.comap (x s) inferInstance] =ᵐ[μ] fun ω => gradient f (x s ω))
  (hg_indep : ∀ s,
    ProbabilityTheory.iCondIndepFun (MeasurableSpace.comap (x s) inferInstance)
      (hx_meas s).comap_le (fun (i : Fin m) => g s i) μ)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_smooth : LipschitzOnWith (Real.toNNReal β) (gradient f) 𝓧)
  (hf_differentiable : ∀ z ∈ 𝓧, DifferentiableAt ℝ f z)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star)
  (hf_ae_comp : ∀ s, AEMeasurable (fun ω => f (x s ω)) μ)
  (havg_succ_ae :
    AEMeasurable
      (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)) μ) :
  ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f x_star ≤
  (2 * R * B) / (Real.sqrt (m * t : ℝ)) + (β * R ^ 2) / (t : ℝ) := by
  classical
  have hm_real : (0:ℝ) < m := Nat.cast_pos.mpr hm_pos
  have ht_real : (0:ℝ) < t := Nat.cast_pos.mpr ht_pos
  dsimp only [IsMinibatchStochasticGradientDescentSequence] at h_minibatch_sgd_seq
  obtain ⟨-, hx0mem, hx0min, hproj⟩ := h_minibatch_sgd_seq
  set σ : ℝ := Real.sqrt ((2 * B ^ 2) / (m : ℝ)) with hσ_def
  set q : ℝ := Real.sqrt (2 / (t : ℝ)) with hq_def
  set η : ℝ := (R / σ) * q with hη_def
  have hσ_pos : 0 < σ := Real.sqrt_pos.mpr (by positivity)
  have hq_pos : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hη_pos : 0 < η := by positivity
  set c : ℝ := β + 1 / η with hc_def
  have hc_pos : 0 < c := by positivity
  -- all iterates lie in 𝓧
  have hxmem : ∀ s ω, x s ω ∈ 𝓧 := by
    intro s ω
    cases s with
    | zero => exact hx0mem ω
    | succ s => exact (hproj s ω).1
  -- bounds on 𝓧
  obtain ⟨D, hD⟩ := h𝓧_compact.isBounded.exists_norm_le
  obtain ⟨K, hK⟩ := h𝓧_compact.exists_bound_of_continuousOn hf_smooth.continuousOn
  have hf_cont : ContinuousOn f 𝓧 := fun z hz =>
    (hf_differentiable z hz).continuousAt.continuousWithinAt
  obtain ⟨Cf, hCf⟩ := h𝓧_compact.exists_bound_of_continuousOn hf_cont
  -- measurability of the gradient
  have hgrad_meas : Measurable (gradient f) := by
    have h1 : Measurable (fderiv ℝ f) := measurable_fderiv ℝ f
    exact (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous.measurable.comp h1
  -- minibatch average and noise
  set G : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun s ω => (1 / (m : ℝ)) • ∑ i, g s i ω
    with hG_def
  set d : ℕ → Ω → EuclideanSpace ℝ (Fin n) := fun s ω => gradient f (x s ω) - G s ω
    with hd_def
  have hG_bound : ∀ s ω, ‖G s ω‖ ≤ B := by
    intro s ω
    simp only [hG_def]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    calc 1 / (m : ℝ) * ‖∑ i, g s i ω‖ ≤ 1 / (m : ℝ) * ∑ i : Fin m, ‖g s i ω‖ := by
          gcongr; exact norm_sum_le _ _
      _ ≤ 1 / (m : ℝ) * ∑ i : Fin m, B := by
          gcongr with i; exact hg_bound s i ω
      _ = B := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
  have hd_bound : ∀ s ω, ‖d s ω‖ ≤ K + B := fun s ω =>
    (norm_sub_le _ _).trans (add_le_add (hK _ (hxmem s ω)) (hG_bound s ω))
  have hW_bound : ∀ s ω, ‖x s ω - x_star‖ ≤ D + D := fun s ω =>
    (norm_sub_le _ _).trans (add_le_add (hD _ (hxmem s ω)) (hD _ hx_star_mem))
  have hG_meas : ∀ s, Measurable (G s) := by
    intro s
    show Measurable (fun ω => (1 / (m : ℝ)) • ∑ i, g s i ω)
    exact (Finset.measurable_sum _ (fun i _ => hg_meas s i)).const_smul (1 / (m : ℝ))
  have hd_meas : ∀ s, Measurable (d s) := fun s =>
    (hgrad_meas.comp (hx_meas s)).sub (hG_meas s)
  -- one step
  have hstep : ∀ s ω, f (x (s + 1) ω) - f x_star ≤
      c / 2 * (‖x s ω - x_star‖ ^ 2 - ‖x (s + 1) ω - x_star‖ ^ 2)
        + η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫ := by
    intro s ω
    have hb := hproj s ω
    have e : (1 / c / (m : ℝ)) • ∑ i, g s i ω = (1 / c) • G s ω := by
      simp only [hG_def, smul_smul]
      congr 1
      ring
    rw [e] at hb
    exact one_step h𝓧_convex hf_convex hβ_pos hη_pos hf_smooth hf_differentiable
      (hxmem s ω) hx_star_mem hb
  -- telescoping
  have hsum : ∀ ω, ∑ s ∈ Finset.range t, (f (x (s + 1) ω) - f x_star) ≤
      c / 2 * ‖x0 - x_star‖ ^ 2
        + ∑ s ∈ Finset.range t, (η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫) := by
    intro ω
    have h1 := Finset.sum_le_sum (fun s (_ : s ∈ Finset.range t) => hstep s ω)
    have h2 : ∑ s ∈ Finset.range t,
        c / 2 * (‖x s ω - x_star‖ ^ 2 - ‖x (s + 1) ω - x_star‖ ^ 2)
        = c / 2 * ‖x 0 ω - x_star‖ ^ 2 - c / 2 * ‖x t ω - x_star‖ ^ 2 := by
      rw [← Finset.mul_sum, Finset.sum_range_sub' (fun s => ‖x s ω - x_star‖ ^ 2)]
      ring
    have h3 : 0 ≤ c / 2 * ‖x t ω - x_star‖ ^ 2 := by positivity
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h2, hx0 ω] at h1
    rw [Finset.sum_add_distrib]
    linarith
  -- Jensen
  have hw_sum : ∑ _s ∈ Finset.range t, (1 / (t : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have havg_mem : ∀ ω, (1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω ∈ 𝓧 := by
    intro ω
    rw [Finset.smul_sum]
    exact h𝓧_convex.sum_mem (fun _ _ => by positivity) hw_sum (fun s _ => hxmem (s + 1) ω)
  have hjensen : ∀ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)
      ≤ (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (x (s + 1) ω) := by
    intro ω
    have h := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t : ℝ))
      (p := fun s => x (s + 1) ω) (fun _ _ => by positivity) hw_sum
      (fun s _ => hxmem (s + 1) ω)
    simp only [smul_eq_mul] at h
    rw [Finset.smul_sum, Finset.mul_sum]
    exact h
  -- pointwise bound
  have hpt : ∀ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f x_star ≤
      (1 / (t : ℝ)) * (c / 2 * ‖x0 - x_star‖ ^ 2
        + ∑ s ∈ Finset.range t, (η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫)) := by
    intro ω
    have h1 := hjensen ω
    have h2 := hsum ω
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h2
    have h3 : (1 / (t : ℝ)) * (∑ s ∈ Finset.range t, f (x (s + 1) ω) - t * f x_star)
        = (1 / (t : ℝ)) * ∑ s ∈ Finset.range t, f (x (s + 1) ω) - f x_star := by
      field_simp
    have h4 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 1 / (t : ℝ))
    linarith
  -- integrability
  have hint_avg : Integrable (fun ω => f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω)) μ :=
    Integrable.of_bound havg_succ_ae.aestronglyMeasurable Cf
      (ae_of_all _ fun ω => hCf _ (havg_mem ω))
  have hint_sq : ∀ s, Integrable (fun ω => ‖d s ω‖ ^ 2) μ := fun s =>
    Integrable.of_bound ((hd_meas s).norm.pow_const 2).aestronglyMeasurable ((K + B) ^ 2)
      (ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (hd_bound s ω) 2)
  have hint_in : ∀ s, Integrable (fun ω => ⟪d s ω, x s ω - x_star⟫) μ := fun s =>
    integrable_inner_of_bound (hd_meas s) ((hx_meas s).sub_const _) (hd_bound s) (hW_bound s)
  -- the noise term has mean zero
  have hE1 : ∀ s, ∫ ω, ⟪d s ω, x s ω - x_star⟫ ∂μ = 0 := by
    intro s
    have hWm : StronglyMeasurable[MeasurableSpace.comap (x s) inferInstance]
        (fun ω => x s ω - x_star) :=
      ((Measurable.of_comap_le le_rfl).sub_const x_star).stronglyMeasurable
    have hgi : ∀ i, ∫ ω, ⟪g s i ω, x s ω - x_star⟫ ∂μ
        = ∫ ω, ⟪gradient f (x s ω), x s ω - x_star⟫ ∂μ := fun i =>
      integral_inner_eq_of_condExp (hx_meas s).comap_le hWm
        (Integrable.of_bound (hg_meas s i).aestronglyMeasurable B (ae_of_all _ (hg_bound s i)))
        (integrable_inner_of_bound (hg_meas s i) ((hx_meas s).sub_const _) (hg_bound s i)
          (hW_bound s)) (hg_unbiased s i)
    have e : ∀ ω, ⟪d s ω, x s ω - x_star⟫ = ⟪gradient f (x s ω), x s ω - x_star⟫
        - (1 / (m : ℝ)) * ∑ i, ⟪g s i ω, x s ω - x_star⟫ := by
      intro ω
      simp only [hd_def, hG_def, inner_sub_left, real_inner_smul_left, sum_inner]
    have i1 : Integrable (fun ω => ⟪gradient f (x s ω), x s ω - x_star⟫) μ :=
      integrable_inner_of_bound (hgrad_meas.comp (hx_meas s)) ((hx_meas s).sub_const _)
        (fun ω => hK _ (hxmem s ω)) (hW_bound s)
    have i2 : ∀ i, Integrable (fun ω => ⟪g s i ω, x s ω - x_star⟫) μ := fun i =>
      integrable_inner_of_bound (hg_meas s i) ((hx_meas s).sub_const _) (hg_bound s i)
        (hW_bound s)
    have i3 : Integrable (fun ω => (1 / (m : ℝ)) * ∑ i, ⟪g s i ω, x s ω - x_star⟫) μ :=
      (integrable_finset_sum _ (fun i _ => i2 i)).const_mul _
    simp_rw [e]
    rw [integral_sub i1 i3, integral_const_mul, integral_finset_sum _ (fun i _ => i2 i)]
    rw [Finset.sum_congr rfl (fun i _ => hgi i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    have : (1 / (m : ℝ)) * ((m : ℝ) * ∫ ω, ⟪gradient f (x s ω), x s ω - x_star⟫ ∂μ)
        = ∫ ω, ⟪gradient f (x s ω), x s ω - x_star⟫ ∂μ := by
      field_simp
    rw [this, sub_self]
  -- variance bound
  have hE2 : ∀ s, ∫ ω, ‖d s ω‖ ^ 2 ∂μ ≤ B ^ 2 / m := by
    intro s
    have hh : StronglyMeasurable[MeasurableSpace.comap (x s) inferInstance]
        (fun ω => gradient f (x s ω)) :=
      (hgrad_meas.comp (Measurable.of_comap_le le_rfl)).stronglyMeasurable
    exact variance_bound (hx_meas s).comap_le hm_pos (fun i => hg_meas s i) (hg_bound s) hh
      (fun ω => hK _ (hxmem s ω)) (hg_indep s) (hg_unbiased s)
  -- distance from x0 to x_star
  have hx0_dist : ‖x0 - x_star‖ ^ 2 ≤ 2 * R ^ 2 := by
    obtain ⟨ω₀⟩ := nonempty_of_isProbabilityMeasure μ
    have hx0C : x0 ∈ 𝓧 := hx0 ω₀ ▸ hx0mem ω₀
    have hproj0 : x0 ∈ projectionMapping 𝓧 0 := by
      refine ⟨hx0C, fun z hz => ?_⟩
      have hmin := isMinOn_iff.mp (hx0min ω₀) z hz
      rw [hx0 ω₀] at hmin
      simp only [sub_zero]
      have : ‖x0‖ ^ 2 ≤ ‖z‖ ^ 2 := by linarith
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
    have hin := proj_inner_le h𝓧_convex hproj0 hx_star_mem
    have hbdd : BddAbove {v | ∃ a ∈ 𝓧, 1 / 2 * (‖a‖ ^ 2 - ‖x0‖ ^ 2) = v} := by
      refine ⟨1 / 2 * D ^ 2, ?_⟩
      rintro v ⟨a, ha, rfl⟩
      have h1 : ‖a‖ ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hD a ha) 2
      have h2 : 0 ≤ ‖x0‖ ^ 2 := by positivity
      linarith
    have hle : 1 / 2 * (‖x_star‖ ^ 2 - ‖x0‖ ^ 2) ≤ R ^ 2 := by
      rw [hR_sq]
      exact le_csSup hbdd ⟨x_star, hx_star_mem, rfl⟩
    have e1 : ‖x0 - x_star‖ ^ 2 = ‖x0‖ ^ 2 - 2 * ⟪x0, x_star⟫ + ‖x_star‖ ^ 2 :=
      norm_sub_sq_real x0 x_star
    have e2 : ⟪0 - x0, x_star - x0⟫ = -⟪x0, x_star⟫ + ‖x0‖ ^ 2 := by
      rw [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq]
      ring
    linarith
  -- integrate the pointwise bound
  have hterm : ∀ s, Integrable (fun ω => η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫) μ :=
    fun s => ((hint_sq s).const_mul _).add (hint_in s)
  have hsum_int : Integrable (fun ω => ∑ s ∈ Finset.range t,
      (η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫)) μ :=
    integrable_finset_sum _ (fun s _ => hterm s)
  have hint_rhs : Integrable (fun ω => (1 / (t : ℝ)) * (c / 2 * ‖x0 - x_star‖ ^ 2
      + ∑ s ∈ Finset.range t, (η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫))) μ :=
    ((integrable_const _).add (integrable_finset_sum _
      (fun s _ => ((hint_sq s).const_mul _).add (hint_in s)))).const_mul _
  have hmain : ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f x_star
      ≤ c * R ^ 2 / t + η * B ^ 2 / (2 * m) := by
    have hlhs : ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f x_star
        = ∫ ω, (f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f x_star) ∂μ := by
      rw [integral_sub hint_avg (integrable_const _), integral_const]
      simp
    rw [hlhs]
    calc ∫ ω, (f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) - f x_star) ∂μ
        ≤ ∫ ω, (1 / (t : ℝ)) * (c / 2 * ‖x0 - x_star‖ ^ 2
          + ∑ s ∈ Finset.range t, (η / 2 * ‖d s ω‖ ^ 2 + ⟪d s ω, x s ω - x_star⟫)) ∂μ :=
          integral_mono (hint_avg.sub (integrable_const _)) hint_rhs hpt
      _ = (1 / (t : ℝ)) * (c / 2 * ‖x0 - x_star‖ ^ 2
          + ∑ s ∈ Finset.range t, (η / 2 * ∫ ω, ‖d s ω‖ ^ 2 ∂μ
            + ∫ ω, ⟪d s ω, x s ω - x_star⟫ ∂μ)) := by
          rw [integral_const_mul, integral_add (integrable_const _) hsum_int, integral_const,
            integral_finset_sum _ (fun s _ => hterm s)]
          congr 2
          · simp
          · refine Finset.sum_congr rfl (fun s _ => ?_)
            rw [integral_add ((hint_sq s).const_mul _) (hint_in s), integral_const_mul]
      _ ≤ (1 / (t : ℝ)) * (c / 2 * (2 * R ^ 2)
          + ∑ s ∈ Finset.range t, (η / 2 * (B ^ 2 / m) + 0)) := by
          gcongr with s hs
          · exact hE2 s
          · exact (hE1 s).le
      _ = c * R ^ 2 / t + η * B ^ 2 / (2 * m) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          field_simp
          ring
  -- final algebra
  have hσsq : σ ^ 2 = 2 * B ^ 2 / m := Real.sq_sqrt (by positivity)
  have hqsq : q ^ 2 = 2 / t := Real.sq_sqrt (by positivity)
  have hS_pos : 0 < Real.sqrt (m * t : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hSsq : Real.sqrt (m * t : ℝ) ^ 2 = m * t := Real.sq_sqrt (by positivity)
  have hkey : σ * q * Real.sqrt (m * t : ℝ) = 2 * B := by
    have h1 : (σ * q * Real.sqrt (m * t : ℝ)) ^ 2 = (2 * B) ^ 2 := by
      rw [mul_pow, mul_pow, hσsq, hqsq, hSsq]
      field_simp
    exact (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).mp h1
  have hqt : q * q * t = 2 := by
    rw [← sq, hqsq]
    field_simp
  have hA : R ^ 2 / (η * t) = R * σ * q / 2 := by
    rw [div_eq_div_iff (by positivity) (by positivity), hη_def,
      show R * σ * q * (R / σ * q * t) = R ^ 2 * (σ / σ) * (q * q * t) by ring,
      div_self hσ_pos.ne', hqt]
    ring
  have hB2 : B ^ 2 = σ ^ 2 * m / 2 := by
    rw [hσsq]
    field_simp
  have hB' : η * B ^ 2 / (2 * m) = R * σ * q / 4 := by
    rw [div_eq_div_iff (by positivity) (by positivity), hη_def, hB2,
      show R / σ * q * (σ ^ 2 * m / 2) * 4 = 2 * R * q * m * σ * (σ / σ) by ring,
      div_self hσ_pos.ne']
    ring
  have hC : 2 * R * B / Real.sqrt (m * t : ℝ) = R * σ * q := by
    rw [div_eq_iff hS_pos.ne']
    linear_combination (-R) * hkey
  have hcR : c * R ^ 2 / t = β * R ^ 2 / t + R ^ 2 / (η * t) := by
    rw [hc_def]
    field_simp
  have hRsq : 0 ≤ R * σ * q := by positivity
  rw [hC]
  calc ∫ ω, f ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, x (s + 1) ω) ∂μ - f x_star
      ≤ c * R ^ 2 / t + η * B ^ 2 / (2 * m) := hmain
    _ = β * R ^ 2 / t + R * σ * q / 2 + R * σ * q / 4 := by rw [hcR, hA, hB']
    _ ≤ R * σ * q + β * R ^ 2 / t := by linarith

end minibatch_stochastic_gradient_descent_bound
