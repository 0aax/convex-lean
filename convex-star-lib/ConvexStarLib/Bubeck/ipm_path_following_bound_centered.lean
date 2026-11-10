import ConvexStarLib.Defs

/-!
# `ipm_path_following_bound_centered`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/ipm_path_following_bound_centered` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace ipm_path_following_bound_centered`, so the main result is `ipm_path_following_bound_centered.ipm_path_following_bound_centered`.
-/

namespace ipm_path_following_bound_centered

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Auxiliary development -/

/-- Standing assumptions on an open convex set `U` and a function `F`. -/
structure SCData {n : ℕ} (U : Set (EuclideanSpace ℝ (Fin n)))
    (F : EuclideanSpace ℝ (Fin n) → ℝ) : Prop where
  isOpen : IsOpen U
  convex : Convex ℝ U
  smooth : ContDiffOn ℝ 3 F U
  sc : ∀ x ∈ U, ∀ h, |inner ℝ h (jerkOperator F x h h)| ≤ 2 * (localNorm F x h) ^ 3
  pd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator F y v)

namespace SCData

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ}

/-! ### Calculus -/

/-- (helper, agent calc) `gradient F` is `C^2` on `U`. -/
lemma calc_contDiffOn_gradient (hD : SCData U F) : ContDiffOn ℝ 2 (gradient F) U := by
  have h1 : ContDiffOn ℝ 2 (fderiv ℝ F) U := hD.smooth.fderiv_of_isOpen hD.isOpen (by norm_num)
  exact h1.continuousLinearMap_comp
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.toContinuousLinearMap

lemma hasFDerivAt_gradient (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasFDerivAt (gradient F) (hessianOperator F x) x := by
  have h := ((calc_contDiffOn_gradient hD).differentiableOn (by norm_num)).differentiableAt
    (hD.isOpen.mem_nhds hx)
  exact h.hasFDerivAt

/-- (helper, agent calc) The Hessian operator is `C^1` on `U`. -/
lemma calc_contDiffOn_hessian (hD : SCData U F) :
    ContDiffOn ℝ 1 (fun y => hessianOperator F y) U :=
  (calc_contDiffOn_gradient hD).fderiv_of_isOpen hD.isOpen (by norm_num)

lemma hasFDerivAt_hessian (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U) :
    HasFDerivAt (fun y => hessianOperator F y) (jerkOperator F x) x := by
  have h := ((calc_contDiffOn_hessian hD).differentiableOn (by norm_num)).differentiableAt
    (hD.isOpen.mem_nhds hx)
  exact h.hasFDerivAt

/-- (helper, agent calc) Derivative of the affine path `s ↦ x + s • d`. -/
lemma calc_hasDerivAt_line (x d : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    HasDerivAt (fun s : ℝ => x + s • d) d s := by
  simpa using ((hasDerivAt_id s).smul_const d).const_add x

lemma hasDerivAt_F_line (hD : SCData U F) {x d : EuclideanSpace ℝ (Fin n)} {s : ℝ}
    (hs : x + s • d ∈ U) :
    HasDerivAt (fun s : ℝ => F (x + s • d)) (inner ℝ (gradient F (x + s • d)) d) s := by
  have hdiff : DifferentiableAt ℝ F (x + s • d) :=
    (hD.smooth.differentiableOn (by norm_num)).differentiableAt (hD.isOpen.mem_nhds hs)
  have h := hdiff.hasFDerivAt.comp_hasDerivAt s (calc_hasDerivAt_line x d s)
  rw [inner_gradient_left hdiff]
  exact h

lemma hasDerivAt_grad_line (hD : SCData U F) {x d u : EuclideanSpace ℝ (Fin n)} {s : ℝ}
    (hs : x + s • d ∈ U) :
    HasDerivAt (fun s : ℝ => inner ℝ u (gradient F (x + s • d)))
      (inner ℝ u (hessianOperator F (x + s • d) d)) s := by
  have h := (hasFDerivAt_gradient hD hs).comp_hasDerivAt s (calc_hasDerivAt_line x d s)
  have h2 := (hasDerivAt_const s u).inner ℝ h
  simpa using h2

lemma hasDerivAt_hess_line (hD : SCData U F) {x d u v : EuclideanSpace ℝ (Fin n)} {s : ℝ}
    (hs : x + s • d ∈ U) :
    HasDerivAt (fun s : ℝ => inner ℝ u (hessianOperator F (x + s • d) v))
      (inner ℝ u (jerkOperator F (x + s • d) d v)) s := by
  have h := (hasFDerivAt_hessian hD hs).comp_hasDerivAt s (calc_hasDerivAt_line x d s)
  have h1 := h.clm_apply (hasDerivAt_const s v)
  have h2 := (hasDerivAt_const s u).inner ℝ h1
  simpa using h2

/-- helper (symm): the Hessian operator, read through the inner product, is the second
Fréchet derivative of `F`. -/
lemma symm_inner_hess_eq (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (hessianOperator F x v) = fderiv ℝ (fderiv ℝ F) x v u := by
  have hF : ContDiffAt ℝ 3 F x := hD.smooth.contDiffAt (hD.isOpen.mem_nhds hx)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ F) x :=
    (hF.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have h1 : HasFDerivAt (fun y => inner ℝ u (gradient F y))
      ((innerSL ℝ u).comp (hessianOperator F x)) x :=
    (innerSL ℝ u).hasFDerivAt.comp x (hD.hasFDerivAt_gradient hx)
  have h2 : HasFDerivAt (fun y => fderiv ℝ F y u)
      ((ContinuousLinearMap.apply ℝ ℝ u).comp (fderiv ℝ (fderiv ℝ F) x)) x :=
    (ContinuousLinearMap.apply ℝ ℝ u).hasFDerivAt.comp x hdiff.hasFDerivAt
  have heq : (fun y => inner ℝ u (gradient F y)) = (fun y => fderiv ℝ F y u) := by
    funext y
    rw [real_inner_comm]
    simp only [gradient, InnerProductSpace.toDual_symm_apply]
  rw [heq] at h1
  have := congrArg (fun L => L v) (h1.unique h2)
  simpa using this

lemma hess_symm (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (u v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ u (hessianOperator F x v) = inner ℝ v (hessianOperator F x u) := by
  have hF : ContDiffAt ℝ 3 F x := hD.smooth.contDiffAt (hD.isOpen.mem_nhds hx)
  have hsymm : IsSymmSndFDerivAt ℝ F x := hF.isSymmSndFDerivAt (by simp; norm_num)
  rw [symm_inner_hess_eq hD hx, symm_inner_hess_eq hD hx]
  exact hsymm v u

lemma jerk_symm12 (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (a b c : EuclideanSpace ℝ (Fin n)) :
    inner ℝ c (jerkOperator F x a b) = inner ℝ c (jerkOperator F x b a) := by
  have hev : ∀ᶠ y in 𝓝 x, HasFDerivAt (gradient F) (hessianOperator F y) y := by
    filter_upwards [hD.isOpen.mem_nhds hx] with y hy
    exact hD.hasFDerivAt_gradient hy
  have := second_derivative_symmetric_of_eventually_of_real hev (hD.hasFDerivAt_hessian hx) a b
  rw [this]

lemma jerk_symm23 (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (a b c : EuclideanSpace ℝ (Fin n)) :
    inner ℝ c (jerkOperator F x a b) = inner ℝ b (jerkOperator F x a c) := by
  let Ψ : (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) →L[ℝ] ℝ :=
    (innerSL ℝ c).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) b) -
    (innerSL ℝ b).comp (ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) c)
  have hΨ : ∀ T : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n),
      Ψ T = inner ℝ c (T b) - inner ℝ b (T c) := by
    intro T
    simp [Ψ]
  have h1 : HasFDerivAt (fun y => Ψ (hessianOperator F y)) (Ψ.comp (jerkOperator F x)) x :=
    Ψ.hasFDerivAt.comp x (hD.hasFDerivAt_hessian hx)
  have hev : (fun y => Ψ (hessianOperator F y)) =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    filter_upwards [hD.isOpen.mem_nhds hx] with y hy
    rw [hΨ, hD.hess_symm hy c b, sub_self]
  have h2 : HasFDerivAt (fun y => Ψ (hessianOperator F y))
      (0 : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) x :=
    (hasFDerivAt_const (0 : ℝ) x).congr_of_eventuallyEq hev
  have h3 := congrArg (fun L => L a) (h1.unique h2)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply, hΨ] at h3
  linarith

lemma gradient_ft (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (c : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    gradient (ft F c a) x = a • c + gradient F x := by
  have hdiff : DifferentiableAt ℝ F x :=
    (hD.smooth.differentiableOn (by norm_num)).differentiableAt (hD.isOpen.mem_nhds hx)
  have h1 : HasFDerivAt (fun y => a * (innerSL ℝ c) y) (a • innerSL ℝ c) x :=
    ((innerSL ℝ c).hasFDerivAt).const_mul a
  have h2 : HasFDerivAt (ft F c a) (a • innerSL ℝ c + fderiv ℝ F x) x := by
    have h3 := h1.add hdiff.hasFDerivAt
    simp only [innerSL_apply_apply] at h3
    exact h3
  apply HasGradientAt.gradient
  rw [hasGradientAt_iff_hasFDerivAt]
  convert h2 using 1
  ext y
  simp [inner_gradient_left hdiff]

lemma hessian_ft (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (c : EuclideanSpace ℝ (Fin n)) (a : ℝ) :
    hessianOperator (ft F c a) x = hessianOperator F x := by
  have hev : (fun y => gradient (ft F c a) y) =ᶠ[𝓝 x] fun y => a • c + gradient F y := by
    filter_upwards [hD.isOpen.mem_nhds hx] with y hy
    exact gradient_ft hD hy c a
  unfold hessianOperator
  rw [hev.fderiv_eq, fderiv_const_add]

/-! ### Linear algebra -/

lemma localInnerProd_nonneg (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (v : EuclideanSpace ℝ (Fin n)) : 0 ≤ localInnerProd F x v v := by
  unfold localInnerProd
  by_cases hv : v = 0
  · subst hv
    simp
  · exact (hD.pd x hx v hv).le

lemma localNorm_sq (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (v : EuclideanSpace ℝ (Fin n)) : localNorm F x v ^ 2 = localInnerProd F x v v := by
  unfold localNorm
  exact Real.sq_sqrt (hD.localInnerProd_nonneg hx v)

lemma eq_zero_of_localNorm (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {v : EuclideanSpace ℝ (Fin n)} (hv : localNorm F x v = 0) : v = 0 := by
  by_contra hne
  have hpos : 0 < localInnerProd F x v v := hD.pd x hx v hne
  have hpos' : 0 < localNorm F x v := Real.sqrt_pos.mpr hpos
  linarith

lemma localNorm_neg (F : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    localNorm F x (-v) = localNorm F x v := by
  unfold localNorm localInnerProd
  rw [map_neg, inner_neg_neg]

lemma localNorm_smul {x : EuclideanSpace ℝ (Fin n)}
    (r : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    localNorm F x (r • v) = |r| * localNorm F x v := by
  have h1 : localInnerProd F x (r • v) (r • v) = r ^ 2 * localInnerProd F x v v := by
    unfold localInnerProd
    rw [map_smul, real_inner_smul_left, real_inner_smul_right]
    ring
  unfold localNorm
  rw [h1, Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq_eq_abs]

lemma hess_apply_inverse (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (g : EuclideanSpace ℝ (Fin n)) :
    hessianOperator F x ((hessianOperator F x).inverse g) = g := by
  have hinj : Function.Injective (hessianOperator F x) := by
    intro a b hab
    by_contra hne
    have hne' : a - b ≠ 0 := sub_ne_zero.mpr hne
    have hpos := hD.pd x hx (a - b) hne'
    rw [map_sub, hab, sub_self, inner_zero_right] at hpos
    exact lt_irrefl _ hpos
  have hsurj : Function.Surjective (hessianOperator F x) :=
    LinearMap.injective_iff_surjective
      (f := ((hessianOperator F x : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) :
        EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n))).mp hinj
  have hinv : (hessianOperator F x).IsInvertible :=
    ⟨ContinuousLinearEquiv.ofBijective (hessianOperator F x)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj),
      ContinuousLinearEquiv.coe_ofBijective _ _ _⟩
  exact hinv.self_apply_inverse g

/-- Cauchy–Schwarz for the local (Hessian) inner product, squared form. -/
lemma linalg_sq_le (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (w v : EuclideanSpace ℝ (Fin n)) :
    localInnerProd F x w v ^ 2 ≤ localInnerProd F x w w * localInnerProd F x v v := by
  have hsymm : inner ℝ v (hessianOperator F x w) = inner ℝ w (hessianOperator F x v) :=
    hD.hess_symm hx v w
  have ha0 := hD.localInnerProd_nonneg hx w
  have hc0 := hD.localInnerProd_nonneg hx v
  have hq := hD.localInnerProd_nonneg hx
    ((inner ℝ v (hessianOperator F x v)) • w - (inner ℝ w (hessianOperator F x v)) • v)
  unfold localInnerProd at *
  rcases hc0.eq_or_lt with hc | hc
  · have hv : v = 0 := by
      by_contra hne
      have := hD.pd x hx v hne
      linarith
    subst hv
    simp
  · simp only [map_sub, map_smul, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, hsymm] at hq
    nlinarith

/-- Cauchy–Schwarz for the local (Hessian) inner product. -/
lemma linalg_cs (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (w v : EuclideanSpace ℝ (Fin n)) :
    localInnerProd F x w v ≤ localNorm F x w * localNorm F x v := by
  unfold localNorm
  rw [← Real.sqrt_mul (hD.localInnerProd_nonneg hx w)]
  calc localInnerProd F x w v ≤ |localInnerProd F x w v| := le_abs_self _
    _ = Real.sqrt (localInnerProd F x w v ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ _ := Real.sqrt_le_sqrt (linalg_sq_le hD hx w v)

lemma linalg_localNorm_nonneg (F : EuclideanSpace ℝ (Fin n) → ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    0 ≤ localNorm F x v :=
  Real.sqrt_nonneg _

lemma linalg_localNorm_zero (F : EuclideanSpace ℝ (Fin n) → ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    localNorm F x 0 = 0 := by
  simp [localNorm, localInnerProd]

/-- Pointwise bound from a bound on the unit ball (no sign condition on `β` needed). -/
lemma linalg_prox_of_unit (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {g : EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (h : ∀ v, localNorm F x v ≤ 1 → inner ℝ g v ≤ β) :
    ∀ v, inner ℝ g v ≤ β * localNorm F x v := by
  intro v
  rcases (linalg_localNorm_nonneg F x v).eq_or_lt with hr | hr
  · have hv : v = 0 := hD.eq_zero_of_localNorm hx hr.symm
    subst hv
    simp [linalg_localNorm_zero]
  · have hunit : localNorm F x ((localNorm F x v)⁻¹ • v) = 1 := by
      rw [localNorm_smul, abs_of_pos (inv_pos.mpr hr), inv_mul_cancel₀ hr.ne']
    have h2 := h ((localNorm F x v)⁻¹ • v) hunit.le
    rw [real_inner_smul_right] at h2
    have h3 : inner ℝ g v = localNorm F x v * ((localNorm F x v)⁻¹ * inner ℝ g v) := by
      field_simp
    rw [h3, mul_comm β]
    exact mul_le_mul_of_nonneg_left h2 hr.le

/-- From a bound on the dual norm, get the pointwise bound. -/
lemma prox_of_dualNorm (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {g : EuclideanSpace ℝ (Fin n)} {β : ℝ} (h : dualNorm (localNorm F x) g ≤ β) :
    ∀ v, inner ℝ g v ≤ β * localNorm F x v := by
  obtain ⟨w, hHw⟩ : ∃ w, hessianOperator F x w = g := ⟨_, hD.hess_apply_inverse hx g⟩
  have hg : ∀ v, inner ℝ g v = localInnerProd F x w v := by
    intro v
    unfold localInnerProd
    rw [← hHw, real_inner_comm]
    exact hD.hess_symm hx v w
  have hbdd : BddAbove {t | ∃ v, localNorm F x v ≤ 1 ∧ t = inner ℝ g v} := by
    refine ⟨localNorm F x w, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [hg v]
    calc localInnerProd F x w v ≤ localNorm F x w * localNorm F x v := linalg_cs hD hx w v
      _ ≤ localNorm F x w * 1 :=
          mul_le_mul_of_nonneg_left hv (linalg_localNorm_nonneg F x w)
      _ = localNorm F x w := mul_one _
  have hunit : ∀ v, localNorm F x v ≤ 1 → inner ℝ g v ≤ β := by
    intro v hv
    have hle : inner ℝ g v ≤ dualNorm (localNorm F x) g := le_csSup hbdd ⟨v, hv, rfl⟩
    linarith
  exact linalg_prox_of_unit hD hx hunit

lemma dualNorm_le_of_unit {x g : EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (h : ∀ v, localNorm F x v ≤ 1 → inner ℝ g v ≤ β) :
    dualNorm (localNorm F x) g ≤ β := by
  unfold dualNorm
  apply csSup_le
  · refine ⟨inner ℝ g 0, 0, ?_, rfl⟩
    simp [localNorm, localInnerProd]
  · rintro _ ⟨v, hv, rfl⟩
    exact h v hv

lemma prox_of_unit (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    {g : EuclideanSpace ℝ (Fin n)} {β : ℝ}
    (h : ∀ v, localNorm F x v ≤ 1 → inner ℝ g v ≤ β) :
    ∀ v, inner ℝ g v ≤ β * localNorm F x v := by
  exact linalg_prox_of_unit hD hx h

/-! ### Self-concordance estimates -/

/-- Real-arithmetic core of `polar` (helper for agent `polar`). -/
lemma polar_aux {A B X Y ε T P Q R : ℝ} (hA : 0 < A) (hB : 0 < B) (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y)
    (hε : 0 < ε) (hεB : ε * B = 3 / 5 * A)
    (hXY : X ^ 2 + Y ^ 2 = 2 * A ^ 2 + 2 * ε ^ 2 * B ^ 2)
    (hpol : P - Q = 6 * ε * T + 2 * ε ^ 3 * R)
    (hP : |P| ≤ 2 * X ^ 3) (hQ : |Q| ≤ 2 * Y ^ 3) (hR : |R| ≤ 2 * B ^ 3) :
    |T| ≤ 11 / 4 * A ^ 2 * B := by
  -- bound on 6 ε |T|
  have hmain : 6 * ε * |T| ≤ 2 * X ^ 3 + 2 * Y ^ 3 + 4 * ε ^ 3 * B ^ 3 := by
    have habs : |6 * ε * T| = 6 * ε * |T| := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 6 * ε)]
    rw [← habs, abs_le]
    obtain ⟨hP1, hP2⟩ := abs_le.mp hP
    obtain ⟨hQ1, hQ2⟩ := abs_le.mp hQ
    obtain ⟨hR1, hR2⟩ := abs_le.mp hR
    have hε3 : 0 < ε ^ 3 := by positivity
    have hR3 := mul_le_mul_of_nonneg_left hR2 hε3.le
    have hR4 := mul_le_mul_of_nonneg_left hR1 hε3.le
    constructor <;> linarith
  -- X^2 + Y^2 = 68/25 A^2
  have hεB2 : ε ^ 2 * B ^ 2 = 9 / 25 * A ^ 2 := by
    rw [← mul_pow, hεB]; ring
  have hXY' : X ^ 2 + Y ^ 2 = 68 / 25 * A ^ 2 := by
    rw [hXY]; linarith
  have hXle : X ≤ 33 / 20 * A := by
    nlinarith [sq_nonneg Y, mul_pos hA hA]
  have hYle : Y ≤ 33 / 20 * A := by
    nlinarith [sq_nonneg X, mul_pos hA hA]
  have hX3 : X ^ 3 ≤ 33 / 20 * A * X ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hXle (sq_nonneg X)]
  have hY3 : Y ^ 3 ≤ 33 / 20 * A * Y ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hYle (sq_nonneg Y)]
  have hsum : 33 / 20 * A * X ^ 2 + 33 / 20 * A * Y ^ 2 = 33 / 20 * 68 / 25 * A ^ 3 := by
    have e : 33 / 20 * A * X ^ 2 + 33 / 20 * A * Y ^ 2 = 33 / 20 * A * (X ^ 2 + Y ^ 2) := by ring
    rw [e, hXY']; ring
  have hcube : X ^ 3 + Y ^ 3 ≤ 33 / 20 * 68 / 25 * A ^ 3 := by
    linarith [hX3, hY3, hsum]
  -- multiply by B and substitute ε B = 3/5 A
  have h7 : 6 * (ε * B) * |T| ≤ 2 * (X ^ 3 + Y ^ 3) * B + 4 * (ε * B) ^ 3 * B := by
    have := mul_le_mul_of_nonneg_right hmain hB.le
    linarith [this]
  rw [hεB] at h7
  have h8 : 2 * (X ^ 3 + Y ^ 3) * B ≤ 2 * (33 / 20 * 68 / 25 * A ^ 3) * B := by
    have := mul_le_mul_of_nonneg_right hcube hB.le
    linarith [this]
  have h9 : A * (18 / 5 * |T|) ≤ A * (246 / 25 * A ^ 2 * B) := by
    linarith [h7, h8]
  have h10 : 18 / 5 * |T| ≤ 246 / 25 * A ^ 2 * B := le_of_mul_le_mul_left h9 hA
  have hAB : 0 ≤ A ^ 2 * B := by positivity
  linarith [h10, hAB]

lemma polar (hD : SCData U F) {x : EuclideanSpace ℝ (Fin n)} (hx : x ∈ U)
    (a b : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ b (jerkOperator F x a a)| ≤ 11 / 4 * (localNorm F x a) ^ 2 * localNorm F x b := by
  by_cases ha : a = 0
  · subst ha; simp only [map_zero, inner_zero_right, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _)
  by_cases hb : b = 0
  · subst hb; simp only [inner_zero_left, abs_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) (Real.sqrt_nonneg _)
  have hA0 : 0 ≤ localNorm F x a := Real.sqrt_nonneg _
  have hB0 : 0 ≤ localNorm F x b := Real.sqrt_nonneg _
  have hA : 0 < localNorm F x a :=
    lt_of_le_of_ne hA0 (fun h => ha (hD.eq_zero_of_localNorm hx h.symm))
  have hB : 0 < localNorm F x b :=
    lt_of_le_of_ne hB0 (fun h => hb (hD.eq_zero_of_localNorm hx h.symm))
  set ε : ℝ := 3 / 5 * localNorm F x a / localNorm F x b with hε
  have hεpos : 0 < ε := by positivity
  have hεB : ε * localNorm F x b = 3 / 5 * localNorm F x a := by
    rw [hε]; field_simp
  -- symmetry facts
  have h1 : inner ℝ a (jerkOperator F x a b) = inner ℝ b (jerkOperator F x a a) :=
    hD.jerk_symm23 hx a b a
  have h2 : inner ℝ a (jerkOperator F x b a) = inner ℝ b (jerkOperator F x a a) := by
    rw [hD.jerk_symm12 hx b a a, h1]
  -- polarization identity
  have hpol : inner ℝ (a + ε • b) (jerkOperator F x (a + ε • b) (a + ε • b))
      - inner ℝ (a - ε • b) (jerkOperator F x (a - ε • b) (a - ε • b))
      = 6 * ε * inner ℝ b (jerkOperator F x a a)
        + 2 * ε ^ 3 * inner ℝ b (jerkOperator F x b b) := by
    simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right, h1, h2]
    ring
  -- sum of squares of local norms
  have hsq : localNorm F x (a + ε • b) ^ 2 + localNorm F x (a - ε • b) ^ 2
      = 2 * localNorm F x a ^ 2 + 2 * ε ^ 2 * localNorm F x b ^ 2 := by
    rw [hD.localNorm_sq hx, hD.localNorm_sq hx, hD.localNorm_sq hx, hD.localNorm_sq hx]
    unfold localInnerProd
    simp only [map_add, map_sub, map_smul, inner_add_left,
      inner_add_right, inner_sub_left, inner_sub_right, real_inner_smul_left,
      real_inner_smul_right]
    ring
  exact polar_aux hA hB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hεpos hεB hsq hpol
    (hD.sc x hx _) (hD.sc x hx _) (hD.sc x hx _)

/-- Monotonicity on `Icc` from `HasDerivAt` at every point of `Icc`. -/
lemma diag_monotoneOn {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ s ∈ Set.Icc a b, HasDerivAt f (f' s) s)
    (h0 : ∀ s ∈ Set.Icc a b, 0 ≤ f' s) : MonotoneOn f (Set.Icc a b) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc a b)
  · exact fun s hs => (hf s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (hf s (Set.Ioo_subset_Icc_self hs)).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact h0 s (Set.Ioo_subset_Icc_self hs)

/-- Antitonicity on `Icc` from `HasDerivAt` at every point of `Icc`. -/
lemma diag_antitoneOn {a b : ℝ} {f f' : ℝ → ℝ}
    (hf : ∀ s ∈ Set.Icc a b, HasDerivAt f (f' s) s)
    (h0 : ∀ s ∈ Set.Icc a b, f' s ≤ 0) : AntitoneOn f (Set.Icc a b) := by
  apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc a b)
  · exact fun s hs => (hf s hs).continuousAt.continuousWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact (hf s (Set.Ioo_subset_Icc_self hs)).hasDerivWithinAt
  · intro s hs
    rw [interior_Icc] at hs
    exact h0 s (Set.Ioo_subset_Icc_self hs)

/-- Derivative of `χ(t) = 1 / ‖d‖_{y + t d}` along the segment. -/
lemma diag_chi_deriv (hD : SCData U F) {y d : EuclideanSpace ℝ (Fin n)} (hd : d ≠ 0) {s : ℝ}
    (hs : y + s • d ∈ U) :
    HasDerivAt (fun t : ℝ => (localNorm F (y + t • d) d)⁻¹)
      (-(inner ℝ d (jerkOperator F (y + s • d) d d) / (2 * localNorm F (y + s • d) d)) /
        localNorm F (y + s • d) d ^ 2) s := by
  have hpos : 0 < inner ℝ d (hessianOperator F (y + s • d) d) := hD.pd _ hs d hd
  have h1 : HasDerivAt (fun t : ℝ => inner ℝ d (hessianOperator F (y + t • d) d))
      (inner ℝ d (jerkOperator F (y + s • d) d d)) s := hasDerivAt_hess_line hD hs
  exact (h1.sqrt hpos.ne').fun_inv (Real.sqrt_pos.mpr hpos).ne'

/-- The derivative of `χ` is bounded by `1` in absolute value (self-concordance). -/
lemma diag_chi_bound (hD : SCData U F) {y d : EuclideanSpace ℝ (Fin n)} (hd : d ≠ 0) {s : ℝ}
    (hs : y + s • d ∈ U) :
    |-(inner ℝ d (jerkOperator F (y + s • d) d d) / (2 * localNorm F (y + s • d) d)) /
        localNorm F (y + s • d) d ^ 2| ≤ 1 := by
  have hpos : 0 < localNorm F (y + s • d) d := Real.sqrt_pos.mpr (hD.pd _ hs d hd)
  have hsc := hD.sc _ hs d
  set g := localNorm F (y + s • d) d
  set j := inner ℝ d (jerkOperator F (y + s • d) d d)
  have key : -(j / (2 * g)) / g ^ 2 = -j / (2 * g ^ 3) := by ring
  rw [key, abs_div, abs_neg, abs_of_pos (by positivity : (0:ℝ) < 2 * g ^ 3),
    div_le_one (by positivity)]
  exact hsc

lemma diag (hD : SCData U F) {y d : EuclideanSpace ℝ (Fin n)} {S : ℝ}
    (hseg : ∀ σ ∈ Set.Icc 0 S, y + σ • d ∈ U) (hd : d ≠ 0) {σ : ℝ} (hσ : σ ∈ Set.Icc 0 S) :
    localNorm F y d / (1 + σ * localNorm F y d) ≤ localNorm F (y + σ • d) d ∧
    (σ * localNorm F y d < 1 →
      localNorm F (y + σ • d) d ≤ localNorm F y d / (1 - σ * localNorm F y d)) := by
  have h0 : (0:ℝ) ∈ Set.Icc 0 S := ⟨le_refl 0, hσ.1.trans hσ.2⟩
  have hmono : MonotoneOn (fun t : ℝ => (localNorm F (y + t • d) d)⁻¹ + t) (Set.Icc 0 S) := by
    refine diag_monotoneOn
      (fun t ht => (diag_chi_deriv hD hd (hseg t ht)).add (hasDerivAt_id t)) ?_
    intro t ht
    have := (abs_le.mp (diag_chi_bound hD hd (hseg t ht))).1
    linarith
  have hanti : AntitoneOn (fun t : ℝ => (localNorm F (y + t • d) d)⁻¹ - t) (Set.Icc 0 S) := by
    refine diag_antitoneOn
      (fun t ht => (diag_chi_deriv hD hd (hseg t ht)).sub (hasDerivAt_id t)) ?_
    intro t ht
    have := (abs_le.mp (diag_chi_bound hD hd (hseg t ht))).2
    linarith
  have e1 := hmono h0 hσ hσ.1
  have e2 := hanti h0 hσ hσ.1
  simp only [zero_smul, add_zero, sub_zero] at e1 e2
  have hy : y ∈ U := by simpa using hseg 0 h0
  have hq : 0 < localNorm F y d := Real.sqrt_pos.mpr (hD.pd y hy d hd)
  have hg : 0 < localNorm F (y + σ • d) d := Real.sqrt_pos.mpr (hD.pd _ (hseg σ hσ) d hd)
  set q := localNorm F y d
  set g := localNorm F (y + σ • d) d
  constructor
  · have h1 : g⁻¹ ≤ (1 + σ * q) / q := by
      rw [add_div, one_div, mul_div_assoc, div_self hq.ne', mul_one]
      linarith
    have h2 : 0 < (1 + σ * q) / q := by
      have : 0 ≤ σ * q := mul_nonneg hσ.1 hq.le
      positivity
    have h3 := (inv_le_comm₀ hg h2).mp h1
    rwa [inv_div] at h3
  · intro hσq
    have h1 : (1 - σ * q) / q ≤ g⁻¹ := by
      rw [_root_.sub_div, one_div, mul_div_assoc, div_self hq.ne', mul_one]
      linarith
    have h2 : 0 < (1 - σ * q) / q := div_pos (by linarith) hq
    have h3 := (le_inv_comm₀ h2 hg).mp h1
    rwa [inv_div] at h3

lemma hess_comp (hD : SCData U F) {y d u : EuclideanSpace ℝ (Fin n)}
    (hseg : ∀ σ ∈ Set.Icc (0:ℝ) 1, y + σ • d ∈ U) (hlam : localNorm F y d < 1)
    {σ : ℝ} (hσ : σ ∈ Set.Icc (0:ℝ) 1) :
    localInnerProd F (y + σ • d) u u * (1 - localNorm F y d) ^ 3 ≤
      localInnerProd F (y + d) u u * (1 - σ * localNorm F y d) ^ 3 := by
  by_cases hd : d = 0
  · subst hd
    simp [localNorm, localInnerProd]
  have hl0 : 0 ≤ localNorm F y d := Real.sqrt_nonneg _
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < 1 - t * localNorm F y d := by
    intro t ht
    have : t * localNorm F y d ≤ localNorm F y d := mul_le_of_le_one_left hl0 ht.2
    linarith
  have hψ : ∀ t ∈ Set.Icc (0:ℝ) 1,
      HasDerivAt (fun t : ℝ => localInnerProd F (y + t • d) u u)
        (inner ℝ u (jerkOperator F (y + t • d) d u)) t :=
    fun t ht => hasDerivAt_hess_line hD (hseg t ht)
  have hden : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (1 - t * localNorm F y d) ^ 3)
      ((3:ℕ) * (1 - t * localNorm F y d) ^ (3 - 1) * (-(1 * localNorm F y d))) t := by
    intro t
    exact (((hasDerivAt_id t).mul_const (localNorm F y d)).const_sub 1).fun_pow 3
  have hmono : MonotoneOn
      (fun t : ℝ => localInnerProd F (y + t • d) u u / (1 - t * localNorm F y d) ^ 3)
      (Set.Icc 0 1) := by
    refine diag_monotoneOn
      (fun t ht => (hψ t ht).fun_div (hden t) (pow_pos (hpos t ht) 3).ne') ?_
    intro t ht
    have hx := hseg t ht
    have hw := hpos t ht
    have hψnn : 0 ≤ localInnerProd F (y + t • d) u u := localInnerProd_nonneg hD hx u
    have hJ : inner ℝ u (jerkOperator F (y + t • d) d u) =
        inner ℝ d (jerkOperator F (y + t • d) u u) := by
      rw [jerk_symm12 hD hx d u u, jerk_symm23 hD hx u d u]
    have hpol := polar hD hx u d
    rw [localNorm_sq hD hx u] at hpol
    have htl : t * localNorm F y d < 1 := by linarith
    have hdiag := (diag hD hseg hd ht).2 htl
    rw [le_div_iff₀ hw] at hdiag
    rw [hJ]
    set l := localNorm F y d
    set j := inner ℝ d (jerkOperator F (y + t • d) u u)
    set ψ := localInnerProd F (y + t • d) u u
    set N := localNorm F (y + t • d) d
    set w := 1 - t * l
    apply div_nonneg _ (sq_nonneg _)
    have key : j * w ^ 3 - ψ * ((3:ℕ) * w ^ (3 - 1) * (-(1 * l))) =
        w ^ 2 * (j * w + 3 * l * ψ) := by push_cast; ring
    rw [key]
    apply mul_nonneg (sq_nonneg w)
    have h1 : -j ≤ 11 / 4 * ψ * N := by linarith [(abs_le.mp hpol).1]
    have h2 : -j * w ≤ 11 / 4 * ψ * N * w := mul_le_mul_of_nonneg_right h1 hw.le
    have h3 : 11 / 4 * ψ * N * w ≤ 11 / 4 * ψ * l := by
      have := mul_le_mul_of_nonneg_left hdiag (by positivity : (0:ℝ) ≤ 11 / 4 * ψ)
      linarith
    have h4 : 0 ≤ l * ψ := mul_nonneg hl0 hψnn
    nlinarith
  have h1mem : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_refl 1⟩
  have e := hmono hσ h1mem hσ.2
  simp only at e
  rw [div_le_div_iff₀ (pow_pos (hpos σ hσ) 3) (pow_pos (hpos 1 h1mem) 3)] at e
  simpa only [one_smul, one_mul] using e

/-- Monotonicity on `[0,1]` from a nonnegative derivative at every point of `[0,1]`. -/
lemma newton_mono_aux {f f' : ℝ → ℝ} (hder : ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt f (f' τ) τ)
    (hnn : ∀ τ ∈ Set.Icc (0:ℝ) 1, 0 ≤ f' τ) : MonotoneOn f (Set.Icc 0 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := f') (convex_Icc 0 1)
  · exact fun τ hτ => (hder τ hτ).continuousAt.continuousWithinAt
  · intro τ hτ
    rw [interior_Icc] at hτ
    exact (hder τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
  · intro τ hτ
    rw [interior_Icc] at hτ
    exact hnn τ (Set.Ioo_subset_Icc_self hτ)

/-- Pure real-arithmetic core of the jerk bound along the segment. -/
lemma newton_key_ineq {A B s lam : ℝ} (hA0 : 0 ≤ A) (hB0 : 0 ≤ B)
    (h1lam : 0 < 1 - lam) (hs_ge : 1 - lam ≤ s) (hAs : A * s ≤ lam)
    (hB2 : B ^ 2 * (1 - lam) ^ 3 ≤ s ^ 3) :
    A ^ 2 * B ≤ (lam / (1 - lam)) ^ 2 := by
  have hs_pos : 0 < s := by linarith
  have hAs4 : (A * s) ^ 4 ≤ lam ^ 4 := pow_le_pow_left₀ (by positivity) hAs 4
  have h1 : A ^ 4 * s ^ 4 * (B ^ 2 * (1 - lam) ^ 3) ≤ lam ^ 4 * s ^ 3 := by
    have e : A ^ 4 * s ^ 4 = (A * s) ^ 4 := by ring
    rw [e]
    exact mul_le_mul hAs4 hB2 (by positivity) (by positivity)
  have h2 : A ^ 4 * B ^ 2 * (1 - lam) ^ 3 * s ≤ lam ^ 4 := by
    have h3 : (A ^ 4 * B ^ 2 * (1 - lam) ^ 3 * s) * s ^ 3 ≤ lam ^ 4 * s ^ 3 := by
      calc (A ^ 4 * B ^ 2 * (1 - lam) ^ 3 * s) * s ^ 3
          = A ^ 4 * s ^ 4 * (B ^ 2 * (1 - lam) ^ 3) := by ring
        _ ≤ lam ^ 4 * s ^ 3 := h1
    exact le_of_mul_le_mul_right h3 (by positivity)
  have h4 : (A ^ 2 * B * (1 - lam) ^ 2) ^ 2 ≤ (lam ^ 2) ^ 2 := by
    calc (A ^ 2 * B * (1 - lam) ^ 2) ^ 2 = A ^ 4 * B ^ 2 * (1 - lam) ^ 3 * (1 - lam) := by ring
      _ ≤ A ^ 4 * B ^ 2 * (1 - lam) ^ 3 * s :=
          mul_le_mul_of_nonneg_left hs_ge (by positivity)
      _ ≤ lam ^ 4 := h2
      _ = (lam ^ 2) ^ 2 := by ring
  have h5 : A ^ 2 * B * (1 - lam) ^ 2 ≤ lam ^ 2 :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h4
  rw [div_pow, le_div_iff₀ (by positivity)]
  exact h5

lemma newton_bound (hD : SCData U F) {y d c : EuclideanSpace ℝ (Fin n)} {a : ℝ}
    (hy : y ∈ U) (hyd : y + d ∈ U)
    (hd : hessianOperator F y d = -(a • c + gradient F y)) (hlam : localNorm F y d < 1)
    (u : EuclideanSpace ℝ (Fin n)) (hu : localNorm F (y + d) u ≤ 1) :
    inner ℝ (a • c + gradient F (y + d)) u ≤
      11 / 8 * (localNorm F y d / (1 - localNorm F y d)) ^ 2 := by
  have hseg : ∀ σ ∈ Set.Icc (0:ℝ) 1, y + σ • d ∈ U := fun σ hσ =>
    hD.convex.add_smul_mem hy hyd hσ
  have hlam0 : 0 ≤ localNorm F y d := Real.sqrt_nonneg _
  have h1lam : 0 < 1 - localNorm F y d := by linarith
  by_cases hd0 : d = 0
  · subst hd0
    have h0 : a • c + gradient F y = 0 := by
      rw [map_zero] at hd
      exact neg_eq_zero.mp hd.symm
    rw [add_zero, h0, inner_zero_left]
    positivity
  set lam := localNorm F y d with hlam_def
  set K := 11 / 4 * (lam / (1 - lam)) ^ 2 with hK_def
  -- the jerk bound along the segment
  have hJ : ∀ τ ∈ Set.Icc (0:ℝ) 1, inner ℝ u (jerkOperator F (y + τ • d) d d) ≤ K := by
    intro τ hτ
    have hp := hseg τ hτ
    have hpol := hD.polar hp d u
    have hτlam : τ * lam < 1 := by nlinarith [hτ.1, hτ.2]
    have hdiag := (hD.diag hseg hd0 hτ).2 hτlam
    have hcomp := hD.hess_comp (u := u) hseg hlam hτ
    have hA0 : 0 ≤ localNorm F (y + τ • d) d := Real.sqrt_nonneg _
    have hB0 : 0 ≤ localNorm F (y + τ • d) u := Real.sqrt_nonneg _
    have hBsq := hD.localNorm_sq hp u
    have hu2 : localInnerProd F (y + d) u u ≤ 1 := by
      rw [← hD.localNorm_sq hyd u]
      have : 0 ≤ localNorm F (y + d) u := Real.sqrt_nonneg _
      nlinarith
    have hs_ge : 1 - lam ≤ 1 - τ * lam := by nlinarith [hτ.1, hτ.2]
    have hs_pos : 0 < 1 - τ * lam := by linarith
    have hAs : localNorm F (y + τ • d) d * (1 - τ * lam) ≤ lam := by
      rw [le_div_iff₀ hs_pos] at hdiag; exact hdiag
    have hB2 : localNorm F (y + τ • d) u ^ 2 * (1 - lam) ^ 3 ≤ (1 - τ * lam) ^ 3 := by
      rw [hBsq]
      calc localInnerProd F (y + τ • d) u u * (1 - lam) ^ 3
          ≤ localInnerProd F (y + d) u u * (1 - τ * lam) ^ 3 := hcomp
        _ ≤ 1 * (1 - τ * lam) ^ 3 := by
            apply mul_le_mul_of_nonneg_right hu2 (by positivity)
        _ = (1 - τ * lam) ^ 3 := one_mul _
    have hkey := newton_key_ineq hA0 hB0 h1lam hs_ge hAs hB2
    calc inner ℝ u (jerkOperator F (y + τ • d) d d)
        ≤ |inner ℝ u (jerkOperator F (y + τ • d) d d)| := le_abs_self _
      _ ≤ 11 / 4 * localNorm F (y + τ • d) d ^ 2 * localNorm F (y + τ • d) u := hpol
      _ = 11 / 4 * (localNorm F (y + τ • d) d ^ 2 * localNorm F (y + τ • d) u) := by ring
      _ ≤ 11 / 4 * (lam / (1 - lam)) ^ 2 := by
          apply mul_le_mul_of_nonneg_left hkey (by norm_num)
  -- g(τ) - g(0) ≤ K τ, where g(τ) = ⟪u, H(y+τd) d⟫
  have hg : ∀ τ ∈ Set.Icc (0:ℝ) 1,
      inner ℝ u (hessianOperator F (y + τ • d) d) - inner ℝ u (hessianOperator F y d) ≤ K * τ := by
    have hmono : MonotoneOn
        (fun τ : ℝ => K * τ - inner ℝ u (hessianOperator F (y + τ • d) d)) (Set.Icc 0 1) := by
      apply newton_mono_aux (f' := fun τ => K - inner ℝ u (jerkOperator F (y + τ • d) d d))
      · intro τ hτ
        have h1 := hD.hasDerivAt_hess_line (u := u) (v := d) (hseg τ hτ)
        have h2 : HasDerivAt (fun τ : ℝ => K * τ) K τ := by
          simpa using (hasDerivAt_id τ).const_mul K
        exact h2.sub h1
      · intro τ hτ
        have := hJ τ hτ
        simp only
        linarith
    intro τ hτ
    have := hmono ⟨le_refl 0, zero_le_one⟩ hτ hτ.1
    simp only [zero_smul, add_zero, mul_zero, zero_sub] at this
    linarith
  -- m(τ) := K τ^2/2 - f(τ) + τ g(0) is monotone, where f(τ) = ⟪u, ∇F(y+τd)⟫
  have hmono2 : MonotoneOn (fun τ : ℝ => K * τ ^ 2 / 2 - inner ℝ u (gradient F (y + τ • d))
      + τ * inner ℝ u (hessianOperator F y d)) (Set.Icc 0 1) := by
    apply newton_mono_aux (f' := fun τ => K * τ - inner ℝ u (hessianOperator F (y + τ • d) d)
      + inner ℝ u (hessianOperator F y d))
    · intro τ hτ
      have h1 := hD.hasDerivAt_grad_line (u := u) (hseg τ hτ)
      have h2 : HasDerivAt (fun τ : ℝ => K * τ ^ 2 / 2) (K * τ) τ := by
        have := ((hasDerivAt_pow 2 τ).const_mul K).div_const 2
        convert this using 1
        push_cast
        ring
      have h3 : HasDerivAt (fun τ : ℝ => τ * inner ℝ u (hessianOperator F y d))
          (inner ℝ u (hessianOperator F y d)) τ := by
        simpa using (hasDerivAt_id τ).mul_const (inner ℝ u (hessianOperator F y d))
      exact (h2.sub h1).add h3
    · intro τ hτ
      have := hg τ hτ
      simp only
      linarith
  have hm := hmono2 ⟨le_refl 0, zero_le_one⟩ ⟨zero_le_one, le_refl 1⟩ zero_le_one
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul] at hm
  rw [hd, inner_neg_right, inner_add_right] at hm
  rw [inner_add_left, real_inner_comm u (a • c), real_inner_comm u (gradient F (y + d))]
  have hK2 : 11 / 8 * (lam / (1 - lam)) ^ 2 = K / 2 := by rw [hK_def]; ring
  rw [hK2]
  norm_num at hm
  linarith

end SCData

/-! ### Barrier estimates -/

/-- Derivative of `F` along a line, from differentiability at the point. -/
lemma barrier_aux_line {n : ℕ} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {x d : EuclideanSpace ℝ (Fin n)} {s : ℝ}
    (hd : DifferentiableAt ℝ F (x + s • d)) :
    HasDerivAt (fun s : ℝ => F (x + s • d)) (inner ℝ (gradient F (x + s • d)) d) s := by
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have := hd.hasFDerivAt.comp_hasDerivAt s hline
  rw [inner_gradient_left hd]
  exact this

/-- Derivative of `s ↦ ⟪u, ∇F(x + s • d)⟫`, from `C³` smoothness on an open set. -/
lemma barrier_aux_grad_line {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))}
    {F : EuclideanSpace ℝ (Fin n) → ℝ} (hU : IsOpen U) (hF : ContDiffOn ℝ 3 F U)
    {x d u : EuclideanSpace ℝ (Fin n)} {s : ℝ} (hs : x + s • d ∈ U) :
    HasDerivAt (fun s : ℝ => inner ℝ u (gradient F (x + s • d)))
      (inner ℝ u (hessianOperator F (x + s • d) d)) s := by
  have hgrad : ContDiffOn ℝ 2 (gradient F) U := by
    have h1 : ContDiffOn ℝ 2 (fderiv ℝ F) U := hF.fderiv_of_isOpen hU (by norm_num)
    have hg : gradient F =
        fun y => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm (fderiv ℝ F y) := by
      funext y
      rfl
    rw [hg]
    exact (InnerProductSpace.toDual ℝ
      (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.contDiff.comp_contDiffOn h1
  have hdiff : DifferentiableAt ℝ (gradient F) (x + s • d) :=
    (hgrad.contDiffAt (hU.mem_nhds hs)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun s : ℝ => x + s • d) d s := by
    simpa using ((hasDerivAt_id s).smul_const d).const_add x
  have h1 := hdiff.hasFDerivAt.comp_hasDerivAt s hline
  have h2 := ((innerSL ℝ u).hasFDerivAt).comp_hasDerivAt s h1
  exact h2

lemma barrier_A {n : ℕ} {𝓧 : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {ν : ℝ} (hconv : Convex ℝ 𝓧) (hF : ContDiffOn ℝ 3 F (interior 𝓧)) (hν : 0 < ν)
    (hconc : ConcaveOn ℝ (interior 𝓧) (fun x => Real.exp ((-1 / ν) * (F x))))
    {z x : EuclideanSpace ℝ (Fin n)} (hz : z ∈ interior 𝓧) (hx : x ∈ 𝓧) :
    inner ℝ (gradient F z) (x - z) ≤ ν := by
  set G := inner ℝ (gradient F z) (x - z) with hG
  have hxcl : x ∈ closure 𝓧 := subset_closure hx
  -- points of the half-open segment `[z, x)` lie in the interior
  have hseg : ∀ s : ℝ, 0 ≤ s → s < 1 → z + s • (x - z) ∈ interior 𝓧 := by
    intro s hs0 hs1
    have := hconv.combo_interior_closure_mem_interior hz hxcl (a := 1 - s) (b := s)
      (by linarith) hs0 (by ring)
    convert this using 1
    rw [sub_smul, one_smul, smul_sub]
    abel
  -- concavity along the line
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap z x
  have hL : ∀ s : ℝ, L s = z + s • (x - z) := by
    intro s
    simp only [L, AffineMap.lineMap_apply_module', add_comm]
  set phi : ℝ → ℝ := fun s => Real.exp ((-1 / ν) * F (z + s • (x - z))) with hφ_
  have hc : ConcaveOn ℝ (L ⁻¹' interior 𝓧) phi := by
    have := hconc.comp_affineMap L
    convert this using 1
    funext s
    simp only [Function.comp, hL, phi]
  have h0S : (0:ℝ) ∈ L ⁻¹' interior 𝓧 := by
    simp only [Set.mem_preimage, hL, zero_smul, add_zero]
    exact hz
  -- derivative at `0`
  have hz' : z + (0:ℝ) • (x - z) ∈ interior 𝓧 := by simpa using hz
  have hdiff : DifferentiableAt ℝ F (z + (0:ℝ) • (x - z)) :=
    (hF.contDiffAt (isOpen_interior.mem_nhds hz')).differentiableAt (by norm_num)
  set E := Real.exp ((-1 / ν) * F z) with hE
  have hEpos : 0 < E := Real.exp_pos _
  have hderiv : HasDerivAt phi (E * ((-1 / ν) * G)) 0 := by
    have h2 := ((barrier_aux_line hdiff).const_mul (-1 / ν)).exp
    simp only [zero_smul, add_zero] at h2
    exact h2
  -- conclude by contradiction
  by_contra hcon
  push_neg at hcon
  have hGpos : 0 < G := lt_trans hν hcon
  set s := ν / G with hs
  have hs0 : 0 < s := div_pos hν hGpos
  have hs1 : s < 1 := (div_lt_one hGpos).mpr hcon
  have hsS : s ∈ L ⁻¹' interior 𝓧 := by
    simp only [Set.mem_preimage, hL]
    exact hseg s hs0.le hs1
  have hslope := hc.slope_le_of_hasDerivAt h0S hsS hs0 hderiv
  rw [slope_def_field] at hslope
  have hφ_0 : phi 0 = E := by simp [phi, E]
  have hφ_s : 0 < phi s := Real.exp_pos _
  rw [hφ_0, sub_zero, div_le_iff₀ hs0] at hslope
  have hkey : E * ((-1 / ν) * G) * s = -E := by
    rw [hs]
    field_simp
  linarith

lemma barrier_B {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {ν : ℝ} (hD : SCData U F) (hν : 0 < ν)
    (hconc : ConcaveOn ℝ U (fun x => Real.exp ((-1 / ν) * (F x))))
    {z : EuclideanSpace ℝ (Fin n)} (hz : z ∈ U) (v : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ (gradient F z) v) ^ 2 ≤ ν * localInnerProd F z v v := by
  -- the line through `z` in direction `v`
  let L : ℝ →ᵃ[ℝ] EuclideanSpace ℝ (Fin n) := AffineMap.lineMap z (z + v)
  have hL : ∀ s : ℝ, L s = z + s • v := by
    intro s
    simp only [L, AffineMap.lineMap_apply_module', add_sub_cancel_left, add_comm]
  have hLc : Continuous (L : ℝ → EuclideanSpace ℝ (Fin n)) := by
    rw [show (L : ℝ → EuclideanSpace ℝ (Fin n)) = fun s => z + s • v from funext hL]
    fun_prop
  set S : Set ℝ := L ⁻¹' U with hS
  have hSopen : IsOpen S := hD.isOpen.preimage hLc
  have h0S : (0:ℝ) ∈ S := by
    simp only [hS, Set.mem_preimage, hL, zero_smul, add_zero]
    exact hz
  have hSnhds : S ∈ 𝓝 (0:ℝ) := hSopen.mem_nhds h0S
  set psi : ℝ → ℝ := fun s => Real.exp ((-1 / ν) * F (z + s • v)) with hpsi
  have hc : ConcaveOn ℝ S psi := by
    have := hconc.comp_affineMap L
    convert this using 1
    funext s
    simp only [Function.comp, hL, psi]
  -- first derivative
  have hd1 : ∀ s ∈ S,
      HasDerivAt psi (psi s * ((-1 / ν) * inner ℝ v (gradient F (z + s • v)))) s := by
    intro s hs
    have hs' : z + s • v ∈ U := by
      have := hs
      simp only [hS, Set.mem_preimage, hL] at this
      exact this
    have hdF : DifferentiableAt ℝ F (z + s • v) :=
      (hD.smooth.contDiffAt (hD.isOpen.mem_nhds hs')).differentiableAt (by norm_num)
    have h := ((barrier_aux_line hdF).const_mul (-1 / ν)).exp
    rw [real_inner_comm]
    exact h
  -- the derivative is antitone on `S`
  have hanti : AntitoneOn (deriv psi) S :=
    hc.antitoneOn_deriv (fun s hs => (hd1 s hs).differentiableAt)
  have hgeq : deriv psi =ᶠ[𝓝 (0:ℝ)]
      (fun s => psi s * ((-1 / ν) * inner ℝ v (gradient F (z + s • v)))) := by
    filter_upwards [hSnhds] with s hs
    exact (hd1 s hs).deriv
  have hz0 : z + (0:ℝ) • v ∈ U := by simpa using hz
  have hgrad := barrier_aux_grad_line (u := v) hD.isOpen hD.smooth hz0
  have hg' := (hd1 0 h0S).mul (hgrad.const_mul (-1 / ν))
  have hg'' := (hg'.congr_of_eventuallyEq hgeq).hasDerivWithinAt (s := S)
  have hacc : AccPt (0:ℝ) (Filter.principal S) := by
    rw [accPt_iff_nhds]
    intro W hW
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (Filter.inter_mem hW hSnhds)
    refine ⟨ε / 2, hball ?_, (by positivity : (0:ℝ) < ε / 2).ne'⟩
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have hnonpos := hg''.nonpos_of_antitoneOn hacc hanti
  simp only [zero_smul, add_zero] at hnonpos
  have hP : 0 < psi 0 := Real.exp_pos _
  have hcomm : inner ℝ (gradient F z) v = inner ℝ v (gradient F z) := real_inner_comm _ _
  rw [hcomm]
  unfold localInnerProd
  set P := psi 0
  set G := inner ℝ v (gradient F z)
  set Q := inner ℝ v (hessianOperator F z v)
  have h1 : (-1 / ν * G) * (-1 / ν * G) + (-1 / ν * Q) ≤ 0 := by
    nlinarith
  have h2 : G ^ 2 - ν * Q = ν ^ 2 * ((-1 / ν * G) * (-1 / ν * G) + (-1 / ν * Q)) := by
    field_simp
    ring
  nlinarith [sq_nonneg ν]

lemma subopt {n : ℕ} {𝓧 : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ}
    {ν t β : ℝ} (hconv : Convex ℝ 𝓧) (hD : SCData (interior 𝓧) F) (hν : 1 ≤ ν)
    (hconc : ConcaveOn ℝ (interior 𝓧) (fun x => Real.exp ((-1 / ν) * (F x))))
    {y c xs : EuclideanSpace ℝ (Fin n)} (hy : y ∈ interior 𝓧) (hxs : xs ∈ 𝓧)
    (hβ : β ≤ 1 / 3)
    (hprox : ∀ v, inner ℝ (t • c + gradient F y) v ≤ β * localNorm F y v) :
    t * (inner ℝ c y - inner ℝ c xs) ≤ 2 * ν := by
  by_cases h0 : xs - y = 0
  · have hxy : xs = y := sub_eq_zero.mp h0
    subst hxy
    simp only [sub_self, mul_zero]
    linarith
  obtain ⟨h, hh⟩ : ∃ h, h = xs - y := ⟨_, rfl⟩
  rw [← hh] at h0
  -- segment points lie in the interior
  have hseg : ∀ σ ∈ Set.Icc (0:ℝ) (1/3), y + σ • h ∈ interior 𝓧 := by
    intro σ hσ
    have h1 : (1 - σ) • y + σ • xs ∈ interior 𝓧 :=
      hconv.combo_interior_self_mem_interior hy hxs (by linarith [hσ.2]) hσ.1 (by ring)
    have h2 : (1 - σ) • y + σ • xs = y + σ • h := by
      rw [hh]; module
    rw [← h2]; exact h1
  obtain ⟨q, hq⟩ : ∃ q, q = localNorm F y h := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  have hz : y + (1/3 : ℝ) • h ∈ interior 𝓧 := hseg (1/3) ⟨by norm_num, le_refl _⟩
  -- (1) barrier bound at z
  have h1 : inner ℝ (gradient F (y + (1/3 : ℝ) • h)) h ≤ 3/2 * ν := by
    have := barrier_A hconv hD.smooth (by linarith) hconc hz hxs
    have hxz : xs - (y + (1/3 : ℝ) • h) = (2/3 : ℝ) • h := by
      rw [hh]; module
    rw [hxz, real_inner_smul_right] at this
    linarith
  -- (2) monotonicity of the directional derivative
  have h2 : q^2 / (3 + q) ≤
      inner ℝ (gradient F (y + (1/3 : ℝ) • h)) h - inner ℝ (gradient F y) h := by
    let g : ℝ → ℝ := fun s => inner ℝ h (gradient F (y + s • h)) - s * q^2 / (1 + s * q)
    have hderiv : ∀ σ ∈ Set.Icc (0:ℝ) (1/3),
        HasDerivAt g (localNorm F (y + σ • h) h ^ 2 - q^2 / (1 + σ * q)^2) σ := by
      intro σ hσ
      have hρ := hD.hasDerivAt_grad_line (u := h) (hseg σ hσ)
      have hpos : 1 + σ * q ≠ 0 := by have := hσ.1; positivity
      have hr : HasDerivAt (fun s : ℝ => s * q^2 / (1 + s * q)) (q^2 / (1 + σ * q)^2) σ := by
        have := ((hasDerivAt_id' σ).mul_const (q^2)).div
          (((hasDerivAt_id' σ).mul_const q).const_add 1) hpos
        convert this using 1
        field_simp
        ring
      have := hρ.sub hr
      convert this using 1
      rw [hD.localNorm_sq (hseg σ hσ)]
      rfl
    have hmono : MonotoneOn g (Set.Icc 0 (1/3)) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 (1/3))
      · intro x hx; exact (hderiv x hx).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x (Set.Ioo_subset_Icc_self hx)).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hx' := Set.Ioo_subset_Icc_self hx
        have hd := (hD.diag hseg h0 hx').1
        rw [← hq] at hd
        have hnn : 0 ≤ q / (1 + x * q) := by have := hx.1.le; positivity
        have : (q / (1 + x * q))^2 ≤ localNorm F (y + x • h) h ^ 2 :=
          pow_le_pow_left₀ hnn hd 2
        rw [div_pow] at this
        linarith
    have := hmono ⟨le_refl 0, by norm_num⟩ ⟨by norm_num, le_refl _⟩ (by norm_num : (0:ℝ) ≤ 1/3)
    simp only [g, zero_smul, add_zero, zero_mul, zero_div, sub_zero] at this
    rw [real_inner_comm h (gradient F (y + (1/3:ℝ) • h)), real_inner_comm h (gradient F y)]
    have e : (1/3 : ℝ) * q^2 / (1 + 1/3 * q) = q^2 / (3 + q) := by
      field_simp
    linarith
  -- (3) prox bound with v = -h
  have h3 : - inner ℝ (t • c + gradient F y) h ≤ q / 3 := by
    have := hprox (-h)
    rw [inner_neg_right, SCData.localNorm_neg, ← hq] at this
    have : β * q ≤ 1/3 * q := mul_le_mul_of_nonneg_right hβ hq0
    linarith
  -- (4) assemble
  have h4 : t * (inner ℝ c y - inner ℝ c xs) =
      - inner ℝ (t • c + gradient F y) h + inner ℝ (gradient F y) h := by
    rw [hh, inner_add_left, real_inner_smul_left, inner_sub_right]
    ring
  have key : q / 3 - q^2 / (3 + q) ≤ 1/8 := by
    rw [div_sub_div _ _ (by norm_num) (by positivity), div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg (q - 21/32)]
  linarith

/-! ### Newton steps and the main assembly -/

namespace SCData

variable {n : ℕ} {U : Set (EuclideanSpace ℝ (Fin n))} {F : EuclideanSpace ℝ (Fin n) → ℝ}

lemma newton_dir_bound (hD : SCData U F) {y g : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) {β : ℝ}
    (hβ : 0 ≤ β) (hprox : ∀ v, inner ℝ g v ≤ β * localNorm F y v) :
    localNorm F y (-((hessianOperator F y).inverse g)) ≤ β ∧
    hessianOperator F y (-((hessianOperator F y).inverse g)) = -g := by
  set w := (hessianOperator F y).inverse g with hw
  have hHw : hessianOperator F y w = g := hD.hess_apply_inverse hy g
  have h2 : hessianOperator F y (-w) = -g := by rw [map_neg, hHw]
  refine ⟨?_, h2⟩
  have hsq := hD.localNorm_sq hy (-w)
  have hloc : localInnerProd F y (-w) (-w) = inner ℝ g w := by
    unfold localInnerProd
    rw [h2, inner_neg_left, inner_neg_right, neg_neg, real_inner_comm]
  have hp := hprox w
  rw [← localNorm_neg F y w] at hp
  have hN : 0 ≤ localNorm F y (-w) := Real.sqrt_nonneg _
  rw [hloc] at hsq
  nlinarith

lemma newton_prox (hD : SCData U F) {y c : EuclideanSpace ℝ (Fin n)} {a β : ℝ} (hy : y ∈ U)
    (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hprox : ∀ v, inner ℝ (a • c + gradient F y) v ≤ β * localNorm F y v)
    (hmem : y - (hessianOperator F y).inverse (a • c + gradient F y) ∈ U) :
    ∀ v, inner ℝ (a • c + gradient F
        (y - (hessianOperator F y).inverse (a • c + gradient F y))) v ≤
      11 / 8 * (β / (1 - β)) ^ 2 *
        localNorm F (y - (hessianOperator F y).inverse (a • c + gradient F y)) v := by
  obtain ⟨hdn, hHd⟩ := hD.newton_dir_bound hy hβ0 hprox
  have hyd : y - (hessianOperator F y).inverse (a • c + gradient F y) =
      y + -((hessianOperator F y).inverse (a • c + gradient F y)) := sub_eq_add_neg _ _
  rw [hyd] at hmem ⊢
  set d := -((hessianOperator F y).inverse (a • c + gradient F y)) with hd
  have hlam : localNorm F y d < 1 := lt_of_le_of_lt hdn hβ1
  apply hD.prox_of_unit hmem
  intro u hu
  refine (hD.newton_bound hy hmem hHd hlam u hu).trans ?_
  have hl0 : 0 ≤ localNorm F y d := Real.sqrt_nonneg _
  have h1 : localNorm F y d / (1 - localNorm F y d) ≤ β / (1 - β) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have h2 : 0 ≤ localNorm F y d / (1 - localNorm F y d) := div_nonneg hl0 (by linarith)
  have h3 : (localNorm F y d / (1 - localNorm F y d)) ^ 2 ≤ (β / (1 - β)) ^ 2 :=
    pow_le_pow_left₀ h2 h1 2
  linarith

end SCData

set_option linter.unusedVariables false in
theorem ipm_path_following_bound_centered
  {n k : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (F : EuclideanSpace ℝ (Fin n) → ℝ)
  (t : ℕ → ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (ν : ℝ)
  (c : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0_mem : x0 ∈ interior 𝓧)
  (h_dec0 : newtonDecrement (ft F c (t 0)) x0 ≤ 1 / 4)
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn (fun x => inner ℝ c x) 𝓧 x_star)
  (ht_pos : ∀ j, 0 < t j)
  (ht_rec : ∀ j, t (j + 1) =
    (1 + 1 / (13 * Real.sqrt ν)) * t j)
  (h𝓧_closed : IsClosed 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_frontier_nonempty : Set.Nonempty (frontier 𝓧))
  (hF : IsNuSelfConcordantBarrier 𝓧 F ν)
  (hFt_levelBounded :
    ∀ a > 0, LevelBoundedOn (interior 𝓧) (ft F c a))
  (hxC_mem : ∀ j, xCentered F t x0 ν c j ∈ interior 𝓧) :
  inner ℝ c (xCentered F t x0 ν c k) - inner ℝ c x_star
  ≤ (2 * ν) / (t 0) *
    Real.exp (-(↑k : ℝ) / (1 + 13 * Real.sqrt ν)) := by
  obtain ⟨hν1, ⟨_, hsmooth, hsc, hpd⟩, hconc, _⟩ := hF
  have hD : SCData (interior 𝓧) F :=
    ⟨isOpen_interior, h𝓧_convex.interior, hsmooth, hsc, hpd⟩
  have hν0 : (0:ℝ) < ν := by linarith
  have hsq1 : (1:ℝ) ≤ Real.sqrt ν := by
    rw [show (1:ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hν1
  have hsqpos : 0 < Real.sqrt ν := by linarith
  set r : ℝ := 1 / (13 * Real.sqrt ν) with hr
  have hr0 : 0 < r := by positivity
  have hr1 : r ≤ 1 / 13 := by
    rw [hr, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hrs : r * Real.sqrt ν = 1 / 13 := by
    rw [hr]; field_simp
  -- the centering invariant
  have key : ∀ j, ∀ v, inner ℝ (t j • c + gradient F (xCentered F t x0 ν c j)) v ≤
      (31 / 200) * localNorm F (xCentered F t x0 ν c j) v := by
    intro j
    induction j with
    | zero =>
      have hx0' : xCentered F t x0 ν c 0 =
          x0 - (hessianOperator F x0).inverse (t 0 • c + gradient F x0) := by
        show newtonStep (ft F c (t 0)) x0 = _
        unfold newtonStep
        rw [hD.hessian_ft hx0_mem, hD.gradient_ft hx0_mem]
      have hloc : localNorm (ft F c (t 0)) x0 = localNorm F x0 := by
        funext v
        unfold localNorm localInnerProd
        rw [hD.hessian_ft hx0_mem]
      have hdec : dualNorm (localNorm F x0) (t 0 • c + gradient F x0) ≤ 1 / 4 := by
        have h := h_dec0
        unfold newtonDecrement at h
        rwa [hloc, hD.gradient_ft hx0_mem] at h
      have hprox0 := hD.prox_of_dualNorm hx0_mem hdec
      have hmem := hxC_mem 0
      rw [hx0'] at hmem ⊢
      have h := hD.newton_prox hx0_mem (by norm_num) (by norm_num) hprox0 hmem
      intro v
      refine (h v).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      norm_num
    | succ j ih =>
      have hxj := hxC_mem j
      set xj := xCentered F t x0 ν c j with hxj_def
      have hstep : xCentered F t x0 ν c (j + 1) =
          xj - (hessianOperator F xj).inverse (t (j + 1) • c + gradient F xj) := by
        show (pathFollowingStep F (t j) ν xj c).2 = _
        simp only [pathFollowingStep]
        rw [ht_rec j]
      have hprox1 : ∀ v, inner ℝ (t (j + 1) • c + gradient F xj) v ≤
          (31 / 200 + (31 / 200 + 1) / 13) * localNorm F xj v := by
        intro v
        have h1 := ih v
        have hN : 0 ≤ localNorm F xj v := Real.sqrt_nonneg _
        have h2 : -inner ℝ (gradient F xj) v ≤ Real.sqrt ν * localNorm F xj v := by
          have hb := barrier_B hD hν0 hconc hxj v
          rw [← hD.localNorm_sq hxj v] at hb
          have habs := Real.abs_le_sqrt hb
          rw [Real.sqrt_mul hν0.le, Real.sqrt_sq hN] at habs
          linarith [neg_abs_le (inner ℝ (gradient F xj) v)]
        have hexp : inner ℝ (t (j + 1) • c + gradient F xj) v =
            (1 + r) * inner ℝ (t j • c + gradient F xj) v - r * inner ℝ (gradient F xj) v := by
          rw [ht_rec j]
          simp only [inner_add_left, inner_smul_left, RCLike.conj_to_real]
          ring
        rw [hexp]
        have h3 : (1 + r) * inner ℝ (t j • c + gradient F xj) v ≤
            (1 + r) * (31 / 200 * localNorm F xj v) :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
        have h4 : -(r * inner ℝ (gradient F xj) v) ≤ r * (Real.sqrt ν * localNorm F xj v) := by
          have := mul_le_mul_of_nonneg_left h2 hr0.le
          linarith
        have h5 : r * (Real.sqrt ν * localNorm F xj v) = 1 / 13 * localNorm F xj v := by
          rw [← mul_assoc, hrs]
        nlinarith
      have hmem := hxC_mem (j + 1)
      rw [hstep] at hmem ⊢
      have h := hD.newton_prox hxj (by norm_num) (by norm_num) hprox1 hmem
      intro v
      refine (h v).trans ?_
      apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
      norm_num
  -- suboptimality at step k
  have hk := subopt h𝓧_convex hD hν1 hconc (hxC_mem k) hx_star_mem
    (by norm_num : (31 / 200 : ℝ) ≤ 1 / 3) (key k)
  have htk : ∀ m : ℕ, t m = t 0 * (1 + r) ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm => rw [ht_rec m, ihm, pow_succ]; ring
  have ht0 := ht_pos 0
  have hpow_pos : 0 < (1 + r) ^ k := by positivity
  -- exponential estimate
  have hrr : r / (1 + r) = 1 / (1 + 13 * Real.sqrt ν) := by
    rw [hr]; field_simp; ring
  have hexp1 : Real.exp (r / (1 + r)) ≤ 1 + r := by
    have h := Real.add_one_le_exp (-(r / (1 + r)))
    have h' : -(r / (1 + r)) + 1 = 1 / (1 + r) := by field_simp; ring
    rw [h', Real.exp_neg] at h
    have hpos := Real.exp_pos (r / (1 + r))
    rw [div_le_iff₀ (by linarith)] at h
    rw [inv_mul_eq_div, le_div_iff₀ hpos] at h
    linarith
  have hexpk : Real.exp ((k : ℝ) / (1 + 13 * Real.sqrt ν)) ≤ (1 + r) ^ k := by
    have : Real.exp ((k : ℝ) / (1 + 13 * Real.sqrt ν)) = Real.exp (r / (1 + r)) ^ k := by
      rw [← Real.exp_nat_mul, hrr]; ring_nf
    rw [this]
    exact pow_le_pow_left₀ (Real.exp_pos _).le hexp1 k
  have hgap : inner ℝ c (xCentered F t x0 ν c k) - inner ℝ c x_star ≤ 2 * ν / t k := by
    rw [le_div_iff₀ (ht_pos k)]; linarith
  refine hgap.trans ?_
  rw [htk k, neg_div, Real.exp_neg]
  have hE := Real.exp_pos ((k : ℝ) / (1 + 13 * Real.sqrt ν))
  have hinv : ((1 + r) ^ k)⁻¹ ≤ (Real.exp ((k : ℝ) / (1 + 13 * Real.sqrt ν)))⁻¹ :=
    inv_anti₀ hE hexpk
  have h2ν : 0 ≤ 2 * ν / t 0 := by positivity
  calc 2 * ν / (t 0 * (1 + r) ^ k) = 2 * ν / t 0 * ((1 + r) ^ k)⁻¹ := by
        field_simp
    _ ≤ 2 * ν / t 0 * (Real.exp ((k : ℝ) / (1 + 13 * Real.sqrt ν)))⁻¹ :=
        mul_le_mul_of_nonneg_left hinv h2ν

end ipm_path_following_bound_centered
