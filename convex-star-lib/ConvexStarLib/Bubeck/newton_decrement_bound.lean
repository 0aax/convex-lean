import ConvexStarLib.Defs

/-!
# `newton_decrement_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/newton_decrement_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace newton_decrement_bound`, so the main result is `newton_decrement_bound.newton_decrement_bound`.
-/

namespace newton_decrement_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-! ## Pure algebra: cubic quadrature (sharp Bernstein-type bound for binary cubics) -/
lemma cubic_quadrature (A B C D M c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1)
    (hp : ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 →
      |α ^ 3 * A + 3 * α ^ 2 * β * B + 3 * α * β ^ 2 * C + β ^ 3 * D| ≤ M) :
    |(4 * c ^ 3 - 3 * c) * A + (3 * s - 4 * s ^ 3) * B| ≤ M := by
  -- t = √3; the nodes are the rotations of (c, s) by 0, -120°, +120°
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t ^ 2 = 3 := ⟨Real.sqrt 3, Real.sq_sqrt (by norm_num)⟩
  have h1 : (-c / 2 + t / 2 * s) ^ 2 + (-s / 2 - t / 2 * c) ^ 2 = 1 := by
    linear_combination (t ^ 2 / 4 + 1 / 4) * hcs + (1 / 4) * ht
  have h2 : (-c / 2 - t / 2 * s) ^ 2 + (-s / 2 + t / 2 * c) ^ 2 = 1 := by
    linear_combination (t ^ 2 / 4 + 1 / 4) * hcs + (1 / 4) * ht
  have hp0 := hp c s hcs
  have hp1 := hp (-c / 2 + t / 2 * s) (-s / 2 - t / 2 * c) h1
  have hp2 := hp (-c / 2 - t / 2 * s) (-s / 2 + t / 2 * c) h2
  -- nonnegative weights summing to one
  have hw0 : 0 ≤ (4 * c ^ 2 - 1) ^ 2 / 9 := by positivity
  have hw1 : 0 ≤ (4 * (-c / 2 + t / 2 * s) ^ 2 - 1) ^ 2 / 9 := by positivity
  have hw2 : 0 ≤ (4 * (-c / 2 - t / 2 * s) ^ 2 - 1) ^ 2 / 9 := by positivity
  have hsum : (4 * c ^ 2 - 1) ^ 2 / 9 + (4 * (-c / 2 + t / 2 * s) ^ 2 - 1) ^ 2 / 9 + (4 * (-c / 2 - t / 2 * s) ^ 2 - 1) ^ 2 / 9 = 1 := by
    linear_combination (2*c^2 + 4*s^2*t^2/3 - 2*s^2 + 2/3) * hcs + (2*s^4*t^2/9 - 2*s^4/3 + 8*s^2/9) * ht
  -- the quadrature identity
  have hid : (4 * c ^ 3 - 3 * c) * A + (3 * s - 4 * s ^ 3) * B =
      (4 * c ^ 2 - 1) ^ 2 / 9 * (c ^ 3 * A + 3 * c ^ 2 * s * B + 3 * c * s ^ 2 * C + s ^ 3 * D) +
      (4 * (-c / 2 + t / 2 * s) ^ 2 - 1) ^ 2 / 9 * ((-c / 2 + t / 2 * s) ^ 3 * A + 3 * (-c / 2 + t / 2 * s) ^ 2 * (-s / 2 - t / 2 * c) * B + 3 * (-c / 2 + t / 2 * s) * (-s / 2 - t / 2 * c) ^ 2 * C + (-s / 2 - t / 2 * c) ^ 3 * D) +
      (4 * (-c / 2 - t / 2 * s) ^ 2 - 1) ^ 2 / 9 * ((-c / 2 - t / 2 * s) ^ 3 * A + 3 * (-c / 2 - t / 2 * s) ^ 2 * (-s / 2 + t / 2 * c) * B + 3 * (-c / 2 - t / 2 * s) * (-s / 2 + t / 2 * c) ^ 2 * C + (-s / 2 + t / 2 * c) ^ 3 * D) := by
    linear_combination
      (A*(-7*c^5/4 + 7*c^3*s^2*t^2/12 + 7*c^3*s^2/4 - 11*c^3/12 + 35*c*s^4*t^4/36 - 7*c*s^4*t^2/12 - 7*c*s^4/4 + c*s^2*t^2/36 + 8*c*s^2/3 + 3*c) + B*(-c^4*s*t^2/2 - 21*c^4*s/4 - 5*c^2*s^3*t^4/3 + 7*c^2*s^3*t^2/4 + 21*c^2*s^3/4 + c^2*s*t^2/6 - 11*c^2*s/4 - s^5*t^6/2 + 35*s^5*t^4/12 - 7*s^5*t^2/4 - 21*s^5/4 - s^3*t^4 + 7*s^3*t^2/12 + 8*s^3 - 3*s) + C*(c^5*t^2/12 + 5*c^3*s^2*t^4/6 - 11*c^3*s^2*t^2/12 - 21*c^3*s^2/4 - c^3*t^2/12 + 5*c*s^4*t^6/12 - 5*c*s^4*t^4/2 + 7*c*s^4*t^2/4 + 21*c*s^4/4 + c*s^2*t^4/3 + c*s^2*t^2/6 - 11*c*s^2/4) + D*(-c^4*s*t^4/9 + c^4*s*t^2/12 - c^2*s^3*t^6/9 + 11*c^2*s^3*t^4/18 - 5*c^2*s^3*t^2/12 - 7*c^2*s^3/4 - c^2*s*t^2/12 + 7*s^5*t^6/36 - 17*s^5*t^4/18 + 7*s^5*t^2/12 + 7*s^5/4 - s^3*t^6/9 + 4*s^3*t^4/9 - 11*s^3/12)) * hcs +
      (A*(7*c*s^6*t^4/36 - 7*c*s^6*t^2/18 - 7*c*s^6/12 + 25*c*s^4*t^2/36 + 53*c*s^4/36 + c*s^2/9) + B*(7*s^7*t^4/12 - 7*s^7*t^2/6 - 7*s^7/4 - s^5*t^4/2 + 9*s^5*t^2/4 + 53*s^5/12 - s^3*t^2 - 7*s^3/3) + C*(-7*c*s^6*t^4/12 + 7*c*s^6*t^2/6 + 7*c*s^6/4 + 5*c*s^4*t^4/12 - 5*c*s^4*t^2/4 - 8*c*s^4/3 + c*s^2*t^2/3 + c*s^2) + D*(-7*s^7*t^4/36 + 7*s^7*t^2/18 + 7*s^7/12 + 11*s^5*t^4/36 - 17*s^5*t^2/36 - 8*s^5/9 - s^3*t^4/9 + s^3*t^2/9 + s^3/3)) * ht
  have key : ∀ w0 w1 w2 p0 p1 p2 : ℝ, 0 ≤ w0 → 0 ≤ w1 → 0 ≤ w2 → w0 + w1 + w2 = 1 →
      |p0| ≤ M → |p1| ≤ M → |p2| ≤ M → |w0 * p0 + w1 * p1 + w2 * p2| ≤ M := by
    intro w0 w1 w2 p0 p1 p2 hw0 hw1 hw2 hs h0 h1 h2
    calc |w0 * p0 + w1 * p1 + w2 * p2| ≤ |w0 * p0| + |w1 * p1| + |w2 * p2| :=
          abs_add_three _ _ _
      _ = w0 * |p0| + w1 * |p1| + w2 * |p2| := by
          rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg hw0, abs_of_nonneg hw1,
            abs_of_nonneg hw2]
      _ ≤ w0 * M + w1 * M + w2 * M := by gcongr
      _ = M := by linear_combination M * hs
  rw [hid]
  exact key _ _ _ _ _ _ hw0 hw1 hw2 hsum hp0 hp1 hp2

/-! ## Abstract sharp trilinear bound -/
/-- Unit-normalized version of `trilinear_bound`: if `⟪a, H a⟫ = ⟪b, H b⟫ = 1` then
`|⟪b, J a a⟫| ≤ M`. -/
lemma trilinear_bound_unit {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (H : V →L[ℝ] V) (J : V →L[ℝ] V →L[ℝ] V) (M : ℝ)
    (hHsym : ∀ a b, inner ℝ a (H b) = inner ℝ b (H a))
    (hHpd : ∀ v, v ≠ 0 → 0 < inner ℝ v (H v))
    (hJsym1 : ∀ b c, J b c = J c b)
    (hJsym2 : ∀ a b c, inner ℝ a (J b c) = inner ℝ c (J b a))
    (hsc : ∀ v, |inner ℝ v (J v v)| ≤ M * (Real.sqrt (inner ℝ v (H v))) ^ 3)
    (a b : V) (ha : inner ℝ a (H a) = 1) (hb : inner ℝ b (H b) = 1) :
    |inner ℝ b (J a a)| ≤ M := by
  -- nonnegativity and definiteness of the quadratic form
  have hQnn : ∀ v, 0 ≤ inner ℝ v (H v) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hHpd v hv).le
  have hQ0 : ∀ v, inner ℝ v (H v) = 0 → v = 0 := by
    intro v hv
    by_contra hne
    exact (hHpd v hne).ne' hv
  -- the self-concordance bound for unit vectors
  have hsc1 : ∀ v, inner ℝ v (H v) = 1 → |inner ℝ v (J v v)| ≤ M := by
    intro v hv
    have := hsc v
    rwa [hv, Real.sqrt_one, one_pow, mul_one] at this
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = inner ℝ a (H b) := ⟨_, rfl⟩
  have hba : inner ℝ b (H a) = ρ := by rw [hρ]; exact hHsym b a
  obtain ⟨e', he'⟩ : ∃ e' : V, e' = b - ρ • a := ⟨_, rfl⟩
  have hae' : inner ℝ a (H e') = 0 := by
    rw [he', map_sub, map_smul, inner_sub_right, real_inner_smul_right, ha, ← hρ]
    ring
  have he'e' : inner ℝ e' (H e') = 1 - ρ ^ 2 := by
    rw [he', map_sub, map_smul, inner_sub_left, inner_sub_right, inner_sub_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      ha, hb, hba, ← hρ]
    ring
  have hρ2 : ρ ^ 2 ≤ 1 := by
    have := hQnn e'
    linarith
  have hρ1 : -1 ≤ ρ ∧ ρ ≤ 1 := by
    constructor <;> nlinarith
  rcases eq_or_lt_of_le hρ2 with hρeq | hρlt
  · -- degenerate case: `b = ρ • a` with `|ρ| = 1`
    have he'0 : e' = 0 := hQ0 e' (by rw [he'e', hρeq]; ring)
    have hb' : b = ρ • a := by
      rw [he'] at he'0
      exact sub_eq_zero.mp he'0
    have habs : |ρ| = 1 := by
      have h1 : |ρ| ^ 2 = 1 := by rw [sq_abs]; exact hρeq
      have h2 : 0 ≤ |ρ| := abs_nonneg ρ
      nlinarith
    rw [hb', real_inner_smul_left, abs_mul, habs, one_mul]
    exact hsc1 a ha
  · -- generic case: `b = ρ • a + σ • e` with `e` a unit vector `H`-orthogonal to `a`
    obtain ⟨σ, hσ⟩ : ∃ σ : ℝ, σ = Real.sqrt (1 - ρ ^ 2) := ⟨_, rfl⟩
    have hσpos : 0 < σ := by rw [hσ]; exact Real.sqrt_pos.mpr (by linarith)
    have hσsq : σ ^ 2 = 1 - ρ ^ 2 := by rw [hσ]; exact Real.sq_sqrt (by linarith)
    obtain ⟨e, he⟩ : ∃ e : V, e = σ⁻¹ • e' := ⟨_, rfl⟩
    have hae : inner ℝ a (H e) = 0 := by
      rw [he, map_smul, real_inner_smul_right, hae', mul_zero]
    have hea : inner ℝ e (H a) = 0 := by rw [hHsym]; exact hae
    have hee : inner ℝ e (H e) = 1 := by
      rw [he, map_smul, real_inner_smul_left, real_inner_smul_right, he'e', ← hσsq]
      field_simp
    -- symmetry identities for the trilinear form
    have hT1 : inner ℝ a (J a e) = inner ℝ e (J a a) := hJsym2 a a e
    have hT2 : inner ℝ a (J e a) = inner ℝ e (J a a) := by
      rw [hJsym1 e a]; exact hJsym2 a a e
    have hT3 : inner ℝ e (J a e) = inner ℝ a (J e e) := by
      rw [hJsym1 a e]; exact hJsym2 e e a
    have hT4 : inner ℝ e (J e a) = inner ℝ a (J e e) := hJsym2 e e a
    have hp : ∀ α β : ℝ, α ^ 2 + β ^ 2 = 1 →
        |α ^ 3 * inner ℝ a (J a a) + 3 * α ^ 2 * β * inner ℝ e (J a a)
          + 3 * α * β ^ 2 * inner ℝ a (J e e) + β ^ 3 * inner ℝ e (J e e)| ≤ M := by
      intro α β hαβ
      have hv : inner ℝ (α • a + β • e) (H (α • a + β • e)) = 1 := by
        simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
          real_inner_smul_right, ha, hae, hea, hee]
        linear_combination hαβ
      have hexp : inner ℝ (α • a + β • e) (J (α • a + β • e) (α • a + β • e)) =
          α ^ 3 * inner ℝ a (J a a) + 3 * α ^ 2 * β * inner ℝ e (J a a)
          + 3 * α * β ^ 2 * inner ℝ a (J e e) + β ^ 3 * inner ℝ e (J e e) := by
        simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
          ContinuousLinearMap.smul_apply, inner_add_left, inner_add_right,
          real_inner_smul_left, real_inner_smul_right]
        linear_combination (α ^ 2 * β) * hT1 + (α ^ 2 * β) * hT2 + (α * β ^ 2) * hT3
          + (α * β ^ 2) * hT4
      rw [← hexp]
      exact hsc1 _ hv
    have hcs : Real.cos (Real.arccos ρ / 3) ^ 2 + Real.sin (Real.arccos ρ / 3) ^ 2 = 1 :=
      Real.cos_sq_add_sin_sq _
    have key := cubic_quadrature _ _ _ _ M _ _ hcs hp
    have h3 : 3 * (Real.arccos ρ / 3) = Real.arccos ρ := by ring
    have hc3 : 4 * Real.cos (Real.arccos ρ / 3) ^ 3 - 3 * Real.cos (Real.arccos ρ / 3) = ρ := by
      rw [← Real.cos_three_mul, h3, Real.cos_arccos hρ1.1 hρ1.2]
    have hs3 : 3 * Real.sin (Real.arccos ρ / 3) - 4 * Real.sin (Real.arccos ρ / 3) ^ 3 = σ := by
      rw [← Real.sin_three_mul, h3, Real.sin_arccos, hσ]
    rw [hc3, hs3] at key
    have hbexp : inner ℝ b (J a a) = ρ * inner ℝ a (J a a) + σ * inner ℝ e (J a a) := by
      rw [he, he', real_inner_smul_left, inner_sub_left, real_inner_smul_left]
      field_simp
      ring
    rw [hbexp]
    exact key

lemma trilinear_bound {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (H : V →L[ℝ] V) (J : V →L[ℝ] V →L[ℝ] V) (M : ℝ)
    (hHsym : ∀ a b, inner ℝ a (H b) = inner ℝ b (H a))
    (hHpd : ∀ v, v ≠ 0 → 0 < inner ℝ v (H v))
    (hJsym1 : ∀ b c, J b c = J c b)
    (hJsym2 : ∀ a b c, inner ℝ a (J b c) = inner ℝ c (J b a))
    (hsc : ∀ v, |inner ℝ v (J v v)| ≤ M * (Real.sqrt (inner ℝ v (H v))) ^ 3)
    (a b : V) :
    |inner ℝ b (J a a)| ≤ M * inner ℝ a (H a) * Real.sqrt (inner ℝ b (H b)) := by
  by_cases ha0 : a = 0
  · subst ha0; simp
  by_cases hb0 : b = 0
  · subst hb0; simp
  have hpa : 0 < inner ℝ a (H a) := hHpd a ha0
  have hpb : 0 < inner ℝ b (H b) := hHpd b hb0
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = inner ℝ a (H a) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = inner ℝ b (H b) := ⟨_, rfl⟩
  rw [← hp] at hpa ⊢
  rw [← hq] at hpb ⊢
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hpa
  have hsq : 0 < Real.sqrt q := Real.sqrt_pos.mpr hpb
  have hpp : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hpa.le
  have hqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hpb.le
  -- normalize `a` and `b`
  have ha' : inner ℝ ((Real.sqrt p)⁻¹ • a) (H ((Real.sqrt p)⁻¹ • a)) = 1 := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← hp, ← mul_assoc, ← mul_inv,
      hpp, inv_mul_cancel₀ hpa.ne']
  have hb' : inner ℝ ((Real.sqrt q)⁻¹ • b) (H ((Real.sqrt q)⁻¹ • b)) = 1 := by
    rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← hq, ← mul_assoc, ← mul_inv,
      hqq, inv_mul_cancel₀ hpb.ne']
  have key := trilinear_bound_unit H J M hHsym hHpd hJsym1 hJsym2 hsc _ _ ha' hb'
  have hexp : inner ℝ ((Real.sqrt q)⁻¹ • b) (J ((Real.sqrt p)⁻¹ • a) ((Real.sqrt p)⁻¹ • a)) =
      (Real.sqrt q)⁻¹ * ((Real.sqrt p)⁻¹ * ((Real.sqrt p)⁻¹ * inner ℝ b (J a a))) := by
    simp only [map_smul, ContinuousLinearMap.smul_apply, real_inner_smul_left,
      real_inner_smul_right]
    ring
  rw [hexp, abs_mul, abs_mul, abs_mul, abs_of_pos (inv_pos.mpr hsq),
    abs_of_pos (inv_pos.mpr hsp), inv_mul_le_iff₀ hsq, inv_mul_le_iff₀ hsp,
    inv_mul_le_iff₀ hsp] at key
  calc |inner ℝ b (J a a)| ≤ Real.sqrt p * (Real.sqrt p * (Real.sqrt q * M)) := key
    _ = M * p * Real.sqrt q := by linear_combination (Real.sqrt q * M) * hpp

/-! ## Calculus facts on the open set `U` -/
section Calculus
variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}

lemma hasFDerivAt_f (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) :
    HasFDerivAt f (fderiv ℝ f y) y := by
  exact ((hcd.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num)).hasFDerivAt

lemma hasFDerivAt_gradient (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) :
    HasFDerivAt (gradient f) (hessianOperator f y) y := by
  have h3 : ContDiffAt ℝ 3 f y := hcd.contDiffAt (hU.mem_nhds hy)
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := h3.fderiv_right (by norm_num)
  have hL : ContDiff ℝ 2 (fun L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) =>
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L) :=
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toLinearIsometry.toContinuousLinearMap :
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n)).contDiff
  have hg : ContDiffAt ℝ 2 (gradient f) y := hL.contDiffAt.comp y h2
  exact (hg.differentiableAt (by norm_num)).hasFDerivAt

lemma hasFDerivAt_hessian (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) :
    HasFDerivAt (hessianOperator f) (jerkOperator f y) y := by
  have h3 : ContDiffAt ℝ 3 f y := hcd.contDiffAt (hU.mem_nhds hy)
  have h2 : ContDiffAt ℝ 2 (fderiv ℝ f) y := h3.fderiv_right (by norm_num)
  have hL : ContDiff ℝ 2 (fun L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) =>
      (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm L) :=
    ((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toLinearIsometry.toContinuousLinearMap :
      StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n)).contDiff
  have hg : ContDiffAt ℝ 2 (gradient f) y := hL.contDiffAt.comp y h2
  have hH : ContDiffAt ℝ 1 (hessianOperator f) y := hg.fderiv_right (by norm_num)
  exact (hH.differentiableAt (by norm_num)).hasFDerivAt

/-- Helper: over `ℝ`, `(toDual ℝ E).symm` is a continuous `ℝ`-linear map `L`, and
`gradient g = L ∘ fderiv ℝ g`. -/
lemma symmAux_exists_gradient_clm :
    ∃ L : StrongDual ℝ (EuclideanSpace ℝ (Fin n)) →L[ℝ] EuclideanSpace ℝ (Fin n),
      (∀ p, L p = (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm p) ∧
      ∀ g : EuclideanSpace ℝ (Fin n) → ℝ, gradient g = L ∘ fderiv ℝ g :=
  ⟨{ toFun := fun p => (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm p
     map_add' := fun p q => map_add _ p q
     map_smul' := fun c p => by simp
     cont := (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.continuous },
    fun _ => rfl, fun _ => rfl⟩

/-- Helper: the gradient of a `C³` function is `C²` at interior points. -/
lemma symmAux_gradient_contDiffAt (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) : ContDiffAt ℝ 2 (gradient f) y := by
  obtain ⟨L, -, hL⟩ := symmAux_exists_gradient_clm (n := n)
  rw [hL f]
  exact L.contDiff.contDiffAt.comp y
    ((hcd.contDiffAt (hU.mem_nhds hy)).fderiv_right (by norm_num))

lemma hess_symm (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (a b : EuclideanSpace ℝ (Fin n)) :
    inner ℝ a (hessianOperator f y b) = inner ℝ b (hessianOperator f y a) := by
  have hf : ContDiffAt ℝ 3 f y := hcd.contDiffAt (hU.mem_nhds hy)
  have hsymm : IsSymmSndFDerivAt ℝ f y :=
    hf.isSymmSndFDerivAt (by rw [minSmoothness_of_isRCLikeNormedField]; norm_num)
  obtain ⟨L, hL1, hL2⟩ := symmAux_exists_gradient_clm (n := n)
  have hdiff : DifferentiableAt ℝ (fderiv ℝ f) y :=
    (hf.fderiv_right (m := 2) (by norm_num)).differentiableAt (by norm_num)
  have hH : hessianOperator f y = L.comp (fderiv ℝ (fderiv ℝ f) y) := by
    have h1 : HasFDerivAt (L ∘ fderiv ℝ f) (L.comp (fderiv ℝ (fderiv ℝ f) y)) y :=
      L.hasFDerivAt.comp y hdiff.hasFDerivAt
    rw [← hL2 f] at h1
    exact h1.fderiv
  have key : ∀ u v, inner ℝ u (hessianOperator f y v) = fderiv ℝ (fderiv ℝ f) y v u := by
    intro u v
    rw [hH, ContinuousLinearMap.comp_apply, hL1, real_inner_comm,
      InnerProductSpace.toDual_symm_apply]
  rw [key, key]
  exact hsymm b a

lemma jerk_symm1 (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (b c : EuclideanSpace ℝ (Fin n)) :
    jerkOperator f y b c = jerkOperator f y c b :=
  (symmAux_gradient_contDiffAt hU hcd hy).isSymmSndFDerivAt
    (by rw [minSmoothness_of_isRCLikeNormedField]) b c

lemma jerk_symm2 (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (a b c : EuclideanSpace ℝ (Fin n)) :
    inner ℝ a (jerkOperator f y b c) = inner ℝ c (jerkOperator f y b a) := by
  have hJ : HasFDerivAt (hessianOperator f) (jerkOperator f y) y :=
    (((symmAux_gradient_contDiffAt hU hcd hy).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasFDerivAt
  have hd : ∀ u v : EuclideanSpace ℝ (Fin n),
      HasFDerivAt (fun z => inner ℝ u (hessianOperator f z v))
        ((innerSL ℝ u).comp
          ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) v).comp (jerkOperator f y))) y :=
    fun u v => (innerSL ℝ u).hasFDerivAt.comp y
      ((ContinuousLinearMap.apply ℝ (EuclideanSpace ℝ (Fin n)) v).hasFDerivAt.comp y hJ)
  have hev : (fun z => inner ℝ a (hessianOperator f z c) - inner ℝ c (hessianOperator f z a))
      =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    rw [hess_symm hU hcd hz a c, sub_self]
  have h0 := ((hasFDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq hev).unique ((hd a c).sub (hd c a))
  have h1 := congrArg (fun T => T b) h0
  simp only [ContinuousLinearMap.zero_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, innerSL_apply_apply] at h1
  linarith

lemma path_deriv_f (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {x h : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : x + t • h ∈ U) :
    HasDerivAt (fun s : ℝ => f (x + s • h)) (inner ℝ (gradient f (x + t • h)) h) t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hc := (hasFDerivAt_f hU hcd ht).comp_hasDerivAt t hp
  rw [gradient, InnerProductSpace.toDual_symm_apply]
  exact hc

lemma path_deriv_grad (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {x h : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : x + t • h ∈ U) (u : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => inner ℝ (gradient f (x + s • h)) u)
      (inner ℝ u (hessianOperator f (x + t • h) h)) t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hg := (hasFDerivAt_gradient hU hcd ht).comp_hasDerivAt t hp
  have hc := hg.inner ℝ (hasDerivAt_const t u)
  convert hc using 1
  rw [inner_zero_right, zero_add, real_inner_comm]

lemma path_deriv_hess (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    {x h : EuclideanSpace ℝ (Fin n)} {t : ℝ} (ht : x + t • h ∈ U) (v w : EuclideanSpace ℝ (Fin n)) :
    HasDerivAt (fun s : ℝ => inner ℝ v (hessianOperator f (x + s • h) w))
      (inner ℝ v (jerkOperator f (x + t • h) h w)) t := by
  have hp : HasDerivAt (fun s : ℝ => x + s • h) h t := by
    simpa using ((hasDerivAt_id t).smul_const h).const_add x
  have hH := (hasFDerivAt_hessian hU hcd ht).comp_hasDerivAt t hp
  have hHw := hH.clm_apply (hasDerivAt_const t w)
  have hc := (hasDerivAt_const t v).inner ℝ hHw
  convert hc using 1
  rw [map_zero, add_zero, inner_zero_left, add_zero]

lemma mixed_bound (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    (hsc : ∀ y ∈ U, ∀ v, |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ U) (a b : EuclideanSpace ℝ (Fin n)) :
    |inner ℝ b (jerkOperator f y a a)| ≤
      2 * inner ℝ a (hessianOperator f y a) * Real.sqrt (inner ℝ b (hessianOperator f y b)) :=
  trilinear_bound (hessianOperator f y) (jerkOperator f y) 2
    (hess_symm hU hcd hy) (hpd y hy) (jerk_symm1 hU hcd hy) (jerk_symm2 hU hcd hy)
    (fun v => hsc y hy v) a b

end Calculus

/-! ## Analysis along the Newton segment `t ↦ x + t • h` -/
section Segment
variable {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → ℝ} {U : Set (EuclideanSpace ℝ (Fin n))}

/-- `ψ(t) = ‖h‖²_{x+th} ≤ r²/(1-tr)²`, via monotonicity of `t ↦ ψ(t)^{-1/2} + t`. -/
lemma psi_bound (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    (hsc : ∀ y ∈ U, ∀ v, |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {x h : EuclideanSpace ℝ (Fin n)} (hh : h ≠ 0) {r : ℝ}
    (hr : r = Real.sqrt (inner ℝ h (hessianOperator f x h))) (hr4 : r ≤ 1 / 4)
    {τ : ℝ} (hτ1 : τ ≤ 1) (hseg : ∀ t ∈ Set.Icc (0:ℝ) τ, x + t • h ∈ U) :
    ∀ t ∈ Set.Icc (0:ℝ) τ,
      inner ℝ h (hessianOperator f (x + t • h) h) ≤ r ^ 2 / (1 - t * r) ^ 2 := by
  intro t ht
  have hτ0 : 0 ≤ τ := ht.1.trans ht.2
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) τ := ⟨le_refl _, hτ0⟩
  -- positivity of `ψ` along the segment
  have hψpos : ∀ s ∈ Set.Icc (0:ℝ) τ, 0 < inner ℝ h (hessianOperator f (x + s • h) h) :=
    fun s hs => hpd _ (hseg s hs) h hh
  have hψ0 : inner ℝ h (hessianOperator f (x + (0:ℝ) • h) h) =
      inner ℝ h (hessianOperator f x h) := by
    rw [zero_smul, add_zero]
  have hr0 : 0 < r := by
    rw [hr, ← hψ0]
    exact Real.sqrt_pos.mpr (hψpos 0 h0mem)
  -- derivative of `G(s) = ψ(s)^{-1/2} + s`
  have hG : ∀ s ∈ Set.Icc (0:ℝ) τ,
      HasDerivAt (fun y : ℝ => (Real.sqrt (inner ℝ h (hessianOperator f (x + y • h) h)))⁻¹ + y)
        (-(inner ℝ h (jerkOperator f (x + s • h) h h) /
            (2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)))) /
          (Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h))) ^ 2 + 1) s := by
    intro s hs
    have h1 := path_deriv_hess hU hcd (hseg s hs) h h
    have h2 := h1.sqrt (ne_of_gt (hψpos s hs))
    have h3 := h2.inv (Real.sqrt_ne_zero'.mpr (hψpos s hs))
    exact h3.add (hasDerivAt_id' s)
  -- the derivative of `G` is nonnegative (self-concordance)
  have hG'nonneg : ∀ s ∈ Set.Icc (0:ℝ) τ,
      0 ≤ -(inner ℝ h (jerkOperator f (x + s • h) h h) /
            (2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)))) /
          (Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h))) ^ 2 + 1 := by
    intro s hs
    have hq : 0 < Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) :=
      Real.sqrt_pos.mpr (hψpos s hs)
    have hb := hsc _ (hseg s hs) h
    simp only [localNorm, localInnerProd] at hb
    have hd : inner ℝ h (jerkOperator f (x + s • h) h h) ≤
        2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) *
          Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) ^ 2 := by
      calc inner ℝ h (jerkOperator f (x + s • h) h h)
          ≤ |inner ℝ h (jerkOperator f (x + s • h) h h)| := le_abs_self _
        _ ≤ 2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) ^ 3 := hb
        _ = 2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) *
              Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h)) ^ 2 := by ring
    have key : inner ℝ h (jerkOperator f (x + s • h) h h) /
          (2 * Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h))) /
          (Real.sqrt (inner ℝ h (hessianOperator f (x + s • h) h))) ^ 2 ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]
      exact hd
    rw [neg_div]
    linarith
  -- hence `G` is monotone on `[0, τ]`
  have hmono : MonotoneOn
      (fun y : ℝ => (Real.sqrt (inner ℝ h (hessianOperator f (x + y • h) h)))⁻¹ + y)
      (Set.Icc 0 τ) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 τ)
      (fun y hy => (hG y hy).continuousAt.continuousWithinAt)
      (fun y hy => (hG y (interior_subset hy)).hasDerivWithinAt)
      (fun y hy => hG'nonneg y (interior_subset hy))
  have hle := hmono h0mem ht ht.1
  simp only [zero_smul, add_zero] at hle
  rw [← hr] at hle
  -- hle : r⁻¹ ≤ (√ψ(t))⁻¹ + t
  have hq : 0 < Real.sqrt (inner ℝ h (hessianOperator f (x + t • h) h)) :=
    Real.sqrt_pos.mpr (hψpos t ht)
  have hsq : Real.sqrt (inner ℝ h (hessianOperator f (x + t • h) h)) ^ 2 =
      inner ℝ h (hessianOperator f (x + t • h) h) := Real.sq_sqrt (hψpos t ht).le
  rw [← hsq]
  generalize Real.sqrt (inner ℝ h (hessianOperator f (x + t • h) h)) = q at hq hle ⊢
  have htr : t * r ≤ 1 / 4 := by nlinarith [ht.1, ht.2]
  have hpos : 0 < 1 - t * r := by linarith
  have hkey : q * (1 - t * r) ≤ r := by
    have h1 := mul_le_mul_of_nonneg_right hle (le_of_lt (mul_pos hq hr0))
    have e1 : r⁻¹ * (q * r) = q := by field_simp
    have e2 : (q⁻¹ + t) * (q * r) = r + t * q * r := by field_simp
    rw [e1, e2] at h1
    linarith
  have hnn : 0 ≤ q * (1 - t * r) := by positivity
  rw [le_div_iff₀ (by positivity)]
  have := mul_le_mul hkey hkey hnn hr0.le
  linarith

/-- `f` stays bounded along the part of the segment inside `U`. -/
lemma f_bound (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    (hsc : ∀ y ∈ U, ∀ v, |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {x h : EuclideanSpace ℝ (Fin n)} (hh : h ≠ 0) {r : ℝ}
    (hr : r = Real.sqrt (inner ℝ h (hessianOperator f x h))) (hr4 : r ≤ 1 / 4)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hseg : ∀ t ∈ Set.Icc (0:ℝ) τ, x + t • h ∈ U) :
    f (x + τ • h) ≤ f x + |inner ℝ (gradient f x) h| + 1 := by
  have hψ := psi_bound hU hcd hsc hpd hh hr hr4 hτ1 hseg
  have hr0 : 0 ≤ r := by rw [hr]; exact Real.sqrt_nonneg _
  have h0mem : (0:ℝ) ∈ Set.Icc (0:ℝ) τ := ⟨le_refl _, hτ0⟩
  -- `ψ ≤ 1` on the segment
  have hψ1 : ∀ t ∈ Set.Icc (0:ℝ) τ, inner ℝ h (hessianOperator f (x + t • h) h) ≤ 1 := by
    intro t ht
    have h1 := hψ t ht
    have htr : t * r ≤ 1 / 4 := by nlinarith [ht.1, ht.2]
    have hpos : 3 / 4 ≤ 1 - t * r := by linarith
    have h2 : r ^ 2 / (1 - t * r) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    linarith
  -- `s ↦ ⟪∇f(x+sh), h⟫ - s` is antitone on `[0, τ]`
  have hanti1 : AntitoneOn (fun s : ℝ => inner ℝ (gradient f (x + s • h)) h - s)
      (Set.Icc 0 τ) := by
    have hd : ∀ s ∈ Set.Icc (0:ℝ) τ,
        HasDerivAt (fun s : ℝ => inner ℝ (gradient f (x + s • h)) h - s)
          (inner ℝ h (hessianOperator f (x + s • h) h) - 1) s :=
      fun s hs => (path_deriv_grad hU hcd (hseg s hs) h).sub (hasDerivAt_id' s)
    exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 τ)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => by linarith [hψ1 s (interior_subset hs)])
  -- hence `⟪∇f(x+sh), h⟫ ≤ |⟪∇f(x), h⟫| + 1` on `[0, τ]`
  have hF : ∀ s ∈ Set.Icc (0:ℝ) τ,
      inner ℝ (gradient f (x + s • h)) h ≤ |inner ℝ (gradient f x) h| + 1 := by
    intro s hs
    have h1 := hanti1 h0mem hs hs.1
    simp only [zero_smul, add_zero, sub_zero] at h1
    have h2 := le_abs_self (inner ℝ (gradient f x) h)
    linarith [hs.2]
  -- `s ↦ f(x+sh) - s (|⟪∇f(x), h⟫| + 1)` is antitone on `[0, τ]`
  have hanti2 : AntitoneOn
      (fun s : ℝ => f (x + s • h) - s * (|inner ℝ (gradient f x) h| + 1)) (Set.Icc 0 τ) := by
    have hd : ∀ s ∈ Set.Icc (0:ℝ) τ,
        HasDerivAt (fun s : ℝ => f (x + s • h) - s * (|inner ℝ (gradient f x) h| + 1))
          (inner ℝ (gradient f (x + s • h)) h - (|inner ℝ (gradient f x) h| + 1)) s :=
      fun s hs => (path_deriv_f hU hcd (hseg s hs)).sub
        (hasDerivAt_mul_const (|inner ℝ (gradient f x) h| + 1))
    exact antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 τ)
      (fun s hs => (hd s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hd s (interior_subset hs)).hasDerivWithinAt)
      (fun s hs => by linarith [hF s (interior_subset hs)])
  have h1 := hanti2 h0mem ⟨hτ0, le_refl _⟩ hτ0
  simp only [zero_smul, add_zero, zero_mul, sub_zero] at h1
  have h2 : τ * (|inner ℝ (gradient f x) h| + 1) ≤ |inner ℝ (gradient f x) h| + 1 := by
    have := abs_nonneg (inner ℝ (gradient f x) h)
    nlinarith
  linarith

/-- The whole segment `[x, x + h]` lies in the interior (Dikin ellipsoid + barrier property). -/
lemma seg_in_U {𝓧 : Set (EuclideanSpace ℝ (Fin n))} (hblow : BlowsUpOnBoundary 𝓧 f)
    (hcd : ContDiffOn ℝ 3 f (interior 𝓧))
    (hsc : ∀ y ∈ interior 𝓧, ∀ v,
      |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ interior 𝓧, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {x h : EuclideanSpace ℝ (Fin n)} (hx : x ∈ interior 𝓧) (hh : h ≠ 0) {r : ℝ}
    (hr : r = Real.sqrt (inner ℝ h (hessianOperator f x h))) (hr4 : r ≤ 1 / 4) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ interior 𝓧 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₀, ht₀, ht₀n⟩ := hcon
  -- the path `γ t = x + t • h`
  have hγc : Continuous (fun t : ℝ => x + t • h) :=
    continuous_const.add (continuous_id.smul continuous_const)
  -- the set of "bad" times
  let S : Set ℝ := Set.Icc (0:ℝ) 1 ∩ (fun t : ℝ => x + t • h) ⁻¹' (interior 𝓧)ᶜ
  have hSc : IsClosed S :=
    isClosed_Icc.inter (isOpen_interior.isClosed_compl.preimage hγc)
  have hSne : S.Nonempty := ⟨t₀, ht₀, ht₀n⟩
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1.1⟩
  have htsS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  have hts1 : sInf S ≤ 1 := htsS.1.2
  have htsn : x + sInf S • h ∉ interior 𝓧 := htsS.2
  have hts0 : 0 < sInf S := by
    rcases (htsS.1.1).lt_or_eq with h0 | h0
    · exact h0
    · exfalso
      apply htsn
      rw [← h0, zero_smul, add_zero]
      exact hx
  -- points strictly before `sInf S` lie in the interior
  have hbefore : ∀ t ∈ Set.Ico (0:ℝ) (sInf S), x + t • h ∈ interior 𝓧 := by
    intro t ht
    have hnot : t ∉ S := notMem_of_lt_csInf ht.2 hSbdd
    by_contra hc
    exact hnot ⟨⟨ht.1, le_trans ht.2.le hts1⟩, hc⟩
  -- `f` is bounded there
  have hfb : ∀ t ∈ Set.Ico (0:ℝ) (sInf S),
      f (x + t • h) ≤ f x + |inner ℝ (gradient f x) h| + 1 := by
    intro t ht
    apply f_bound isOpen_interior hcd hsc hpd hh hr hr4 ht.1 (le_trans ht.2.le hts1)
    intro s hs
    exact hbefore s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩
  -- limit along the left neighbourhood of `sInf S`
  have hlim : Filter.Tendsto (fun t : ℝ => x + t • h) (𝓝[<] (sInf S))
      (𝓝 (x + sInf S • h)) :=
    (hγc.tendsto (sInf S)).mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ t in 𝓝[<] (sInf S), x + t • h ∈ interior 𝓧 := by
    filter_upwards [Ioo_mem_nhdsLT hts0] with t ht
    exact hbefore t ⟨ht.1.le, ht.2⟩
  have hclos : x + sInf S • h ∈ closure 𝓧 :=
    closure_mono interior_subset (mem_closure_of_tendsto hlim hev)
  have hfront : x + sInf S • h ∈ frontier 𝓧 := ⟨hclos, htsn⟩
  have hlim' : Filter.Tendsto (fun t : ℝ => x + t • h) (𝓝[<] (sInf S))
      (𝓝[interior 𝓧] (x + sInf S • h)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, hev⟩
  have hbig : ∀ᶠ t in 𝓝[<] (sInf S),
      f x + |inner ℝ (gradient f x) h| + 1 + 1 ≤ f (x + t • h) :=
    hlim'.eventually (hblow (x + sInf S • h) hfront (f x + |inner ℝ (gradient f x) h| + 1 + 1))
  have hsmall : ∀ᶠ t in 𝓝[<] (sInf S),
      f (x + t • h) ≤ f x + |inner ℝ (gradient f x) h| + 1 := by
    filter_upwards [Ioo_mem_nhdsLT hts0] with t ht
    exact hfb t ⟨ht.1.le, ht.2⟩
  obtain ⟨t, ht1, ht2⟩ := (hbig.and hsmall).exists
  linarith

/-- Hessian comparison along the segment: `t ↦ ‖u‖²_{x+th} / (1-tr)²` is monotone. -/
lemma chi_compare (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    (hsc : ∀ y ∈ U, ∀ v, |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {x h : EuclideanSpace ℝ (Fin n)} (hh : h ≠ 0) {r : ℝ}
    (hr : r = Real.sqrt (inner ℝ h (hessianOperator f x h))) (hr4 : r ≤ 1 / 4)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ U) (u : EuclideanSpace ℝ (Fin n)) :
    ∀ t ∈ Set.Icc (0:ℝ) 1, inner ℝ u (hessianOperator f (x + t • h) u) ≤
      inner ℝ u (hessianOperator f (x + h) u) * ((1 - t * r) / (1 - r)) ^ 2 := by
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 < 1 - t * r := by
    intro t ht
    have : t * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht.2 hr0
    linarith
  have hχnn : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ inner ℝ u (hessianOperator f (x + t • h) u) := by
    intro t ht
    by_cases hu0 : u = 0
    · simp [hu0]
    · exact (hpd _ (hseg t ht) u hu0).le
  have hψ := psi_bound hU hcd hsc hpd hh hr hr4 le_rfl hseg
  -- derivative bound: χ'(1 - t r) + 2 r χ ≥ 0
  have hχd_bd : ∀ t ∈ Set.Icc (0:ℝ) 1,
      0 ≤ inner ℝ u (jerkOperator f (x + t • h) h u) * (1 - t * r)
        + 2 * r * inner ℝ u (hessianOperator f (x + t • h) u) := by
    intro t ht
    have hy := hseg t ht
    have e1 : inner ℝ u (jerkOperator f (x + t • h) h u)
        = inner ℝ h (jerkOperator f (x + t • h) u u) := by
      rw [jerk_symm1 hU hcd hy h u, jerk_symm2 hU hcd hy u u h]
    have hmb := mixed_bound hU hcd hsc hpd hy u h
    rw [← e1] at hmb
    have ha := hpos t ht
    have hsq : Real.sqrt (inner ℝ h (hessianOperator f (x + t • h) h)) * (1 - t * r) ≤ r := by
      have h1 := Real.sqrt_le_sqrt (hψ t ht)
      rw [← div_pow, Real.sqrt_sq (div_nonneg hr0 ha.le)] at h1
      exact (le_div_iff₀ ha).mp h1
    have hc := hχnn t ht
    have k1 := neg_le_abs (inner ℝ u (jerkOperator f (x + t • h) h u))
    have k2 := mul_le_mul_of_nonneg_right hmb ha.le
    have k3 := mul_le_mul_of_nonneg_left hsq hc
    have k4 := mul_le_mul_of_nonneg_right k1 ha.le
    nlinarith
  have hdd : ∀ t : ℝ, HasDerivAt (fun s : ℝ => (1 - s * r) ^ 2) (-(2 * r * (1 - t * r))) t := by
    intro t
    have := (((hasDerivAt_id' t).mul_const r).const_sub 1).fun_pow 2
    convert this using 1
    simp; ring
  have hGd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
      (fun s : ℝ => inner ℝ u (hessianOperator f (x + s • h) u) / (1 - s * r) ^ 2)
      ((inner ℝ u (jerkOperator f (x + t • h) h u) * (1 - t * r) ^ 2
        - inner ℝ u (hessianOperator f (x + t • h) u) * (-(2 * r * (1 - t * r))))
        / ((1 - t * r) ^ 2) ^ 2) t := by
    intro t ht
    exact (path_deriv_hess hU hcd (hseg t ht) u u).fun_div (hdd t)
      (pow_ne_zero 2 (hpos t ht).ne')
  have hGmono : MonotoneOn
      (fun s : ℝ => inner ℝ u (hessianOperator f (x + s • h) u) / (1 - s * r) ^ 2)
      (Set.Icc 0 1) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1)
      (f' := fun t => (inner ℝ u (jerkOperator f (x + t • h) h u) * (1 - t * r) ^ 2
        - inner ℝ u (hessianOperator f (x + t • h) u) * (-(2 * r * (1 - t * r))))
        / ((1 - t * r) ^ 2) ^ 2) ?_ ?_ ?_
    · intro t ht
      exact (hGd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hGd t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have ht' := Set.Ioo_subset_Icc_self ht
      have ha := hpos t ht'
      apply div_nonneg _ (by positivity)
      have := mul_nonneg ha.le (hχd_bd t ht')
      nlinarith
  intro t ht
  have h1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have key := hGmono ht h1 ht.2
  simp only [one_smul, one_mul] at key
  have ha := hpos t ht
  have hb : 0 < 1 - r := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)] at key
  rw [div_pow, ← mul_div_assoc, le_div_iff₀ (by positivity)]
  exact key

/-- The key estimate: `⟪∇f(x⁺), u⟫ ≤ r²/(1-r)²` whenever `‖u‖_{x⁺} ≤ 1`. -/
lemma grad_bound (hU : IsOpen U) (hcd : ContDiffOn ℝ 3 f U)
    (hsc : ∀ y ∈ U, ∀ v, |inner ℝ v (jerkOperator f y v v)| ≤ 2 * (localNorm f y v) ^ 3)
    (hpd : ∀ y ∈ U, ∀ v ≠ 0, 0 < inner ℝ v (hessianOperator f y v))
    {x h : EuclideanSpace ℝ (Fin n)} (hh : h ≠ 0) {r : ℝ}
    (hr : r = Real.sqrt (inner ℝ h (hessianOperator f x h))) (hr4 : r ≤ 1 / 4)
    (hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, x + t • h ∈ U)
    (hnewton : hessianOperator f x h = -gradient f x)
    (u : EuclideanSpace ℝ (Fin n)) (hu : inner ℝ u (hessianOperator f (x + h) u) ≤ 1) :
    inner ℝ (gradient f (x + h)) u ≤ r ^ 2 / (1 - r) ^ 2 := by
  have hr0 : 0 ≤ r := hr ▸ Real.sqrt_nonneg _
  have hb : 0 < 1 - r := by linarith
  have hpos : ∀ t ∈ Set.Icc (0:ℝ) 1, 1 - r ≤ 1 - t * r := by
    intro t ht
    have : t * r ≤ 1 * r := mul_le_mul_of_nonneg_right ht.2 hr0
    linarith
  have hψ := psi_bound hU hcd hsc hpd hh hr hr4 le_rfl hseg
  have hχ := chi_compare hU hcd hsc hpd hh hr hr4 hseg u
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 2 * r ^ 2 / (1 - r) ^ 2 := ⟨_, rfl⟩
  -- second derivative bound: φ''(t) ≤ K
  have hφ2 : ∀ t ∈ Set.Icc (0:ℝ) 1, inner ℝ u (jerkOperator f (x + t • h) h h) ≤ K := by
    intro t ht
    have hy := hseg t ht
    have ha : 0 < 1 - t * r := lt_of_lt_of_le hb (hpos t ht)
    have ha' : 1 - t * r ≠ 0 := ha.ne'
    have hb' : 1 - r ≠ 0 := hb.ne'
    have hmb := mixed_bound hU hcd hsc hpd hy h u
    have hχt : inner ℝ u (hessianOperator f (x + t • h) u) ≤ ((1 - t * r) / (1 - r)) ^ 2 := by
      have hsq : 0 ≤ ((1 - t * r) / (1 - r)) ^ 2 := by positivity
      calc _ ≤ _ := hχ t ht
        _ ≤ 1 * ((1 - t * r) / (1 - r)) ^ 2 := mul_le_mul_of_nonneg_right hu hsq
        _ = _ := one_mul _
    have hsqrt : Real.sqrt (inner ℝ u (hessianOperator f (x + t • h) u))
        ≤ (1 - t * r) / (1 - r) := by
      have h1 := Real.sqrt_le_sqrt hχt
      rwa [Real.sqrt_sq (div_nonneg ha.le hb.le)] at h1
    calc inner ℝ u (jerkOperator f (x + t • h) h h)
        ≤ |inner ℝ u (jerkOperator f (x + t • h) h h)| := le_abs_self _
      _ ≤ 2 * inner ℝ h (hessianOperator f (x + t • h) h)
            * Real.sqrt (inner ℝ u (hessianOperator f (x + t • h) u)) := hmb
      _ ≤ 2 * (r ^ 2 / (1 - t * r) ^ 2) * ((1 - t * r) / (1 - r)) :=
          mul_le_mul (by linarith [hψ t ht]) hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = 2 * r ^ 2 / ((1 - t * r) * (1 - r)) := by
          field_simp
      _ ≤ 2 * r ^ 2 / ((1 - r) * (1 - r)) :=
          div_le_div_of_nonneg_left (by positivity) (mul_pos hb hb)
            (mul_le_mul_of_nonneg_right (hpos t ht) hb.le)
      _ = K := by rw [hK]; ring
  have hIcc0 : (0:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have hIcc1 : (1:ℝ) ∈ Set.Icc (0:ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  -- t ↦ φ'(t) - t K is antitone
  have hA : AntitoneOn
      (fun s : ℝ => inner ℝ u (hessianOperator f (x + s • h) h) - s * K) (Set.Icc 0 1) := by
    have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
        (fun s : ℝ => inner ℝ u (hessianOperator f (x + s • h) h) - s * K)
        (inner ℝ u (jerkOperator f (x + t • h) h h) - K) t := fun t ht =>
      (path_deriv_hess hU hcd (hseg t ht) u h).sub (hasDerivAt_mul_const K)
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (f' := fun t => inner ℝ u (jerkOperator f (x + t • h) h h) - K) ?_ ?_ ?_
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      have := hφ2 t (Set.Ioo_subset_Icc_self ht)
      simp only
      linarith
  obtain ⟨p0, hp0⟩ : ∃ p : ℝ, p = inner ℝ u (hessianOperator f x h) := ⟨_, rfl⟩
  have hφ1 : ∀ t ∈ Set.Icc (0:ℝ) 1,
      inner ℝ u (hessianOperator f (x + t • h) h) - p0 - t * K ≤ 0 := by
    intro t ht
    have := hA hIcc0 ht ht.1
    simp only [zero_smul, add_zero, zero_mul, sub_zero] at this
    rw [hp0]
    linarith
  -- t ↦ φ(t) - t φ'(0) - t² K/2 is antitone
  have hB : AntitoneOn
      (fun s : ℝ => inner ℝ (gradient f (x + s • h)) u - s * p0 - s ^ 2 * (K / 2))
      (Set.Icc 0 1) := by
    have hd : ∀ t ∈ Set.Icc (0:ℝ) 1, HasDerivAt
        (fun s : ℝ => inner ℝ (gradient f (x + s • h)) u - s * p0 - s ^ 2 * (K / 2))
        (inner ℝ u (hessianOperator f (x + t • h) h) - p0 - t * K) t := by
      intro t ht
      have := ((path_deriv_grad hU hcd (hseg t ht) u).sub (hasDerivAt_mul_const p0)).sub
        ((hasDerivAt_pow 2 t).mul_const (K / 2))
      convert this using 1
      push_cast
      ring
    refine antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      (f' := fun t => inner ℝ u (hessianOperator f (x + t • h) h) - p0 - t * K) ?_ ?_ ?_
    · intro t ht
      exact (hd t ht).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact (hd t (Set.Ioo_subset_Icc_self ht)).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      exact hφ1 t (Set.Ioo_subset_Icc_self ht)
  have key := hB hIcc0 hIcc1 zero_le_one
  simp only [zero_smul, add_zero, one_smul, zero_mul, one_mul, sub_zero, one_pow,
    ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] at key
  have hsum : inner ℝ (gradient f x) u + p0 = 0 := by
    rw [hp0, hnewton, inner_neg_right, real_inner_comm]
    ring
  have hK2 : K / 2 = r ^ 2 / (1 - r) ^ 2 := by rw [hK]; ring
  linarith

end Segment

/-! ## Cauchy–Schwarz for a symmetric positive semidefinite form -/
lemma cs_form {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] (H : V →L[ℝ] V)
    (hsym : ∀ a b, inner ℝ a (H b) = inner ℝ b (H a)) (hpsd : ∀ v, 0 ≤ inner ℝ v (H v))
    (a b : V) :
    |inner ℝ a (H b)| ≤ Real.sqrt (inner ℝ a (H a)) * Real.sqrt (inner ℝ b (H b)) := by
  have key : ∀ t : ℝ, 0 ≤ inner ℝ b (H b) * (t * t) + 2 * inner ℝ a (H b) * t
      + inner ℝ a (H a) := by
    intro t
    have h0 := hpsd (a + t • b)
    simp only [map_add, map_smul, inner_add_left, inner_add_right, real_inner_smul_left,
      real_inner_smul_right] at h0
    rw [hsym b a] at h0
    nlinarith [h0]
  have hd := discrim_le_zero key
  unfold discrim at hd
  rw [← Real.sqrt_mul (hpsd a)]
  apply Real.abs_le_sqrt
  nlinarith [hd]

theorem newton_decrement_bound
  {n : ℕ}
  (𝓧 : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : EuclideanSpace ℝ (Fin n))
  (hx : x ∈ interior 𝓧)
  (h_dec : newtonDecrement f x ≤ 1 / 4)
  (hf : IsStandardSelfConcordantBarrier 𝓧 f) :
  newtonDecrement f (newtonStep f x)
    ≤ 2 * (newtonDecrement f x) ^ 2 := by
  obtain ⟨⟨_hconvOn, hcd, hsc, hpd⟩, hblow⟩ := hf
  have hU : IsOpen (interior 𝓧) := isOpen_interior
  set g := gradient f x with hg
  set H := hessianOperator f x with hH
  have hpsd : ∀ v, 0 ≤ inner ℝ v (H v) := by
    intro v
    by_cases hv : v = 0
    · simp [hv]
    · exact (hpd x hx v hv).le
  -- injectivity / invertibility of the Hessian
  have hinj : Function.Injective H := by
    intro a b hab
    by_contra hne
    have h1 := hpd x hx (a - b) (sub_ne_zero.mpr hne)
    rw [map_sub, hab, sub_self, inner_zero_right] at h1
    exact lt_irrefl _ h1
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    (LinearEquiv.ofInjectiveEndo
      (H : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n)) hinj).toContinuousLinearEquiv
  have he : (e : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)) = H := by
    ext v; rfl
  have hinv : ∀ v, H (H.inverse v) = v := by
    intro v
    rw [← he, ContinuousLinearMap.inverse_equiv]
    simp
  set h := -(H.inverse g) with hhdef
  have hstep : newtonStep f x = x + h := by
    simp only [newtonStep, hhdef]
    rw [sub_eq_add_neg]
  have hnewton : H h = -g := by
    rw [hhdef, map_neg, hinv]
  have hg' : g = -(H h) := by rw [hnewton, neg_neg]
  set r := Real.sqrt (inner ℝ h (H h)) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r ^ 2 = inner ℝ h (H h) := Real.sq_sqrt (hpsd h)
  -- r ≤ λ(x)
  have hrlam : r ≤ newtonDecrement f x := by
    unfold newtonDecrement dualNorm
    have hbdd : BddAbove {v | ∃ w, localNorm f x w ≤ 1 ∧ v = inner ℝ (gradient f x) w} := by
      refine ⟨r, ?_⟩
      rintro v ⟨w, hw, rfl⟩
      have hw' : Real.sqrt (inner ℝ w (H w)) ≤ 1 := hw
      have hcs := cs_form H (hess_symm hU hcd hx) hpsd w h
      rw [← hg, hg', inner_neg_left, real_inner_comm]
      have : -inner ℝ w (H h) ≤ |inner ℝ w (H h)| := neg_le_abs _
      have h2 : Real.sqrt (inner ℝ w (H w)) * r ≤ 1 * r :=
        mul_le_mul_of_nonneg_right hw' hr0
      linarith
    by_cases hrz : r = 0
    · rw [hrz]
      apply le_csSup hbdd
      refine ⟨0, ?_, ?_⟩
      · simp [localNorm, localInnerProd]
      · simp
    · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrz)
      apply le_csSup hbdd
      refine ⟨-(r⁻¹) • h, ?_, ?_⟩
      · show Real.sqrt (inner ℝ (-(r⁻¹) • h) (H (-(r⁻¹) • h))) ≤ 1
        rw [map_smul, real_inner_smul_left, real_inner_smul_right, ← hrr]
        have : -r⁻¹ * (-r⁻¹ * r ^ 2) = 1 := by field_simp
        rw [this, Real.sqrt_one]
      · rw [← hg, real_inner_smul_right, hg', inner_neg_left, real_inner_comm, ← hrr]
        field_simp
  have hr4 : r ≤ 1 / 4 := hrlam.trans h_dec
  by_cases hh : h = 0
  · have hg0 : g = 0 := by rw [hg', hh, map_zero, neg_zero]
    have hle : newtonDecrement f (newtonStep f x) ≤ 0 := by
      rw [hstep, hh, add_zero]
      unfold newtonDecrement dualNorm
      apply Real.sSup_nonpos
      rintro v ⟨w, -, rfl⟩
      rw [← hg, hg0, inner_zero_left]
    nlinarith [sq_nonneg (newtonDecrement f x)]
  · have hseg := seg_in_U hblow hcd hsc hpd hx hh hr hr4
    have key : newtonDecrement f (newtonStep f x) ≤ r ^ 2 / (1 - r) ^ 2 := by
      rw [hstep]
      unfold newtonDecrement dualNorm
      apply Real.sSup_le
      · rintro v ⟨u, hu, rfl⟩
        apply grad_bound hU hcd hsc hpd hh hr hr4 hseg hnewton u
        have hu' : Real.sqrt (inner ℝ u (hessianOperator f (x + h) u)) ≤ 1 := hu
        exact Real.sqrt_le_one.mp hu'
      · positivity
    have h1 : r ^ 2 / (1 - r) ^ 2 ≤ 2 * r ^ 2 := by
      rw [div_le_iff₀ (by nlinarith)]
      nlinarith [sq_nonneg r]
    have h2 : 2 * r ^ 2 ≤ 2 * (newtonDecrement f x) ^ 2 := by
      nlinarith
    linarith

end newton_decrement_bound
