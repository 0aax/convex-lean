import ConvexStarLib.Defs

/-!
# `FCA_chap_B_4_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_4_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_4_2_1`, so the main result is `FCA_chap_B_4_2_1.FCA_chap_B_4_2_1`.
-/

namespace FCA_chap_B_4_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_4_2_1
  (f : E → EReal)
  (x : E)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ y, ⊥ < f y)
  (hx : x ∈ interior (effDom f)) :
  let g := fun (d : E) =>
    limUnder (𝓝[>] 0) (fun (t : ℝ) => t⁻¹ * ((f (x + t • d)).toReal - (f x).toReal))
  List.TFAE [
    IsLinearOn Set.univ (liftRealtoEReal g),
    ∃ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E),
      ∀ i, DifferentiableAt ℝ (fun (t : ℝ) => (f (x + t • b i)).toReal) 0,
    DifferentiableAt ℝ (fun y => (f y).toReal) x
  ] := by
  intro g
  obtain ⟨ε, hε, hball⟩ : ∃ ε > 0, Metric.ball x ε ⊆ effDom f :=
    Metric.mem_nhds_iff.mp (mem_interior_iff_mem_nhds.mp hx)
  have hfin : ∀ y ∈ Metric.ball x ε, f y = ((f y).toReal : EReal) := by
    intro y hy
    exact (EReal.coe_toReal (hball hy).ne (f_ne_bot y).ne').symm
  have hFconv : ConvexOn ℝ (Metric.ball x ε) (fun y => (f y).toReal) := by
    refine ⟨convex_ball x ε, ?_⟩
    intro y hy z hz a b ha hb hab
    have hyz : a • y + b • z ∈ Metric.ball x ε := convex_ball x ε hy hz ha hb hab
    have hmem := hf_convex.2.2 (show (y, (f y).toReal) ∈ epigraph f from le_of_eq (hfin y hy))
      (show (z, (f z).toReal) ∈ epigraph f from le_of_eq (hfin z hz)) ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
    rw [hfin _ hyz] at hmem
    exact_mod_cast hmem
  have dir_deriv_aux : ∀ (F : E → ℝ), ConvexOn ℝ (Metric.ball x ε) F → ∀ d : E,
      HasDerivWithinAt (fun t : ℝ => F (x + t • d))
        (limUnder (𝓝[>] 0) (fun t : ℝ => t⁻¹ * (F (x + t • d) - F x))) (Set.Ioi 0) 0 := by
    intro F hF d
    set S : Set ℝ := {t : ℝ | x + t • d ∈ Metric.ball x ε} with hS
    have hSopen : IsOpen S :=
      Metric.isOpen_ball.preimage (continuous_const.add (continuous_id.smul continuous_const))
    have h0S : (0 : ℝ) ∈ S := by simp [hS, hε]
    have hconv : ConvexOn ℝ S (fun t : ℝ => F (x + t • d)) := by
      have := (hF.translate_right x).comp_linearMap (LinearMap.toSpanSingleton ℝ E d)
      exact this
    have h0int : (0:ℝ) ∈ interior S := by rw [hSopen.interior_eq]; exact h0S
    have hR := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior h0int
    have hlim : limUnder (𝓝[>] 0) (fun t : ℝ => t⁻¹ * (F (x + t • d) - F x)) =
        derivWithin (fun t : ℝ => F (x + t • d)) (Set.Ioi 0) 0 := by
      apply Filter.Tendsto.limUnder_eq
      have ht := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl (0:ℝ))).mp hR
      refine ht.congr ?_
      intro t
      simp [slope_def_field, div_eq_inv_mul]
    rw [hlim]; exact hR
  have diff_of_partial : ∀ (F : E → ℝ), ConvexOn ℝ (Metric.ball x ε) F →
      ∀ (b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E),
      (∀ i, DifferentiableAt ℝ (fun t : ℝ => F (x + t • b i)) 0) → DifferentiableAt ℝ F x := by
    intro F hF b hb
    classical
    set c : Fin (Module.finrank ℝ E) → ℝ := fun i => deriv (fun t : ℝ => F (x + t • b i)) 0 with hc_def
    have hc : ∀ i, HasDerivAt (fun t : ℝ => F (x + t • b i)) (c i) 0 := fun i => (hb i).hasDerivAt
    have hr : ∀ i, (fun s : ℝ => F (x + s • b i) - F x - s * c i) =o[𝓝 0] (fun s => s) := by
      intro i
      have := hasDerivAt_iff_isLittleO.mp (hc i)
      simpa using this
    let p : Fin (Module.finrank ℝ E) → (E →L[ℝ] ℝ) := fun i => LinearMap.toContinuousLinearMap (b.coord i)
    have hp : ∀ i h, p i h = b.repr h i := fun i h => rfl
    let L : E →L[ℝ] ℝ := ∑ i, c i • p i
    have hL : ∀ h, L h = ∑ i, c i * b.repr h i := by
      intro h; simp [L, hp]
    refine ⟨L, ?_⟩
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    set N : ℝ := (Fintype.card (Fin (Module.finrank ℝ E)) : ℝ) with hN
    have hq : ∀ (σ : ℝ) (i : Fin (Module.finrank ℝ E)), (fun h : E => ‖F (x + (σ * b.repr h i) • b i) - F x
        - (σ * b.repr h i) * c i‖) =o[𝓝 0] (fun h => h) := by
      intro σ i
      let q : E →L[ℝ] ℝ := σ • p i
      have hq_apply : ∀ h, q h = σ * b.repr h i := fun h => rfl
      have hqt : Filter.Tendsto (fun h : E => q h) (𝓝 0) (𝓝 0) := by
        have := q.continuous.tendsto 0
        simpa using this
      have h1 := (hr i).comp_tendsto hqt
      have h2 := (h1.trans_isBigO (q.isBigO_id (𝓝 0))).norm_left
      simpa [Function.comp_def, hq_apply] using h2
    have hRo : (fun h : E => ∑ i, (‖F (x + (N * b.repr h i) • b i) - F x - (N * b.repr h i) * c i‖
        + ‖F (x + (-N * b.repr h i) • b i) - F x - (-N * b.repr h i) * c i‖)) =o[𝓝 0]
        (fun h => h) :=
      Asymptotics.IsLittleO.sum fun i _ => (hq N i).add (hq (-N) i)
    refine Asymptotics.IsBigO.trans_isLittleO ?_ hRo
    refine Asymptotics.IsBigO.of_bound' ?_
    have key : ∀ u : E → E, Continuous u → u 0 = x → ∀ᶠ h in 𝓝 (0:E), u h ∈ Metric.ball x ε := by
      intro u hu hu0
      have := hu.tendsto 0
      rw [hu0] at this
      exact this.eventually_mem (Metric.ball_mem_nhds x hε)
    have hpc : ∀ i, Continuous (fun h : E => b.repr h i) := fun i => (p i).continuous
    have hev1 : ∀ᶠ h in 𝓝 (0:E), x + h ∈ Metric.ball x ε :=
      key _ (by fun_prop) (by simp)
    have hev2 : ∀ᶠ h in 𝓝 (0:E), x + -h ∈ Metric.ball x ε :=
      key _ (by fun_prop) (by simp)
    have hev3 : ∀ᶠ h in 𝓝 (0:E), ∀ i, x + (N * b.repr h i) • b i ∈ Metric.ball x ε := by
      refine Filter.eventually_all.mpr fun i => key _ ?_ (by simp)
      have := hpc i
      fun_prop
    have hev4 : ∀ᶠ h in 𝓝 (0:E), ∀ i, x + (-N * b.repr h i) • b i ∈ Metric.ball x ε := by
      refine Filter.eventually_all.mpr fun i => key _ ?_ (by simp)
      have := hpc i
      fun_prop
    filter_upwards [hev1, hev2, hev3, hev4] with h h1 h2 h3 h4

    rcases isEmpty_or_nonempty (Fin (Module.finrank ℝ E)) with hι | hι
    · have hh0 : h = 0 := by
        rw [← b.sum_repr h]; simp
      subst hh0
      simp
    · have hNpos : (0:ℝ) < N := by rw [hN]; exact_mod_cast Fintype.card_pos
      have hN1 : 1 / N ≤ 1 := by
        rw [div_le_one hNpos, hN]; exact_mod_cast Fintype.card_pos
      have hw0 : ∀ i ∈ (Finset.univ : Finset (Fin (Module.finrank ℝ E))), (0:ℝ) ≤ 1/N := fun _ _ => by positivity
      have hw1 : ∑ _i : Fin (Module.finrank ℝ E), (1/N : ℝ) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hN]; field_simp
      have hJ1 := hF.map_sum_le hw0 hw1 (p := fun i => x + (N * b.repr h i) • b i)
        (fun i _ => h3 i)
      have hJ2 := hF.map_sum_le hw0 hw1 (p := fun i => x + (-N * b.repr h i) • b i)
        (fun i _ => h4 i)
      have hsum1 : ∑ i, (1/N : ℝ) • (x + (N * b.repr h i) • b i) = x + h := by
        simp only [smul_add, Finset.sum_add_distrib, smul_smul]
        rw [← Finset.sum_smul, hw1, one_smul]
        congr 1
        conv_rhs => rw [← b.sum_repr h]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        field_simp
      have hsum2 : ∑ i, (1/N : ℝ) • (x + (-N * b.repr h i) • b i) = x + -h := by
        simp only [smul_add, Finset.sum_add_distrib, smul_smul]
        rw [← Finset.sum_smul, hw1, one_smul]
        congr 1
        conv_rhs => rw [← b.sum_repr h, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← neg_smul]
        congr 1
        field_simp
      simp only at hJ1 hJ2
      rw [hsum1] at hJ1
      rw [hsum2] at hJ2
      have hmid := hF.2 h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      have hmid' : (1/2 : ℝ) • (x + h) + (1/2 : ℝ) • (x + -h) = x := by
        rw [← smul_add]
        have : x + h + (x + -h) = (2:ℝ) • x := by rw [two_smul]; abel
        rw [this, smul_smul]; norm_num
      rw [hmid'] at hmid
      simp only [smul_eq_mul] at hJ1 hJ2 hmid
      have hLsum : L h = ∑ i, (1/N) * ((N * b.repr h i) * c i) := by
        rw [hL]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
      have hLsum' : L h = - ∑ i, (1/N) * ((-N * b.repr h i) * c i) := by
        rw [hL, ← Finset.sum_neg_distrib]; refine Finset.sum_congr rfl fun i _ => ?_; field_simp
      have hFx : ∑ _i : Fin (Module.finrank ℝ E), (1/N) * F x = F x := by rw [← Finset.sum_mul, hw1, one_mul]
      have hterm : ∀ r : ℝ, (1/N) * r ≤ ‖r‖ := fun r =>
        (mul_le_mul_of_nonneg_left (Real.le_norm_self r) (by positivity)).trans
          (mul_le_of_le_one_left (norm_nonneg _) hN1)
      have eU : F (x + h) - F x - L h ≤
          ∑ i, ‖F (x + (N * b.repr h i) • b i) - F x - N * b.repr h i * c i‖ := by
        have e1 : ∑ i, (1/N) * F (x + (N * b.repr h i) • b i) - F x - L h =
            ∑ i, (1/N) * (F (x + (N * b.repr h i) • b i) - F x - N * b.repr h i * c i) := by
          rw [hLsum]
          conv_lhs => rw [← hFx]
          simp only [mul_sub, Finset.sum_sub_distrib]
        calc F (x + h) - F x - L h ≤ ∑ i, (1/N) * F (x + (N * b.repr h i) • b i) - F x - L h := by
              linarith
          _ = ∑ i, (1/N) * (F (x + (N * b.repr h i) • b i) - F x - N * b.repr h i * c i) := e1
          _ ≤ _ := Finset.sum_le_sum fun i _ => hterm _
      have eV : -(F (x + h) - F x - L h) ≤
          ∑ i, ‖F (x + (-N * b.repr h i) • b i) - F x - -N * b.repr h i * c i‖ := by
        have e1 : ∑ i, (1/N) * F (x + (-N * b.repr h i) • b i) - F x + L h =
            ∑ i, (1/N) * (F (x + (-N * b.repr h i) • b i) - F x - -N * b.repr h i * c i) := by
          rw [hLsum']
          conv_lhs => rw [← hFx]
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        calc -(F (x + h) - F x - L h) ≤ ∑ i, (1/N) * F (x + (-N * b.repr h i) • b i) - F x + L h := by
              linarith
          _ = ∑ i, (1/N) * (F (x + (-N * b.repr h i) • b i) - F x - -N * b.repr h i * c i) := e1
          _ ≤ _ := Finset.sum_le_sum fun i _ => hterm _
      have hs1 : 0 ≤ ∑ i, ‖F (x + (N * b.repr h i) • b i) - F x - N * b.repr h i * c i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      have hs2 : 0 ≤ ∑ i, ‖F (x + (-N * b.repr h i) • b i) - F x - -N * b.repr h i * c i‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      rw [Finset.sum_add_distrib, Real.norm_of_nonneg (add_nonneg hs1 hs2), Real.norm_eq_abs,
        abs_le]
      constructor <;> linarith
  have hdir : ∀ d : E,
      HasDerivWithinAt (fun t : ℝ => (f (x + t • d)).toReal) (g d) (Set.Ioi 0) 0 :=
    fun d => dir_deriv_aux (fun y => (f y).toReal) hFconv d
  tfae_have 1 → 2 := by
    intro hlin
    have hneg : ∀ d, g (-d) = -g d := by
      intro d
      have h := hlin d d (-1) 0 (Set.mem_univ _) (Set.mem_univ _) (Set.mem_univ _)
      simp only [liftRealtoEReal] at h
      have e : (-1 : ℝ) • d + (0:ℝ) • d = -d := by simp
      rw [e] at h
      have h2 : g (-d) = -1 * g d + 0 * g d := by exact_mod_cast h
      linarith
    have hderiv : ∀ d, HasDerivAt (fun t : ℝ => (f (x + t • d)).toReal) (g d) 0 := by
      intro d
      have hR := hdir d
      have hL : HasDerivWithinAt (fun t : ℝ => (f (x + t • d)).toReal) (g d) (Set.Iio 0) 0 := by
        have h1 := hdir (-d)
        have h2 : HasDerivWithinAt (fun t : ℝ => -t) (-1) (Set.Iio 0) 0 :=
          (hasDerivAt_neg' 0).hasDerivWithinAt
        have hmaps : Set.MapsTo (fun t : ℝ => -t) (Set.Iio 0) (Set.Ioi 0) := by
          intro t ht; simpa using ht
        have h3 := h1.comp_of_eq 0 h2 hmaps (by simp)
        have e1 : ((fun t : ℝ => (f (x + t • -d)).toReal) ∘ (fun t : ℝ => -t)) =
            (fun t : ℝ => (f (x + t • d)).toReal) := by
          funext t; simp
        rw [e1, hneg d] at h3
        simpa using h3
      have hU := hL.union hR
      rw [Set.Iio_union_Ioi, Set.compl_eq_univ_diff, hasDerivWithinAt_diff_singleton,
        hasDerivWithinAt_univ] at hU
      exact hU
    exact ⟨Module.finBasis ℝ E, fun i => (hderiv _).differentiableAt⟩
  tfae_have 2 → 3 := by
    rintro ⟨b, hb⟩
    exact diff_of_partial (fun y => (f y).toReal) hFconv b hb
  tfae_have 3 → 1 := by
    intro hdiff
    have hgd : ∀ d, g d = fderiv ℝ (fun y => (f y).toReal) x d := by
      intro d
      have hline : HasDerivAt (fun t : ℝ => x + t • d) d 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const d).const_add x
      have hcomp := hdiff.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp)
      exact (uniqueDiffWithinAt_Ioi 0).eq_deriv _ (hdir d) hcomp.hasDerivWithinAt
    intro x₁ x₂ t₁ t₂ _ _ _
    simp only [liftRealtoEReal, hgd, map_add, map_smul, smul_eq_mul]
    norm_cast
  tfae_finish

end FCA_chap_B_4_2_1
