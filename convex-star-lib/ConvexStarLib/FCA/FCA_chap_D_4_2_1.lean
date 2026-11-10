import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_2_1`, so the main result is `FCA_chap_D_4_2_1.FCA_chap_D_4_2_1`.
-/

namespace FCA_chap_D_4_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_D_4_2_1 (g : F → ℝ) (A₀ : E →ₗ[ℝ] F) (b : F)
    (hf_convex : ConvexOn ℝ Set.univ g) :
    ∀ x : E,
      directionalSubdifferential (fun v ↦ g (A₀ v + b)) x =
        Set.image A₀.adjoint (directionalSubdifferential (liftRealtoEReal g) (A₀ x + b)) := by
  intro x
  -- convexity along lines
  have hline : ∀ y w : F, ConvexOn ℝ Set.univ (fun t : ℝ => g (y + t • w)) := by
    intro y w
    have := (hf_convex.translate_right y).comp_linearMap (LinearMap.toSpanSingleton ℝ F w)
    simpa [Function.comp_def] using this
  -- the (real) directional derivative
  let P : F → F → ℝ := fun y w => sInf ((fun t : ℝ => (g (y + t • w) - g y) / t) '' Set.Ioi 0)
  have hlim : ∀ y w : F, Filter.Tendsto (fun t : ℝ => (g (y + t • w) - g y) / t) (𝓝[>] 0)
      (𝓝 (P y w)) := by
    intro y w
    have key : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → s ≤ t →
        (g (y + s • w) - g y) / s ≤ (g (y + t • w) - g y) / t := by
      intro s t hs ht hst
      have := (hline y w).secant_mono (Set.mem_univ 0) (Set.mem_univ s) (Set.mem_univ t) hs ht hst
      simpa using this
    refine MonotoneOn.tendsto_nhdsGT ?_ ?_
    · intro s hs t ht hst
      exact key s t (ne_of_gt hs) (ne_of_gt ht) hst
    · refine ⟨(g (y + (-1 : ℝ) • w) - g y) / (-1), ?_⟩
      rintro _ ⟨t, ht, rfl⟩
      exact key (-1) t (by norm_num) (ne_of_gt ht) (by linarith [ht.out])
  have hD : ∀ y w, directionalDeriv (liftRealtoEReal g) y w = (P y w : EReal) := by
    intro y w
    unfold directionalDeriv differenceQuotient liftRealtoEReal
    apply Filter.Tendsto.limUnder_eq
    have : (fun t : ℝ => ((g (y + t • w) : EReal) - (g y : EReal)) / (t : EReal)) =
        fun t : ℝ => (((g (y + t • w) - g y) / t : ℝ) : EReal) := by
      funext t
      rw [EReal.coe_div, EReal.coe_sub]
    rw [this]
    exact EReal.tendsto_coe.2 (hlim y w)
  have hDf : ∀ d, directionalDeriv (fun v ↦ (g (A₀ v + b) : EReal)) x d =
      (P (A₀ x + b) (A₀ d) : EReal) := by
    intro d
    rw [← hD]
    unfold directionalDeriv differenceQuotient liftRealtoEReal
    congr 1
    funext t
    beta_reduce
    rw [map_add, map_smul, add_right_comm]
  -- sublinearity
  have hpos : ∀ c : ℝ, 0 < c → Filter.Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
    intro c hc
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Filter.Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
        (continuous_mul_left c).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact mul_pos hc ht
  have p_hom : ∀ y, ∀ c : ℝ, 0 < c → ∀ w, P y (c • w) = c * P y w := by
    intro y c hc w
    have h2 : Filter.Tendsto (fun t : ℝ => c * ((g (y + (c * t) • w) - g y) / (c * t))) (𝓝[>] 0)
        (𝓝 (c * P y w)) :=
      ((hlim y w).comp (hpos c hc)).const_mul c
    have h3 : (fun t : ℝ => c * ((g (y + (c * t) • w) - g y) / (c * t))) =
        fun t : ℝ => (g (y + t • (c • w)) - g y) / t := by
      funext t
      rw [smul_smul, mul_comm t c, mul_div_assoc', mul_div_mul_left _ _ hc.ne']
    rw [h3] at h2
    exact tendsto_nhds_unique (hlim y (c • w)) h2
  have p_add : ∀ y w₁ w₂, P y (w₁ + w₂) ≤ P y w₁ + P y w₂ := by
    intro y w₁ w₂
    have h1 := ((hlim y w₁).comp (hpos 2 two_pos)).add ((hlim y w₂).comp (hpos 2 two_pos))
    refine le_of_tendsto_of_tendsto (hlim y (w₁ + w₂)) h1 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0:ℝ) < t := ht
    simp only [Function.comp]
    have hconv := hf_convex.2 (Set.mem_univ (y + (2 * t) • w₁)) (Set.mem_univ (y + (2 * t) • w₂))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have heq : (1/2 : ℝ) • (y + (2 * t) • w₁) + (1/2 : ℝ) • (y + (2 * t) • w₂) =
        y + t • (w₁ + w₂) := by
      module
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    rw [← add_div, div_le_div_iff₀ ht' (by positivity)]
    nlinarith
  have p_zero : ∀ y, P y 0 = 0 := by
    intro y
    have := p_hom y 2 two_pos 0
    rw [smul_zero] at this
    linarith
  ext s
  simp only [directionalSubdifferential, Set.mem_setOf_eq, Set.mem_image, hD, hDf,
    EReal.coe_le_coe_iff]
  constructor
  · intro hs
    have hker : LinearMap.ker A₀ ≤ LinearMap.ker (innerₛₗ ℝ s) := by
      intro d hd
      rw [LinearMap.mem_ker] at hd ⊢
      rw [innerₛₗ_apply_apply]
      have h1 := hs d
      have h2 := hs (-d)
      rw [hd, p_zero] at h1
      rw [map_neg, hd, neg_zero, p_zero, inner_neg_right] at h2
      linarith
    let ℓ : LinearMap.range A₀ →ₗ[ℝ] ℝ :=
      ((LinearMap.ker A₀).liftQ (innerₛₗ ℝ s) hker).comp A₀.quotKerEquivRange.symm.toLinearMap
    have hℓ : ∀ d : E, ℓ ⟨A₀ d, LinearMap.mem_range_self A₀ d⟩ = inner ℝ s d := by
      intro d
      simp only [ℓ, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearMap.quotKerEquivRange_symm_apply_image, Submodule.mkQ_apply, Submodule.liftQ_apply,
        innerₛₗ_apply_apply]
    let f : F →ₗ.[ℝ] ℝ := ⟨LinearMap.range A₀, ℓ⟩
    obtain ⟨L, hLf, hLp⟩ := exists_extension_of_le_sublinear f (P (A₀ x + b))
      (p_hom (A₀ x + b)) (p_add (A₀ x + b)) (by
        rintro ⟨z, d, rfl⟩
        exact (hℓ d).trans_le (hs d))
    refine ⟨(InnerProductSpace.toDual ℝ F).symm (LinearMap.toContinuousLinearMap L), ?_, ?_⟩
    · intro w
      rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
      exact hLp w
    · apply ext_inner_right ℝ
      intro d
      rw [LinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply,
        LinearMap.coe_toContinuousLinearMap']
      exact (hLf ⟨A₀ d, LinearMap.mem_range_self A₀ d⟩).trans (hℓ d)
  · rintro ⟨u, hu, rfl⟩ d
    rw [LinearMap.adjoint_inner_left]
    exact hu (A₀ d)

end FCA_chap_D_4_2_1
