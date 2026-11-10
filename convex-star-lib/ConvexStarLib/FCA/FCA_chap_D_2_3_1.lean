import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_3_1`, so the main result is `FCA_chap_D_2_3_1.FCA_chap_D_2_3_1`.
-/

namespace FCA_chap_D_2_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_D_2_3_1
  (f : E → ℝ)
  (x y : E) (t : ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) (ht : 0 ≤ t ∧ t ≤ 1) :
  let x' := fun (v : ℝ) => v • y + (1 - v) • x
  let phi := fun (v : EuclideanSpace ℝ (Fin 1)) => f (x' (v 0))
  let t_asvec : EuclideanSpace ℝ (Fin 1) := (WithLp.equiv 2 _).symm (fun _ => t)
  let subdiff := {v : ℝ | ∃ v' ∈ directionalSubdifferential (liftRealtoEReal phi) t_asvec, v' 0 = v}
  subdiff =
  {z : ℝ | ∃ s ∈ (directionalSubdifferential (liftRealtoEReal f) (x' t)), z = inner ℝ s (y - x)} := by
  intro x' phi t_asvec subdiff
  set p : E := x' t with hp
  -- the directional derivative of phi reduces to one of f
  have key : ∀ d : EuclideanSpace ℝ (Fin 1),
      directionalDeriv (liftRealtoEReal phi) t_asvec d
        = directionalDeriv (liftRealtoEReal f) p (d 0 • (y - x)) := by
    intro d
    unfold directionalDeriv
    congr 1
    funext τ
    unfold differenceQuotient liftRealtoEReal
    have h1 : phi (t_asvec + τ • d) = f (p + τ • (d 0 • (y - x))) := by
      simp only [phi, t_asvec, hp, x']
      congr 1
      simp
      module
    have h2 : phi t_asvec = f p := by
      simp [phi, t_asvec, hp, x']
    rw [h1, h2]
  -- inner product on EuclideanSpace ℝ (Fin 1)
  have hinner : ∀ a b : EuclideanSpace ℝ (Fin 1), inner ℝ a b = a 0 * b 0 := by
    intro a b
    simp [PiLp.inner_apply, RCLike.inner_apply]
    ring
  -- convexity of f along lines
  have hline : ∀ e : E, ConvexOn ℝ Set.univ (fun τ : ℝ => f (p + τ • e)) := by
    intro e
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ μ ν hμ hν hμν
    have : p + (μ • a + ν • b) • e = μ • (p + a • e) + ν • (p + b • e) := by
      obtain rfl : ν = 1 - μ := by linarith
      simp only [smul_eq_mul]
      module
    simp only [this]
    exact hf_convex.2 trivial trivial hμ hν hμν
  -- existence of the limit of difference quotients
  have hlim : ∀ e : E, ∃ D : ℝ,
      Filter.Tendsto (fun τ : ℝ => (f (p + τ • e) - f p) / τ) (𝓝[>] 0) (𝓝 D) := by
    intro e
    have h := (hline e).hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
    rw [hasDerivWithinAt_iff_tendsto_slope] at h
    have hs : Set.Ioi (0:ℝ) \ {0} = Set.Ioi 0 := by simp
    rw [hs] at h
    exact ⟨_, h.congr (fun τ => by simp [slope_def_field])⟩
  let N : E → ℝ := fun e => limUnder (𝓝[>] (0:ℝ)) (fun τ : ℝ => (f (p + τ • e) - f p) / τ)
  have hN : ∀ e : E,
      Filter.Tendsto (fun τ : ℝ => (f (p + τ • e) - f p) / τ) (𝓝[>] 0) (𝓝 (N e)) :=
    fun e => tendsto_nhds_limUnder (hlim e)
  have hdd : ∀ e : E, directionalDeriv (liftRealtoEReal f) p e = (N e : EReal) := by
    intro e
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    refine ((continuous_coe_real_ereal.tendsto (N e)).comp (hN e)).congr ?_
    intro τ
    simp [differenceQuotient, liftRealtoEReal, EReal.coe_div]
  -- scaling of the parameter
  have hscale : ∀ c : ℝ, 0 < c →
      Filter.Tendsto (fun τ : ℝ => c * τ) (𝓝[>] 0) (𝓝[>] 0) := by
    intro c hc
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Filter.Tendsto (fun τ : ℝ => c * τ) (𝓝 0) (𝓝 (c * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact mul_pos hc hτ
  have N_hom : ∀ c : ℝ, 0 < c → ∀ e, N (c • e) = c * N e := by
    intro c hc e
    have h1 := hN (c • e)
    have h2 : Filter.Tendsto (fun τ : ℝ => c * ((f (p + (c * τ) • e) - f p) / (c * τ)))
        (𝓝[>] 0) (𝓝 (c * N e)) := ((hN e).comp (hscale c hc)).const_mul c
    refine tendsto_nhds_unique h1 (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (τ:ℝ) ≠ 0 := ne_of_gt hτ
    rw [smul_smul, mul_comm τ c]
    field_simp
  have N_add : ∀ e₁ e₂, N (e₁ + e₂) ≤ N e₁ + N e₂ := by
    intro e₁ e₂
    have h1 := hN (e₁ + e₂)
    have h2 : Filter.Tendsto (fun τ : ℝ => (f (p + (2 * τ) • e₁) - f p) / (2 * τ)
        + (f (p + (2 * τ) • e₂) - f p) / (2 * τ)) (𝓝[>] 0) (𝓝 (N e₁ + N e₂)) :=
      ((hN e₁).comp (hscale 2 two_pos)).add ((hN e₂).comp (hscale 2 two_pos))
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : (0:ℝ) < τ := hτ
    have hc : f (p + τ • (e₁ + e₂))
        ≤ (1/2 : ℝ) • f (p + (2 * τ) • e₁) + (1/2 : ℝ) • f (p + (2 * τ) • e₂) := by
      have : p + τ • (e₁ + e₂)
          = (1/2 : ℝ) • (p + (2 * τ) • e₁) + (1/2 : ℝ) • (p + (2 * τ) • e₂) := by
        module
      rw [this]
      exact hf_convex.2 trivial trivial (by norm_num) (by norm_num) (by norm_num)
    simp only [smul_eq_mul] at hc
    rw [← add_div, div_le_div_iff₀ hτ' (by positivity)]
    nlinarith
  have N_zero : N 0 = 0 := by
    have := N_hom 2 two_pos 0
    rw [smul_zero] at this
    linarith
  -- main argument
  ext z
  simp only [subdiff, directionalSubdifferential, Set.mem_setOf_eq]
  constructor
  · rintro ⟨v', hv', rfl⟩
    have hv : ∀ c : ℝ, c * v' 0 ≤ N (c • (y - x)) := by
      intro c
      have := hv' ((WithLp.equiv 2 _).symm (fun _ => c))
      rw [key, hdd, hinner] at this
      have h3 : ((WithLp.equiv 2 (Fin 1 → ℝ)).symm (fun _ => c)) 0 = c := by simp
      rw [h3] at this
      have := EReal.coe_le_coe_iff.mp this
      linarith
    have H : ∀ c : ℝ, c • (y - x) = 0 → c • v' 0 = 0 := by
      intro c hc
      have h1 := hv c
      have h2 := hv (-c)
      rw [hc, N_zero] at h1
      rw [neg_smul, hc, neg_zero, N_zero] at h2
      rw [smul_eq_mul]
      linarith
    obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mkSpanSingleton' (y - x) (v' 0) H) N N_hom N_add (by
        rintro ⟨w, hw⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
        rw [LinearPMap.mkSpanSingleton'_apply]
        simpa [smul_eq_mul] using hv c)
    refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g), ?_, ?_⟩
    · intro e
      rw [InnerProductSpace.toDual_symm_apply, hdd]
      simp only [LinearMap.coe_toContinuousLinearMap']
      exact_mod_cast hg2 e
    · rw [InnerProductSpace.toDual_symm_apply]
      simp only [LinearMap.coe_toContinuousLinearMap']
      have := hg1 ⟨y - x, Submodule.mem_span_singleton_self _⟩
      rw [LinearPMap.mkSpanSingleton'_apply_self] at this
      exact this.symm
  · rintro ⟨s, hs, rfl⟩
    refine ⟨(WithLp.equiv 2 _).symm (fun _ => inner ℝ s (y - x)), ?_, ?_⟩
    · intro d
      rw [key d, hinner]
      have := hs (d 0 • (y - x))
      convert this using 2
      simp [inner_smul_right]
      ring
    · simp

end FCA_chap_D_2_3_1
