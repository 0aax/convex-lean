import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_1_1`, so the main result is `FCA_chap_D_4_1_1.FCA_chap_D_4_1_1`.
-/

namespace FCA_chap_D_4_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_D411_tendsto {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : F → ℝ) (hf : ConvexOn ℝ Set.univ f) (x d : F) :
    Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0)
      (𝓝 (derivWithin (fun t : ℝ => f (x + t • d)) (Set.Ioi 0) 0)) := by
  have hg : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have h := hf.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
    have e : x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) := by
      obtain rfl : ν = 1 - μ := by linarith
      module
    show f (x + (μ • a + ν • b) • d) ≤ μ • f (x + a • d) + ν • f (x + b • d)
    rw [smul_eq_mul μ a, smul_eq_mul ν b, e]
    exact h
  have h := hg.hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
  rw [hasDerivWithinAt_iff_tendsto_slope] at h
  simp only [Set.mem_Ioi, lt_self_iff_false, not_false_eq_true, Set.diff_singleton_eq_self] at h
  refine h.congr' ?_
  filter_upwards with t
  simp [slope_def_field]

theorem FCA_D411_dd_eq {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : F → ℝ) (x d : F) (L : ℝ)
    (h : Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 L)) :
    directionalDeriv (liftRealtoEReal f) x d = (L : EReal) := by
  unfold directionalDeriv
  apply Filter.Tendsto.limUnder_eq
  have e : (fun t => differenceQuotient (liftRealtoEReal f) x d t) =
      (fun t : ℝ => (((f (x + t • d) - f x) / t : ℝ) : EReal)) := by
    funext t
    simp [differenceQuotient, liftRealtoEReal, EReal.coe_sub, EReal.coe_div]
  rw [e]
  exact (continuous_coe_real_ereal.tendsto L).comp h

theorem FCA_D411_mul_tendsto (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  rw [tendsto_nhdsWithin_iff]
  refine ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) :=
      (continuous_mul_left c).tendsto 0
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

theorem FCA_D411_hom {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : F → ℝ) (x d : F) (c L L' : ℝ) (hc : 0 < c)
    (h1 : Filter.Tendsto (fun t : ℝ => (f (x + t • (c • d)) - f x) / t) (𝓝[>] 0) (𝓝 L'))
    (h2 : Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 L)) :
    L' = c * L := by
  have h3 := (h2.comp (FCA_D411_mul_tendsto c hc)).const_mul c
  refine tendsto_nhds_unique h1 (h3.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : t ≠ 0 := ne_of_gt ht
  simp only [Function.comp]
  rw [smul_smul, mul_comm t c]
  field_simp

theorem FCA_D411_add {F : Type*} [AddCommGroup F] [Module ℝ F]
    (f : F → ℝ) (hf : ConvexOn ℝ Set.univ f) (x d₁ d₂ : F) (L₁ L₂ L : ℝ)
    (h0 : Filter.Tendsto (fun t : ℝ => (f (x + t • (d₁ + d₂)) - f x) / t) (𝓝[>] 0) (𝓝 L))
    (h1 : Filter.Tendsto (fun t : ℝ => (f (x + t • d₁) - f x) / t) (𝓝[>] 0) (𝓝 L₁))
    (h2 : Filter.Tendsto (fun t : ℝ => (f (x + t • d₂) - f x) / t) (𝓝[>] 0) (𝓝 L₂)) :
    L ≤ L₁ + L₂ := by
  have h3 := (h1.comp (FCA_D411_mul_tendsto 2 two_pos)).add
    (h2.comp (FCA_D411_mul_tendsto 2 two_pos))
  refine le_of_tendsto_of_tendsto h0 h3 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  simp only [Function.comp]
  have hconv := hf.2 (Set.mem_univ (x + (2*t) • d₁)) (Set.mem_univ (x + (2*t) • d₂))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have e : (1/2 : ℝ) • (x + (2*t) • d₁) + (1/2 : ℝ) • (x + (2*t) • d₂) = x + t • (d₁ + d₂) := by
    module
  rw [e] at hconv
  simp only [smul_eq_mul] at hconv
  have key : (f (x + (2*t) • d₁) - f x) / (2*t) + (f (x + (2*t) • d₂) - f x) / (2*t)
      = ((1/2) * f (x + (2*t) • d₁) + (1/2) * f (x + (2*t) • d₂) - f x) / t := by
    field_simp
    ring
  rw [key]
  exact div_le_div_of_nonneg_right (by linarith) ht'.le

theorem FCA_D411_key {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (f : F → ℝ) (hf : ConvexOn ℝ Set.univ f) (x : F) :
    ∃ D : F → ℝ,
      (∀ d, directionalDeriv (liftRealtoEReal f) x d = (D d : EReal)) ∧
      (∀ d, Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 (D d))) ∧
      (∀ c : ℝ, 0 < c → ∀ d, D (c • d) = c * D d) ∧
      (∀ d e, D (d + e) ≤ D d + D e) := by
  refine ⟨fun d => derivWithin (fun t : ℝ => f (x + t • d)) (Set.Ioi 0) 0,
    fun d => FCA_D411_dd_eq f x d _ (FCA_D411_tendsto f hf x d),
    fun d => FCA_D411_tendsto f hf x d,
    fun c hc d => FCA_D411_hom f x d c _ _ hc (FCA_D411_tendsto f hf x _)
      (FCA_D411_tendsto f hf x d),
    fun d e => FCA_D411_add f hf x d e _ _ _ (FCA_D411_tendsto f hf x _)
      (FCA_D411_tendsto f hf x d) (FCA_D411_tendsto f hf x e)⟩

theorem FCA_chap_D_4_1_1
  (f₁ f₂ : E → ℝ)
  (t₁ t₂ : ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f₁ ∧ ConvexOn ℝ Set.univ f₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  ∀ (x : E),
  directionalSubdifferential (liftRealtoEReal (fun x => t₁ • (f₁ x) + t₂ • (f₂ x))) x =
  {v | ∃ v₁ ∈ (directionalSubdifferential (liftRealtoEReal f₁) x),
       ∃ v₂ ∈ (directionalSubdifferential (liftRealtoEReal f₂) x),
       v = t₁ • v₁ + t₂ • v₂} := by
  intro x
  obtain ⟨hc₁, hc₂⟩ := hf_convex
  obtain ⟨ht₁, ht₂⟩ := ht
  obtain ⟨D₁, hD₁, hT₁, hhom₁, hadd₁⟩ := FCA_D411_key f₁ hc₁ x
  obtain ⟨D₂, hD₂, hT₂, hhom₂, hadd₂⟩ := FCA_D411_key f₂ hc₂ x
  have hDs : ∀ d, directionalDeriv (liftRealtoEReal (fun x => t₁ • (f₁ x) + t₂ • (f₂ x))) x d
      = ((t₁ * D₁ d + t₂ * D₂ d : ℝ) : EReal) := by
    intro d
    apply FCA_D411_dd_eq
    have h := ((hT₁ d).const_mul t₁).add ((hT₂ d).const_mul t₂)
    refine h.congr' ?_
    filter_upwards with t
    simp only [smul_eq_mul]
    ring
  have hD₁0 : D₁ 0 = 0 := by
    have h := hhom₁ 2 two_pos 0
    rw [smul_zero] at h
    linarith
  have hD₂0 : D₂ 0 = 0 := by
    have h := hhom₂ 2 two_pos 0
    rw [smul_zero] at h
    linarith
  ext v
  simp only [directionalSubdifferential, Set.mem_setOf_eq, hD₁, hD₂, hDs, EReal.coe_le_coe_iff]
  constructor
  · intro hv
    let N : E × E → ℝ := fun p => t₁ * D₁ p.1 + t₂ * D₂ p.2
    have N_hom : ∀ c : ℝ, 0 < c → ∀ p, N (c • p) = c * N p := by
      intro c hc p
      simp only [N, Prod.smul_fst, Prod.smul_snd, hhom₁ c hc, hhom₂ c hc]
      ring
    have N_add : ∀ p q, N (p + q) ≤ N p + N q := by
      intro p q
      simp only [N, Prod.fst_add, Prod.snd_add]
      have h1 := hadd₁ p.1 q.1
      have h2 := hadd₂ p.2 q.2
      nlinarith
    let K : Submodule ℝ (E × E) := LinearMap.ker (LinearMap.fst ℝ E E - LinearMap.snd ℝ E E)
    let ψ : E × E →ₗ.[ℝ] ℝ := ⟨K, ((innerₛₗ ℝ v) ∘ₗ LinearMap.fst ℝ E E).domRestrict K⟩
    have hψ : ∀ p : ψ.domain, ψ p ≤ N p := by
      rintro ⟨p, hp⟩
      have hp' : p.1 = p.2 := by
        have : p.1 - p.2 = 0 := by simpa [K] using hp
        exact sub_eq_zero.mp this
      show inner ℝ v p.1 ≤ t₁ * D₁ p.1 + t₂ * D₂ p.2
      rw [← hp']
      exact hv p.1
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear ψ N N_hom N_add hψ
    have hgdiag : ∀ d, g (d, d) = inner ℝ v d := by
      intro d
      have hmem : (d, d) ∈ K := by simp [K]
      exact hg_ext ⟨(d, d), hmem⟩
    let g₁ : E →ₗ[ℝ] ℝ := g ∘ₗ LinearMap.inl ℝ E E
    let g₂ : E →ₗ[ℝ] ℝ := g ∘ₗ LinearMap.inr ℝ E E
    let w₁ : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g₁)
    let w₂ : E := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g₂)
    have hw₁ : ∀ d, inner ℝ w₁ d = g (d, 0) := by
      intro d
      simp only [w₁, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap', g₁,
        LinearMap.comp_apply, LinearMap.inl_apply]
    have hw₂ : ∀ d, inner ℝ w₂ d = g (0, d) := by
      intro d
      simp only [w₂, InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap', g₂,
        LinearMap.comp_apply, LinearMap.inr_apply]
    refine ⟨t₁⁻¹ • w₁, ?_, t₂⁻¹ • w₂, ?_, ?_⟩
    · intro d
      rw [real_inner_smul_left, hw₁]
      have h := hg_le (d, 0)
      simp only [N, hD₂0, mul_zero, add_zero] at h
      rw [inv_mul_le_iff₀ ht₁]
      exact h
    · intro d
      rw [real_inner_smul_left, hw₂]
      have h := hg_le (0, d)
      simp only [N, hD₁0, mul_zero, zero_add] at h
      rw [inv_mul_le_iff₀ ht₂]
      exact h
    · rw [smul_smul, smul_smul, mul_inv_cancel₀ ht₁.ne', mul_inv_cancel₀ ht₂.ne', one_smul,
        one_smul]
      apply ext_inner_right ℝ
      intro d
      rw [inner_add_left, hw₁, hw₂, ← map_add, Prod.mk_add_mk, add_zero, zero_add, hgdiag]
  · rintro ⟨v₁, hv₁, v₂, hv₂, rfl⟩ d
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    have h1 := hv₁ d
    have h2 := hv₂ d
    nlinarith

end FCA_chap_D_4_1_1
