import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_1_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_1_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_1_5`, so the main result is `FCA_chap_D_2_1_5.FCA_chap_D_2_1_5`.
-/

namespace FCA_chap_D_2_1_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_2_1_5
  (f : E → ℝ)
  (x d : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := fun (d : E) =>
    directionalDeriv (liftRealtoEReal f) x d
  exposedFace (directionalSubdifferential (liftRealtoEReal f) x) d =
    directionalSubdifferential f' d := by
  intro f'
  -- For a convex real function, the difference quotient has a real right limit at `0`,
  -- which is a lower bound for the quotient at every `t > 0`.
  have dirDeriv_aux : ∀ g : E → ℝ, ConvexOn ℝ Set.univ g → ∀ y v : E,
      ∃ L : ℝ, Filter.Tendsto (fun t : ℝ => (g (y + t • v) - g y) / t) (𝓝[>] 0) (𝓝 L) ∧
        ∀ t : ℝ, 0 < t → L ≤ (g (y + t • v) - g y) / t := by
    intro g hg y v
    set h : ℝ → ℝ := fun t => g (y + t • v) with hh
    have hconv : ConvexOn ℝ Set.univ h := by
      refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
      have key : y + (μ • a + ν • b) • v = μ • (y + a • v) + ν • (y + b • v) := by
        obtain rfl : ν = 1 - μ := by linarith
        simp only [smul_eq_mul]
        module
      simp only [h, key]
      exact hg.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν
    have h0 : (0:ℝ) ∈ interior (Set.univ : Set ℝ) := by simp
    refine ⟨derivWithin h (Set.Ioi 0) 0, ?_, ?_⟩
    · have := hconv.hasDerivWithinAt_rightDeriv_of_mem_interior h0
      rw [hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi] at this
      refine this.congr' ?_
      filter_upwards with t
      simp [slope_def_field, h]
    · intro t ht
      have := hconv.rightDeriv_le_slope_of_mem_interior h0 (Set.mem_univ t) ht
      simpa [slope_def_field, h] using this
  -- The `EReal`-valued directional derivative is the real limit.
  have dirDeriv_eq : ∀ (g : E → ℝ) (y v : E) (L : ℝ),
      Filter.Tendsto (fun t : ℝ => (g (y + t • v) - g y) / t) (𝓝[>] 0) (𝓝 L) →
      directionalDeriv (liftRealtoEReal g) y v = (L : EReal) := by
    intro g y v L hL
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have : (fun t => differenceQuotient (liftRealtoEReal g) y v t) =
        fun t : ℝ => (((g (y + t • v) - g y) / t : ℝ) : EReal) := rfl
    rw [this]
    exact EReal.tendsto_coe.mpr hL
  choose D₁ hD₁ hD₁le using fun e => dirDeriv_aux f hf x e
  have hf'e : ∀ e, directionalDeriv (liftRealtoEReal f) x e = (D₁ e : EReal) :=
    fun e => dirDeriv_eq f x e (D₁ e) (hD₁ e)
  have hf'eq : f' = liftRealtoEReal D₁ := funext hf'e
  have hD₁0 : D₁ 0 = 0 := by
    have : Filter.Tendsto (fun t : ℝ => (f (x + t • (0:E)) - f x) / t) (𝓝[>] 0) (𝓝 0) := by
      simp
    exact tendsto_nhds_unique (hD₁ 0) this
  -- positive homogeneity
  have hD₁_hom : ∀ c : ℝ, 0 < c → ∀ e, D₁ (c • e) = c * D₁ e := by
    intro c hc e
    have h1 : Filter.Tendsto (fun t : ℝ => t * c) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun t : ℝ => t * c) (𝓝 0) (𝓝 (0 * c)) :=
          Filter.tendsto_id.mul_const c
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t) using mul_pos ht hc
    have h2 : Filter.Tendsto (fun t : ℝ => c * ((f (x + (t * c) • e) - f x) / (t * c)))
        (𝓝[>] 0) (𝓝 (c * D₁ e)) :=
      ((hD₁ e).comp h1).const_mul c
    refine tendsto_nhds_unique (hD₁ (c • e)) (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [smul_smul]
    field_simp
  -- convexity
  have hD₁_conv : ConvexOn ℝ Set.univ D₁ := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    refine le_of_tendsto_of_tendsto (hD₁ _) (((hD₁ u).const_mul a).add ((hD₁ v).const_mul b)) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    have key : x + t • (a • u + b • v) = a • (x + t • u) + b • (x + t • v) := by
      obtain rfl : b = 1 - a := by linarith
      module
    have hc := hf.2 (Set.mem_univ (x + t • u)) (Set.mem_univ (x + t • v)) ha hb hab
    rw [← key, smul_eq_mul, smul_eq_mul] at hc
    calc (f (x + t • (a • u + b • v)) - f x) / t
        ≤ (a * f (x + t • u) + b * f (x + t • v) - f x) / t := by gcongr
      _ = a * ((f (x + t • u) - f x) / t) + b * ((f (x + t • v) - f x) / t) := by
        obtain rfl : b = 1 - a := by linarith
        field_simp
        ring
  have hD₁_add : ∀ u v, D₁ (u + v) ≤ D₁ u + D₁ v := by
    intro u v
    have := hD₁_conv.2 (Set.mem_univ ((2:ℝ) • u)) (Set.mem_univ ((2:ℝ) • v))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    rw [hD₁_hom 2 two_pos, hD₁_hom 2 two_pos, smul_smul, smul_smul] at this
    norm_num at this
    linarith
  choose D₂ hD₂ hD₂le using fun e => dirDeriv_aux D₁ hD₁_conv d e
  have hD₂e : ∀ e, directionalDeriv f' d e = (D₂ e : EReal) := by
    intro e
    rw [hf'eq]
    exact dirDeriv_eq D₁ d e (D₂ e) (hD₂ e)
  ext s
  simp only [exposedFace, argmax, directionalSubdifferential, Set.mem_setOf_eq, hf'e, hD₂e,
    EReal.coe_le_coe_iff]
  constructor
  · rintro ⟨hs, hmax⟩ e
    -- Hahn–Banach: a linear functional below `D₁` that agrees with `D₁` at `d`.
    have hH : ∀ c : ℝ, c • d = 0 → c • D₁ d = 0 := by
      intro c hc
      rcases smul_eq_zero.mp hc with rfl | rfl
      · simp
      · simp [hD₁0]
    obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear
      (LinearPMap.mkSpanSingleton' d (D₁ d) hH) D₁ hD₁_hom hD₁_add (by
        rintro ⟨z, hz⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
        rw [LinearPMap.mkSpanSingleton'_apply, smul_eq_mul]
        show c * D₁ d ≤ D₁ (c • d)
        rcases lt_trichotomy c 0 with hc | rfl | hc
        · have h1 : c • d = (-c) • (-d) := by rw [neg_smul_neg]
          rw [h1, hD₁_hom (-c) (by linarith)]
          have h2 := hD₁_add d (-d)
          rw [add_neg_cancel, hD₁0] at h2
          nlinarith
        · simp [hD₁0]
        · rw [hD₁_hom c hc])
    have hgd : g d = D₁ d := by
      rw [hg_ext ⟨d, Submodule.mem_span_singleton_self d⟩,
        LinearPMap.mkSpanSingleton'_apply_self]
    -- Represent `g` by a vector via the Riesz representation theorem.
    set s' := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g) with hs'
    have hs'e : ∀ e, inner ℝ s' e = g e := by
      intro e
      rw [hs', InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
    have hsd : D₁ d ≤ inner ℝ s d := by
      have := hmax s' (fun e => (hs'e e).trans_le (hg_le e))
      rw [real_inner_comm s' d, real_inner_comm s d, hs'e, hgd] at this
      exact this
    refine ge_of_tendsto (hD₂ e) ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    rw [le_div_iff₀ ht]
    have := hs (d + t • e)
    rw [inner_add_right, real_inner_smul_right] at this
    linarith
  · intro hs
    have hsS : ∀ e, inner ℝ s e ≤ D₁ e := by
      intro e
      have h1 := hD₂le e 1 one_pos
      simp only [one_smul, div_one] at h1
      linarith [hs e, hD₁_add d e]
    refine ⟨hsS, fun s' hs' => ?_⟩
    have h1 := hD₂le (-d) (1/2) (by norm_num)
    have h2 : d + (1/2 : ℝ) • (-d) = (1/2 : ℝ) • d := by module
    rw [h2, hD₁_hom (1/2) (by norm_num)] at h1
    have h3 := hs (-d)
    rw [inner_neg_right] at h3
    have h4 := hs' d
    have h5 : ((1/2 : ℝ) * D₁ d - D₁ d) / (1/2) = - D₁ d := by ring
    rw [h5] at h1
    rw [real_inner_comm s' d, real_inner_comm s d]
    linarith

end FCA_chap_D_2_1_5
