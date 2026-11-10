import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_1_2`, so the main result is `FCA_chap_D_1_1_2.FCA_chap_D_1_1_2`.
-/

namespace FCA_chap_D_1_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 2000000 in
theorem FCA_chap_D_1_1_2
  (f : E → ℝ)
  (x : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := fun d => directionalDeriv (liftRealtoEReal f) x d
  (∀ (z : E), f' z < ⊤ ∧ f' z > ⊥) ∧ (IsSublinear f') := by
  intro f'
  -- the (real-valued) one-sided directional derivative
  set D : E → ℝ := fun d => derivWithin (fun t : ℝ => f (x + t • d)) (Set.Ioi 0) 0 with hD
  have hconv : ∀ d : E, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
    intro d
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have h := hf.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
    have e : x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) := by
      linear_combination (norm := module) -(hμν • x)
    simpa only [smul_eq_mul, e] using h
  have key : ∀ d : E, Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t)
      (𝓝[>] 0) (𝓝 (D d)) := by
    intro d
    have h1 := (hconv d).hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at h1
    refine h1.congr (fun t => ?_)
    simp [slope_def_field]
  have hf'eq : ∀ d, f' d = ((D d : ℝ) : EReal) := by
    intro d
    show limUnder (𝓝[>] 0) (fun t : ℝ => (((f (x + t • d) - f x) / t : ℝ) : EReal)) = _
    exact (EReal.tendsto_coe.2 (key d)).limUnder_eq
  have hDconv : ∀ d₁ d₂ : E, ∀ μ ν : ℝ, 0 ≤ μ → 0 ≤ ν → μ + ν = 1 →
      D (μ • d₁ + ν • d₂) ≤ μ * D d₁ + ν * D d₂ := by
    intro d₁ d₂ μ ν hμ hν hμν
    have h1 := key (μ • d₁ + ν • d₂)
    have h2 := ((key d₁).const_mul μ).add ((key d₂).const_mul ν)
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    have e : x + t • (μ • d₁ + ν • d₂) = μ • (x + t • d₁) + ν • (x + t • d₂) := by
      linear_combination (norm := module) -(hμν • x)
    have h : f (μ • (x + t • d₁) + ν • (x + t • d₂)) ≤ μ * f (x + t • d₁) + ν * f (x + t • d₂) :=
      hf.2 (Set.mem_univ (x + t • d₁)) (Set.mem_univ (x + t • d₂)) hμ hν hμν
    calc (f (x + t • (μ • d₁ + ν • d₂)) - f x) / t
        ≤ (μ * f (x + t • d₁) + ν * f (x + t • d₂) - f x) / t := by
          rw [e]; gcongr
      _ = μ * ((f (x + t • d₁) - f x) / t) + ν * ((f (x + t • d₂) - f x) / t) := by
          have : ν = 1 - μ := by linarith
          subst this
          ring
  have hDhom : ∀ d : E, ∀ s : ℝ, 0 < s → D (s • d) = s * D d := by
    intro d s hs
    have hmap : Filter.Tendsto (fun t : ℝ => t * s) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
      · have : Filter.Tendsto (fun t : ℝ => t * s) (𝓝 0) (𝓝 (0 * s)) :=
          Filter.tendsto_id.mul_const s
        simpa using this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        exact mul_pos ht hs
    have h2 := ((key d).comp hmap).const_mul s
    refine tendsto_nhds_unique (key (s • d)) (h2.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht : 0 < t := ht
    simp only [Function.comp_apply, mul_smul]
    field_simp
  have hfin : ∀ z, f' z < ⊤ ∧ f' z > ⊥ := by
    intro z
    rw [hf'eq z]
    exact ⟨EReal.coe_lt_top _, EReal.bot_lt_coe _⟩
  refine ⟨hfin, ⟨⟨fun z => (hfin z).2, ⟨0, (hfin 0).1⟩, ?_⟩, ?_⟩⟩
  · intro p hp q hq a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq, hf'eq, EReal.coe_le_coe_iff] at hp hq ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    calc D (a • p.1 + b • q.1) ≤ a * D p.1 + b * D q.1 := hDconv _ _ _ _ ha hb hab
      _ ≤ a * p.2 + b * q.2 := by gcongr
  · intro z s hs
    rw [hf'eq, hf'eq, hDhom z s hs, EReal.coe_mul]

end FCA_chap_D_1_1_2
