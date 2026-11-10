import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_1_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_1_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_1_6`, so the main result is `FCA_chap_D_1_1_6.FCA_chap_D_1_1_6`.
-/

namespace FCA_chap_D_1_1_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_1_6
  (f : E → ℝ)
  (x : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let σ := fun (d : E) => directionalDeriv (liftRealtoEReal f) x d
  let σ' := fun (d : E) => directionalDeriv σ 0 d
  (∀ (δ : E), σ' δ = σ δ) ∧
  (∀ (δ : E), (σ δ = σ 0 + σ' δ) ∧ (σ δ = σ' δ)) ∧
  (directionalSubdifferential σ 0 = directionalSubdifferential (liftRealtoEReal f) x) := by
  intro σ σ'
  -- existence of a real one-sided directional derivative
  have key : ∀ d : E, ∃ L : ℝ,
      Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 L) := by
    intro d
    have hφ : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
      refine ⟨convex_univ, ?_⟩
      intro a _ b _ μ ν hμ hν hμν
      have h := hf.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
      have e : x + (μ • a + ν • b) • d = μ • (x + a • d) + ν • (x + b • d) := by
        rw [smul_add, smul_add, smul_smul, smul_smul, add_smul, smul_eq_mul, smul_eq_mul]
        rw [show μ • x + (μ * a) • d + (ν • x + (ν * b) • d)
            = (μ + ν) • x + ((μ * a) • d + (ν * b) • d) by rw [add_smul]; abel]
        rw [hμν, one_smul]
      show f (x + (μ • a + ν • b) • d) ≤ μ • f (x + a • d) + ν • f (x + b • d)
      rw [e]; exact h
    have hd := hφ.hasDerivWithinAt_rightDeriv_of_mem_interior (x := 0) (by simp)
    rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)] at hd
    refine ⟨_, hd.congr' ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp [slope_def_field]
  choose L hL using key
  have hσ : ∀ d, σ d = (L d : EReal) := by
    intro d
    show limUnder _ _ = _
    apply Filter.Tendsto.limUnder_eq
    have : (fun t : ℝ => differenceQuotient (liftRealtoEReal f) x d t)
        = fun t => ((((f (x + t • d) - f x) / t : ℝ)) : EReal) := by
      funext t
      simp only [differenceQuotient, liftRealtoEReal, EReal.coe_sub, EReal.coe_div]
    rw [this]
    exact (continuous_coe_real_ereal.tendsto _).comp (hL d)
  have hL0 : L 0 = 0 := by
    have h := hL 0
    simp only [smul_zero, add_zero, sub_self, zero_div] at h
    exact tendsto_nhds_unique h tendsto_const_nhds
  have hLsmul : ∀ d, ∀ t : ℝ, 0 < t → L (t • d) = t * L d := by
    intro d t ht
    have h3 : Filter.Tendsto (fun s : ℝ => s * t) (𝓝[>] 0) (𝓝[>] 0) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · have : Filter.Tendsto (fun s : ℝ => s * t) (𝓝 0) (𝓝 (0 * t)) :=
          Filter.tendsto_id.mul_const t
        rw [zero_mul] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with s hs
        exact mul_pos hs ht
    have h4 := ((hL d).comp h3).const_mul t
    refine tendsto_nhds_unique (hL (t • d)) (h4.congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (0:ℝ) < s := hs
    simp only [Function.comp, smul_smul]
    field_simp
  have hσ' : ∀ δ, σ' δ = σ δ := by
    intro δ
    show limUnder _ _ = _
    apply Filter.Tendsto.limUnder_eq
    rw [hσ δ]
    apply tendsto_const_nhds.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [differenceQuotient, zero_add, hσ, hLsmul δ t ht, hL0]
    rw [← EReal.coe_sub, ← EReal.coe_div]
    congr 1
    have ht' : t ≠ 0 := ne_of_gt ht
    rw [sub_zero, mul_div_cancel_left₀ _ ht']
  have hσ0 : σ 0 = 0 := by rw [hσ, hL0]; rfl
  refine ⟨hσ', fun δ => ⟨?_, (hσ' δ).symm⟩, ?_⟩
  · rw [hσ0, zero_add, hσ']
  · ext s
    simp only [directionalSubdifferential, Set.mem_setOf_eq]
    constructor <;> intro h d
    · have := h d
      rwa [show directionalDeriv σ 0 d = σ d from hσ' d] at this
    · rw [show directionalDeriv σ 0 d = σ d from hσ' d]
      exact h d

end FCA_chap_D_1_1_6
