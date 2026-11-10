import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_5`, so the main result is `FCA_chap_D_6_2_5.FCA_chap_D_6_2_5`.
-/

namespace FCA_chap_D_6_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_2_5
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ (x : E),
  ∀ (d : E),
  directionalDeriv (liftRealtoEReal f) x d =
  Filter.limsup (fun y => directionalDeriv (liftRealtoEReal f) y d) (𝓝 x) := by
  intro x d
  set q : E → ℝ → ℝ := fun y t => (f (y + t • d) - f y) / t with hq
  -- the difference quotient is monotone in `t` on `(0, ∞)`
  have hmono : ∀ y : E, ∀ s t : ℝ, 0 < s → s ≤ t → q y s ≤ q y t := by
    intro y s t hs hst
    have ht : 0 < t := lt_of_lt_of_le hs hst
    have key : f (y + s • d) ≤ (1 - s / t) * f y + (s / t) * f (y + t • d) := by
      have h := hf_convex.2 (Set.mem_univ y) (Set.mem_univ (y + t • d))
        (sub_nonneg.2 (div_le_one_of_le₀ hst ht.le)) (div_nonneg hs.le ht.le) (by ring)
      have hc : (1 - s / t) • y + (s / t) • (y + t • d) = y + s • d := by
        rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', sub_smul, one_smul]
        abel
      rw [hc] at h
      simpa [smul_eq_mul] using h
    simp only [hq]
    rw [div_le_div_iff₀ hs ht]
    have e : (1 - s / t) * f y + (s / t) * f (y + t • d) = f y + s / t * (f (y + t • d) - f y) := by
      ring
    rw [e] at key
    have : t * (f (y + s • d) - f y) ≤ s * (f (y + t • d) - f y) := by
      have h2 : t * (f (y + s • d) - f y) ≤ t * (s / t * (f (y + t • d) - f y)) := by
        apply mul_le_mul_of_nonneg_left _ ht.le
        linarith
      calc t * (f (y + s • d) - f y) ≤ t * (s / t * (f (y + t • d) - f y)) := h2
        _ = s * (f (y + t • d) - f y) := by field_simp
    linarith
  -- the directional derivative is the infimum of the difference quotients
  have hdd : ∀ y : E, directionalDeriv (liftRealtoEReal f) y d =
      ⨅ t ∈ Set.Ioi (0 : ℝ), ((q y t : ℝ) : EReal) := by
    intro y
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have heq : ∀ t, differenceQuotient (liftRealtoEReal f) y d t = ((q y t : ℝ) : EReal) := by
      intro t
      simp only [differenceQuotient, liftRealtoEReal, hq, EReal.coe_div, EReal.coe_sub]
    simp_rw [heq]
    rw [tendsto_order]
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact lt_of_lt_of_le ha (iInf₂_le t ht)
    · intro a ha
      obtain ⟨t₀, ht₀, hlt⟩ : ∃ t₀ ∈ Set.Ioi (0 : ℝ), ((q y t₀ : ℝ) : EReal) < a := by
        simpa [iInf_lt_iff] using ha
      filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
      exact lt_of_le_of_lt (EReal.coe_le_coe_iff.2 (hmono y t t₀ ht.1 ht.2.le)) hlt
  have hcont : Continuous f := hf_convex.locallyLipschitz.continuous
  apply le_antisymm
  · refine Filter.le_limsup_of_frequently_le ?_ (by isBoundedDefault)
    rw [Filter.frequently_iff]
    intro U hU
    exact ⟨x, mem_of_mem_nhds hU, le_rfl⟩
  · rw [hdd x]
    apply le_iInf₂
    intro t ht
    have h1 : Filter.limsup (fun y => directionalDeriv (liftRealtoEReal f) y d) (𝓝 x) ≤
        Filter.limsup (fun y => ((q y t : ℝ) : EReal)) (𝓝 x) := by
      refine Filter.limsup_le_limsup ?_ (by isBoundedDefault) (by isBoundedDefault)
      exact Filter.Eventually.of_forall (fun y => by
        show directionalDeriv (liftRealtoEReal f) y d ≤ ((q y t : ℝ) : EReal)
        rw [hdd y]
        exact iInf₂_le t ht)
    have h2 : Filter.limsup (fun y => ((q y t : ℝ) : EReal)) (𝓝 x) = ((q x t : ℝ) : EReal) := by
      apply Filter.Tendsto.limsup_eq
      apply Continuous.tendsto
      apply EReal.continuous_coe_iff.2
      simp only [hq]
      fun_prop
    rw [h2] at h1
    exact h1

end FCA_chap_D_6_2_5
