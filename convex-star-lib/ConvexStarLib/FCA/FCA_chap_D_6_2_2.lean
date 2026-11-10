import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_2`, so the main result is `FCA_chap_D_6_2_2.FCA_chap_D_6_2_2`.
-/

namespace FCA_chap_D_6_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_2_2 (f : E → ℝ) (hf_convex : ConvexOn ℝ Set.univ f) :
    let subdiff_im := fun C : Set E =>
      {v | ∃ x ∈ C, v ∈ directionalSubdifferential (liftRealtoEReal f) x}
    ∀ B : Set E, Bornology.IsBounded B → Bornology.IsBounded (subdiff_im B) := by
  intro subdiff_im B hB
  -- Key lemma: the directional derivative is at most `f (x + d) - f x`
  have key : ∀ x d : E,
      directionalDeriv (liftRealtoEReal f) x d ≤ ((f (x + d) - f x : ℝ) : EReal) := by
    intro x d
    have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
      refine ⟨convex_univ, ?_⟩
      intro a _ b _ μ ν hμ hν hμν
      have hxy : x + (μ • a + ν • b) • d = μ • (x + a • d) + ν • (x + b • d) := by
        rw [smul_add, smul_add, add_smul, smul_smul, smul_smul]
        calc x + ((μ • a) • d + (ν • b) • d) = (μ + ν) • x + ((μ * a) • d + (ν * b) • d) := by
              rw [hμν, one_smul]; rfl
          _ = μ • x + (μ * a) • d + (ν • x + (ν * b) • d) := by
              rw [add_smul]; abel
      simp only [smul_eq_mul] at hxy ⊢
      rw [show x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) from hxy]
      exact hf_convex.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν
    set g : ℝ → EReal := fun t => differenceQuotient (liftRealtoEReal f) x d t with hg
    have hg_eq : ∀ t, g t = (((f (x + t • d) - f x) / t : ℝ) : EReal) := fun t => rfl
    have hmono : MonotoneOn g (Set.Ioi 0) := by
      intro s hs t ht hst
      rw [hg_eq, hg_eq, EReal.coe_le_coe_iff]
      have := hconv.secant_mono (a := 0) (x := s) (y := t) (Set.mem_univ _) (Set.mem_univ _)
        (Set.mem_univ _) (ne_of_gt hs) (ne_of_gt ht) hst
      simpa using this
    have hlim := hmono.tendsto_nhdsGT (OrderBot.bddBelow _)
    have h1 : directionalDeriv (liftRealtoEReal f) x d = sInf (g '' Set.Ioi 0) :=
      hlim.limUnder_eq
    rw [h1]
    calc sInf (g '' Set.Ioi 0) ≤ g 1 := sInf_le (Set.mem_image_of_mem g (Set.mem_Ioi.mpr one_pos))
      _ = _ := by rw [hg_eq]; simp
  -- `f` is bounded on a closed ball containing `B` and all unit perturbations of it
  obtain ⟨R, hR⟩ := hB.subset_closedBall 0
  have hcont : Continuous f := hf_convex.locallyLipschitz.continuous
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (0 : E) (R + 1)).exists_bound_of_continuousOn hcont.continuousOn
  refine (Metric.isBounded_closedBall (x := (0 : E)) (r := 2 * C)).subset ?_
  rintro v ⟨x, hx, hv⟩
  have hxR : ‖x‖ ≤ R := by simpa using hR hx
  have hx' : x ∈ Metric.closedBall (0 : E) (R + 1) := by
    rw [mem_closedBall_zero_iff]; linarith
  have h1 := hC x hx'
  rw [Real.norm_eq_abs] at h1
  rw [mem_closedBall_zero_iff]
  by_cases hv0 : v = 0
  · subst hv0
    simp only [norm_zero]
    linarith [abs_nonneg (f x)]
  · have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
    set d : E := ‖v‖⁻¹ • v with hd
    have hdnorm : ‖d‖ = 1 := by
      rw [hd, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvpos.ne']
    have hinner : inner ℝ v d = ‖v‖ := by
      rw [hd, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have hvd : ((inner ℝ v d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal f) x d := hv d
    have := hvd.trans (key x d)
    rw [hinner, EReal.coe_le_coe_iff] at this
    have hxd : x + d ∈ Metric.closedBall (0 : E) (R + 1) := by
      rw [mem_closedBall_zero_iff]
      calc ‖x + d‖ ≤ ‖x‖ + ‖d‖ := norm_add_le _ _
        _ ≤ R + 1 := by rw [hdnorm]; linarith
    have h2 := hC (x + d) hxd
    rw [Real.norm_eq_abs] at h2
    linarith [abs_le.mp h1, abs_le.mp h2]

end FCA_chap_D_6_2_2
