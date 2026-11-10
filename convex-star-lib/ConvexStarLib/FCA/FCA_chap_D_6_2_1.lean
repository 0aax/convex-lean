import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_1`, so the main result is `FCA_chap_D_6_2_1.FCA_chap_D_6_2_1`.
-/

namespace FCA_chap_D_6_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_2_1
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let graph_subdiff := graph (directionalSubdifferential (liftRealtoEReal f))
  IsClosed graph_subdiff := by
  intro graph_subdiff
  -- the difference quotient as a real number
  have hdq : ∀ x d : E, ∀ t : ℝ, differenceQuotient (liftRealtoEReal f) x d t
      = (((f (x + t • d) - f x) / t : ℝ) : EReal) := fun x d t => rfl
  -- monotonicity of the difference quotient
  have hmono : ∀ x d : E, MonotoneOn (fun t : ℝ => (f (x + t • d) - f x) / t) (Set.Ioi 0) := by
    intro x d s hs t ht hst
    simp only [Set.mem_Ioi] at hs ht
    have h1 : (0:ℝ) ≤ 1 - s / t := by rw [sub_nonneg, div_le_one ht]; exact hst
    have h2 : (0:ℝ) ≤ s / t := by positivity
    have h3 : 1 - s / t + s / t = 1 := by ring
    have key := hf_convex.2 (Set.mem_univ x) (Set.mem_univ (x + t • d)) h1 h2 h3
    have heq : (1 - s / t) • x + (s / t) • (x + t • d) = x + s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', sub_smul, one_smul]
      abel
    rw [heq, smul_eq_mul, smul_eq_mul] at key
    rw [div_le_div_iff₀ hs ht]
    have : f (x + s • d) - f x ≤ s / t * (f (x + t • d) - f x) := by linarith
    calc (f (x + s • d) - f x) * t ≤ s / t * (f (x + t • d) - f x) * t := by
          exact mul_le_mul_of_nonneg_right this ht.le
      _ = (f (x + t • d) - f x) * s := by field_simp
  -- the directional derivative is the infimum of the difference quotients
  have hderiv : ∀ x d : E, directionalDeriv (liftRealtoEReal f) x d
      = sInf ((fun t => differenceQuotient (liftRealtoEReal f) x d t) '' Set.Ioi 0) := by
    intro x d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    apply MonotoneOn.tendsto_nhdsGT _ (OrderBot.bddBelow _)
    intro s hs t ht hst
    dsimp only
    rw [hdq, hdq, EReal.coe_le_coe_iff]
    exact hmono x d hs ht hst
  have hmem : ∀ p : E × E, p ∈ graph_subdiff ↔
      ∀ d : E, ∀ t : ℝ, 0 < t → inner ℝ p.2 d ≤ (f (p.1 + t • d) - f p.1) / t := by
    intro p
    show (∀ d, ((inner ℝ p.2 d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal f) p.1 d) ↔ _
    refine forall_congr' fun d => ?_
    rw [hderiv, le_sInf_iff, Set.forall_mem_image]
    refine forall_congr' fun t => ?_
    rw [hdq, EReal.coe_le_coe_iff, Set.mem_Ioi]
  have hset : graph_subdiff = ⋂ d : E, ⋂ t : ℝ, ⋂ (_ : 0 < t),
      {p : E × E | inner ℝ p.2 d ≤ (f (p.1 + t • d) - f p.1) / t} := by
    ext p
    simp only [hmem, Set.mem_iInter, Set.mem_setOf_eq]
  rw [hset]
  have hcont : Continuous f := hf_convex.locallyLipschitz.continuous
  refine isClosed_iInter fun d => isClosed_iInter fun t => isClosed_iInter fun _ => ?_
  apply isClosed_le
  · exact continuous_snd.inner continuous_const
  · exact ((hcont.comp (continuous_fst.add continuous_const)).sub
      (hcont.comp continuous_fst)).div_const _

end FCA_chap_D_6_2_1
