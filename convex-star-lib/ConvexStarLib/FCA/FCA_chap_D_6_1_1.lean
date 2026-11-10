import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_1_1`, so the main result is `FCA_chap_D_6_1_1.FCA_chap_D_6_1_1`.
-/

namespace FCA_chap_D_6_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_1_1
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  IsMonotone (directionalSubdifferential (liftRealtoEReal f)) := by
  -- for every `t`, the difference quotient is the coercion of the real difference quotient
  have hq : ∀ (x d : E) (t : ℝ), differenceQuotient (liftRealtoEReal f) x d t
      = (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
    intro x d t
    simp only [differenceQuotient, liftRealtoEReal]
    rw [EReal.coe_div, EReal.coe_sub]
  -- by convexity, the difference quotient is monotone in `t > 0`
  have hmono : ∀ (x d : E),
      MonotoneOn (fun t => differenceQuotient (liftRealtoEReal f) x d t) (Set.Ioi 0) := by
    intro x d s hs t ht hst
    simp only [hq]
    rw [EReal.coe_le_coe_iff]
    have hs' : (0 : ℝ) < s := hs
    have ht' : (0 : ℝ) < t := ht
    have hb0 : 0 ≤ s / t := div_nonneg hs'.le ht'.le
    have hb1 : 0 ≤ 1 - s / t := by rw [sub_nonneg, div_le_one ht']; exact hst
    have key := hf_convex.2 (Set.mem_univ x) (Set.mem_univ (x + t • d)) hb1 hb0 (by ring)
    have heq : (1 - s / t) • x + (s / t) • (x + t • d) = x + s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ s ht'.ne', ← add_assoc, ← add_smul,
        sub_add_cancel, one_smul]
    rw [heq, smul_eq_mul, smul_eq_mul] at key
    rw [div_le_div_iff₀ hs' ht']
    have h2 := mul_le_mul_of_nonneg_right key ht'.le
    have e : ((1 - s / t) * f x + s / t * f (x + t • d)) * t
        = t * f x - s * f x + s * f (x + t • d) := by
      field_simp
    linarith
  -- hence the directional derivative is at most `f (x + d) - f x`
  have hdd : ∀ (x d : E),
      directionalDeriv (liftRealtoEReal f) x d ≤ ((f (x + d) - f x : ℝ) : EReal) := by
    intro x d
    have ht := (hmono x d).tendsto_nhdsGT (OrderBot.bddBelow _)
    unfold directionalDeriv
    rw [ht.limUnder_eq]
    have h1 : differenceQuotient (liftRealtoEReal f) x d 1 ∈
        (fun t => differenceQuotient (liftRealtoEReal f) x d t) '' Set.Ioi 0 :=
      ⟨1, by norm_num, rfl⟩
    refine (sInf_le h1).trans ?_
    rw [hq]
    simp
  intro x₀ x₁ v₀ v₁ hv₀ hv₁
  have h0 := (hv₀ (x₁ - x₀)).trans (hdd x₀ (x₁ - x₀))
  have h1 := (hv₁ (x₀ - x₁)).trans (hdd x₁ (x₀ - x₁))
  rw [EReal.coe_le_coe_iff, add_sub_cancel] at h0 h1
  have e1 : inner ℝ v₁ (x₀ - x₁) = - inner ℝ v₁ (x₁ - x₀) := by
    rw [← inner_neg_right, neg_sub]
  rw [inner_sub_left]
  linarith

end FCA_chap_D_6_1_1
