import ConvexStarLib.Defs

/-!
# `FCA_chap_D_2_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_2_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_2_2_1`, so the main result is `FCA_chap_D_2_2_1.FCA_chap_D_2_2_1`.
-/

namespace FCA_chap_D_2_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_2_2_1
  (f : E → ℝ)
  (x : E)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  List.TFAE [
    ∀ (y : E), f y ≥ f x,
    0 ∈ directionalSubdifferential (liftRealtoEReal f) x,
    ∀ (d : E), directionalDeriv (liftRealtoEReal f) x d ≥ 0
  ] := by
  -- the difference quotient is the coercion of the real difference quotient
  have hdq : ∀ d t, differenceQuotient (liftRealtoEReal f) x d t
      = (((f (x + t • d) - f x) / t : ℝ) : EReal) := fun d t => rfl
  -- the real difference quotient is monotone on `(0, ∞)`
  have hmono : ∀ d, MonotoneOn (fun t : ℝ => (f (x + t • d) - f x) / t) (Set.Ioi 0) := by
    intro d s hs t ht hst
    simp only [Set.mem_Ioi] at hs ht
    have hpt : (1 - s / t) • x + (s / t) • (x + t • d) = x + s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', sub_smul, one_smul]
      abel
    have ha : (0 : ℝ) ≤ 1 - s / t := by rw [sub_nonneg, div_le_one ht]; exact hst
    have hb : (0 : ℝ) ≤ s / t := div_nonneg hs.le ht.le
    have hab : (1 - s / t) + s / t = 1 := by ring
    have hconv := hf_convex.2 (Set.mem_univ x) (Set.mem_univ (x + t • d)) ha hb hab
    rw [hpt, smul_eq_mul, smul_eq_mul] at hconv
    have h2 : t * f (x + s • d) ≤ (t - s) * f x + s * f (x + t • d) := by
      have := mul_le_mul_of_nonneg_left hconv ht.le
      have e : t * ((1 - s / t) * f x + s / t * f (x + t • d))
          = (t - s) * f x + s * f (x + t • d) := by
        field_simp
      linarith
    simp only
    rw [div_le_div_iff₀ hs ht]
    nlinarith
  -- monotone in EReal
  have hmonoE : ∀ d, MonotoneOn (fun t : ℝ => differenceQuotient (liftRealtoEReal f) x d t)
      (Set.Ioi 0) := by
    intro d s hs t ht hst
    simp only [hdq]
    exact EReal.coe_le_coe_iff.2 (hmono d hs ht hst)
  -- the directional derivative is the infimum of the difference quotients
  have hlim : ∀ d, directionalDeriv (liftRealtoEReal f) x d
      = sInf ((fun t : ℝ => differenceQuotient (liftRealtoEReal f) x d t) '' Set.Ioi 0) := by
    intro d
    exact ((hmonoE d).tendsto_nhdsGT (OrderBot.bddBelow _)).limUnder_eq
  tfae_have 1 → 3 := by
    intro hmin d
    rw [hlim d]
    apply le_sInf
    rintro _ ⟨t, ht, rfl⟩
    simp only [Set.mem_Ioi] at ht
    simp only [hdq]
    exact EReal.coe_nonneg.2 (div_nonneg (sub_nonneg.2 (hmin _)) ht.le)
  tfae_have 3 → 1 := by
    intro hd y
    have h := hd (y - x)
    rw [hlim] at h
    have h1 : sInf ((fun t : ℝ => differenceQuotient (liftRealtoEReal f) x (y - x) t)
        '' Set.Ioi 0) ≤ differenceQuotient (liftRealtoEReal f) x (y - x) 1 :=
      sInf_le ⟨1, Set.mem_Ioi.2 one_pos, rfl⟩
    rw [hdq] at h1
    have h2 := EReal.coe_nonneg.1 (le_trans h h1)
    simp only [one_smul, add_sub_cancel, div_one] at h2
    linarith
  tfae_have 2 ↔ 3 := by
    simp only [directionalSubdifferential, Set.mem_setOf_eq, inner_zero_left, EReal.coe_zero, ge_iff_le]
  tfae_finish

end FCA_chap_D_2_2_1
