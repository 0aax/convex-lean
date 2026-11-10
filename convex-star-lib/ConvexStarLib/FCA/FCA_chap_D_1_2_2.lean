import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_2_2`, so the main result is `FCA_chap_D_1_2_2.FCA_chap_D_1_2_2`.
-/

namespace FCA_chap_D_1_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_2_2
  (f : E → ℝ)
  (x : E) (s : E)
  (hf : ConvexOn ℝ Set.univ f) :
  s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔ s ∈ convexSubdifferential (liftRealtoEReal f) x := by
  -- real difference quotient
  have hq : ∀ d : E, ∀ t : ℝ, differenceQuotient (liftRealtoEReal f) x d t
      = (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
    intro d t
    simp only [differenceQuotient, liftRealtoEReal]
    rw [EReal.coe_div, EReal.coe_sub]
  -- monotonicity of real slope
  have hmono : ∀ d : E, ∀ a b : ℝ, 0 < a → a ≤ b →
      (f (x + a • d) - f x) / a ≤ (f (x + b • d) - f x) / b := by
    intro d a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have hconv := hf.2 (Set.mem_univ x) (Set.mem_univ (x + b • d))
      (sub_nonneg.mpr ((div_le_one hb).mpr hab)) (div_nonneg ha.le hb.le) (sub_add_cancel 1 (a / b))
    have heq : (1 - a / b) • x + (a / b) • (x + b • d) = x + a • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ a hb.ne']
      rw [sub_smul, one_smul]
      abel
    rw [heq, smul_eq_mul, smul_eq_mul] at hconv
    rw [div_le_div_iff₀ ha hb]
    have : f (x + a • d) - f x ≤ a / b * (f (x + b • d) - f x) := by nlinarith
    calc (f (x + a • d) - f x) * b ≤ (a / b * (f (x + b • d) - f x)) * b := by
          exact mul_le_mul_of_nonneg_right this hb.le
      _ = (f (x + b • d) - f x) * a := by field_simp
  have hlim : ∀ d : E, directionalDeriv (liftRealtoEReal f) x d
      = sInf ((fun t => differenceQuotient (liftRealtoEReal f) x d t) '' Set.Ioi 0) := by
    intro d
    apply Filter.Tendsto.limUnder_eq
    apply MonotoneOn.tendsto_nhdsGT
    · intro a ha b hb hab
      simp only [hq]
      exact EReal.coe_le_coe_iff.mpr (hmono d a b ha hab)
    · exact OrderBot.bddBelow _
  constructor
  · intro h
    simp only [directionalSubdifferential, Set.mem_setOf_eq] at h
    simp only [convexSubdifferential, Set.mem_setOf_eq]
    intro y
    have h1 := h (y - x)
    rw [hlim] at h1
    have h2 : sInf ((fun t => differenceQuotient (liftRealtoEReal f) x (y - x) t) '' Set.Ioi 0)
        ≤ differenceQuotient (liftRealtoEReal f) x (y - x) 1 :=
      sInf_le ⟨1, Set.mem_Ioi.mpr one_pos, rfl⟩
    rw [hq] at h2
    have h3 := h1.trans h2
    simp only [one_smul, add_sub_cancel, div_one] at h3
    have h4 : inner ℝ s (y - x) ≤ f y - f x := EReal.coe_le_coe_iff.mp h3
    simp only [liftRealtoEReal]
    rw [← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  · intro h
    simp only [convexSubdifferential, Set.mem_setOf_eq, liftRealtoEReal] at h
    simp only [directionalSubdifferential, Set.mem_setOf_eq]
    intro d
    rw [hlim]
    apply le_sInf
    rintro _ ⟨t, ht, rfl⟩
    simp only [hq]
    apply EReal.coe_le_coe_iff.mpr
    have ht' : (0:ℝ) < t := ht
    have h1 := h (x + t • d)
    rw [← EReal.coe_add] at h1
    have h2 : f x + inner ℝ s (x + t • d - x) ≤ f (x + t • d) := EReal.coe_le_coe_iff.mp h1
    rw [add_sub_cancel_left, inner_smul_right] at h2
    rw [le_div_iff₀ ht']
    linarith

end FCA_chap_D_1_2_2
