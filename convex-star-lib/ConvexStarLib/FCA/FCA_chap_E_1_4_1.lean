import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_4_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_4_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_4_1`, so the main result is `FCA_chap_E_1_4_1.FCA_chap_E_1_4_1`.
-/

namespace FCA_chap_E_1_4_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_4_1
  (f : E → EReal)
  (x s : E)
  (hf_nondegenerate : IsNondegenerate f)
  (hf_convex : InConvRn f)
  (hx : x ∈ effDom f) :
  s ∈ convexSubdifferential f x ↔ (conjugate f s) + f x - (inner ℝ s x) = 0 := by
  have hxtop : f x < ⊤ := hx
  have hxbot : ⊥ < f x := hf_convex.1 x
  have ha : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
  set a : ℝ := (f x).toReal with ha_def
  -- every value of f is either ⊤ or a real number
  have hreal : ∀ y, f y = ⊤ ∨ f y = ((f y).toReal : EReal) := by
    intro y
    rcases eq_top_or_lt_top (f y) with hyt | hyt
    · exact Or.inl hyt
    · exact Or.inr (EReal.coe_toReal hyt.ne (hf_convex.1 y).ne').symm
  unfold convexSubdifferential conjugate
  simp only [Set.mem_setOf_eq, Set.image_univ]
  rw [ha]
  constructor
  · intro h
    have hsup : sSup (Set.range fun y => ((inner ℝ s y : ℝ) : EReal) - f y)
        = ((inner ℝ s x - a : ℝ) : EReal) := by
      apply le_antisymm
      · apply sSup_le
        rintro _ ⟨y, rfl⟩
        dsimp only
        have hy := h y
        rcases hreal y with hyt | hyr
        · rw [hyt]; simp
        · rw [hyr] at hy ⊢
          rw [← EReal.coe_add] at hy
          have hy' := EReal.coe_le_coe_iff.mp hy
          rw [← EReal.coe_sub]
          apply EReal.coe_le_coe_iff.mpr
          rw [inner_sub_right] at hy'
          linarith
      · apply le_sSup
        refine ⟨x, ?_⟩
        dsimp only
        rw [ha, ← EReal.coe_sub]
    rw [hsup, ← EReal.coe_add, ← EReal.coe_sub]
    norm_num
  · intro h y
    have hle : ((inner ℝ s y : ℝ) : EReal) - f y
        ≤ sSup (Set.range fun y => ((inner ℝ s y : ℝ) : EReal) - f y) := le_sSup ⟨y, rfl⟩
    generalize sSup (Set.range fun y => ((inner ℝ s y : ℝ) : EReal) - f y) = S at h hle
    induction S using EReal.rec with
    | bot => simp at h
    | top => simp at h
    | coe c =>
      rw [← EReal.coe_add, ← EReal.coe_sub] at h
      have hc : c + a - inner ℝ s x = 0 := by exact_mod_cast h
      rcases hreal y with hyt | hyr
      · rw [hyt]; exact le_top
      · rw [hyr] at hle ⊢
        rw [← EReal.coe_sub] at hle
        have hle' := EReal.coe_le_coe_iff.mp hle
        rw [← EReal.coe_add]
        apply EReal.coe_le_coe_iff.mpr
        rw [inner_sub_right]
        linarith

end FCA_chap_E_1_4_1
