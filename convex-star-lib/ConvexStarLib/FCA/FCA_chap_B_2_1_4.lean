import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_1_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_1_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_1_4`, so the main result is `FCA_chap_B_2_1_4.FCA_chap_B_2_1_4`.
-/

namespace FCA_chap_B_2_1_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_B_2_1_4
  (f : E → EReal)
  (A : AffineMap ℝ F E)
  (hf_nonempty : (Set.range A) ∩ (effDom f) ≠ ∅)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let g := fun x => f (A x)
  (InConvRn f → InConvRn g) ∧
  (InClosedConvRn f → InClosedConvRn g) := by
  intro g
  have h1 : InConvRn f → InConvRn g := by
    rintro ⟨-, -, hconv⟩
    refine ⟨fun x => f_ne_bot (A x), ?_, ?_⟩
    · obtain ⟨y, ⟨x, rfl⟩, hy⟩ := Set.nonempty_iff_ne_empty.mpr hf_nonempty
      exact ⟨x, hy⟩
    · intro p hp q hq a b ha hb hab
      have key : a • ((A p.1, p.2) : E × ℝ) + b • ((A q.1, q.2) : E × ℝ) ∈ epigraph f :=
        @hconv (A p.1, p.2) hp (A q.1, q.2) hq a b ha hb hab
      show f (A (a • p + b • q).1) ≤ (((a • p + b • q).2 : ℝ) : EReal)
      simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd]
      rw [Convex.combo_affine_apply hab]
      exact key
  refine ⟨h1, ?_⟩
  rintro ⟨hc, hlsc⟩
  exact ⟨h1 hc, hlsc.comp A.continuous_of_finiteDimensional⟩

end FCA_chap_B_2_1_4
