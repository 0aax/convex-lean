import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_1_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_1_1`, so the main result is `CAMA_chap_3_4_1_1.CAMA_chap_3_4_1_1`.
-/

namespace CAMA_chap_3_4_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_1_1
  (C : Set E)
  (x : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hx : x ∉ C) :
  ∃ (s : E), (s ≠ 0) ∧
    BddAbove ((fun y => inner ℝ s y) '' C) ∧
    sSup ((fun y => inner ℝ s y) '' C) < inner ℝ s x := by
  obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hx
  have key : ∀ y, inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) y = f y := fun y =>
    InnerProductSpace.toDual_symm_apply
  have hbdd : ∀ z ∈ (fun y => inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) y) '' C, z ≤ u := by
    rintro z ⟨a, ha, rfl⟩
    dsimp only
    rw [key]
    exact (hfu a ha).le
  refine ⟨(InnerProductSpace.toDual ℝ E).symm f, ?_, ⟨u, hbdd⟩, ?_⟩
  · intro h0
    obtain ⟨a, ha⟩ := hC_nonempty
    have h1 := hfu a ha
    have h2 := key a
    have h3 := key x
    rw [h0, inner_zero_left] at h2 h3
    linarith
  · rw [key]
    exact lt_of_le_of_lt (csSup_le (hC_nonempty.image _) hbdd) hux

end CAMA_chap_3_4_1_1
