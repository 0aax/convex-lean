import ConvexStarLib.Defs

/-!
# `Duchi_P4_1_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_P4_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_P4_1_1`, so the main result is `Duchi_P4_1_1.Duchi_P4_1_1`.
-/

namespace Duchi_P4_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem Duchi_P4_1_1 {n : ℕ}
  (hn : 1 ≤ n)
  (A B : Set (EuclideanSpace ℝ (Fin n)))
  (hA_convex : Convex ℝ A)
  (hB_convex : Convex ℝ B)
  (hA_int : Set.Nonempty (interior A))
  (h_disjoint : Disjoint (interior A) B) :
  ∃ (l : EuclideanSpace ℝ (Fin n)),
    (l ≠ 0) ∧
    (∀ a ∈ A, ∀ b ∈ B, inner ℝ l b ≤ inner ℝ l a) := by
  rcases B.eq_empty_or_nonempty with hB | hB
  · refine ⟨EuclideanSpace.single ⟨0, by omega⟩ 1, ?_, ?_⟩
    · intro h
      have := congrArg (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp ⟨0, by omega⟩) h
      simp at this
    · intro a _ b hb
      simp [hB] at hb
  · obtain ⟨f, u, hfA, hfB⟩ :=
      geometric_hahn_banach_open hA_convex.interior isOpen_interior hB_convex h_disjoint
    set l : EuclideanSpace ℝ (Fin n) :=
      -((InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm f) with hl
    have hlx : ∀ x, inner ℝ l x = - f x := by
      intro x
      rw [hl, inner_neg_left, InnerProductSpace.toDual_symm_apply]
    refine ⟨l, ?_, ?_⟩
    · intro h0
      obtain ⟨a, ha⟩ := hA_int
      obtain ⟨b, hb⟩ := hB
      have h1 := hfA a ha
      have h2 := hfB b hb
      have ha0 := hlx a
      have hb0 := hlx b
      rw [h0, inner_zero_left] at ha0 hb0
      linarith
    · intro a ha b hb
      have hsub : interior A ⊆ {x | f x ≤ u} := fun x hx => (hfA x hx).le
      have hclosed : IsClosed {x : EuclideanSpace ℝ (Fin n) | f x ≤ u} :=
        isClosed_le f.continuous continuous_const
      have h1 : closure (interior A) ⊆ {x | f x ≤ u} := closure_minimal hsub hclosed
      rw [hA_convex.closure_interior_eq_closure_of_nonempty_interior hA_int] at h1
      have h2 : f a ≤ u := h1 (subset_closure ha)
      have h3 := hfB b hb
      rw [hlx, hlx]
      linarith

end Duchi_P4_1_1
