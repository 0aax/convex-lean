import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_2_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_2_1`, so the main result is `CAMA_chap_3_4_2_1.CAMA_chap_3_4_2_1`.
-/

namespace CAMA_chap_3_4_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_2_1
  (C : Set E)
  (x : E)
  (hC_convex : Convex ℝ C)
  (hC_nonempty : Set.Nonempty C)
  (hC_closed : IsClosed C)
  (hx : x ∈ frontier C) :
  ∃ (r : ℝ) (s : E), SupportingHyperplaneAt s x r C := by
  have hxC : x ∈ C := hC_closed.frontier_subset hx
  have hxi : x ∉ interior C := hx.2
  by_cases hint : (interior C).Nonempty
  · -- Nonempty interior: separate `x` from the open convex set `interior C`.
    obtain ⟨f, hf⟩ :=
      geometric_hahn_banach_open_point hC_convex.interior isOpen_interior hxi
    set s : E := (InnerProductSpace.toDual ℝ E).symm f
    have hs : ∀ y, inner ℝ s y = f y := fun y => InnerProductSpace.toDual_symm_apply
    refine ⟨f x, s, ?_, hxC, ?_, ?_⟩
    · intro h0
      obtain ⟨a, ha⟩ := hint
      have := hf a ha
      rw [← hs a, ← hs x, h0] at this
      simp at this
    · intro y hy
      show inner ℝ s y ≤ f x
      rw [hs]
      have hcl : y ∈ closure (interior C) := by
        rw [hC_convex.closure_interior_eq_closure_of_nonempty_interior hint,
          hC_closed.closure_eq]
        exact hy
      have hsub : closure (interior C) ⊆ {z | f z ≤ f x} :=
        closure_minimal (fun z hz => (hf z hz).le) (isClosed_le f.continuous continuous_const)
      exact hsub hcl
    · show inner ℝ s x = f x
      rw [hs]
  · -- Empty interior: `C` lies in a proper affine subspace; take a normal vector to it.
    have hspan : affineSpan ℝ C ≠ ⊤ := by
      rwa [Ne, ← hC_convex.interior_nonempty_iff_affineSpan_eq_top]
    have hdir : (affineSpan ℝ C).direction ≠ ⊤ := by
      rwa [Ne, AffineSubspace.direction_eq_top_iff_of_nonempty
        (hC_nonempty.mono (subset_affineSpan ℝ C))]
    have hperp : (affineSpan ℝ C).directionᗮ ≠ ⊥ := by
      rwa [Ne, Submodule.orthogonal_eq_bot_iff]
    obtain ⟨s, hsmem, hs0⟩ := (Submodule.ne_bot_iff _).mp hperp
    refine ⟨inner ℝ s x, s, hs0, hxC, ?_, rfl⟩
    intro y hy
    show inner ℝ s y ≤ inner ℝ s x
    have hyx : y -ᵥ x ∈ (affineSpan ℝ C).direction :=
      AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hy) (subset_affineSpan ℝ C hxC)
    have h0 : inner ℝ s (y - x) = 0 := Submodule.inner_left_of_mem_orthogonal hyx hsmem
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0.le

end CAMA_chap_3_4_2_1
