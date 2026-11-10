import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_1_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_1_3`, so the main result is `CAMA_chap_3_2_1_3.CAMA_chap_3_2_1_3`.
-/

namespace CAMA_chap_3_2_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_3
  (C : Set E)
  (hC₀ : Nonempty C)
  (hC₁ : Convex ℝ C) :
  (Set.Nonempty (intrinsicInterior ℝ C)) ∧
  (Module.finrank ℝ (affineSpan ℝ C).direction) =
  (Module.finrank ℝ (affineSpan ℝ (intrinsicInterior ℝ C)).direction) := by
  have hne : C.Nonempty := Set.nonempty_coe_sort.mp hC₀
  have h1 : (intrinsicInterior ℝ C).Nonempty := hne.intrinsicInterior hC₁
  refine ⟨h1, ?_⟩
  have key : affineSpan ℝ (intrinsicInterior ℝ C) = affineSpan ℝ C := by
    apply le_antisymm (affineSpan_mono ℝ intrinsicInterior_subset)
    haveI : Nonempty (affineSpan ℝ C) := by
      obtain ⟨x, hx⟩ := hne
      exact ⟨⟨x, subset_affineSpan ℝ C hx⟩⟩
    have hU : IsOpen (interior ((↑) ⁻¹' C : Set (affineSpan ℝ C))) := isOpen_interior
    have hUne : (interior ((↑) ⁻¹' C : Set (affineSpan ℝ C))).Nonempty := by
      obtain ⟨x, y, hy, rfl⟩ := h1
      exact ⟨y, hy⟩
    have htop := hU.affineSpan_eq_top hUne
    have hmap := AffineSubspace.map_span (affineSpan ℝ C).subtype
      (interior ((↑) ⁻¹' C : Set (affineSpan ℝ C)))
    rw [htop] at hmap
    intro p hp
    have hp' : p ∈ (⊤ : AffineSubspace ℝ (affineSpan ℝ C)).map (affineSpan ℝ C).subtype := by
      rw [AffineSubspace.mem_map]
      exact ⟨⟨p, hp⟩, AffineSubspace.mem_top _ _ _, rfl⟩
    rw [hmap] at hp'
    rw [intrinsicInterior]
    simpa [AffineSubspace.coe_subtype] using hp'
  rw [key]

end CAMA_chap_3_2_1_3
