import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_1_8`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_1_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_1_8`, so the main result is `CAMA_chap_3_2_1_8.CAMA_chap_3_2_1_8`.
-/

namespace CAMA_chap_3_2_1_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_1_8
  (C : Set E)
  (hC_nonempty : Set.Nonempty C)
  (hC_convex : Convex ℝ C) :
  (affineHull (intrinsicInterior ℝ C) = affineHull C) ∧
  (affineHull (closure C) = affineHull C) ∧
  (intrinsicInterior ℝ (intrinsicInterior ℝ C) = intrinsicInterior ℝ C) ∧
  (intrinsicInterior ℝ (closure C) = intrinsicInterior ℝ C) ∧
  (closure (intrinsicInterior ℝ C) = closure C) := by
  have hhull : ∀ s : Set E, affineHull s = (affineSpan ℝ s : Set E) := by
    intro s
    ext v
    simp only [affineHull, Set.mem_iUnion, Set.mem_setOf_eq, SetLike.mem_coe]
    constructor
    · rintro ⟨k, hk, x, hx, a, ha, rfl⟩
      have ha' : ∑ i ∈ Finset.univ, a i = 1 := ha
      have h1 := affineCombination_mem_affineSpan (k := ℝ) (s := Finset.univ) (w := a) ha' x
      rw [Finset.affineCombination_eq_linear_combination _ _ _ ha'] at h1
      exact affineSpan_mono ℝ (by rintro _ ⟨i, rfl⟩; exact hx i) h1
    · intro hv
      have hv' : v ∈ affineSpan ℝ (Set.range (Subtype.val : s → E)) := by
        rwa [Subtype.range_coe]
      obtain ⟨t, w, hw, rfl⟩ := eq_affineCombination_of_mem_affineSpan hv'
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
      have htne : t.Nonempty := by
        by_contra h
        rw [Finset.not_nonempty_iff_eq_empty] at h
        simp [h] at hw
      refine ⟨t.card, Finset.card_pos.2 htne, fun j => ((t.equivFin.symm j : s) : E),
        fun j => (t.equivFin.symm j : s).2, fun j => w (t.equivFin.symm j), ?_, ?_⟩
      · rw [Equiv.sum_comp t.equivFin.symm (fun i => w (i : s)), Finset.sum_coe_sort t w, hw]
      · rw [Equiv.sum_comp t.equivFin.symm (fun i => w (i : s) • ((i : s) : E)),
          Finset.sum_coe_sort t (fun i => w i • (i : E))]
  simp only [hhull, SetLike.coe_set_eq]
  obtain ⟨p, hp⟩ := hC_nonempty
  obtain ⟨A, hA⟩ : ∃ A : AffineSubspace ℝ E, affineSpan ℝ C = A := ⟨_, rfl⟩
  -- In a space where `D` has full affine span, the intrinsic interior is the interior.
  have key : ∀ D : Set A.direction, affineSpan ℝ D = ⊤ → intrinsicInterior ℝ D = interior D := by
    intro D h
    have key' : ∀ B : AffineSubspace ℝ A.direction, B = ⊤ →
        ((↑) : B → A.direction) '' interior ((↑) ⁻¹' D : Set B) = interior D := by
      rintro B rfl
      have hopen : IsOpenMap ((↑) : (⊤ : AffineSubspace ℝ A.direction) → A.direction) :=
        IsOpen.isOpenMap_subtype_val (s := ((⊤ : AffineSubspace ℝ A.direction) : Set A.direction))
          (by simp)
      rw [← hopen.preimage_interior_eq_interior_preimage continuous_subtype_val,
        Set.image_preimage_eq_inter_range]
      simp
    exact key' _ h
  have hCA : C ⊆ A := hA ▸ subset_affineSpan ℝ C
  have hpA : p ∈ A := hCA hp
  -- The affine isometry `v ↦ v + p` from the direction of `A` onto `A`.
  let g : A.direction →ᵃⁱ[ℝ] E :=
    (AffineIsometryEquiv.vaddConst ℝ p).toAffineIsometry.comp
      A.direction.subtypeₗᵢ.toAffineIsometry
  have hg : ∀ v, g v = (v : E) + p := fun v => rfl
  have hrange : C ⊆ Set.range g := by
    intro x hx
    refine ⟨⟨x - p, ?_⟩, ?_⟩
    · exact AffineSubspace.vsub_mem_direction (hCA hx) hpA
    · simp [hg]
  obtain ⟨D, hD⟩ : ∃ D : Set A.direction, D = g ⁻¹' C := ⟨_, rfl⟩
  have hCD : g '' D = C := hD ▸ Set.image_preimage_eq_of_subset hrange
  have hD_convex : Convex ℝ D := hD ▸ hC_convex.affine_preimage g.toAffineMap
  have hmap : ∀ s : Set A.direction,
      (affineSpan ℝ s).map g.toAffineMap = affineSpan ℝ (g '' s) :=
    fun s => AffineSubspace.map_span g.toAffineMap s
  have hD_span : affineSpan ℝ D = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : g v ∈ affineSpan ℝ (g '' D) := by
      rw [hCD, hA, hg]
      exact AffineSubspace.vadd_mem_of_mem_direction v.2 hpA
    rw [← hmap] at h1
    obtain ⟨w, hw, hwv⟩ := h1
    have : w = v := g.injective hwv
    rwa [← this]
  have hD_int : (interior D).Nonempty := by
    rw [hD_convex.interior_nonempty_iff_affineSpan_eq_top]
    exact hD_span
  have hS : intrinsicInterior ℝ C = g '' interior D := by
    rw [← hCD, AffineIsometry.image_intrinsicInterior, key D hD_span]
  have hcl : closure C = g '' closure D := by
    rw [← hCD]
    exact g.isometry.isClosedEmbedding.closure_image_eq D
  have hspan_int : affineSpan ℝ (interior D) = ⊤ := isOpen_interior.affineSpan_eq_top hD_int
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [hS, ← hmap, hspan_int, ← hD_span, hmap, hCD]
  · apply le_antisymm
    · apply affineSpan_le.2
      rw [hA]
      exact closure_minimal hCA (AffineSubspace.closed_of_finiteDimensional _)
    · exact affineSpan_mono ℝ subset_closure
  · rw [hS, AffineIsometry.image_intrinsicInterior, key _ hspan_int, interior_interior]
  · have hspan_cl : affineSpan ℝ (closure D) = ⊤ :=
      top_unique (hD_span ▸ affineSpan_mono ℝ subset_closure)
    rw [hcl, AffineIsometry.image_intrinsicInterior, key _ hspan_cl,
      hD_convex.interior_closure_eq_interior_of_nonempty_interior hD_int, hS]
  · rw [hS, g.isometry.isClosedEmbedding.closure_image_eq,
      hD_convex.closure_interior_eq_closure_of_nonempty_interior hD_int, hcl]

end CAMA_chap_3_2_1_8
