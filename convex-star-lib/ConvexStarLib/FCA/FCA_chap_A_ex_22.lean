import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_22`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_22` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_22`, so the main result is `FCA_chap_A_ex_22.FCA_chap_A_ex_22`.
-/

namespace FCA_chap_A_ex_22

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_22
  (C : Set E)
  (hC_convex : Convex ℝ C) :
  IsClosed C ↔
  (∀ (a d : E), d ≠ 0 →
    IsClosed (C ∩ {x | ∃ t : ℝ, x = a + t • d})) := by
  have hline : ∀ a d : E, IsClosed {x : E | ∃ t : ℝ, x = a + t • d} := by
    intro a d
    have : {x : E | ∃ t : ℝ, x = a + t • d} =
        (fun x => x - a) ⁻¹' (Submodule.span ℝ {d} : Set E) := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_preimage, SetLike.mem_coe, Submodule.mem_span_singleton]
      constructor
      · rintro ⟨t, rfl⟩; exact ⟨t, by abel⟩
      · rintro ⟨t, ht⟩; exact ⟨t, by rw [ht]; abel⟩
    rw [this]
    exact (Submodule.closed_of_finiteDimensional _).preimage (continuous_id.sub continuous_const)
  constructor
  · intro hC a d _
    exact hC.inter (hline a d)
  · intro h
    rcases C.eq_empty_or_nonempty with hCe | ⟨c, hc⟩
    · rw [hCe]; exact isClosed_empty
    apply isClosed_of_closure_subset
    intro x hx
    set S : Set E := (fun p => p - c) '' C with hS_def
    set V : Submodule ℝ E := Submodule.span ℝ S with hV_def
    set D : Set V := ((↑) : V → E) ⁻¹' S with hD_def
    have hS_convex : Convex ℝ S := by
      have : S = (fun p => -c + p) '' C := by
        rw [hS_def]; congr 1; funext p; abel
      rw [this]; exact hC_convex.translate (-c)
    have hD_convex : Convex ℝ D := hS_convex.linear_preimage V.subtype
    have hD_span : Submodule.span ℝ D = ⊤ := Submodule.span_span_coe_preimage
    have h0D : (0 : V) ∈ D := by
      show ((0 : V) : E) ∈ S
      exact ⟨c, hc, by simp⟩
    have hD_aff : affineSpan ℝ D = ⊤ := by
      have h1 : (affineSpan ℝ D : Set V) = Set.univ := by
        rw [← Set.insert_eq_of_mem h0D, affineSpan_insert_zero, hD_span, Submodule.top_coe]
      exact (AffineSubspace.coe_eq_univ_iff _).mp h1
    obtain ⟨y, hy⟩ := (hD_convex.interior_nonempty_iff_affineSpan_eq_top).mpr hD_aff
    have hxS : x - c ∈ closure S :=
      map_mem_closure (f := fun p : E => p - c) (continuous_id.sub continuous_const) hx
        (fun p hp => ⟨p, hp, rfl⟩)
    have hV_closed : IsClosed (V : Set E) := Submodule.closed_of_finiteDimensional V
    have hxV : x - c ∈ V := by
      have : closure S ⊆ V := hV_closed.closure_subset_iff.mpr Submodule.subset_span
      exact this hxS
    set x' : V := ⟨x - c, hxV⟩ with hx'_def
    have hx'D : x' ∈ closure D := by
      rw [closure_subtype]
      have : ((↑) : V → E) '' D = S := by
        apply Set.image_preimage_eq_of_subset
        rw [Subtype.range_coe_subtype]
        exact Submodule.subset_span
      rw [this]; exact hxS
    have hseg := hD_convex.openSegment_interior_closure_subset_interior hy hx'D
    have hyD : y ∈ D := interior_subset hy
    set a : E := c + (y : E) with ha_def
    have haC : a ∈ C := by
      obtain ⟨p, hp, hpy⟩ := hyD
      have hpy' : p - c = (y : E) := hpy
      have : a = p := by rw [ha_def, ← hpy']; abel
      rw [this]; exact hp
    by_cases hd : x - a = 0
    · have : x = a := sub_eq_zero.mp hd
      rw [this]; exact haC
    · have hcl := h a (x - a) hd
      have key : ∀ t ∈ Set.Ioo (0:ℝ) 1, a + t • (x - a) ∈ C := by
        intro t ht
        have hmem : (1 - t) • y + t • x' ∈ openSegment ℝ y x' :=
          ⟨1 - t, t, by linarith [ht.2], ht.1, by ring, rfl⟩
        obtain ⟨p, hp, hpe⟩ := interior_subset (hseg hmem)
        have hpe' : p - c = (1 - t) • (y : E) + t • (x - c) := by
          simp only at hpe
          rw [hpe]
          rfl
        have : a + t • (x - a) = p := by
          rw [show p = c + ((1 - t) • (y : E) + t • (x - c)) by rw [← hpe']; abel, ha_def]
          module
        rw [this]; exact hp
      have hx_cl : x ∈ closure (C ∩ {z | ∃ t : ℝ, z = a + t • (x - a)}) := by
        have htend : Filter.Tendsto (fun t : ℝ => a + t • (x - a)) (𝓝[<] 1) (𝓝 x) := by
          have : Filter.Tendsto (fun t : ℝ => a + t • (x - a)) (𝓝 1)
              (𝓝 (a + (1:ℝ) • (x - a))) :=
            (continuous_const.add (continuous_id.smul continuous_const)).tendsto 1
          rw [one_smul, add_sub_cancel] at this
          exact this.mono_left nhdsWithin_le_nhds
        apply mem_closure_of_tendsto htend
        filter_upwards [Ioo_mem_nhdsLT (show (0:ℝ) < 1 by norm_num)] with t ht
        exact ⟨key t ht, t, rfl⟩
      rw [hcl.closure_eq] at hx_cl
      exact hx_cl.1

end FCA_chap_A_ex_22
