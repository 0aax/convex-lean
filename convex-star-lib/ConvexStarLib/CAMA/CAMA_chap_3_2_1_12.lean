import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_1_12`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_1_12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_1_12`, so the main result is `CAMA_chap_3_2_1_12.CAMA_chap_3_2_1_12`.
-/

namespace CAMA_chap_3_2_1_12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem CAMA_aux_ri_ball_iff {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (s : Set G) (x : G) :
    x ∈ intrinsicInterior ℝ s ↔
      x ∈ s ∧ ∃ r > 0, ∀ y ∈ affineSpan ℝ s, dist y x < r → y ∈ s := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hys : y ∈ (Subtype.val ⁻¹' s : Set (affineSpan ℝ s)) := interior_subset hy
    refine ⟨hys, ?_⟩
    rw [mem_interior_iff_mem_nhds] at hy
    obtain ⟨u, hu, hus⟩ := (mem_nhds_subtype _ _ _).1 hy
    obtain ⟨r, hr, hru⟩ := Metric.mem_nhds_iff.1 hu
    refine ⟨r, hr, fun z hz hzx => ?_⟩
    have : (⟨z, hz⟩ : affineSpan ℝ s) ∈ Subtype.val ⁻¹' u := hru hzx
    exact hus this
  · rintro ⟨hx, r, hr, h⟩
    refine ⟨⟨x, subset_affineSpan ℝ s hx⟩, ?_, rfl⟩
    rw [mem_interior_iff_mem_nhds]
    refine (mem_nhds_subtype _ _ _).2 ⟨Metric.ball x r, Metric.ball_mem_nhds x hr, fun z hz => ?_⟩
    exact h z z.2 hz

theorem CAMA_aux_ri_extend {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set G} {x y : G} (hx : x ∈ intrinsicInterior ℝ s) (hy : y ∈ s) :
    ∃ ε : ℝ, 0 < ε ∧ AffineMap.lineMap y x (1 + ε) ∈ s := by
  obtain ⟨hxs, r, hr, h⟩ := (CAMA_aux_ri_ball_iff s x).1 hx
  have hd : 0 ≤ dist y x := dist_nonneg
  refine ⟨r / (dist y x + 1), by positivity, h _ ?_ ?_⟩
  · exact AffineMap.lineMap_mem _ (subset_affineSpan ℝ s hy) (subset_affineSpan ℝ s hxs)
  · rw [dist_lineMap_right]
    rw [show (1 : ℝ) - (1 + r / (dist y x + 1)) = -(r / (dist y x + 1)) by ring, norm_neg,
      Real.norm_of_nonneg (by positivity)]
    rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith

theorem CAMA_aux_ri_lineMap {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {s : Set G}
    (hs : Convex ℝ s) {y z : G} (hy : y ∈ intrinsicInterior ℝ s) (hz : z ∈ s) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t < 1) : AffineMap.lineMap y z t ∈ intrinsicInterior ℝ s := by
  obtain ⟨hys, r, hr, h⟩ := (CAMA_aux_ri_ball_iff s y).1 hy
  have h1t : 0 < 1 - t := by linarith
  rw [CAMA_aux_ri_ball_iff]
  refine ⟨hs.lineMap_mem hys hz ⟨ht0, ht1.le⟩, (1 - t) * r, by positivity, fun w hw hwx => ?_⟩
  set x := AffineMap.lineMap y z t with hx
  set c := (1 - t)⁻¹ with hc
  have hc1 : c * (1 - t) = 1 := inv_mul_cancel₀ h1t.ne'
  have hc0 : 0 < c := inv_pos.2 h1t
  set y' := c • (w - x) + y with hy'
  have hxs : x ∈ affineSpan ℝ s :=
    AffineMap.lineMap_mem _ (subset_affineSpan ℝ s hys) (subset_affineSpan ℝ s hz)
  have hy'a : y' ∈ affineSpan ℝ s := by
    have : c • (w -ᵥ x) +ᵥ y ∈ affineSpan ℝ s :=
      AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ c (AffineSubspace.vsub_mem_direction hw hxs))
        (subset_affineSpan ℝ s hys)
    simpa using this
  have hy's : y' ∈ s := by
    apply h y' hy'a
    rw [dist_eq_norm, hy', add_sub_cancel_right, norm_smul, Real.norm_of_nonneg hc0.le,
      ← dist_eq_norm]
    calc c * dist w x < c * ((1 - t) * r) := by gcongr
      _ = r := by rw [← mul_assoc, hc1, one_mul]
  have hw' : w = AffineMap.lineMap z y' (1 - t) := by
    rw [AffineMap.lineMap_apply_module', hy', hx, AffineMap.lineMap_apply_module']
    linear_combination (norm := module) -(hc1 • (w - (t • (z - y) + y)))
  rw [hw']
  exact hs.lineMap_mem hz hy's ⟨h1t.le, by linarith⟩

theorem CAMA_chap_3_2_1_12
  (A : AffineMap ℝ E F)
  (C : Set E)
  (D : Set F)
  (hC : Convex ℝ C)
  (hD₀ : Convex ℝ D)
  (hD₁ : Set.Nonempty (Set.preimage A (intrinsicInterior ℝ D))) :
  (intrinsicInterior ℝ (Set.image A C) = Set.image A (intrinsicInterior ℝ C)) ∧
  (intrinsicInterior ℝ (Set.preimage A D) = Set.preimage A (intrinsicInterior ℝ D)) := by
  constructor
  · -- Part 1: image
    have hAC : Convex ℝ (A '' C) := hC.affine_image A
    apply Set.Subset.antisymm
    · -- ri (A '' C) ⊆ A '' ri C
      intro z hz
      obtain ⟨x, hxC, rfl⟩ := intrinsicInterior_subset hz
      obtain ⟨x0, hx0⟩ := Set.Nonempty.intrinsicInterior hC ⟨x, hxC⟩
      obtain ⟨ε, hε, hmem⟩ :=
        CAMA_aux_ri_extend hz (Set.mem_image_of_mem A (intrinsicInterior_subset hx0))
      obtain ⟨x1, hx1C, hx1⟩ := hmem
      refine ⟨AffineMap.lineMap x0 x1 (1 + ε)⁻¹,
        CAMA_aux_ri_lineMap hC hx0 hx1C (by positivity) (inv_lt_one_of_one_lt₀ (by linarith)), ?_⟩
      rw [AffineMap.apply_lineMap, hx1, AffineMap.lineMap_lineMap_right,
        inv_mul_cancel₀ (by positivity), AffineMap.lineMap_apply_one]
    · -- A '' ri C ⊆ ri (A '' C)
      rintro _ ⟨x, hx, rfl⟩
      have hxC : x ∈ C := intrinsicInterior_subset hx
      obtain ⟨w, hw⟩ := Set.Nonempty.intrinsicInterior hAC ⟨A x, x, hxC, rfl⟩
      obtain ⟨x', hx'C, rfl⟩ := intrinsicInterior_subset hw
      obtain ⟨ε, hε, hmem⟩ := CAMA_aux_ri_extend hx hx'C
      have := CAMA_aux_ri_lineMap hAC hw (Set.mem_image_of_mem A hmem) (t := (1 + ε)⁻¹)
        (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
      rwa [AffineMap.apply_lineMap, AffineMap.lineMap_lineMap_right,
        inv_mul_cancel₀ (by positivity), AffineMap.lineMap_apply_one] at this
  · -- Part 2: preimage
    have hAD : Convex ℝ (A ⁻¹' D) := hD₀.affine_preimage A
    obtain ⟨x0, hx0⟩ := hD₁
    have hx0' : A x0 ∈ intrinsicInterior ℝ D := hx0
    have hx0D : A x0 ∈ D := intrinsicInterior_subset hx0'
    apply Set.Subset.antisymm
    · -- ri (A ⁻¹' D) ⊆ A ⁻¹' ri D
      intro x hx
      obtain ⟨ε, hε, hmem⟩ := CAMA_aux_ri_extend hx (show x0 ∈ A ⁻¹' D from hx0D)
      have := CAMA_aux_ri_lineMap hD₀ hx0'
        (show A (AffineMap.lineMap x0 x (1 + ε)) ∈ D from hmem) (t := (1 + ε)⁻¹)
        (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
      show A x ∈ intrinsicInterior ℝ D
      rwa [AffineMap.apply_lineMap, AffineMap.lineMap_lineMap_right,
        inv_mul_cancel₀ (by positivity), AffineMap.lineMap_apply_one] at this
    · -- A ⁻¹' ri D ⊆ ri (A ⁻¹' D)
      intro x hx
      have hx' : A x ∈ intrinsicInterior ℝ D := hx
      have hxD : A x ∈ D := intrinsicInterior_subset hx'
      obtain ⟨y, hy⟩ :=
        Set.Nonempty.intrinsicInterior hAD ⟨x, (show x ∈ A ⁻¹' D from hxD)⟩
      have hyD : A y ∈ D := (intrinsicInterior_subset hy : y ∈ A ⁻¹' D)
      obtain ⟨ε, hε, hmem⟩ := CAMA_aux_ri_extend hx' hyD
      have hz : AffineMap.lineMap y x (1 + ε) ∈ A ⁻¹' D := by
        show A (AffineMap.lineMap y x (1 + ε)) ∈ D
        rwa [AffineMap.apply_lineMap]
      have := CAMA_aux_ri_lineMap hAD hy hz (t := (1 + ε)⁻¹)
        (by positivity) (inv_lt_one_of_one_lt₀ (by linarith))
      rwa [AffineMap.lineMap_lineMap_right, inv_mul_cancel₀ (by positivity),
        AffineMap.lineMap_apply_one] at this

end CAMA_chap_3_2_1_12
