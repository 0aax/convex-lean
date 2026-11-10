import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_2_7`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_2_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_2_7`, so the main result is `FCA_chap_C_3_2_7.FCA_chap_C_3_2_7`.
-/

namespace FCA_chap_C_3_2_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_2_7
  (C : Set E)
  (d s : E)
  (hC_nonempty : Set.Nonempty C)
  (hC_compact : IsCompact C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ interior C) :
  let C' := polarBody C
  let Hs := {y | inner ℝ s y = 1}
  let Hd := {y | inner ℝ d y = 1}
  List.TFAE [
    ∃ (s' : E) (t' : ℝ), (SupportingHyperplaneAt s' d t' C) ∧
                                                 (affineHyperplane s' t' = Hs),
    ∃ (d' : E) (t' : ℝ), (SupportingHyperplaneAt d' s t' C') ∧
                                                 (affineHyperplane d' t' = Hd),
    (d ∈ frontier C) ∧ (s ∈ frontier C') ∧ (inner ℝ s d = 1),
    (d ∈ C) ∧ (s ∈ C') ∧ (inner ℝ s d = 1)
  ] := by
  intro C' Hs Hd
  have h0C : (0:E) ∈ C := interior_subset hC_origin
  have hCclosed : IsClosed C := hC_compact.isClosed
  have h0C' : (0:E) ∈ C' := by
    intro x _
    simp
  have hC'closed : IsClosed C' := by
    have : C' = ⋂ x ∈ C, {y : E | inner ℝ x y ≤ 1} := by
      ext y; simp [C', polarBody]
    rw [this]
    exact isClosed_biInter fun x _ =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  -- key lemma: from equality of hyperplanes, deduce the halfspace bound
  have key : ∀ (a b : E) (t : ℝ) (K : Set E), (0:E) ∈ K → a ≠ 0 →
      K ⊆ hyperplaneHalfspace a t → affineHyperplane a t = {y | inner ℝ b y = 1} →
      ∀ x ∈ K, inner ℝ b x ≤ 1 := by
    intro a b t K h0 ha hK hH x hx
    have ha2 : (0:ℝ) < inner ℝ a a := by
      rw [real_inner_self_eq_norm_sq]
      have : 0 < ‖a‖ := norm_pos_iff.mpr ha
      positivity
    have hmem : ∀ z : E, inner ℝ b (z + ((t - inner ℝ a z) / inner ℝ a a) • a) = 1 := by
      intro z
      have : z + ((t - inner ℝ a z) / inner ℝ a a) • a ∈ affineHyperplane a t := by
        show inner ℝ a (z + ((t - inner ℝ a z) / inner ℝ a a) • a) = t
        rw [inner_add_right, real_inner_smul_right]
        field_simp
        ring
      rw [hH] at this
      exact this
    have h1 := hmem 0
    have h2 := hmem x
    simp only [inner_add_right, real_inner_smul_right, inner_zero_right, zero_add,
      sub_zero] at h1 h2
    have ht : 0 ≤ t := by
      have := hK h0
      simpa [hyperplaneHalfspace] using this
    have hxt : inner ℝ a x ≤ t := hK hx
    have hba : 0 < inner ℝ b a := by
      by_contra hcon
      push_neg at hcon
      have : t / inner ℝ a a * inner ℝ b a ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (div_nonneg ht ha2.le) hcon
      linarith
    have : 0 ≤ (t - inner ℝ a x) / inner ℝ a a * inner ℝ b a :=
      mul_nonneg (div_nonneg (by linarith) ha2.le) hba.le
    linarith
  -- bipolar
  have bipolar : ∀ z : E, (∀ y ∈ C', inner ℝ z y ≤ 1) → z ∈ C := by
    intro z hz
    by_contra hzC
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hC_convex hCclosed hzC
    have hu : 0 < u := by
      have := hfu 0 h0C
      simpa using this
    have hvx : ∀ x, inner ℝ ((InnerProductSpace.toDual ℝ E).symm f) x = f x :=
      fun x => InnerProductSpace.toDual_symm_apply
    have hy : u⁻¹ • (InnerProductSpace.toDual ℝ E).symm f ∈ C' := by
      intro x hx
      rw [real_inner_smul_right, real_inner_comm, hvx]
      have := hfu x hx
      rw [inv_mul_le_iff₀ hu]
      linarith
    have := hz _ hy
    rw [real_inner_smul_right, real_inner_comm, hvx] at this
    rw [inv_mul_le_iff₀ hu] at this
    linarith
  -- points of the boundary
  have not_int : ∀ (K : Set E) (z w : E), (∀ x ∈ K, inner ℝ x w ≤ 1) → inner ℝ z w = 1 →
      z ∉ interior K := by
    intro K z w hK hzw hz
    have hc : Continuous (fun r : ℝ => r • z) := continuous_id.smul continuous_const
    have h1 : ∀ᶠ r in 𝓝 (1:ℝ), r • z ∈ interior K := by
      have := hc.continuousAt (x := 1)
      rw [ContinuousAt, one_smul] at this
      exact this (isOpen_interior.mem_nhds hz)
    have h2 : ∀ᶠ r in 𝓝[>] (1:ℝ), r • z ∈ interior K := nhdsWithin_le_nhds h1
    obtain ⟨r, hr1, hr2⟩ := (h2.and self_mem_nhdsWithin).exists
    have := hK _ (interior_subset hr1)
    rw [real_inner_smul_left, hzw] at this
    have hr2' : (1:ℝ) < r := hr2
    linarith
  tfae_have 1 → 4 := by
    rintro ⟨s', t', ⟨hs'0, hdC, hsupp, hdH⟩, hH⟩
    rw [hH] at hdH
    refine ⟨hdC, ?_, hdH⟩
    intro x hx
    rw [real_inner_comm]
    exact key s' s t' C h0C hs'0 hsupp hH x hx
  tfae_have 4 → 1 := by
    rintro ⟨hdC, hsC', hsd⟩
    refine ⟨s, 1, ⟨?_, hdC, ?_, hsd⟩, rfl⟩
    · rintro rfl
      simp at hsd
    · intro x hx
      show inner ℝ s x ≤ 1
      rw [real_inner_comm]
      exact hsC' x hx
  tfae_have 2 → 4 := by
    rintro ⟨d', t', ⟨hd'0, hsC', hsupp, hsH⟩, hH⟩
    rw [hH] at hsH
    have hds : inner ℝ d s = 1 := hsH
    refine ⟨bipolar d (key d' d t' C' h0C' hd'0 hsupp hH), hsC', ?_⟩
    rw [real_inner_comm]
    exact hds
  tfae_have 4 → 2 := by
    rintro ⟨hdC, hsC', hsd⟩
    refine ⟨d, 1, ⟨?_, hsC', ?_, ?_⟩, rfl⟩
    · rintro rfl
      simp at hsd
    · intro y hy
      exact hy d hdC
    · show inner ℝ d s = 1
      rw [real_inner_comm]
      exact hsd
  tfae_have 3 → 4 := by
    rintro ⟨hd, hs, hsd⟩
    exact ⟨hCclosed.frontier_subset hd, hC'closed.frontier_subset hs, hsd⟩
  tfae_have 4 → 3 := by
    rintro ⟨hdC, hsC', hsd⟩
    refine ⟨⟨subset_closure hdC, ?_⟩, ⟨subset_closure hsC', ?_⟩, hsd⟩
    · exact not_int C d s hsC' (by rw [real_inner_comm]; exact hsd)
    · refine not_int C' s d ?_ hsd
      intro y hy
      rw [real_inner_comm]
      exact hy d hdC
  tfae_finish

end FCA_chap_C_3_2_7
