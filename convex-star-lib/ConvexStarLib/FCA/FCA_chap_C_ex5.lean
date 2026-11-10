import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex5`, so the main result is `FCA_chap_C_ex5.FCA_chap_C_ex5`.
-/

namespace FCA_chap_C_ex5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_ex5 (C : Set E)
  (hC_compact : IsCompact C)
  (hC_convex : Convex ℝ C)
  (hC_origin_int : 0 ∈ interior C) :
  let C_circ := polarBody C
  ∀ (s x : E),
  List.TFAE [
    SupportingHyperplaneAt s x 1 C,
    SupportingHyperplaneAt x s 1 C_circ,
    (x ∈ frontier C) ∧ (s ∈ frontier C_circ) ∧ (inner ℝ s x = 1)
  ] := by
  intro C_circ s x
  have hC_closed : IsClosed C := hC_compact.isClosed
  have h0C : (0 : E) ∈ C := interior_subset hC_origin_int
  have hCcirc_closed : IsClosed C_circ := by
    have : C_circ = ⋂ y ∈ C, {z : E | inner ℝ y z ≤ 1} := by
      ext z
      simp [C_circ, polarBody]
    rw [this]
    exact isClosed_biInter fun y _ =>
      isClosed_le (continuous_const.inner continuous_id) continuous_const
  -- a point on the supporting hyperplane is never an interior point
  have key : ∀ (D : Set E) (a b : E), a ≠ 0 → (∀ z ∈ D, inner ℝ a z ≤ (1:ℝ)) →
      inner ℝ a b = (1:ℝ) → b ∉ interior D := by
    intro D a b ha hD hab hb
    have hcont : Continuous (fun t : ℝ => b + t • a) := by fun_prop
    have h0 : (fun t : ℝ => b + t • a) 0 ∈ interior D := by simpa using hb
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), b + t • a ∈ interior D :=
      ((hcont.tendsto 0).mono_left nhdsWithin_le_nhds).eventually (isOpen_interior.mem_nhds h0)
    obtain ⟨t, htD, ht⟩ := (hev.and self_mem_nhdsWithin).exists
    have h1 := hD _ (interior_subset htD)
    rw [inner_add_right, real_inner_smul_right, hab, real_inner_self_eq_norm_sq] at h1
    have : 0 < ‖a‖ := norm_pos_iff.mpr ha
    have ht' : (0:ℝ) < t := ht
    have : 0 < t * ‖a‖ ^ 2 := by positivity
    linarith
  tfae_have 1 → 2 := by
    rintro ⟨hs0, hxC, hsupp, hsx⟩
    have hsx' : inner ℝ s x = (1:ℝ) := hsx
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      simp at hsx'
    · intro y hy
      rw [real_inner_comm]
      exact hsupp hy
    · intro z hz
      exact hz x hxC
    · show inner ℝ x s = (1:ℝ)
      rw [real_inner_comm]; exact hsx'
  tfae_have 2 → 1 := by
    rintro ⟨hx0, hsC, hsupp, hxs⟩
    have hxs' : inner ℝ x s = (1:ℝ) := hxs
    refine ⟨?_, ?_, ?_, ?_⟩
    · rintro rfl
      simp at hxs'
    · by_contra hxC
      obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hC_convex hC_closed hxC
      have hu : 0 < u := by simpa using hfu 0 h0C
      obtain ⟨z, hzf⟩ : ∃ z : E, ∀ y, inner ℝ z y = f y :=
        ⟨(InnerProductSpace.toDual ℝ E).symm f, fun y => InnerProductSpace.toDual_symm_apply⟩
      have hw : u⁻¹ • z ∈ C_circ := by
        intro y hy
        rw [real_inner_smul_right, real_inner_comm, hzf]
        have := hfu y hy
        rw [inv_mul_le_iff₀ hu]
        linarith
      have h1 : inner ℝ x (u⁻¹ • z) ≤ (1:ℝ) := hsupp hw
      rw [real_inner_smul_right, real_inner_comm, hzf, inv_mul_le_iff₀ hu] at h1
      linarith
    · intro y hy
      show inner ℝ s y ≤ (1:ℝ)
      rw [real_inner_comm]
      exact hsC y hy
    · show inner ℝ s x = (1:ℝ)
      rw [real_inner_comm]; exact hxs'
  tfae_have 1 → 3 := by
    rintro ⟨hs0, hxC, hsupp, hsx⟩
    have hsx' : inner ℝ s x = (1:ℝ) := hsx
    have hx0 : x ≠ 0 := by rintro rfl; simp at hsx'
    have hsC : s ∈ C_circ := fun y hy => by rw [real_inner_comm]; exact hsupp hy
    exact ⟨⟨subset_closure hxC, key C s x hs0 (fun z hz => hsupp hz) hsx'⟩,
      ⟨subset_closure hsC, key C_circ x s hx0 (fun z hz => hz x hxC)
        (by rw [real_inner_comm]; exact hsx')⟩, hsx'⟩
  tfae_have 3 → 1 := by
    rintro ⟨hxF, hsF, hsx⟩
    have hxC : x ∈ C := hC_closed.frontier_subset hxF
    have hsC : s ∈ C_circ := hCcirc_closed.frontier_subset hsF
    refine ⟨?_, hxC, fun y hy => ?_, hsx⟩
    · rintro rfl; simp at hsx
    · show inner ℝ s y ≤ (1:ℝ)
      rw [real_inner_comm]; exact hsC y hy
  tfae_finish

end FCA_chap_C_ex5
