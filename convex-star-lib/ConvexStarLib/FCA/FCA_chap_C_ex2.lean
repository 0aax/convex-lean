import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex2`, so the main result is `FCA_chap_C_ex2.FCA_chap_C_ex2`.
-/

namespace FCA_chap_C_ex2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_ex2 {n : ℕ}
  (P : Polytope (EuclideanSpace ℝ (Fin n)))
  (hn : n > 0)
  (hP_bounded : Bornology.IsBounded P.carrier)
  (hP_full : P.IsFullDimensional) :
  ∃ S : Finset (Set (EuclideanSpace ℝ (Fin n))),
    (∀ F ∈ S, F ∈ P.facets) ∧ S.card ≥ n + 1 := by
  classical
  -- the polyhedron cut out by a subfamily `J` of the inequalities
  let Q : Finset (Fin P.m) → Set (EuclideanSpace ℝ (Fin n)) :=
    fun J => {x | ∀ i ∈ J, inner ℝ (P.a i) x ≤ P.b i}
  have hQuniv : Q Finset.univ = P.carrier := by
    ext x; simp [Q, Polytope.carrier]
  have hQanti : ∀ J J' : Finset (Fin P.m), J ⊆ J' → Q J' ⊆ Q J := by
    intro J J' h x hx i hi
    exact hx i (h hi)
  -- convexity of the carrier
  have hconv : Convex ℝ P.carrier := by
    intro x hx y hy α β hα hβ hαβ i
    have h1 := hx i
    have h2 := hy i
    rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
    obtain rfl : β = 1 - α := by linarith
    nlinarith [mul_nonneg hα (sub_nonneg.2 h1), mul_nonneg hβ (sub_nonneg.2 h2)]
  -- an interior point
  obtain ⟨x₀, hx₀⟩ : (interior P.carrier).Nonempty :=
    (hconv.interior_nonempty_iff_affineSpan_eq_top).2 hP_full
  have hx₀P : x₀ ∈ P.carrier := interior_subset hx₀
  have hstrict : ∀ i, P.a i ≠ 0 → inner ℝ (P.a i) x₀ < P.b i := by
    intro i hai
    have hnhds : P.carrier ∈ 𝓝 x₀ := mem_interior_iff_mem_nhds.1 hx₀
    have hcont : Continuous (fun t : ℝ => x₀ + t • P.a i) := by fun_prop
    have hev : ∀ᶠ t in 𝓝 (0:ℝ), x₀ + t • P.a i ∈ P.carrier := by
      have := hcont.tendsto 0
      simp only [zero_smul, add_zero] at this
      exact this hnhds
    obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
    have hmem := hball (y := ε / 2) (by
      rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
    have := hmem i
    rw [inner_add_right, real_inner_smul_right, real_inner_self_eq_norm_sq] at this
    have : 0 < ‖P.a i‖ := norm_pos_iff.2 hai
    have : 0 < ε / 2 * ‖P.a i‖ ^ 2 := by positivity
    linarith
  -- a minimal subfamily `J` describing the carrier
  obtain ⟨J, hJmem, hJmin⟩ := Finset.exists_min_image
    (Finset.univ.filter (fun J : Finset (Fin P.m) => Q J = P.carrier)) Finset.card
    ⟨Finset.univ, by simp [hQuniv]⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hJmem hJmin
  have hwit : ∀ i ∈ J, ∃ y, y ∈ Q (J.erase i) ∧ P.b i < inner ℝ (P.a i) y := by
    intro i hi
    by_contra hcon
    push_neg at hcon
    have hQe : Q (J.erase i) = P.carrier := by
      apply Set.Subset.antisymm
      · intro y hy
        rw [← hJmem]
        intro j hj
        by_cases hji : j = i
        · subst hji; exact hcon y hy
        · exact hy j (Finset.mem_erase.2 ⟨hji, hj⟩)
      · rw [← hJmem]; exact hQanti _ _ (Finset.erase_subset _ _)
    have h1 := hJmin (J.erase i) hQe
    have h2 := Finset.card_erase_lt_of_mem hi
    omega
  have hane : ∀ i ∈ J, P.a i ≠ 0 := by
    intro i hi hai
    obtain ⟨y, -, hy⟩ := hwit i hi
    have := hx₀P i
    rw [hai, inner_zero_left] at hy this
    linarith
  -- points in the relative interior of each candidate facet
  have hz : ∀ i ∈ J, ∃ z, z ∈ P.carrier ∧ inner ℝ (P.a i) z = P.b i ∧
      ∀ j ∈ J.erase i, inner ℝ (P.a j) z < P.b j := by
    intro i hi
    obtain ⟨y, hyQ, hy⟩ := hwit i hi
    have h0 := hstrict i (hane i hi)
    have hden : 0 < inner ℝ (P.a i) y - inner ℝ (P.a i) x₀ := by linarith
    set t := (P.b i - inner ℝ (P.a i) x₀) / (inner ℝ (P.a i) y - inner ℝ (P.a i) x₀) with ht
    have ht0 : 0 < t := div_pos (by linarith) hden
    have ht1 : t < 1 := by rw [ht, div_lt_one hden]; linarith
    have hzi : inner ℝ (P.a i) (x₀ + t • (y - x₀)) = P.b i := by
      rw [inner_add_right, real_inner_smul_right, inner_sub_right, ht]
      field_simp
      ring
    have hzj : ∀ j ∈ J.erase i, inner ℝ (P.a j) (x₀ + t • (y - x₀)) < P.b j := by
      intro j hj
      have h1 := hstrict j (hane j (Finset.mem_of_mem_erase hj))
      have h2 := hyQ j hj
      rw [inner_add_right, real_inner_smul_right, inner_sub_right]
      nlinarith
    refine ⟨x₀ + t • (y - x₀), ?_, hzi, hzj⟩
    rw [← hJmem]
    intro j hj
    by_cases hji : j = i
    · subst hji; exact hzi.le
    · exact (hzj j (Finset.mem_erase.2 ⟨hji, hj⟩)).le
  -- each `F i` is a facet
  have hfacet : ∀ i ∈ J, (P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i}) ∈ P.facets := by
    intro i hi
    obtain ⟨z, hzP, hzi, hzj⟩ := hz i hi
    refine ⟨⟨?_, ⟨z, hzP, hzi⟩, ?_⟩, ?_⟩
    · -- convex
      intro x hx y hy α β hα hβ hαβ
      refine ⟨hconv hx.1 hy.1 hα hβ hαβ, ?_⟩
      have h1 : inner ℝ (P.a i) x = P.b i := hx.2
      have h2 : inner ℝ (P.a i) y = P.b i := hy.2
      show inner ℝ (P.a i) (α • x + β • y) = P.b i
      rw [inner_add_right, real_inner_smul_right, real_inner_smul_right, h1, h2]
      linear_combination P.b i * hαβ
    · -- extreme
      refine ⟨Set.inter_subset_left, ?_⟩
      rintro x₁ hx₁ x₂ hx₂ x ⟨-, hx⟩ ⟨α, β, hα, hβ, hαβ, rfl⟩
      have h1 := hx₁ i
      have h2 := hx₂ i
      have hx' : α * inner ℝ (P.a i) x₁ + β * inner ℝ (P.a i) x₂ = P.b i := by
        have : inner ℝ (P.a i) (α • x₁ + β • x₂) = P.b i := hx
        rwa [inner_add_right, real_inner_smul_right, real_inner_smul_right] at this
      obtain rfl : β = 1 - α := by linarith
      have hm1 := mul_nonneg hα.le (sub_nonneg.2 h1)
      have hm2 := mul_nonneg hβ.le (sub_nonneg.2 h2)
      have e1 : α * (P.b i - inner ℝ (P.a i) x₁) = 0 := by nlinarith
      refine ⟨hx₁, ?_⟩
      show inner ℝ (P.a i) x₁ = P.b i
      rcases mul_eq_zero.1 e1 with h | h
      · exact absurd h hα.ne'
      · linarith
    · -- dimension
      have hdir : (affineSpan ℝ (P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i})).direction
          = (ℝ ∙ P.a i)ᗮ := by
        rw [direction_affineSpan]
        apply le_antisymm
        · rw [vectorSpan_def, Submodule.span_le]
          rintro _ ⟨x, ⟨-, hx⟩, y, ⟨-, hy⟩, rfl⟩
          have hx' : inner ℝ (P.a i) x = P.b i := hx
          have hy' : inner ℝ (P.a i) y = P.b i := hy
          simp only [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right,
            vsub_eq_sub, inner_sub_right, hx', hy', sub_self]
        · intro v hv
          rw [Submodule.mem_orthogonal_singleton_iff_inner_right] at hv
          have hev : ∀ᶠ t in 𝓝 (0:ℝ), ∀ j ∈ J.erase i, inner ℝ (P.a j) (z + t • v) < P.b j := by
            rw [Filter.eventually_all_finset]
            intro j hj
            have hc : Continuous (fun t : ℝ => inner ℝ (P.a j) (z + t • v)) := by fun_prop
            exact hc.continuousAt.eventually_lt continuousAt_const (by simpa using hzj j hj)
          obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
          have ht := hball (y := ε / 2) (by
            rw [Real.dist_eq, sub_zero, abs_of_pos (half_pos hε)]; linarith)
          have hvi : inner ℝ (P.a i) (z + (ε / 2) • v) = P.b i := by
            rw [inner_add_right, real_inner_smul_right, hv, hzi, mul_zero, add_zero]
          have hmem : z + (ε / 2) • v ∈ P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i} := by
            refine ⟨?_, hvi⟩
            rw [← hJmem]
            intro j hj
            by_cases hji : j = i
            · subst hji; exact hvi.le
            · exact (ht j (Finset.mem_erase.2 ⟨hji, hj⟩)).le
          have hvs := vsub_mem_vectorSpan ℝ hmem ⟨hzP, hzi⟩
          rw [vsub_eq_sub, add_sub_cancel_left] at hvs
          have := Submodule.smul_mem _ (ε / 2)⁻¹ hvs
          rwa [smul_smul, inv_mul_cancel₀ (half_pos hε).ne', one_smul] at this
      unfold Set.affineFinrank
      rw [hdir]
      have hfull : affineSpan ℝ P.carrier = ⊤ := hP_full
      rw [hfull, AffineSubspace.direction_top, finrank_top, finrank_euclideanSpace_fin]
      have h1 := Submodule.finrank_add_finrank_orthogonal (ℝ ∙ P.a i)
      rw [finrank_span_singleton (hane i hi), finrank_euclideanSpace_fin] at h1
      omega
  -- the facets are pairwise distinct
  have hinj : Set.InjOn (fun i => P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i}) J := by
    intro i hi i' hi' heq
    by_contra hne
    obtain ⟨z, hzP, hzi, hzj⟩ := hz i hi
    have hzF : z ∈ P.carrier ∩ {x | inner ℝ (P.a i') x = P.b i'} := by
      have : z ∈ P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i} := ⟨hzP, hzi⟩
      simp only at heq
      rwa [heq] at this
    have h1 := hzj i' (Finset.mem_erase.2 ⟨Ne.symm hne, hi'⟩)
    have h2 : inner ℝ (P.a i') z = P.b i' := hzF.2
    linarith
  -- there are at least `n + 1` constraints in `J`
  have hcard : n + 1 ≤ J.card := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨d, hd0, hd⟩ : ∃ d : EuclideanSpace ℝ (Fin n), d ≠ 0 ∧
        ∀ j ∈ J, inner ℝ (P.a j) d ≤ 0 := by
      rcases J.eq_empty_or_nonempty with hJe | ⟨i₀, hi₀⟩
      · haveI : Nontrivial (EuclideanSpace ℝ (Fin n)) := by
          rw [← Module.finrank_pos_iff (R := ℝ), finrank_euclideanSpace_fin]; exact hn
        obtain ⟨d, hd⟩ := exists_ne (0 : EuclideanSpace ℝ (Fin n))
        exact ⟨d, hd, by simp [hJe]⟩
      · let L : EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (↥(J.erase i₀) → ℝ) :=
          LinearMap.pi (fun j => innerₛₗ ℝ (P.a j))
        have hlt' : Module.finrank ℝ (↥(J.erase i₀) → ℝ)
            < Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
          rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe,
            Finset.card_erase_of_mem hi₀, finrank_euclideanSpace_fin]
          omega
        obtain ⟨d, hdker, hd0⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := L) hlt')
        have hdj : ∀ j ∈ J.erase i₀, inner ℝ (P.a j) d = 0 := by
          intro j hj
          have := congrFun (LinearMap.mem_ker.1 hdker) ⟨j, hj⟩
          simpa [L] using this
        rcases le_total (inner ℝ (P.a i₀) d) 0 with h | h
        · refine ⟨d, hd0, fun j hj => ?_⟩
          by_cases hji : j = i₀
          · subst hji; exact h
          · exact (hdj j (Finset.mem_erase.2 ⟨hji, hj⟩)).le
        · refine ⟨-d, neg_ne_zero.2 hd0, fun j hj => ?_⟩
          rw [inner_neg_right]
          by_cases hji : j = i₀
          · subst hji; linarith
          · rw [hdj j (Finset.mem_erase.2 ⟨hji, hj⟩)]; simp
    obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).1 hP_bounded
    have hd_pos : 0 < ‖d‖ := norm_pos_iff.2 hd0
    have hx₀r : ‖x₀‖ ≤ r := by simpa using hr hx₀P
    set t := (r + ‖x₀‖ + 1) / ‖d‖ with ht
    have ht0 : 0 ≤ t := div_nonneg (by linarith [norm_nonneg x₀]) hd_pos.le
    have hmem : x₀ + t • d ∈ P.carrier := by
      rw [← hJmem]
      intro j hj
      rw [inner_add_right, real_inner_smul_right]
      have h1 := hx₀P j
      have h2 := hd j hj
      nlinarith [mul_nonneg ht0 (neg_nonneg.2 h2)]
    have h1 : ‖x₀ + t • d‖ ≤ r := by simpa using hr hmem
    have h2 : ‖t • d‖ = r + ‖x₀‖ + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht0, ht, div_mul_cancel₀ _ hd_pos.ne']
    have h3 : ‖t • d‖ ≤ ‖x₀ + t • d‖ + ‖x₀‖ := by
      have := norm_sub_le (x₀ + t • d) x₀
      rwa [add_sub_cancel_left] at this
    linarith
  refine ⟨J.image (fun i => P.carrier ∩ {x | inner ℝ (P.a i) x = P.b i}), ?_, ?_⟩
  · intro F hF
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hF
    exact hfacet i hi
  · rw [Finset.card_image_of_injOn hinj]
    exact hcard

end FCA_chap_C_ex2
