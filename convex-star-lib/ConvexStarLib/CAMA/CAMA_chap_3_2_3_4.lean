import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_3_4`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_3_4`, so the main result is `CAMA_chap_3_2_3_4.CAMA_chap_3_2_3_4`.
-/

namespace CAMA_chap_3_2_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_2_3_4
    (C : Set E)
    (hC₀ : C.Nonempty)
    (hC₁ : Convex ℝ C)
    (hC₂ : IsCompact C) :
    C = convexHull ℝ (Set.extremePoints ℝ C) := by
  have exists_support_aux : ∀ (C : Set E), Convex ℝ C → ∀ b ∈ C, ∀ v ∈ vectorSpan ℝ C,
      (∀ ε : ℝ, 0 < ε → b + ε • v ∉ C) →
      ∃ f : E →L[ℝ] ℝ, (∀ c ∈ C, f c ≤ f b) ∧ ∃ c ∈ C, f c < f b := by
    intro C hCc b hb v hv hout
    set S₀ : Set E := (· -ᵥ b) '' C with hS₀
    set V : Submodule ℝ E := Submodule.span ℝ S₀ with hV
    have hVeq : vectorSpan ℝ C = V := vectorSpan_eq_span_vsub_set_right ℝ hb
    have hS₀mem : ∀ w : E, w ∈ S₀ ↔ w + b ∈ C := by
      intro w
      constructor
      · rintro ⟨c, hc, rfl⟩
        simpa using hc
      · intro h
        exact ⟨w + b, h, by simp⟩
    have hS₀eq : S₀ = (fun x => x + b) ⁻¹' C := by
      ext w
      exact hS₀mem w
    have hS₀conv : Convex ℝ S₀ := by
      rw [hS₀eq]
      exact hCc.translate_preimage_left b
    let S : Set V := V.subtype ⁻¹' S₀
    have hSconv : Convex ℝ S := hS₀conv.linear_preimage V.subtype
    have hSspan : Submodule.span ℝ S = ⊤ := Submodule.span_span_coe_preimage
    have h0 : (0 : V) ∈ S := by
      show ((0 : V) : E) ∈ S₀
      rw [hS₀mem]
      simpa using hb
    have haff : affineSpan ℝ S = ⊤ := by
      rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty _ _ _ ⟨0, h0⟩,
        vectorSpan_eq_span_vsub_set_right ℝ h0]
      simpa using hSspan
    have hint : (interior S).Nonempty := hSconv.interior_nonempty_iff_affineSpan_eq_top.2 haff
    have hvV : v ∈ V := hVeq ▸ hv
    have h0int : (0 : V) ∉ interior S := by
      intro h
      obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 h)
      set ε : ℝ := r / (2 * (‖v‖ + 1)) with hε_def
      have hε : 0 < ε := by positivity
      have hmem : ε • (⟨v, hvV⟩ : V) ∈ Metric.ball (0 : V) r := by
        rw [mem_ball_zero_iff, norm_smul, Real.norm_of_nonneg hε.le]
        have hn : ‖(⟨v, hvV⟩ : V)‖ = ‖v‖ := rfl
        rw [hn, hε_def]
        have h1 : 0 ≤ ‖v‖ := norm_nonneg v
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith
      have := hball hmem
      apply hout ε hε
      have h2 : ((ε • (⟨v, hvV⟩ : V) : V) : E) ∈ S₀ := this
      rw [hS₀mem] at h2
      simpa [add_comm] using h2
    obtain ⟨f, hf⟩ := _root_.geometric_hahn_banach_open_point hSconv.interior
      isOpen_interior h0int
    have hfS : ∀ a ∈ S, f a ≤ 0 := by
      intro a ha
      have hcl : a ∈ closure (interior S) := by
        rw [hSconv.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure ha
      have hsub : closure (interior S) ⊆ {a | f a ≤ 0} :=
        closure_minimal (fun a ha => by simpa using (hf a ha).le)
          (isClosed_le f.continuous continuous_const)
      exact hsub hcl
    obtain ⟨g, hg, -⟩ := Real.exists_extension_norm_eq V f
    refine ⟨g, ?_, ?_⟩
    · intro c hc
      have hmem : c - b ∈ V := Submodule.subset_span ⟨c, hc, rfl⟩
      have h1 : f ⟨c - b, hmem⟩ ≤ 0 := hfS _ (show c - b ∈ S₀ from ⟨c, hc, rfl⟩)
      rw [← hg] at h1
      simp only [map_sub] at h1
      linarith
    · obtain ⟨a, ha⟩ := hint
      have haS' : a ∈ S := interior_subset ha
      have haS : (a : E) ∈ S₀ := haS'
      refine ⟨(a : E) + b, (hS₀mem _).1 haS, ?_⟩
      have h1 := hf a ha
      rw [map_zero, ← hg] at h1
      rw [map_add]
      linarith
  have main_aux : ∀ (m : ℕ) (C : Set E), Module.finrank ℝ (vectorSpan ℝ C) = m →
      IsCompact C → Convex ℝ C → C ⊆ convexHull ℝ (C.extremePoints ℝ) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro C hdim hC hCc x hx
    have key : ∀ b ∈ C, ∀ v ∈ vectorSpan ℝ C, (∀ ε : ℝ, 0 < ε → b + ε • v ∉ C) →
        b ∈ convexHull ℝ (C.extremePoints ℝ) := by
      intro b hb v hv hout
      obtain ⟨f, hf, c₀, hc₀, hfc₀⟩ := exists_support_aux C hCc b hb v hv hout
      set F : Set E := {c ∈ C | ∀ c' ∈ C, f c' ≤ f c} with hF
      have hexp : IsExposed ℝ C F := fun _ => ⟨f, rfl⟩
      have hbF : b ∈ F := ⟨hb, hf⟩
      have hlt : vectorSpan ℝ F < vectorSpan ℝ C := by
        refine lt_of_le_of_ne (vectorSpan_mono ℝ hexp.subset) ?_
        intro heq
        have hmem : c₀ -ᵥ b ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ hc₀ hb
        rw [← heq] at hmem
        have hker : vectorSpan ℝ F ≤ LinearMap.ker (f : E →ₗ[ℝ] ℝ) := by
          rw [vectorSpan_def, Submodule.span_le]
          rintro _ ⟨p, hp, q, hq, rfl⟩
          have h1 := hp.2 q hq.1
          have h2 := hq.2 p hp.1
          simp only [SetLike.mem_coe, LinearMap.mem_ker, vsub_eq_sub, map_sub,
            ContinuousLinearMap.coe_coe]
          linarith
        have := hker hmem
        simp only [LinearMap.mem_ker, vsub_eq_sub, map_sub, ContinuousLinearMap.coe_coe] at this
        linarith
      have hFdim : Module.finrank ℝ (vectorSpan ℝ F) < m :=
        hdim ▸ Submodule.finrank_lt_finrank_of_lt hlt
      have := ih _ hFdim F rfl (hexp.isCompact hC) (hexp.convex hCc) hbF
      exact convexHull_mono hexp.isExtreme.extremePoints_subset_extremePoints this
    by_cases hxe : x ∈ C.extremePoints ℝ
    · exact subset_convexHull ℝ _ hxe
    rw [mem_extremePoints] at hxe
    push_neg at hxe
    obtain ⟨y, hy, z, hz, hxyz, hne⟩ := hxe hx
    obtain ⟨α, β, hα, hβ, hαβ, hxe'⟩ := hxyz
    set v := z - y with hv_def
    have hvmem : v ∈ vectorSpan ℝ C := vsub_mem_vectorSpan ℝ hz hy
    have hzx : z = x + α • v := by
      rw [← hxe', hv_def]
      calc z = (α + β) • z := by rw [hαβ, one_smul]
        _ = α • y + β • z + α • (z - y) := by module
    have hyx : y = x + (-β) • v := by
      rw [← hxe', hv_def]
      calc y = (α + β) • y := by rw [hαβ, one_smul]
        _ = α • y + β • z + (-β) • (z - y) := by module
    have hv0 : v ≠ 0 := by
      intro h0
      have h1 : y = x := by rw [hyx, h0, smul_zero, add_zero]
      have h2 : z = x := by rw [hzx, h0, smul_zero, add_zero]
      exact hne h1 h2
    set T : Set ℝ := (fun t : ℝ => x + t • v) ⁻¹' C with hT
    have hTc : IsCompact T := by
      have hemb : Topology.IsClosedEmbedding (fun t : ℝ => x + t • v) :=
        (Homeomorph.addLeft x).isClosedEmbedding.comp (isClosedEmbedding_smul_left hv0)
      exact hemb.isCompact_preimage hC
    have hT0 : (0 : ℝ) ∈ T := by simp [hT, hx]
    have hαT : α ∈ T := by
      show x + α • v ∈ C
      rw [← hzx]
      exact hz
    have hβT : -β ∈ T := by
      show x + (-β) • v ∈ C
      rw [← hyx]
      exact hy
    set t₂ := sSup T with ht₂_def
    set t₁ := sInf T with ht₁_def
    have ht₂ : t₂ ∈ T := hTc.sSup_mem ⟨0, hT0⟩
    have ht₁ : t₁ ∈ T := hTc.sInf_mem ⟨0, hT0⟩
    have hαt₂ : α ≤ t₂ := le_csSup hTc.bddAbove hαT
    have hβt₁ : t₁ ≤ -β := csInf_le hTc.bddBelow hβT
    have hb := key (x + t₂ • v) ht₂ v hvmem (by
      intro ε hε hmem
      have hm : t₂ + ε ∈ T := by
        show x + (t₂ + ε) • v ∈ C
        rw [add_smul, ← add_assoc]
        exact hmem
      have := le_csSup hTc.bddAbove hm
      linarith)
    have ha := key (x + t₁ • v) ht₁ (-v) (neg_mem hvmem) (by
      intro ε hε hmem
      have hm : t₁ - ε ∈ T := by
        show x + (t₁ - ε) • v ∈ C
        have : x + (t₁ - ε) • v = x + t₁ • v + ε • (-v) := by module
        rw [this]
        exact hmem
      have := csInf_le hTc.bddBelow hm
      linarith)
    have hseg : x ∈ segment ℝ (x + t₁ • v) (x + t₂ • v) := by
      have hd : 0 < t₂ - t₁ := by linarith
      have h1 : t₂ / (t₂ - t₁) + -t₁ / (t₂ - t₁) = 1 := by
        field_simp
        ring
      have h2 : t₂ / (t₂ - t₁) * t₁ + -t₁ / (t₂ - t₁) * t₂ = 0 := by
        field_simp
        ring
      refine ⟨t₂ / (t₂ - t₁), -t₁ / (t₂ - t₁), div_nonneg (by linarith) hd.le,
        div_nonneg (by linarith) hd.le, h1, ?_⟩
      calc (t₂ / (t₂ - t₁)) • (x + t₁ • v) + (-t₁ / (t₂ - t₁)) • (x + t₂ • v)
          = (t₂ / (t₂ - t₁) + -t₁ / (t₂ - t₁)) • x
            + (t₂ / (t₂ - t₁) * t₁ + -t₁ / (t₂ - t₁) * t₂) • v := by module
        _ = x := by rw [h1, h2, one_smul, zero_smul, add_zero]
    exact (convex_convexHull ℝ _).segment_subset ha hb hseg
  apply Set.Subset.antisymm
  · exact main_aux _ C rfl hC₂ hC₁
  · exact convexHull_min extremePoints_subset hC₁

end CAMA_chap_3_2_3_4
