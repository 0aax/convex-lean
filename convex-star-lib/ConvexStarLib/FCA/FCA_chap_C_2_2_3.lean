import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_2_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_2_3`, so the main result is `FCA_chap_C_2_2_3.FCA_chap_C_2_2_3`.
-/

namespace FCA_chap_C_2_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_2_2_3
  (S : Set E)
  (s : E)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S) :
  let σS := supportFunction S
  ((s ∈ affineHull S) ↔ (∀ d, σS d + σS (-1 • d) = 0 → inner ℝ s d = σS d)) ∧
  ((s ∈ intrinsicInterior ℝ S) ↔ ((s ∈ affineHull S) ∧
                                  (∀ d, σS d + σS (-1 • d) > 0 → inner ℝ s d < σS d))) ∧
  ((s ∈ interior S) ↔ (∀ d, d ≠ 0 → inner ℝ s d < σS d)) := by
  intro σS
  have FCA_aux_supporting : ∀ {F : Type _} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [FiniteDimensional ℝ F] (T : Set F) (_hT : Convex ℝ T) (_hne : (interior T).Nonempty)
      (w : F) (_hw : w ∉ interior T), ∃ d : F, d ≠ 0 ∧ ∀ t ∈ T, inner ℝ t d ≤ inner ℝ w d := by
    intro F _ _ _ T hT hne w hw
    haveI : CompleteSpace F := FiniteDimensional.complete ℝ F
    obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hT.interior isOpen_interior hw
    set d := (InnerProductSpace.toDual ℝ F).symm f with hd_def
    have hd : ∀ x, inner ℝ x d = f x := by
      intro x
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    refine ⟨d, ?_, ?_⟩
    · intro h0
      obtain ⟨a, ha⟩ := hne
      have h1 := hf a ha
      rw [← hd, ← hd, h0, inner_zero_right, inner_zero_right] at h1
      exact lt_irrefl _ h1
    · intro t ht
      have hcl : closure (interior T) ⊆ {x | f x ≤ f w} :=
        closure_minimal (fun a ha => (hf a ha).le) (isClosed_le f.continuous continuous_const)
      have ht' : t ∈ closure (interior T) := by
        rw [hT.closure_interior_eq_closure_of_nonempty_interior hne]
        exact subset_closure ht
      rw [hd, hd]
      exact hcl ht'
  obtain ⟨s₀, hs₀⟩ := hS_nonempty
  have hs₀A : s₀ ∈ affineSpan ℝ S := subset_affineSpan ℝ S hs₀
  set V : Submodule ℝ E := (affineSpan ℝ S).direction with hV_def
  have hV : V = vectorSpan ℝ S := direction_affineSpan ℝ S
  -- the custom affine hull agrees with Mathlib's affine span
  have hF0 : ∀ x, x ∈ affineHull S ↔ x ∈ affineSpan ℝ S := by
    intro x
    constructor
    · intro hx
      simp only [affineHull, Set.mem_iUnion, Set.mem_setOf_eq] at hx
      obtain ⟨k, hk, p, hp, a, ha, rfl⟩ := hx
      have h1 : ∑ i ∈ Finset.univ, a i = 1 := ha
      have := affineCombination_mem_affineSpan (k := ℝ) h1 p
      rw [Finset.affineCombination_eq_linear_combination _ _ _ h1] at this
      exact affineSpan_mono ℝ (Set.range_subset_iff.2 hp) this
    · intro hx
      have hx' : x ∈ affineSpan ℝ (Set.range (Subtype.val : S → E)) := by
        rwa [Subtype.range_coe]
      obtain ⟨t, w, hw, rfl⟩ := (mem_affineSpan_iff_eq_affineCombination ℝ E).1 hx'
      rw [Finset.affineCombination_eq_linear_combination _ _ _ hw]
      have hpos : 0 < t.card := by
        rcases Nat.eq_zero_or_pos t.card with h | h
        · rw [Finset.card_eq_zero] at h
          subst h
          simp at hw
        · exact h
      simp only [affineHull, Set.mem_iUnion, Set.mem_setOf_eq]
      refine ⟨t.card, hpos, fun j => ((t.equivFin.symm j : t) : S),
        fun j => ((t.equivFin.symm j : t) : S).2, fun j => w (t.equivFin.symm j), ?_, ?_⟩
      · rw [← hw, ← Finset.sum_coe_sort t]
        exact Equiv.sum_comp t.equivFin.symm (fun i => w i)
      · rw [← Finset.sum_coe_sort t]
        exact (Equiv.sum_comp t.equivFin.symm (fun i => w i • ((i : S) : E))).symm
  -- basic facts on the support function
  have hσ_ge : ∀ d, ∀ v ∈ S, ((inner ℝ v d : ℝ) : EReal) ≤ σS d :=
    fun d v hv => le_sSup ⟨v, hv, rfl⟩
  have hσ_le : ∀ d (c : ℝ), (∀ v ∈ S, inner ℝ v d ≤ c) → σS d ≤ (c : EReal) := by
    intro d c h
    apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    exact EReal.coe_le_coe_iff.2 (h v hv)
  have hneg : ∀ d : E, (-1 : ℤ) • d = -d := fun d => by simp
  have hperp_eval : ∀ d ∈ Vᗮ, ∀ v ∈ S, inner ℝ v d = inner ℝ s₀ d := by
    intro d hd v hv
    have hmem : v - s₀ ∈ V := by rw [hV]; exact vsub_mem_vectorSpan ℝ hv hs₀
    have := (Submodule.mem_orthogonal V d).1 hd _ hmem
    rw [inner_sub_left] at this
    linarith
  have hperp_σ : ∀ d ∈ Vᗮ, σS d = ((inner ℝ s₀ d : ℝ) : EReal) := by
    intro d hd
    apply le_antisymm
    · exact hσ_le d _ (fun v hv => (hperp_eval d hd v hv).le)
    · exact hσ_ge d s₀ hs₀
  have hdiff : ∀ d, ∀ v ∈ S, ∀ w ∈ S,
      ((inner ℝ v d - inner ℝ w d : ℝ) : EReal) ≤ σS d + σS (-d) := by
    intro d v hv w hw
    have h1 := hσ_ge d v hv
    have h2 := hσ_ge (-d) w hw
    rw [inner_neg_right] at h2
    calc ((inner ℝ v d - inner ℝ w d : ℝ) : EReal)
        = ((inner ℝ v d : ℝ) : EReal) + ((-inner ℝ w d : ℝ) : EReal) := by
          rw [← EReal.coe_add]; ring_nf
      _ ≤ σS d + σS (-d) := add_le_add h1 h2
  have hsum_nonneg : ∀ d, 0 ≤ σS d + σS (-1 • d) := by
    intro d
    rw [hneg]
    have := hdiff d s₀ hs₀ s₀ hs₀
    simpa using this
  have hsum_zero_iff : ∀ d, σS d + σS (-1 • d) = 0 ↔ d ∈ Vᗮ := by
    intro d
    rw [hneg]
    constructor
    · intro h
      have hflat : ∀ v ∈ S, inner ℝ v d = inner ℝ s₀ d := by
        intro v hv
        have h1 := hdiff d v hv s₀ hs₀
        have h2 := hdiff d s₀ hs₀ v hv
        rw [h] at h1 h2
        have h1' := EReal.coe_nonpos.1 h1
        have h2' := EReal.coe_nonpos.1 h2
        linarith
      rw [Submodule.mem_orthogonal]
      intro u hu
      rw [hV, vectorSpan_eq_span_vsub_set_right ℝ hs₀] at hu
      induction hu using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨v, hv, rfl⟩ := hx
        show inner ℝ (v -ᵥ s₀) d = 0
        rw [vsub_eq_sub, inner_sub_left, hflat v hv, sub_self]
      | zero => exact inner_zero_left _
      | add x y _ _ hx hy => rw [inner_add_left, hx, hy, add_zero]
      | smul a x _ hx => rw [inner_smul_left, hx, mul_zero]
    · intro hd
      have hd' : -d ∈ Vᗮ := neg_mem hd
      rw [hperp_σ d hd, hperp_σ (-d) hd', inner_neg_right, ← EReal.coe_add]
      simp
  -- metric characterization of the intrinsic interior
  have hri : ∀ x ∈ affineSpan ℝ S, x ∈ intrinsicInterior ℝ S ↔
      ∃ ε > 0, ∀ y ∈ affineSpan ℝ S, dist y x < ε → y ∈ S := by
    intro x hx
    rw [mem_intrinsicInterior]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_subtype] at hy
      obtain ⟨u, hu, hus⟩ := hy
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hu
      refine ⟨ε, hε, fun z hz hdist => ?_⟩
      have : (⟨z, hz⟩ : affineSpan ℝ S) ∈ Subtype.val ⁻¹' u := hball hdist
      exact hus this
    · rintro ⟨ε, hε, h⟩
      refine ⟨⟨x, hx⟩, ?_, rfl⟩
      rw [mem_interior_iff_mem_nhds, mem_nhds_subtype]
      exact ⟨Metric.ball x ε, Metric.ball_mem_nhds x hε, fun z hz => h z.1 z.2 hz⟩
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    constructor
    · intro hs d hd
      rw [hsum_zero_iff] at hd
      rw [hperp_σ d hd]
      have hsA := (hF0 s).1 hs
      have hmem : s - s₀ ∈ V := AffineSubspace.vsub_mem_direction hsA hs₀A
      have := (Submodule.mem_orthogonal V d).1 hd _ hmem
      rw [inner_sub_left] at this
      have h2 : inner ℝ s d = inner ℝ s₀ d := by linarith
      rw [h2]
    · intro H
      apply (hF0 s).2
      rw [← AffineSubspace.vsub_right_mem_direction_iff_mem hs₀A s]
      change s - s₀ ∈ V
      rw [← Submodule.orthogonal_orthogonal V, Submodule.mem_orthogonal]
      intro u hu
      have h1 := H u ((hsum_zero_iff u).2 hu)
      rw [hperp_σ u hu] at h1
      have h2 : inner ℝ s u = inner ℝ s₀ u := by exact_mod_cast h1
      rw [real_inner_comm, inner_sub_left, h2, sub_self]
  · -- part 2
    constructor
    · intro hs
      have hsS : s ∈ S := intrinsicInterior_subset hs
      have hsA : s ∈ affineSpan ℝ S := subset_affineSpan ℝ S hsS
      refine ⟨(hF0 s).2 hsA, ?_⟩
      intro d hd
      have hd0 : σS d + σS (-1 • d) ≠ 0 := ne_of_gt hd
      rw [Ne, hsum_zero_iff, Submodule.mem_orthogonal] at hd0
      push_neg at hd0
      obtain ⟨w, hwV, hwd⟩ := hd0
      obtain ⟨w', hw'V, hw'd⟩ : ∃ w' ∈ V, 0 < inner ℝ w' d := by
        rcases lt_or_gt_of_ne hwd with h | h
        · exact ⟨-w, neg_mem hwV, by rw [inner_neg_left]; linarith⟩
        · exact ⟨w, hwV, h⟩
      obtain ⟨ε, hε, hball⟩ := (hri s hsA).1 hs
      have hw'0 : w' ≠ 0 := by rintro rfl; simp at hw'd
      have hnorm : 0 < ‖w'‖ := norm_pos_iff.2 hw'0
      set t := ε / (2 * ‖w'‖) with ht
      have htpos : 0 < t := by positivity
      have hyA : t • w' + s ∈ affineSpan ℝ S :=
        AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hw'V) hsA
      have hdist : dist (t • w' + s) s < ε := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg htpos.le, ht]
        field_simp
        linarith
      have hyS := hball _ hyA hdist
      calc ((inner ℝ s d : ℝ) : EReal) < ((inner ℝ (t • w' + s) d : ℝ) : EReal) := by
            rw [EReal.coe_lt_coe_iff, inner_add_left, real_inner_smul_left]
            nlinarith
        _ ≤ σS d := hσ_ge d _ hyS
    · rintro ⟨hs, H⟩
      have hsA := (hF0 s).1 hs
      by_contra hns
      set T : Set V := {w | s₀ + (w : E) ∈ S} with hT_def
      have hw₀V : s - s₀ ∈ V := AffineSubspace.vsub_mem_direction hsA hs₀A
      set w₀ : V := ⟨s - s₀, hw₀V⟩ with hw₀_def
      have hTconv : Convex ℝ T := by
        intro x hx y hy a b ha hb hab
        have h := hS_convex hx hy ha hb hab
        show s₀ + ((a • x + b • y : V) : E) ∈ S
        rw [Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
        convert h using 1
        calc s₀ + (a • (x:E) + b • (y:E)) = (a + b) • s₀ + (a • (x:E) + b • (y:E)) := by
              rw [hab, one_smul]
          _ = a • (s₀ + (x:E)) + b • (s₀ + (y:E)) := by module
      have hTint : (interior T).Nonempty := by
        obtain ⟨r, hr⟩ := Set.Nonempty.intrinsicInterior hS_convex ⟨s₀, hs₀⟩
        have hrS : r ∈ S := intrinsicInterior_subset hr
        have hrA : r ∈ affineSpan ℝ S := subset_affineSpan ℝ S hrS
        obtain ⟨ε, hε, hball⟩ := (hri r hrA).1 hr
        have hwrV : r - s₀ ∈ V := AffineSubspace.vsub_mem_direction hrA hs₀A
        refine ⟨⟨r - s₀, hwrV⟩, ?_⟩
        rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
        refine ⟨ε, hε, fun w hw => ?_⟩
        show s₀ + (w : E) ∈ S
        apply hball
        · have := AffineSubspace.vadd_mem_of_mem_direction w.2 hs₀A
          rw [vadd_eq_add, add_comm] at this
          exact this
        · rw [Metric.mem_ball, Subtype.dist_eq] at hw
          rw [dist_eq_norm] at hw ⊢
          convert hw using 2
          simp only
          abel
      have hw₀ : w₀ ∉ interior T := by
        intro hw₀int
        apply hns
        rw [hri s hsA]
        rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hw₀int
        obtain ⟨ε, hε, hball⟩ := hw₀int
        refine ⟨ε, hε, fun y hyA hy => ?_⟩
        have hyV : y - s₀ ∈ V := AffineSubspace.vsub_mem_direction hyA hs₀A
        have : (⟨y - s₀, hyV⟩ : V) ∈ T := by
          apply hball
          rw [Metric.mem_ball, Subtype.dist_eq]
          simp only [w₀]
          rw [dist_sub_right]
          exact hy
        simpa [T] using this
      obtain ⟨d', hd'0, hd'⟩ := FCA_aux_supporting T hTconv hTint w₀ hw₀
      set d : E := (d' : E) with hd_def
      have hd0 : d ≠ 0 := by simpa [d] using hd'0
      have hdV : d ∈ V := d'.2
      have hle : ∀ v ∈ S, inner ℝ v d ≤ inner ℝ s d := by
        intro v hv
        have hvV : v - s₀ ∈ V :=
          AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ S hv) hs₀A
        have := hd' ⟨v - s₀, hvV⟩ (by simpa [T] using hv)
        simp only [Submodule.coe_inner, w₀] at this
        rw [inner_sub_left, inner_sub_left] at this
        linarith
      have hσd : σS d ≤ ((inner ℝ s d : ℝ) : EReal) := hσ_le d _ hle
      have hpos : σS d + σS (-1 • d) > 0 := by
        refine lt_of_le_of_ne (hsum_nonneg d) (fun h => ?_)
        have hperp : d ∈ Vᗮ := (hsum_zero_iff d).1 h.symm
        have := (Submodule.mem_orthogonal V d).1 hperp d hdV
        exact hd0 (inner_self_eq_zero.1 this)
      have := H d hpos
      exact absurd (lt_of_lt_of_le this hσd) (lt_irrefl _)
  · -- part 3
    constructor
    · intro hs d hd
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hs
      obtain ⟨ε, hε, hball⟩ := hs
      have hnorm : 0 < ‖d‖ := norm_pos_iff.2 hd
      set t := ε / (2 * ‖d‖) with ht
      have htpos : 0 < t := by positivity
      have hdist : dist (t • d + s) s < ε := by
        rw [dist_eq_norm, add_sub_cancel_right, norm_smul, Real.norm_of_nonneg htpos.le, ht]
        field_simp
        linarith
      have hyS : t • d + s ∈ S := hball (Metric.mem_ball.2 hdist)
      calc ((inner ℝ s d : ℝ) : EReal) < ((inner ℝ (t • d + s) d : ℝ) : EReal) := by
            rw [EReal.coe_lt_coe_iff, inner_add_left, real_inner_smul_left,
              real_inner_self_eq_norm_sq]
            have : 0 < t * ‖d‖ ^ 2 := by positivity
            linarith
        _ ≤ σS d := hσ_ge d _ hyS
    · intro H
      by_contra hns
      rcases (interior S).eq_empty_or_nonempty with hempty | hne
      · have hAne : affineSpan ℝ S ≠ ⊤ := by
          intro hA
          have := (hS_convex.interior_nonempty_iff_affineSpan_eq_top).2 hA
          rw [hempty] at this
          exact Set.not_nonempty_empty this
        have hVne : V ≠ ⊤ := by
          intro hV'
          apply hAne
          exact (AffineSubspace.direction_eq_top_iff_of_nonempty ⟨s₀, hs₀A⟩).1 hV'
        have hVperp : Vᗮ ≠ ⊥ := by
          rwa [Ne, Submodule.orthogonal_eq_bot_iff]
        obtain ⟨d, hd, hd0⟩ := (Submodule.ne_bot_iff _).1 hVperp
        have h1 := H d hd0
        have h2 := H (-d) (neg_ne_zero.2 hd0)
        rw [hperp_σ d hd] at h1
        rw [hperp_σ (-d) (neg_mem hd)] at h2
        rw [EReal.coe_lt_coe_iff] at h1 h2
        rw [inner_neg_right, inner_neg_right] at h2
        linarith
      · obtain ⟨d, hd0, hd⟩ := FCA_aux_supporting S hS_convex hne s hns
        have h1 := H d hd0
        have h2 : σS d ≤ ((inner ℝ s d : ℝ) : EReal) := hσ_le d _ hd
        exact absurd (lt_of_lt_of_le h1 h2) (lt_irrefl _)

end FCA_chap_C_2_2_3
