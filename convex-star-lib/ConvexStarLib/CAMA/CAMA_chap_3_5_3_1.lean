import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_5_3_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_5_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_5_3_1`, so the main result is `CAMA_chap_3_5_3_1.CAMA_chap_3_5_3_1`.
-/

namespace CAMA_chap_3_5_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem aux_posTangentConeAt_eq {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {C : Set V} (hC : Convex ℝ C) {x : V} (hx : x ∈ C) :
    posTangentConeAt C x = closure {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C, v = t • (c - x)} := by
  apply Set.Subset.antisymm
  · intro v hv
    rw [mem_tangentConeAt_iff_exists_seq] at hv
    obtain ⟨c, d, -, hds, hcd⟩ := hv
    apply mem_closure_of_tendsto hcd
    filter_upwards [hds] with n hn
    exact ⟨(c n : ℝ), (c n).2, x + d n, hn, by simp [NNReal.smul_def]⟩
  · have hcl : IsClosed (posTangentConeAt C x) := by
      unfold posTangentConeAt
      rw [tangentConeAt_def]
      exact isClosed_setOf_clusterPt
    refine closure_minimal ?_ hcl
    rintro v ⟨t, ht, c, hc, rfl⟩
    refine mem_tangentConeAt_of_seq Filter.atTop
      (fun n : ℕ => (⟨t * ((n:ℝ) + 1), by positivity⟩ : NNReal))
      (fun n : ℕ => (1 / ((n:ℝ) + 1)) • (c - x)) ?_ ?_ ?_
    · have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const (c - x)
      simpa using h
    · filter_upwards with n
      apply hC.add_smul_sub_mem hx hc
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by positivity)]
      have : (0:ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    · apply tendsto_const_nhds.congr
      intro n
      rw [NNReal.smul_def, smul_smul]
      congr 1
      simp only [NNReal.coe_mk]
      field_simp

theorem aux_rescale {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {C : Set V} (hC : Convex ℝ C) {x : V} (hx : x ∈ C) {c : V} (hc : c ∈ C)
    {t₁ t : ℝ} (ht₁ : 0 ≤ t₁) (ht : t₁ ≤ t) (htpos : 0 < t) :
    ∃ c' ∈ C, t₁ • (c - x) = t • (c' - x) := by
  refine ⟨x + (t₁ / t) • (c - x),
    hC.add_smul_sub_mem hx hc ⟨by positivity, (div_le_one htpos).2 ht⟩, ?_⟩
  rw [add_sub_cancel_left, smul_smul]
  congr 1
  field_simp

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem aux_prod_tangent (C₁ : Set E) (D : Set F) (hC : Convex ℝ C₁) (hD : Convex ℝ D)
    (x₁ : E) (x₂ : F) (hx₁ : x₁ ∈ C₁) (hx₂ : x₂ ∈ D) :
    posTangentConeAt (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F)))
        (WithLp.toLp 2 (x₁, x₂))
      = WithLp.ofLp ⁻¹' (posTangentConeAt C₁ x₁ ×ˢ posTangentConeAt D x₂) := by
  have hP : Convex ℝ (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F))) :=
    (hC.prod hD).linear_preimage (WithLp.linearEquiv 2 ℝ (E × F)).toLinearMap
  have hp₀ : WithLp.toLp 2 (x₁, x₂) ∈ (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F))) :=
    ⟨hx₁, hx₂⟩
  rw [aux_posTangentConeAt_eq hP hp₀, aux_posTangentConeAt_eq hC hx₁,
    aux_posTangentConeAt_eq hD hx₂, ← closure_prod_eq]
  have hK : {v : WithLp 2 (E × F) | ∃ t : ℝ, 0 ≤ t ∧
      ∃ c ∈ (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F))),
        v = t • (c - WithLp.toLp 2 (x₁, x₂))}
      = WithLp.ofLp ⁻¹' ({v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C₁, v = t • (c - x₁)} ×ˢ
          {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ D, v = t • (c - x₂)}) := by
    ext v
    constructor
    · rintro ⟨t, ht, c, hc, rfl⟩
      exact ⟨⟨t, ht, (WithLp.ofLp c).1, hc.1, by simp⟩, ⟨t, ht, (WithLp.ofLp c).2, hc.2, by simp⟩⟩
    · rintro ⟨⟨t₁, ht₁, c₁, hc₁, h₁⟩, ⟨t₂, ht₂, c₂, hc₂, h₂⟩⟩
      obtain ⟨c₁', hc₁', e₁⟩ :=
        aux_rescale hC hx₁ hc₁ ht₁ (show t₁ ≤ t₁ + t₂ + 1 by linarith) (by linarith)
      obtain ⟨c₂', hc₂', e₂⟩ :=
        aux_rescale hD hx₂ hc₂ ht₂ (show t₂ ≤ t₁ + t₂ + 1 by linarith) (by linarith)
      refine ⟨t₁ + t₂ + 1, by linarith, WithLp.toLp 2 (c₁', c₂'), ⟨hc₁', hc₂'⟩, ?_⟩
      apply WithLp.ofLp_injective 2
      ext
      · simpa [e₁] using h₁
      · simpa [e₂] using h₂
  rw [hK]
  exact ((WithLp.homeomorphProd 2 E F).preimage_closure _).symm

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem aux_prod_normal (C₁ : Set E) (D : Set F) (x₁ : E) (x₂ : F) (hx₁ : x₁ ∈ C₁)
    (hx₂ : x₂ ∈ D) :
    convexNormalCone (WithLp.toLp 2 (x₁, x₂)) (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F)))
      = WithLp.ofLp ⁻¹' (convexNormalCone x₁ C₁ ×ˢ convexNormalCone x₂ D) := by
  ext s
  simp only [convexNormalCone, Set.mem_preimage, Set.mem_prod, Set.mem_setOf_eq]
  constructor
  · intro h
    constructor
    · intro y hy
      have := h (WithLp.toLp 2 (y, x₂)) ⟨hy, hx₂⟩
      simpa using this
    · intro y hy
      have := h (WithLp.toLp 2 (x₁, y)) ⟨hx₁, hy⟩
      simpa using this
  · rintro ⟨h₁, h₂⟩ y hy
    have a := h₁ _ hy.1
    have b := h₂ _ hy.2
    simp only [WithLp.prod_inner_apply, WithLp.ofLp_sub, Prod.fst_sub,
      Prod.snd_sub]
    linarith

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] in
theorem aux_image_tangent (C₁ : Set E) (hC : Convex ℝ C₁) (x : E) (hx : x ∈ C₁) (y₀ : F)
    (A₀ : E →L[ℝ] F) :
    posTangentConeAt ((fun z => y₀ + A₀ z) '' C₁) (y₀ + A₀ x)
      = closure (A₀ '' posTangentConeAt C₁ x) := by
  have hI : Convex ℝ ((fun z => y₀ + A₀ z) '' C₁) := by
    have := (hC.linear_image A₀.toLinearMap).translate y₀
    rw [Set.image_image] at this
    exact this
  have hI₀ : y₀ + A₀ x ∈ (fun z => y₀ + A₀ z) '' C₁ := ⟨x, hx, rfl⟩
  rw [aux_posTangentConeAt_eq hI hI₀, aux_posTangentConeAt_eq hC hx]
  have hK : {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ (fun z => y₀ + A₀ z) '' C₁, v = t • (c - (y₀ + A₀ x))}
      = A₀ '' {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C₁, v = t • (c - x)} := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨t • (z - x), ⟨t, ht, z, hz, rfl⟩, by simp [map_sub, map_smul]⟩
    · rintro ⟨_, ⟨t, ht, z, hz, rfl⟩, rfl⟩
      exact ⟨t, ht, y₀ + A₀ z, ⟨z, hz, rfl⟩, by simp [map_sub, map_smul]⟩
  rw [hK]
  apply Set.Subset.antisymm
  · exact closure_mono (Set.image_mono subset_closure)
  · exact closure_minimal (image_closure_subset_closure_image A₀.continuous) isClosed_closure

theorem aux_image_normal (C₁ : Set E) (x : E) (y₀ : F) (A₀ : E →L[ℝ] F) :
    convexNormalCone (y₀ + A₀ x) ((fun z => y₀ + A₀ z) '' C₁)
      = (ContinuousLinearMap.adjoint A₀) ⁻¹' (convexNormalCone x C₁) := by
  ext s
  simp only [convexNormalCone, Set.mem_preimage, Set.mem_setOf_eq, Set.forall_mem_image]
  apply forall₂_congr
  intro z _
  rw [ContinuousLinearMap.adjoint_inner_left, map_sub, add_sub_add_left_eq_sub]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem aux_setAdd_eq (C₁ C₂ : Set E) : setAdd C₁ C₂ = C₁ + C₂ := by
  ext v
  simp only [setAdd, Set.mem_setOf_eq, Set.mem_add]
  constructor
  · rintro ⟨c, hc, k, hk, rfl⟩
    exact ⟨c, hc, k, hk, rfl⟩
  · rintro ⟨c, hc, k, hk, rfl⟩
    exact ⟨c, hc, k, hk, rfl⟩

omit [FiniteDimensional ℝ E] in
theorem aux_sum_tangent (C₁ C₂ : Set E) (hC₁ : Convex ℝ C₁) (hC₂ : Convex ℝ C₂) (x₁ x₂ : E)
    (hx₁ : x₁ ∈ C₁) (hx₂ : x₂ ∈ C₂) :
    posTangentConeAt (setAdd C₁ C₂) (x₁ + x₂)
      = closure (setAdd (posTangentConeAt C₁ x₁) (posTangentConeAt C₂ x₂)) := by
  have hS : Convex ℝ (setAdd C₁ C₂) := by
    rw [aux_setAdd_eq]
    exact hC₁.add hC₂
  have hS₀ : x₁ + x₂ ∈ setAdd C₁ C₂ := ⟨x₁, hx₁, x₂, hx₂, rfl⟩
  rw [aux_posTangentConeAt_eq hS hS₀, aux_posTangentConeAt_eq hC₁ hx₁,
    aux_posTangentConeAt_eq hC₂ hx₂]
  have hK : {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ setAdd C₁ C₂, v = t • (c - (x₁ + x₂))}
      = setAdd {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C₁, v = t • (c - x₁)}
          {v | ∃ t : ℝ, 0 ≤ t ∧ ∃ c ∈ C₂, v = t • (c - x₂)} := by
    ext v
    constructor
    · rintro ⟨t, ht, _, ⟨c₁, hc₁, c₂, hc₂, rfl⟩, rfl⟩
      refine ⟨t • (c₁ - x₁), ⟨t, ht, c₁, hc₁, rfl⟩, t • (c₂ - x₂), ⟨t, ht, c₂, hc₂, rfl⟩, ?_⟩
      rw [← smul_add]
      congr 1
      abel
    · rintro ⟨_, ⟨t₁, ht₁, c₁, hc₁, rfl⟩, _, ⟨t₂, ht₂, c₂, hc₂, rfl⟩, rfl⟩
      obtain ⟨c₁', hc₁', e₁⟩ :=
        aux_rescale hC₁ hx₁ hc₁ ht₁ (show t₁ ≤ t₁ + t₂ + 1 by linarith) (by linarith)
      obtain ⟨c₂', hc₂', e₂⟩ :=
        aux_rescale hC₂ hx₂ hc₂ ht₂ (show t₂ ≤ t₁ + t₂ + 1 by linarith) (by linarith)
      refine ⟨t₁ + t₂ + 1, by linarith, c₁' + c₂', ⟨c₁', hc₁', c₂', hc₂', rfl⟩, ?_⟩
      rw [e₁, e₂, ← smul_add]
      congr 1
      abel
  rw [hK]
  apply Set.Subset.antisymm
  · apply closure_mono
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact ⟨a, subset_closure ha, b, subset_closure hb, rfl⟩
  · apply closure_minimal _ isClosed_closure
    rintro _ ⟨a, ha, b, hb, rfl⟩
    exact map_mem_closure₂ continuous_add ha hb (fun a ha b hb => ⟨a, ha, b, hb, rfl⟩)

omit [FiniteDimensional ℝ E] in
theorem aux_sum_normal (C₁ C₂ : Set E) (x₁ x₂ : E) (hx₁ : x₁ ∈ C₁) (hx₂ : x₂ ∈ C₂) :
    convexNormalCone (x₁ + x₂) (setAdd C₁ C₂)
      = convexNormalCone x₁ C₁ ∩ convexNormalCone x₂ C₂ := by
  ext s
  simp only [convexNormalCone, setAdd, Set.mem_setOf_eq, Set.mem_inter_iff]
  constructor
  · intro h
    constructor
    · intro y hy
      have := h (y + x₂) ⟨y, hy, x₂, hx₂, rfl⟩
      rwa [add_sub_add_right_eq_sub] at this
    · intro y hy
      have := h (x₁ + y) ⟨x₁, hx₁, y, hy, rfl⟩
      rwa [add_sub_add_left_eq_sub] at this
  · rintro ⟨h₁, h₂⟩ _ ⟨c, hc, k, hk, rfl⟩
    have e : c + k - (x₁ + x₂) = (c - x₁) + (k - x₂) := by abel
    rw [e, inner_add_right]
    linarith [h₁ c hc, h₂ k hk]

set_option linter.unusedVariables false in
theorem CAMA_chap_3_5_3_1
  (x : E)
  (C₁ : Set E)
  (C₂ : Set E)
  (hC₁₀ : Set.Nonempty C₁)
  (hC₁₁ : IsClosed C₁)
  (hC₁₂ : Convex ℝ C₁)
  (hC₂₀ : Set.Nonempty C₂)
  (hC₂₁ : IsClosed C₂)
  (hC₂₂ : Convex ℝ C₂) :
  (x ∈ C₁ ∩ C₂ → posTangentConeAt (C₁ ∩ C₂) x ⊆ posTangentConeAt C₁ x ∩ posTangentConeAt C₂ x ∧
    convexNormalCone x (C₁ ∩ C₂) ⊇ setAdd (convexNormalCone x C₁) (convexNormalCone x C₂)) ∧
  (∀ (D : Set F), Set.Nonempty D → IsClosed D → Convex ℝ D →
    ∀ (x₁ : E) (x₂ : F), x₁ ∈ C₁ → x₂ ∈ D →
      posTangentConeAt (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F))) (WithLp.toLp 2 (x₁, x₂))
        = WithLp.ofLp ⁻¹' (posTangentConeAt C₁ x₁ ×ˢ posTangentConeAt D x₂) ∧
      convexNormalCone (WithLp.toLp 2 (x₁, x₂)) (WithLp.ofLp ⁻¹' (C₁ ×ˢ D) : Set (WithLp 2 (E × F)))
        = WithLp.ofLp ⁻¹' (convexNormalCone x₁ C₁ ×ˢ convexNormalCone x₂ D)) ∧
  (∀ (y₀ : F) (A₀ : E →L[ℝ] F), x ∈ C₁ →
    posTangentConeAt ((fun z => y₀ + A₀ z) '' C₁) (y₀ + A₀ x)
      = closure (A₀ '' posTangentConeAt C₁ x) ∧
    convexNormalCone (y₀ + A₀ x) ((fun z => y₀ + A₀ z) '' C₁)
      = (ContinuousLinearMap.adjoint A₀) ⁻¹' (convexNormalCone x C₁)) ∧
  (∀ (x₁ x₂ : E), x₁ ∈ C₁ → x₂ ∈ C₂ →
    posTangentConeAt (setAdd C₁ C₂) (x₁ + x₂)
      = closure (setAdd (posTangentConeAt C₁ x₁) (posTangentConeAt C₂ x₂)) ∧
    convexNormalCone (x₁ + x₂) (setAdd C₁ C₂)
      = convexNormalCone x₁ C₁ ∩ convexNormalCone x₂ C₂) := by
  refine ⟨fun _ => ⟨?_, ?_⟩, ?_, ?_, ?_⟩
  · exact Set.subset_inter (tangentConeAt_mono Set.inter_subset_left)
      (tangentConeAt_mono Set.inter_subset_right)
  · rintro _ ⟨s₁, hs₁, s₂, hs₂, rfl⟩
    simp only [convexNormalCone, Set.mem_setOf_eq] at hs₁ hs₂ ⊢
    intro y hy
    rw [inner_add_left]
    linarith [hs₁ y hy.1, hs₂ y hy.2]
  · intro D _ _ hD x₁ x₂ hx₁ hx₂
    exact ⟨aux_prod_tangent C₁ D hC₁₂ hD x₁ x₂ hx₁ hx₂, aux_prod_normal C₁ D x₁ x₂ hx₁ hx₂⟩
  · intro y₀ A₀ hx
    exact ⟨aux_image_tangent C₁ hC₁₂ x hx y₀ A₀, aux_image_normal C₁ x y₀ A₀⟩
  · intro x₁ x₂ hx₁ hx₂
    exact ⟨aux_sum_tangent C₁ C₂ hC₁₂ hC₂₂ x₁ x₂ hx₁ hx₂, aux_sum_normal C₁ C₂ x₁ x₂ hx₁ hx₂⟩

end CAMA_chap_3_5_3_1
