import ConvexStarLib.Defs

/-!
# `FCA_chap_E_3_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_3_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_3_3_1`, so the main result is `FCA_chap_E_3_3_1.FCA_chap_E_3_3_1`.
-/

namespace FCA_chap_E_3_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem aux_mem_convexHull_iff {F : Type*} [AddCommGroup F] [Module ℝ F] (k : ℕ) (p : ℕ → F)
    (v : F) :
    v ∈ convexHull ℝ (p '' (Finset.range k : Set ℕ)) ↔
      ∃ α : ℕ → ℝ, (∀ i ∈ Finset.range k, 0 ≤ α i) ∧ ∑ i ∈ Finset.range k, α i = 1 ∧
        ∑ i ∈ Finset.range k, α i • p i = v := by
  constructor
  · intro hv
    refine (convexHull_min ?_ ?_ : convexHull ℝ (p '' (Finset.range k : Set ℕ)) ⊆
      {v | ∃ α : ℕ → ℝ, (∀ i ∈ Finset.range k, 0 ≤ α i) ∧ ∑ i ∈ Finset.range k, α i = 1 ∧
        ∑ i ∈ Finset.range k, α i • p i = v}) hv
    · rintro _ ⟨j, hj, rfl⟩
      refine ⟨fun i => if i = j then 1 else 0, ?_, ?_, ?_⟩
      · intro i _
        dsimp only
        split_ifs <;> norm_num
      · simpa using hj
      · have hj' : j < k := by simpa using hj
        simp [hj']
    · rintro x ⟨α, h0, h1, rfl⟩ y ⟨β, h0', h1', rfl⟩ a c ha hc hac
      refine ⟨fun i => a * α i + c * β i, ?_, ?_, ?_⟩
      · intro i hi
        have := h0 i hi
        have := h0' i hi
        positivity
      · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, h1, h1']
        linarith
      · simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  · rintro ⟨α, h0, h1, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem h0 h1 (fun i hi => subset_convexHull ℝ _ ⟨i, hi, rfl⟩)

theorem FCA_chap_E_3_3_1
  (k : ℕ)
  (s : ℕ → E)
  (b : ℕ → ℝ)
  (hk : k ≥ 1) :
  let f := fun x => sSup (Set.image (fun i => inner ℝ (s i) x - b i) (Finset.range k))
  (effDom ((conjugate (liftRealtoEReal f))) =
  convexHull ℝ (Set.image s (Finset.range k))) ∧
  (∀ v ∈ convexHull ℝ (Set.image s (Finset.range k)),
  (conjugate (liftRealtoEReal f) v) =
  sInf {r : EReal | ∃ (α : ℕ → ℝ),
                    (∀ i ∈ Finset.range k, α i ≥ 0) ∧
                    (∑ i ∈ Finset.range k, α i = 1) ∧
                    (∑ i ∈ Finset.range k, α i • s i = v) ∧
                    (r = (∑ i ∈ Finset.range k, α i * b i : ℝ))}) := by
  intro f
  have hfin : ∀ x : E, ((fun i => inner ℝ (s i) x - b i) '' (Finset.range k : Set ℕ)).Finite :=
    fun x => (Finset.finite_toSet _).image _
  have hne : ∀ x : E, ((fun i => inner ℝ (s i) x - b i) '' (Finset.range k : Set ℕ)).Nonempty :=
    fun x => ⟨_, 0, by simp; omega, rfl⟩
  have hle : ∀ x : E, ∀ i ∈ Finset.range k, inner ℝ (s i) x - b i ≤ f x :=
    fun x i hi => le_csSup (hfin x).bddAbove ⟨i, hi, rfl⟩
  have hmem : ∀ x : E, ∃ i ∈ Finset.range k, f x = inner ℝ (s i) x - b i := by
    intro x
    obtain ⟨i, hi, h⟩ := (hne x).csSup_mem (hfin x)
    exact ⟨i, hi, h.symm⟩
  have hconj : ∀ v : E, conjugate (liftRealtoEReal f) v =
      sSup ((fun x => ((inner ℝ v x - f x : ℝ) : EReal)) '' Set.univ) := by
    intro v
    rfl
  have hconj_ge : ∀ v x : E, ((inner ℝ v x - f x : ℝ) : EReal) ≤ conjugate (liftRealtoEReal f) v := by
    intro v x
    rw [hconj]
    exact le_sSup ⟨x, Set.mem_univ _, rfl⟩
  -- Part B : upper bound from any representation
  have partB : ∀ v : E, ∀ α : ℕ → ℝ, (∀ i ∈ Finset.range k, 0 ≤ α i) →
      ∑ i ∈ Finset.range k, α i = 1 → ∑ i ∈ Finset.range k, α i • s i = v →
      conjugate (liftRealtoEReal f) v ≤ ((∑ i ∈ Finset.range k, α i * b i : ℝ) : EReal) := by
    intro v α h0 h1 h2
    rw [hconj]
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    rw [EReal.coe_le_coe_iff, ← h2, sum_inner]
    simp only [real_inner_smul_left]
    have : f x = ∑ i ∈ Finset.range k, α i * f x := by rw [← Finset.sum_mul, h1, one_mul]
    rw [this, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro i hi
    have := hle x i hi
    have := h0 i hi
    nlinarith
  -- Part A : outside the convex hull the conjugate is infinite
  have partA : ∀ v : E, v ∉ convexHull ℝ (Set.image s (Finset.range k : Set ℕ)) →
      conjugate (liftRealtoEReal f) v = ⊤ := by
    intro v hv
    obtain ⟨ψ, u, hψ1, hψ2⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      ((Finset.finite_toSet _).image _).isClosed_convexHull hv
    have hy : ∀ w, inner ℝ ((InnerProductSpace.toDual ℝ E).symm ψ) w = ψ w :=
      fun w => InnerProductSpace.toDual_symm_apply
    have hsi : ∀ i ∈ Finset.range k, ψ (s i) < u :=
      fun i hi => hψ1 _ (subset_convexHull ℝ _ ⟨i, hi, rfl⟩)
    have hb : ∀ i ∈ Finset.range k, -b i ≤ f 0 := fun i hi => by
      have := hle 0 i hi
      simpa using this
    rw [EReal.eq_top_iff_forall_lt]
    intro r
    have hδ : 0 < ψ v - u := by linarith
    have ht : 0 < (|r| + |f 0| + 1) / (ψ v - u) := by positivity
    have htδ : (|r| + |f 0| + 1) / (ψ v - u) * (ψ v - u) = |r| + |f 0| + 1 := by
      field_simp
    refine lt_of_lt_of_le ?_
      (hconj_ge v (((|r| + |f 0| + 1) / (ψ v - u)) • (InnerProductSpace.toDual ℝ E).symm ψ))
    rw [EReal.coe_lt_coe_iff]
    obtain ⟨j, hj, hfj⟩ := hmem (((|r| + |f 0| + 1) / (ψ v - u)) • (InnerProductSpace.toDual ℝ E).symm ψ)
    rw [hfj]
    simp only [real_inner_smul_right]
    rw [real_inner_comm, hy, real_inner_comm, hy]
    have := hsi j hj
    have := hb j hj
    have h1 : r ≤ |r| := le_abs_self r
    have h2 : f 0 ≤ |f 0| := le_abs_self _
    nlinarith
  -- Part C : lower bound via separation in E × ℝ
  have partC : ∀ v ∈ convexHull ℝ (Set.image s (Finset.range k : Set ℕ)), ∀ r : ℝ,
      (∀ α : ℕ → ℝ, (∀ i ∈ Finset.range k, 0 ≤ α i) → ∑ i ∈ Finset.range k, α i = 1 →
        ∑ i ∈ Finset.range k, α i • s i = v → r < ∑ i ∈ Finset.range k, α i * b i) →
      (r : EReal) < conjugate (liftRealtoEReal f) v := by
    intro v hv r hr
    have hAmem : ∀ w : E × ℝ, w ∈ convexHull ℝ ((fun i => (s i, b i)) '' (Finset.range k : Set ℕ)) ↔
        ∃ α : ℕ → ℝ, (∀ i ∈ Finset.range k, 0 ≤ α i) ∧ ∑ i ∈ Finset.range k, α i = 1 ∧
          ∑ i ∈ Finset.range k, α i • s i = w.1 ∧ ∑ i ∈ Finset.range k, α i * b i = w.2 := by
      intro w
      rw [aux_mem_convexHull_iff]
      constructor
      · rintro ⟨α, h0, h1, h2⟩
        refine ⟨α, h0, h1, ?_, ?_⟩
        · rw [← h2, Prod.fst_sum]
          simp
        · rw [← h2, Prod.snd_sum]
          simp
      · rintro ⟨α, h0, h1, h2, h3⟩
        refine ⟨α, h0, h1, ?_⟩
        ext
        · rw [Prod.fst_sum]
          simpa using h2
        · rw [Prod.snd_sum]
          simpa using h3
    have hnot : (v, r) ∉ convexHull ℝ ((fun i => (s i, b i)) '' (Finset.range k : Set ℕ)) := by
      intro h
      obtain ⟨α, h0, h1, h2, h3⟩ := (hAmem _).mp h
      have := hr α h0 h1 h2
      simp only at h3
      linarith
    obtain ⟨Φ, u, hΦ1, hΦ2⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _)
      ((Finset.finite_toSet _).image _).isClosed_convexHull hnot
    have hΦ : ∀ w : E, ∀ ρ : ℝ, Φ (w, ρ) = Φ (w, 0) + ρ * Φ (0, 1) := by
      intro w ρ
      have : ((w, ρ) : E × ℝ) = (w, 0) + ρ • ((0 : E), (1 : ℝ)) := by ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
    have hy : ∀ w, inner ℝ ((InnerProductSpace.toDual ℝ E).symm
        (Φ.comp (ContinuousLinearMap.inl ℝ E ℝ))) w = Φ (w, 0) := fun w => by
      rw [InnerProductSpace.toDual_symm_apply]
      rfl
    obtain ⟨α₀, h0, h1, h2⟩ := (aux_mem_convexHull_iff k s v).mp hv
    have hr0 := hr α₀ h0 h1 h2
    have hmemA : (v, ∑ i ∈ Finset.range k, α₀ i * b i) ∈
        convexHull ℝ ((fun i => (s i, b i)) '' (Finset.range k : Set ℕ)) :=
      (hAmem _).mpr ⟨α₀, h0, h1, h2, rfl⟩
    have h3 := hΦ1 _ hmemA
    rw [hΦ] at h3 hΦ2
    have hτ : Φ (0, 1) < 0 := by nlinarith
    have hc : 0 < -Φ (0, 1) := by linarith
    refine lt_of_lt_of_le ?_ (hconj_ge v ((-Φ (0, 1))⁻¹ •
      (InnerProductSpace.toDual ℝ E).symm (Φ.comp (ContinuousLinearMap.inl ℝ E ℝ))))
    rw [EReal.coe_lt_coe_iff]
    obtain ⟨j, hj, hfj⟩ := hmem ((-Φ (0, 1))⁻¹ •
      (InnerProductSpace.toDual ℝ E).symm (Φ.comp (ContinuousLinearMap.inl ℝ E ℝ)))
    rw [hfj]
    have hsj := hΦ1 _ (subset_convexHull ℝ _ ⟨j, hj, rfl⟩)
    simp only at hsj
    rw [hΦ] at hsj
    simp only [real_inner_smul_right]
    rw [real_inner_comm, hy, real_inner_comm, hy]
    have key : Φ (s j, 0) - b j * (-Φ (0, 1)) < Φ (v, 0) - r * (-Φ (0, 1)) := by linarith
    have hci : 0 < (-Φ (0, 1))⁻¹ := inv_pos.mpr hc
    have := mul_lt_mul_of_pos_left key hci
    rw [mul_sub, mul_sub, ← mul_assoc, ← mul_assoc, mul_comm _ (b j), mul_comm _ r,
      mul_assoc, mul_assoc, inv_mul_cancel₀ hc.ne', mul_one, mul_one] at this
    linarith
  refine ⟨?_, ?_⟩
  · ext v
    constructor
    · intro hv
      by_contra hv'
      have := partA v hv'
      simp only [effDom, Set.mem_setOf_eq] at hv
      rw [this] at hv
      exact lt_irrefl _ hv
    · intro hv
      obtain ⟨α, h0, h1, h2⟩ := (aux_mem_convexHull_iff k s v).mp hv
      simp only [effDom, Set.mem_setOf_eq]
      exact lt_of_le_of_lt (partB v α h0 h1 h2) (EReal.coe_lt_top _)
  · intro v hv
    apply le_antisymm
    · apply le_sInf
      rintro _ ⟨α, h0, h1, h2, rfl⟩
      exact partB v α h0 h1 h2
    · by_contra hcon
      push_neg at hcon
      obtain ⟨r, hr1, hr2⟩ := EReal.exists_between_coe_real hcon
      have := partC v hv r (fun α h0 h1 h2 => by
        have := lt_of_lt_of_le hr2 (sInf_le ⟨α, h0, h1, h2, rfl⟩)
        exact EReal.coe_lt_coe_iff.mp this)
      exact lt_asymm hr1 this

end FCA_chap_E_3_3_1
