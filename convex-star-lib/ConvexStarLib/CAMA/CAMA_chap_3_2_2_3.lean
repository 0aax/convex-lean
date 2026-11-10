import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_2_2_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_2_2_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_2_2_3`, so the main result is `CAMA_chap_3_2_2_3.CAMA_chap_3_2_2_3`.
-/

namespace CAMA_chap_3_2_2_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_2_2_3
  (C : Set E)
  (hC₀ : IsClosed C)
  (hC₁ : Convex ℝ C)
  (hC₂ : Set.Nonempty C) :
  (IsCompact C) ↔ ∀ x ∈ C, (asymptoticConeAt C x) = {0} := by
  constructor
  · intro hK x hx
    ext d
    simp only [asymptoticConeAt, Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hd
      by_contra hne
      obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall 0
      have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hne
      set t : ℝ := (R + ‖x‖ + 1) / ‖d‖ with ht_def
      have hR0 : 0 ≤ R := by
        have := hR hx
        rw [Metric.mem_closedBall, _root_.dist_zero_right] at this
        exact (norm_nonneg x).trans this
      have htpos : 0 < t := by
        rw [ht_def]
        apply div_pos _ hdpos
        linarith [norm_nonneg x]
      have hmem := hR (hd t htpos)
      rw [Metric.mem_closedBall, _root_.dist_zero_right] at hmem
      have htd : ‖t • d‖ = R + ‖x‖ + 1 := by
        rw [norm_smul, Real.norm_of_nonneg htpos.le, ht_def, div_mul_cancel₀ _ hdpos.ne']
      have htri : ‖t • d‖ ≤ ‖x + t • d‖ + ‖x‖ := by
        calc ‖t • d‖ = ‖(x + t • d) - x‖ := by congr 1; abel
          _ ≤ ‖x + t • d‖ + ‖x‖ := norm_sub_le (x + t • d) x
      linarith
    · rintro rfl t _
      simpa using hx
  · intro h
    obtain ⟨x₀, hx₀⟩ := hC₂
    apply Metric.isCompact_of_isClosed_isBounded hC₀
    by_contra hnb
    rw [Metric.isBounded_iff_subset_closedBall x₀] at hnb
    push_neg at hnb
    have key : ∀ r : ℝ, ∃ y ∈ C, r < dist y x₀ := by
      intro r
      obtain ⟨y, hy, hy'⟩ := Set.not_subset.mp (hnb r)
      exact ⟨y, hy, by simpa [Metric.mem_closedBall, not_le] using hy'⟩
    have seg : ∀ (v : E) (s t : ℝ), 0 ≤ s → s ≤ t → x₀ + t • v ∈ C → x₀ + s • v ∈ C := by
      intro v s t hs hst hv
      rcases eq_or_lt_of_le (hs.trans hst) with h0 | htpos
      · have hs0 : s = 0 := le_antisymm (h0 ▸ hst) hs
        subst hs0
        simpa using hx₀
      · have hmem := hC₁.add_smul_mem hx₀ hv (t := s / t)
          ⟨div_nonneg hs htpos.le, (div_le_one htpos).mpr hst⟩
        rwa [smul_smul, div_mul_cancel₀ s htpos.ne'] at hmem
    let K : ℕ → Set E := fun n => {d | ‖d‖ = 1 ∧ x₀ + (n : ℝ) • d ∈ C}
    have hKmono : ∀ n, K (n+1) ⊆ K n := by
      rintro n d ⟨hd1, hd2⟩
      refine ⟨hd1, ?_⟩
      apply seg d (n : ℝ) ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg n) _ hd2
      push_cast
      linarith
    have hKne : ∀ n, (K n).Nonempty := by
      intro n
      obtain ⟨y, hy, hyd⟩ := key n
      have hpos : 0 < dist y x₀ := lt_of_le_of_lt (Nat.cast_nonneg n) hyd
      refine ⟨(dist y x₀)⁻¹ • (y - x₀), ?_, ?_⟩
      · rw [norm_smul, norm_inv, Real.norm_of_nonneg hpos.le, ← dist_eq_norm,
          inv_mul_cancel₀ hpos.ne']
      · have hmem := hC₁.add_smul_sub_mem hx₀ hy (t := (n : ℝ) / dist y x₀)
          ⟨div_nonneg (Nat.cast_nonneg n) hpos.le, (div_le_one hpos).mpr hyd.le⟩
        rwa [smul_smul, ← div_eq_mul_inv]
    have hK0 : IsCompact (K 0) := by
      have : K 0 = Metric.sphere 0 1 := by
        ext d
        simp [K, hx₀]
      rw [this]
      exact isCompact_sphere 0 1
    have hKcl : ∀ n, IsClosed (K n) := by
      intro n
      apply IsClosed.inter
      · exact isClosed_eq continuous_norm continuous_const
      · exact hC₀.preimage (continuous_const.add (continuous_const.smul continuous_id))
    obtain ⟨d, hd⟩ :=
      IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed K hKmono hKne hK0 hKcl
    rw [Set.mem_iInter] at hd
    have hd1 : ‖d‖ = 1 := (hd 0).1
    have hdC : d ∈ asymptoticConeAt C x₀ := by
      intro t ht
      obtain ⟨n, hn⟩ := exists_nat_ge t
      exact seg d t n ht.le hn (hd n).2
    rw [h x₀ hx₀, Set.mem_singleton_iff] at hdC
    rw [hdC, norm_zero] at hd1
    exact zero_ne_one hd1

end CAMA_chap_3_2_2_3
