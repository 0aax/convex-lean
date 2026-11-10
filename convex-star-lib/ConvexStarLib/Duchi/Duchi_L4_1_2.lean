import ConvexStarLib.Defs

/-!
# `Duchi_L4_1_2`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_L4_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_L4_1_2`, so the main result is `Duchi_L4_1_2.Duchi_L4_1_2`.
-/

namespace Duchi_L4_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Duchi_L4_1_2 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K)
  (hKint : Set.Nonempty (interior K)) :
  (∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0) ∧
  (dualCone K ∩ (Neg.neg '' dualCone K) = {0}) ∧
  (Convex ℝ (interior K) ∧ IsCone (interior K)) ∧
  (∀ (x₀ x₁ : EuclideanSpace ℝ (Fin n)),
    Set.Nonempty ({z | ∃ k ∈ interior K, z = x₀ + k} ∩
      {z | ∃ k ∈ interior K, z = x₁ + k})) := by
  -- Part 1: a dual vector vanishing at an interior point is zero
  have h1 : ∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0 := by
    intro u hu l hl
    constructor
    · intro hlu
      obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
      by_contra hl0
      have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
      have htpos : 0 < ε / (2 * ‖l‖) := by positivity
      have hmem : u - (ε / (2 * ‖l‖)) • l ∈ K := by
        apply interior_subset
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_pos htpos]
        rw [div_mul_eq_mul_div, mul_div_assoc, mul_comm 2 ‖l‖, ← div_div, div_self hlpos.ne']
        linarith
      have key := hl (u - (ε / (2 * ‖l‖)) • l) hmem
      rw [inner_sub_right, real_inner_smul_right, hlu, real_inner_self_eq_norm_sq] at key
      have : 0 < ε / (2 * ‖l‖) * ‖l‖ ^ 2 := by positivity
      linarith
    · rintro rfl
      simp
  -- Part 2: the dual cone is pointed
  have h2 : dualCone K ∩ (Neg.neg '' dualCone K) = {0} := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hz, w, hw, rfl⟩
      obtain ⟨u, hu⟩ := hKint
      have hwu : inner ℝ w u = 0 := by
        have a := hw u (interior_subset hu)
        have b := hz u (interior_subset hu)
        rw [inner_neg_left] at b
        linarith
      rw [(h1 u hu w hw).mp hwu, neg_zero]
    · rintro rfl
      refine ⟨?_, 0, ?_, neg_zero⟩
      · intro x _
        simp
      · intro x _
        simp
  -- Part 3: the interior is a convex cone
  have h3 : Convex ℝ (interior K) ∧ IsCone (interior K) := by
    refine ⟨hK_convex.interior, ?_⟩
    intro x hx s hs
    have hsK : s • K ⊆ K := by
      rintro _ ⟨y, hy, rfl⟩
      exact hK_cone y hy s hs
    have : s • x ∈ interior (s • K) := by
      rw [interior_smul₀ hs.ne']
      exact Set.smul_mem_smul_set hx
    exact interior_mono hsK this
  -- Part 4: any two translates of the interior intersect
  have h4 : ∀ (x₀ x₁ : EuclideanSpace ℝ (Fin n)),
      Set.Nonempty ({z | ∃ k ∈ interior K, z = x₀ + k} ∩
        {z | ∃ k ∈ interior K, z = x₁ + k}) := by
    intro x₀ x₁
    obtain ⟨u, hu⟩ := hKint
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
    have htpos : 0 < ‖x₁ - x₀‖ / ε + 1 := by positivity
    have hmem : u + (‖x₁ - x₀‖ / ε + 1)⁻¹ • (x₁ - x₀) ∈ interior K := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos htpos, inv_mul_lt_iff₀ htpos]
      have : ‖x₁ - x₀‖ / ε * ε = ‖x₁ - x₀‖ := div_mul_cancel₀ _ hε.ne'
      nlinarith
    refine ⟨x₁ + (‖x₁ - x₀‖ / ε + 1) • u,
      ⟨(‖x₁ - x₀‖ / ε + 1) • (u + (‖x₁ - x₀‖ / ε + 1)⁻¹ • (x₁ - x₀)),
        h3.2 _ hmem _ htpos, ?_⟩,
      ⟨(‖x₁ - x₀‖ / ε + 1) • u, h3.2 _ hu _ htpos, rfl⟩⟩
    rw [smul_add, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
    abel
  exact ⟨h1, h2, h3, h4⟩

end Duchi_L4_1_2
