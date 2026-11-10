import ConvexStarLib.Defs

/-!
# `Duchi_L4_1_3`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_L4_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_L4_1_3`, so the main result is `Duchi_L4_1_3.Duchi_L4_1_3`.
-/

namespace Duchi_L4_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem Duchi_L4_1_3 {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K)
  (hK_nonempty : K.Nonempty) :
  (∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0) ∧
  (closure K = dualCone (dualCone K)) ∧
  (IsClosed K → K = dualCone (dualCone K)) ∧
  ((∃ l ∈ dualCone K, ‖l‖ = 1) →
    (∀ u, gammaMin K u ≥ 0 ↔ u ∈ closure K)) ∧
  ((Set.Nonempty (interior K) ∧ ∃ l ∈ dualCone K, ‖l‖ = 1) →
    ∀ u, gammaMin K u > 0 ↔ u ∈ interior K) := by
  -- Part 1
  have part1 : ∀ u ∈ interior K, ∀ l ∈ dualCone K, inner ℝ l u = 0 ↔ l = 0 := by
    intro u hu l hl
    constructor
    · intro h
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hu
      obtain ⟨ε, hε, hball⟩ := hu
      by_contra hl0
      have hlpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
      set t := ε / (2 * ‖l‖) with ht
      have htpos : 0 < t := by positivity
      have hmem : u - t • l ∈ K := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm]
        have : u - t • l - u = -(t • l) := by abel
        rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos htpos, ht]
        field_simp
        linarith
      have h2 := hl (u - t • l) hmem
      rw [inner_sub_right, real_inner_smul_right, h, real_inner_self_eq_norm_sq] at h2
      have : 0 < t * ‖l‖ ^ 2 := by positivity
      linarith
    · rintro rfl
      simp
  -- additivity of K
  have hK_add : ∀ x ∈ K, ∀ y ∈ K, x + y ∈ K := by
    intro x hx y hy
    have h1 := hK_convex hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have h2 := hK_cone _ h1 2 (by norm_num)
    convert h2 using 1
    rw [smul_add, smul_smul, smul_smul]
    norm_num
  let C : ConvexCone ℝ (EuclideanSpace ℝ (Fin n)) :=
    { carrier := K
      smul_mem' := fun c hc x hx => hK_cone x hx c hc
      add_mem' := fun x hx y hy => hK_add x hx y hy }
  have hsub : K ⊆ dualCone (dualCone K) := by
    intro x hx l hl
    rw [real_inner_comm]
    exact hl x hx
  have hclosed_dd : IsClosed (dualCone (dualCone K)) := by
    have : dualCone (dualCone K) = ⋂ l ∈ dualCone K, {s | inner ℝ s l ≥ 0} := by
      ext s; simp [dualCone]
    rw [this]
    apply isClosed_biInter
    intro l _
    exact isClosed_le continuous_const (continuous_id.inner continuous_const)
  have part2 : closure K = dualCone (dualCone K) := by
    apply Set.Subset.antisymm
    · exact closure_minimal hsub hclosed_dd
    · intro b hb
      by_contra hbn
      obtain ⟨y, hy, hyb⟩ := ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem
        C.closure hK_nonempty.closure isClosed_closure hbn
      have hyd : y ∈ dualCone K := by
        intro x hx
        rw [real_inner_comm]
        exact hy x (subset_closure hx)
      have := hb y hyd
      rw [real_inner_comm] at this
      linarith
  have part3 : IsClosed K → K = dualCone (dualCone K) := by
    intro h
    rw [← part2, h.closure_eq]
  -- gammaMin facts
  have hbdd : ∀ u, BddBelow {v | ∃ l ∈ dualCone K, ‖l‖ = 1 ∧ v = inner ℝ l u} := by
    intro u
    refine ⟨-‖u‖, ?_⟩
    rintro v ⟨l, hl, hl1, rfl⟩
    have h := abs_real_inner_le_norm l u
    rw [hl1, one_mul] at h
    linarith [neg_abs_le (inner ℝ l u)]
  have hgamma_le : ∀ u, ∀ l ∈ dualCone K, ‖l‖ = 1 → gammaMin K u ≤ inner ℝ l u := by
    intro u l hl hl1
    exact csInf_le (hbdd u) ⟨l, hl, hl1, rfl⟩
  have hgamma_ge : ∀ u (c : ℝ), (∃ l ∈ dualCone K, ‖l‖ = 1) →
      (∀ l ∈ dualCone K, ‖l‖ = 1 → c ≤ inner ℝ l u) → c ≤ gammaMin K u := by
    rintro u c ⟨l₀, hl₀, hl₀1⟩ h
    unfold gammaMin
    refine le_csInf ⟨inner ℝ l₀ u, l₀, hl₀, hl₀1, rfl⟩ ?_
    rintro v ⟨l, hl, hl1, rfl⟩
    exact h l hl hl1
  have hnormalize : ∀ l ∈ dualCone K, l ≠ 0 →
      (‖l‖⁻¹ • l) ∈ dualCone K ∧ ‖‖l‖⁻¹ • l‖ = 1 := by
    intro l hl hl0
    constructor
    · intro x hx
      rw [real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.mpr (norm_nonneg _)) (hl x hx)
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hl0)]
  have part4 : (∃ l ∈ dualCone K, ‖l‖ = 1) → ∀ u, gammaMin K u ≥ 0 ↔ u ∈ closure K := by
    intro hex u
    rw [part2]
    constructor
    · intro hg l hl
      by_cases hl0 : l = 0
      · rw [hl0, inner_zero_right]
      · obtain ⟨h1, h2⟩ := hnormalize l hl hl0
        have h3 := hgamma_le u _ h1 h2
        rw [real_inner_smul_left] at h3
        have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
        rw [real_inner_comm]
        have h4 : 0 ≤ ‖l‖⁻¹ * inner ℝ l u := le_trans hg h3
        exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hpos)).mp h4
    · intro hu
      apply hgamma_ge u 0 hex
      intro l hl _
      rw [real_inner_comm]
      exact hu l hl
  have part5 : (Set.Nonempty (interior K) ∧ ∃ l ∈ dualCone K, ‖l‖ = 1) →
      ∀ u, gammaMin K u > 0 ↔ u ∈ interior K := by
    rintro ⟨hint, hex⟩ u
    constructor
    · intro hg
      have hball : Metric.ball u (gammaMin K u) ⊆ closure K := by
        intro w hw
        rw [part2]
        intro l hl
        by_cases hl0 : l = 0
        · rw [hl0, inner_zero_right]
        · obtain ⟨h1, h2⟩ := hnormalize l hl hl0
          have h3 := hgamma_le u _ h1 h2
          have h4 : inner ℝ (‖l‖⁻¹ • l) (w - u) ≥ -‖w - u‖ := by
            have := abs_real_inner_le_norm (‖l‖⁻¹ • l) (w - u)
            rw [h2, one_mul] at this
            linarith [neg_abs_le (inner ℝ (‖l‖⁻¹ • l) (w - u))]
          have h5 : ‖w - u‖ < gammaMin K u := by rwa [Metric.mem_ball, dist_eq_norm] at hw
          have h6 : inner ℝ (‖l‖⁻¹ • l) w =
              inner ℝ (‖l‖⁻¹ • l) u + inner ℝ (‖l‖⁻¹ • l) (w - u) := by
            rw [← inner_add_right]; congr 1; abel
          have h7 : 0 ≤ inner ℝ (‖l‖⁻¹ • l) w := by linarith
          rw [real_inner_smul_left] at h7
          have hpos : 0 < ‖l‖ := norm_pos_iff.mpr hl0
          rw [real_inner_comm]
          exact (mul_nonneg_iff_of_pos_left (inv_pos.mpr hpos)).mp h7
      have hu_int_cl : u ∈ interior (closure K) := by
        rw [mem_interior]
        exact ⟨Metric.ball u (gammaMin K u), hball, Metric.isOpen_ball, Metric.mem_ball_self hg⟩
      rwa [hK_convex.interior_closure_eq_interior_of_nonempty_interior hint] at hu_int_cl
    · intro hu
      obtain ⟨ε, hε, hballK⟩ := Metric.isOpen_iff.mp isOpen_interior u hu
      apply lt_of_lt_of_le (half_pos hε)
      apply hgamma_ge u (ε/2) hex
      intro l hl hl1
      have hmem : u - (ε/2) • l ∈ K := by
        apply interior_subset
        apply hballK
        rw [Metric.mem_ball, dist_eq_norm]
        have : u - (ε/2) • l - u = -((ε/2) • l) := by abel
        rw [this, norm_neg, norm_smul, Real.norm_eq_abs, abs_of_pos (half_pos hε), hl1]
        linarith
      have h2 := hl _ hmem
      rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hl1] at h2
      linarith
  exact ⟨part1, part2, part3, part4, part5⟩

end Duchi_L4_1_3
