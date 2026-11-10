import ConvexStarLib.Defs

/-!
# `BC_chap_6_30`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_6_30` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_6_30`, so the main result is `BC_chap_6_30.BC_chap_6_30`.
-/

namespace BC_chap_6_30

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem BC_chap_6_30
  (K : Set E) (x : E)
  (hK_nonempty : Set.Nonempty K)
  (hK_closed : IsClosed K)
  (hK_convex : Convex ℝ K)
  (hK_cone : IsCone K) :
  ∃ (a b : E),
    ((a ∈ K) ∧ (b ∈ polarCone K) ∧ (x = a + b)) ∧
    (inner ℝ a b = 0) ∧
    (‖x‖ ^ 2 = (Metric.infDist x K) ^ 2 + (Metric.infDist x (polarCone K)) ^ 2) := by
  -- `a` is the metric projection of `x` onto `K`
  obtain ⟨a, ha, hmin⟩ :=
    exists_norm_eq_iInf_of_complete_convex hK_nonempty hK_closed.isComplete hK_convex x
  have hvar : ∀ w ∈ K, inner ℝ (x - a) (w - a) ≤ 0 :=
    (norm_eq_iInf_iff_real_inner_le_zero hK_convex ha).1 hmin
  -- test the variational inequality at `2 • a` and `(1/2) • a` to get `⟪x - a, a⟫ = 0`
  have h1 := hvar _ (hK_cone a ha 2 (by norm_num))
  have h2 := hvar _ (hK_cone a ha (1 / 2) (by norm_num))
  have e1 : (2 : ℝ) • a - a = a := by rw [two_smul]; abel
  have e2 : (1 / 2 : ℝ) • a - a = (-1 / 2 : ℝ) • a := by
    rw [show (-1 / 2 : ℝ) = 1 / 2 - 1 by norm_num, sub_smul, one_smul]
  rw [e1] at h1
  rw [e2, real_inner_smul_right] at h2
  have horth : inner ℝ (x - a) a = 0 := by linarith
  obtain ⟨b, hb_def⟩ : ∃ b, b = x - a := ⟨_, rfl⟩
  rw [← hb_def] at hvar horth
  have hx : x = a + b := by rw [hb_def]; abel
  have hb : b ∈ polarCone K := by
    intro y hy
    have := hvar y hy
    rw [inner_sub_right, horth] at this
    linarith
  refine ⟨a, b, ⟨ha, hb, hx⟩, by rw [real_inner_comm]; exact horth, ?_⟩
  have hdK : Metric.infDist x K = ‖b‖ := by
    apply le_antisymm
    · have := Metric.infDist_le_dist_of_mem (x := x) ha
      rwa [dist_eq_norm, ← hb_def] at this
    · rw [Metric.le_infDist hK_nonempty]
      intro y hy
      rw [dist_eq_norm]
      have hy' := hvar y hy
      have key : ‖x - y‖ ^ 2 = ‖b‖ ^ 2 - 2 * inner ℝ b (y - a) + ‖y - a‖ ^ 2 := by
        rw [← norm_sub_sq_real, show x - y = b - (y - a) by rw [hx]; abel]
      have hsq : ‖b‖ ^ 2 ≤ ‖x - y‖ ^ 2 := by nlinarith [sq_nonneg ‖y - a‖]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  have hdP : Metric.infDist x (polarCone K) = ‖a‖ := by
    apply le_antisymm
    · have := Metric.infDist_le_dist_of_mem (x := x) hb
      have e : x - b = a := by rw [hx]; abel
      rwa [dist_eq_norm, e] at this
    · rw [Metric.le_infDist ⟨b, hb⟩]
      intro z hz
      rw [dist_eq_norm]
      have hza : inner ℝ z a ≤ 0 := hz a ha
      have key : ‖x - z‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a (b - z) + ‖b - z‖ ^ 2 := by
        rw [← norm_add_sq_real, show x - z = a + (b - z) by rw [hx]; abel]
      have hab : inner ℝ a (b - z) = - inner ℝ z a := by
        rw [inner_sub_right, real_inner_comm b a, horth, real_inner_comm a z]; ring
      have hsq : ‖a‖ ^ 2 ≤ ‖x - z‖ ^ 2 := by
        rw [key, hab]; nlinarith [sq_nonneg ‖b - z‖]
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hsq
  rw [hdK, hdP, hx, norm_add_sq_real, real_inner_comm, horth]
  ring

end BC_chap_6_30
