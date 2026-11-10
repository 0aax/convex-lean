import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_14`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_14` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_14`, so the main result is `FCA_chap_A_ex_14.FCA_chap_A_ex_14`.
-/

namespace FCA_chap_A_ex_14

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FCA_chap_A_ex_14 (C : ℕ → Set E) (h_closed : ∀ k, IsClosed (C k))
    (h_convex : ∀ k, Convex ℝ (C k)) (h_anti : Antitone C)
    (h_ne : Set.Nonempty (⋂ k, C k)) :
    let Cinf := ⋂ k, C k
    (∀ x : E,
      Filter.Tendsto
        (fun k ↦ pC x (C k) (h_closed k) (h_convex k)
          (h_ne.mono (Set.iInter_subset C k)))
        Filter.atTop
        (𝓝 (pC x Cinf (isClosed_iInter fun k ↦ h_closed k)
          (convex_iInter fun k ↦ h_convex k) h_ne))) ∧
    (∀ x : E,
      Monotone (fun k ↦ Metric.infDist x (C k)) ∧
      Filter.Tendsto (fun k ↦ Metric.infDist x (C k))
        Filter.atTop (𝓝 (Metric.infDist x Cinf))) := by
  intro Cinf
  -- the defining property of `pC`
  have spec : ∀ (x : E) (D : Set E) (h₁ : IsClosed D) (h₂ : Convex ℝ D) (h₃ : D.Nonempty),
      pC x D h₁ h₂ h₃ ∈ D ∧ ‖x - pC x D h₁ h₂ h₃‖ = ⨅ w : D, ‖x - w‖ := fun x D h₁ h₂ h₃ =>
    Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex h₃ h₁.isComplete h₂ x)
  -- `pC` is at minimal distance
  have le_dist : ∀ (x : E) (D : Set E) (h₁ : IsClosed D) (h₂ : Convex ℝ D) (h₃ : D.Nonempty)
      (w : E), w ∈ D → ‖x - pC x D h₁ h₂ h₃‖ ≤ ‖x - w‖ := by
    intro x D h₁ h₂ h₃ w hw
    rw [(spec x D h₁ h₂ h₃).2]
    exact ciInf_le ⟨0, Set.forall_mem_range.2 fun _ => norm_nonneg _⟩ (⟨w, hw⟩ : D)
  -- the distance to `D` is the distance to `pC`
  have infDist_eq : ∀ (x : E) (D : Set E) (h₁ : IsClosed D) (h₂ : Convex ℝ D) (h₃ : D.Nonempty),
      Metric.infDist x D = ‖x - pC x D h₁ h₂ h₃‖ := by
    intro x D h₁ h₂ h₃
    rw [(spec x D h₁ h₂ h₃).2, Metric.infDist_eq_iInf]
    simp only [dist_eq_norm]
  -- uniqueness of the minimizer
  have uniq : ∀ (x : E) (D : Set E) (h₁ : IsClosed D) (h₂ : Convex ℝ D) (h₃ : D.Nonempty)
      (q : E), q ∈ D → ‖x - q‖ ≤ ‖x - pC x D h₁ h₂ h₃‖ → q = pC x D h₁ h₂ h₃ := by
    intro x D h₁ h₂ h₃ q hq hle
    have hpD := (spec x D h₁ h₂ h₃).1
    have hpmin := (spec x D h₁ h₂ h₃).2
    set p := pC x D h₁ h₂ h₃ with hp_def
    have hqmin : ‖x - q‖ = ⨅ w : D, ‖x - w‖ := by
      rw [← hpmin]
      exact le_antisymm hle (le_dist x D h₁ h₂ h₃ q hq)
    have h1 := (norm_eq_iInf_iff_real_inner_le_zero h₂ hpD).1 hpmin q hq
    have h2 := (norm_eq_iInf_iff_real_inner_le_zero h₂ hq).1 hqmin p hpD
    have e : inner ℝ (q - p) (q - p) = inner ℝ (x - p) (q - p) + inner ℝ (x - q) (p - q) := by
      simp only [inner_sub_left, inner_sub_right, real_inner_comm p q]
      ring
    have : inner ℝ (q - p) (q - p) ≤ 0 := by linarith
    exact sub_eq_zero.1 (real_inner_self_nonpos.1 this)
  have part1 : ∀ x : E,
      Filter.Tendsto
        (fun k ↦ pC x (C k) (h_closed k) (h_convex k)
          (h_ne.mono (Set.iInter_subset C k)))
        Filter.atTop
        (𝓝 (pC x Cinf (isClosed_iInter fun k ↦ h_closed k)
          (convex_iInter fun k ↦ h_convex k) h_ne)) := by
    intro x
    have hpC := (spec x Cinf (isClosed_iInter fun k ↦ h_closed k)
          (convex_iInter fun k ↦ h_convex k) h_ne).1
    set p := pC x Cinf (isClosed_iInter fun k ↦ h_closed k)
          (convex_iInter fun k ↦ h_convex k) h_ne with hp
    have hbound : ∀ k, pC x (C k) (h_closed k) (h_convex k) (h_ne.mono (Set.iInter_subset C k))
        ∈ Metric.closedBall x ‖x - p‖ := by
      intro k
      rw [Metric.mem_closedBall, _root_.dist_comm, dist_eq_norm]
      exact le_dist _ _ _ _ _ p (Set.iInter_subset C k hpC)
    apply (isCompact_closedBall x ‖x - p‖).tendsto_nhds_of_unique_mapClusterPt
      (Filter.Eventually.of_forall hbound)
    intro q hq hcl
    have hqC : q ∈ Cinf := by
      refine Set.mem_iInter.2 fun m => ?_
      apply (h_closed m).mem_of_mapClusterPt hcl
      rw [Filter.eventually_atTop]
      exact ⟨m, fun k hk => h_anti hk (spec _ _ _ _ _).1⟩
    apply uniq x Cinf _ _ _ q hqC
    rw [Metric.mem_closedBall, _root_.dist_comm, dist_eq_norm] at hq
    exact hq
  refine ⟨part1, fun x => ⟨?_, ?_⟩⟩
  · intro a b hab
    exact Metric.infDist_le_infDist_of_subset (h_anti hab) (h_ne.mono (Set.iInter_subset C b))
  · have h2 := (tendsto_const_nhds (x := x)).sub (part1 x) |>.norm
    rw [infDist_eq x Cinf (isClosed_iInter fun k ↦ h_closed k) (convex_iInter fun k ↦ h_convex k) h_ne]
    exact h2.congr fun k => (infDist_eq _ _ _ _ _).symm

end FCA_chap_A_ex_14
