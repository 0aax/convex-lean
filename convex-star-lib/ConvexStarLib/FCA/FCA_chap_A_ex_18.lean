import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_18`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_18` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_18`, so the main result is `FCA_chap_A_ex_18.FCA_chap_A_ex_18`.
-/

namespace FCA_chap_A_ex_18

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_A_ex_18 :
  (∀ (C : Set E) (A : E →L[ℝ] F),
    C.Nonempty → IsClosed C → Convex ℝ C →
    (∀ x₀ ∈ C, asymptoticConeAt C x₀ ∩ (LinearMap.ker A.toLinearMap : Set _) = {0}) →
    IsClosed (A '' C)) ∧
  (∀ (C : Set E) (V : Submodule ℝ E) [CompleteSpace V],
    C.Nonempty → IsClosed C → Convex ℝ C →
    (∀ x₀ ∈ C, asymptoticConeAt C x₀ ∩ (V.orthogonal : Set _) = {0}) →
    IsClosed ((fun x ↦ (V.orthogonalProjection x : E)) '' C)) := by
  -- Core statement, for continuous linear maps into `E × F` (so that it covers both parts).
  have core : ∀ (C : Set E) (A : E →L[ℝ] (E × F)) (x₀ : E), x₀ ∈ C → IsClosed C →
      Convex ℝ C → asymptoticConeAt C x₀ ∩ (LinearMap.ker A.toLinearMap : Set E) = {0} →
      IsClosed (A '' C) := by
    intro C A x₀ hx₀ hC hconv h
    -- The part of `C` mapped into a closed ball is bounded.
    have key : ∀ y : E × F, Bornology.IsBounded (C ∩ A ⁻¹' Metric.closedBall y 1) := by
      intro y
      by_contra hb
      rw [isBounded_iff_forall_norm_le] at hb
      push_neg at hb
      choose x hxS hxn using fun n : ℕ => hb n
      have hpos : ∀ n, 0 < ‖x n‖ := fun n => lt_of_le_of_lt (Nat.cast_nonneg n) (hxn n)
      set u : ℕ → E := fun n => ‖x n‖⁻¹ • x n with hu
      have hu_mem : ∀ n, u n ∈ Metric.sphere (0:E) 1 := by
        intro n
        simp [u, norm_smul, (hpos n).ne']
      obtain ⟨d, hd, ns, hns, hlim⟩ := (isCompact_sphere (0:E) 1).tendsto_subseq hu_mem
      have hnorm_top : Filter.Tendsto (fun n => ‖x n‖) Filter.atTop Filter.atTop :=
        Filter.tendsto_atTop_mono (fun n => (hxn n).le) tendsto_natCast_atTop_atTop
      have hinv : Filter.Tendsto (fun n => ‖x n‖⁻¹) Filter.atTop (𝓝 0) :=
        hnorm_top.inv_tendsto_atTop
      -- The limit direction lies in the kernel of `A`.
      have hAd : A d = 0 := by
        have h1 : Filter.Tendsto (fun n => A (u (ns n))) Filter.atTop (𝓝 (A d)) :=
          (A.continuous.tendsto d).comp hlim
        have hbdd : ∀ n, ‖A (x n)‖ ≤ ‖y‖ + 1 := by
          intro n
          have := (hxS n).2
          simp only [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm] at this
          calc ‖A (x n)‖ = ‖(A (x n) - y) + y‖ := by rw [sub_add_cancel]
            _ ≤ ‖A (x n) - y‖ + ‖y‖ := norm_add_le _ _
            _ ≤ ‖y‖ + 1 := by linarith
        have h2 : Filter.Tendsto (fun n => A (u n)) Filter.atTop (𝓝 0) := by
          rw [tendsto_zero_iff_norm_tendsto_zero]
          refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
            (by simpa using hinv.mul_const (‖y‖ + 1))
          simp only [u, map_smul, norm_smul, norm_inv, norm_norm]
          exact mul_le_mul_of_nonneg_left (hbdd n) (inv_nonneg.mpr (norm_nonneg _))
        exact tendsto_nhds_unique h1 (h2.comp hns.tendsto_atTop)
      -- The limit direction lies in the asymptotic cone at `x₀`.
      have hdC : d ∈ asymptoticConeAt C x₀ := by
        intro t ht
        have hz : Filter.Tendsto (fun n => x₀ + t • (u (ns n) - ‖x (ns n)‖⁻¹ • x₀))
            Filter.atTop (𝓝 (x₀ + t • d)) := by
          have h3 : Filter.Tendsto (fun n => ‖x (ns n)‖⁻¹ • x₀) Filter.atTop (𝓝 (0:E)) := by
            have := (hinv.comp hns.tendsto_atTop).smul_const x₀
            simpa using this
          have := ((hlim.sub h3).const_smul t).const_add x₀
          simpa using this
        refine hC.mem_of_tendsto hz ?_
        have hev : ∀ᶠ n in Filter.atTop, t ≤ ‖x (ns n)‖ :=
          (hnorm_top.comp hns.tendsto_atTop).eventually_ge_atTop t
        filter_upwards [hev] with n hn
        have hpn := hpos (ns n)
        have key2 : x₀ + t • (u (ns n) - ‖x (ns n)‖⁻¹ • x₀)
            = (1 - t * ‖x (ns n)‖⁻¹) • x₀ + (t * ‖x (ns n)‖⁻¹) • x (ns n) := by
          simp only [u, smul_sub, smul_smul, sub_smul, one_smul]
          abel
        rw [key2]
        apply hconv hx₀ (hxS (ns n)).1
        · have : t * ‖x (ns n)‖⁻¹ ≤ 1 := by
            rw [← div_eq_mul_inv, div_le_one hpn]; exact hn
          linarith
        · positivity
        · ring
      have hd0 : d ∈ asymptoticConeAt C x₀ ∩ (LinearMap.ker A.toLinearMap : Set E) :=
        ⟨hdC, by simpa using hAd⟩
      rw [h] at hd0
      have hd00 : d = 0 := hd0
      rw [hd00] at hd
      simp at hd
    -- Closedness of the image.
    rw [← closure_subset_iff_isClosed]
    intro y hy
    set S := C ∩ A ⁻¹' Metric.closedBall y 1 with hS
    have hSc : IsCompact S := Metric.isCompact_of_isClosed_isBounded
      (hC.inter (Metric.isClosed_closedBall.preimage A.continuous)) (key y)
    have hAS : IsClosed (A '' S) := (hSc.image A.continuous).isClosed
    have hyS : y ∈ closure (A '' S) := by
      rw [Metric.mem_closure_iff] at hy ⊢
      intro ε hε
      obtain ⟨b, ⟨x, hxC, rfl⟩, hb⟩ := hy (min ε 1) (lt_min hε one_pos)
      refine ⟨A x, ⟨x, ⟨hxC, ?_⟩, rfl⟩, lt_of_lt_of_le hb (min_le_left _ _)⟩
      simp only [Set.mem_preimage, Metric.mem_closedBall]
      rw [_root_.dist_comm]
      exact le_of_lt (lt_of_lt_of_le hb (min_le_right _ _))
    rw [hAS.closure_eq] at hyS
    exact Set.image_mono Set.inter_subset_left hyS
  constructor
  · intro C A hne hC hconv h
    obtain ⟨x₀, hx₀⟩ := hne
    set A' : E →L[ℝ] (E × F) := (0 : E →L[ℝ] E).prod A with hA'
    have hker : (LinearMap.ker A'.toLinearMap : Set E) = (LinearMap.ker A.toLinearMap : Set E) := by
      ext x
      simp [A']
    have hcl := core C A' x₀ hx₀ hC hconv (by rw [hker]; exact h x₀ hx₀)
    have himg : A '' C = (fun y : F => ((0 : E), y)) ⁻¹' (A' '' C) := by
      ext y
      simp [A']
    rw [himg]
    exact hcl.preimage (Continuous.prodMk_right (0 : E))
  · intro C V _ hne hC hconv h
    obtain ⟨x₀, hx₀⟩ := hne
    set A' : E →L[ℝ] (E × F) := V.starProjection.prod 0 with hA'
    have hker : (LinearMap.ker A'.toLinearMap : Set E) = (V.orthogonal : Set E) := by
      ext x
      simp [A']
    have hcl := core C A' x₀ hx₀ hC hconv (by rw [hker]; exact h x₀ hx₀)
    have himg : (fun x ↦ (V.orthogonalProjection x : E)) '' C
        = (fun y : E => (y, (0 : F))) ⁻¹' (A' '' C) := by
      ext y
      simp [A']
    rw [himg]
    exact hcl.preimage (Continuous.prodMk_left (0 : F))

end FCA_chap_A_ex_18
