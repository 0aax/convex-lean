import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_3_1`, so the main result is `FCA_chap_B_1_3_1.FCA_chap_B_1_3_1`.
-/

namespace FCA_chap_B_1_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem FCA_chap_B_1_3_1
  (C : Set (E × ℝ))
  (hC_nonempty : Nonempty C)
  (hC_minorized : ∀ x, IsMinorizedAt C x) :
  (Convex ℝ C → InConvRn (funFromSet C)) ∧
  (Convex ℝ C ∧ IsClosed C → InClosedConvRn (funFromSet C)) := by
  have hmin : ∀ x : E, ∃ k : ℝ, ∀ s : ℝ, (x, s) ∈ C → k ≤ s := by
    intro x
    obtain ⟨k, hk⟩ := hC_minorized x
    exact ⟨k, fun s hs => hk s ⟨(x, s), hs, rfl, rfl⟩⟩
  have hle : ∀ x : E, ∀ s : ℝ, (x, s) ∈ C → funFromSet C x ≤ (s : EReal) := by
    intro x s hs
    exact sInf_le ⟨s, hs, rfl⟩
  have hge : ∀ x : E, ∀ k : ℝ, (∀ s : ℝ, (x, s) ∈ C → k ≤ s) →
      (k : EReal) ≤ funFromSet C x := by
    intro x k hk
    apply le_sInf
    rintro _ ⟨s, hs, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hk s hs)
  have hlt : ∀ x : E, ∀ t : EReal, funFromSet C x < t →
      ∃ s : ℝ, (x, s) ∈ C ∧ (s : EReal) < t := by
    intro x t ht
    obtain ⟨_, ⟨s, hs, rfl⟩, hst⟩ := sInf_lt_iff.mp ht
    exact ⟨s, hs, hst⟩
  have hbot : ∀ x, ⊥ < funFromSet C x := by
    intro x
    obtain ⟨k, hk⟩ := hmin x
    exact lt_of_lt_of_le (EReal.bot_lt_coe k) (hge x k hk)
  obtain ⟨⟨⟨x0, r0⟩, h0⟩⟩ := hC_nonempty
  have htop : ∃ x, funFromSet C x < ⊤ :=
    ⟨x0, lt_of_le_of_lt (hle x0 r0 h0) (EReal.coe_lt_top r0)⟩
  have hconv : Convex ℝ C → InConvRn (funFromSet C) := by
    intro hC
    refine ⟨hbot, htop, ?_⟩
    intro p hp q hq a b ha hb hab
    change funFromSet C p.1 ≤ (p.2 : EReal) at hp
    change funFromSet C q.1 ≤ (q.2 : EReal) at hq
    change funFromSet C (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal)
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : a * p.2 + b * q.2 < z := by
      have := EReal.coe_lt_coe_iff.mp hz
      simpa using this
    set ε := z - (a * p.2 + b * q.2) with hε
    have hεpos : 0 < ε := by linarith
    obtain ⟨s1, hs1, hs1'⟩ := hlt p.1 ((p.2 + ε : ℝ) : EReal)
      (lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.mpr (by linarith)))
    obtain ⟨s2, hs2, hs2'⟩ := hlt q.1 ((q.2 + ε : ℝ) : EReal)
      (lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.mpr (by linarith)))
    have hs1'' : s1 < p.2 + ε := EReal.coe_lt_coe_iff.mp hs1'
    have hs2'' : s2 < q.2 + ε := EReal.coe_lt_coe_iff.mp hs2'
    have hmem := hC hs1 hs2 ha hb hab
    have hmem' : ((a • p + b • q).1, a * s1 + b * s2) ∈ C := by
      simpa using hmem
    refine le_trans (hle _ _ hmem') (EReal.coe_le_coe_iff.mpr ?_)
    have e1 : a * s1 ≤ a * (p.2 + ε) := mul_le_mul_of_nonneg_left hs1''.le ha
    have e2 : b * s2 ≤ b * (q.2 + ε) := mul_le_mul_of_nonneg_left hs2''.le hb
    have : a * (p.2 + ε) + b * (q.2 + ε) = z := by
      rw [hε]
      linear_combination (z - (a * p.2 + b * q.2)) * hab
    linarith
  refine ⟨hconv, ?_⟩
  rintro ⟨hC, hCcl⟩
  refine ⟨hconv hC, ?_⟩
  intro x y hy
  obtain ⟨r, hyr, hrx⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hx : ∀ s : ℝ, (x, s) ∈ C → r < s := by
    intro s hs
    exact EReal.coe_lt_coe_iff.mp (lt_of_lt_of_le hrx (hle x s hs))
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ᶠ x' in 𝓝 x, ∀ s : ℝ, (x', s) ∈ C → L ≤ s := by
    obtain ⟨m, hm⟩ := hmin x0
    have hm0 : m ≤ r0 := hm r0 h0
    have hopen : IsOpen {y : E | (y, m - 1) ∉ C} :=
      hCcl.isOpen_compl.preimage (continuous_id.prodMk continuous_const)
    have hx0 : x0 ∈ {y : E | (y, m - 1) ∉ C} := fun h => by linarith [hm _ h]
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen x0 hx0
    set R := dist x x0 + 1 with hR
    set a := r0 - m + 1 with ha
    refine ⟨min (m - 1) (r0 - a * R / δ), ?_⟩
    filter_upwards [Metric.ball_mem_nhds x one_pos] with x' hx'
    intro s hs
    by_contra hcon
    push_neg at hcon
    have h1 : s < m - 1 := lt_of_lt_of_le hcon (min_le_left _ _)
    have h2 : s < r0 - a * R / δ := lt_of_lt_of_le hcon (min_le_right _ _)
    have hapos : 0 < a := by linarith
    have hb : a < r0 - s := by linarith
    have hbpos : 0 < r0 - s := by linarith
    set lam := a / (r0 - s) with hlam
    have hlam0 : 0 ≤ lam := div_nonneg hapos.le hbpos.le
    have hlam1 : lam ≤ 1 := (div_le_one hbpos).mpr hb.le
    have hP := hC.add_smul_sub_mem h0 hs ⟨hlam0, hlam1⟩
    have hP2 : ((x0, r0) + lam • ((x', s) - (x0, r0)) : E × ℝ) = (x0 + lam • (x' - x0), m - 1) := by
      ext
      · simp
      · simp only [Prod.snd_add, Prod.smul_snd, Prod.snd_sub, smul_eq_mul]
        rw [hlam]
        field_simp
        ring
    rw [hP2] at hP
    apply hball _ hP
    rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hlam0]
    have hxR : ‖x' - x0‖ < R := by
      rw [← dist_eq_norm, hR]
      have := dist_triangle x' x x0
      rw [Metric.mem_ball] at hx'
      linarith
    have hlamR : lam * R < δ := by
      rw [hlam, div_mul_eq_mul_div, div_lt_iff₀ hbpos]
      have : a * R / δ < r0 - s := by linarith
      rw [div_lt_iff₀ hδ] at this
      linarith
    calc lam * ‖x' - x0‖ ≤ lam * R := mul_le_mul_of_nonneg_left hxR.le hlam0
      _ < δ := hlamR
  have htube : ∀ᶠ x' in 𝓝 x, ∀ s ∈ Set.Icc L r, (x', s) ∉ C := by
    apply (isCompact_Icc).eventually_forall_of_forall_eventually
    intro s hs
    have hns : (x, s) ∉ C := fun h => absurd hs.2 (not_le.mpr (hx s h))
    exact hCcl.isOpen_compl.mem_nhds hns
  filter_upwards [hL, htube] with x' h1 h2
  apply lt_of_lt_of_le hyr
  apply hge
  intro s hs
  by_contra hcon
  push_neg at hcon
  exact h2 s ⟨h1 s hs, hcon.le⟩ hs

end FCA_chap_B_1_3_1
