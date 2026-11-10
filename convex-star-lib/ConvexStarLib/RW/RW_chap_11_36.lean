import ConvexStarLib.Defs

/-!
# `RW_chap_11_36`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_36` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_36`, so the main result is `RW_chap_11_36.RW_chap_11_36`.
-/

namespace RW_chap_11_36

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma RW36_dist_le {A : Set E} {x a : E} (ha : a ∈ A) :
    distToSetEReal x A ≤ ((‖x - a‖ : ℝ) : EReal) :=
  sInf_le ⟨a, ha, rfl⟩

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma RW36_le_dist {A : Set E} {x : E} {c : ℝ} (h : ∀ a ∈ A, c ≤ ‖x - a‖) :
    ((c : ℝ) : EReal) ≤ distToSetEReal x A := by
  apply le_sInf
  rintro _ ⟨a, ha, rfl⟩
  exact EReal.coe_le_coe_iff.2 (h a ha)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma RW36_dist_self {A : Set E} {x : E} (hx : x ∈ A) :
    distToSetEReal x A = ((0 : ℝ) : EReal) := by
  apply le_antisymm
  · simpa using RW36_dist_le (x := x) hx
  · exact RW36_le_dist (fun a _ => norm_nonneg _)

omit [FiniteDimensional ℝ E] in
lemma RW36_polar_zero (K : Set E) : (0 : E) ∈ polarCone K := by
  intro x _
  simp

omit [FiniteDimensional ℝ E] in
lemma RW36_polar_smul {K : Set E} {s : E} (hs : s ∈ polarCone K) {t : ℝ} (ht : 0 ≤ t) :
    t • s ∈ polarCone K := by
  intro x hx
  rw [real_inner_smul_left]
  exact mul_nonpos_of_nonneg_of_nonpos ht (hs x hx)

lemma RW36_moreau {K : Set E} (hc : IsClosed K) (hcone : IsPointedCone K) (hconv : Convex ℝ K)
    (x : E) : ∃ p ∈ K, x - p ∈ polarCone K ∧ inner ℝ (x - p) p = 0 := by
  obtain ⟨p, hpK, hp⟩ :=
    exists_norm_eq_iInf_of_complete_convex ⟨0, hcone.1⟩ hc.isComplete hconv x
  have hvi := (norm_eq_iInf_iff_real_inner_le_zero hconv hpK).1 hp
  have h1 := hvi 0 hcone.1
  have h2 := hvi ((2 : ℝ) • p) (hcone.2 p hpK 2 (by norm_num))
  rw [zero_sub, inner_neg_right] at h1
  rw [two_smul, add_sub_cancel_right] at h2
  have h0 : inner ℝ (x - p) p = 0 := by linarith
  refine ⟨p, hpK, ?_, h0⟩
  intro y hy
  have := hvi y hy
  rw [inner_sub_right] at this
  linarith

omit [FiniteDimensional ℝ E] in
lemma RW36_moreau_norm {x p : E} (h0 : inner ℝ (x - p) p = 0) :
    ‖x‖ ^ 2 = ‖p‖ ^ 2 + ‖x - p‖ ^ 2 := by
  have h := norm_add_sq_real p (x - p)
  rw [add_sub_cancel] at h
  rw [h, real_inner_comm, h0]
  ring

omit [FiniteDimensional ℝ E] in
lemma RW36_moreau_dist {K : Set E} {x p : E} (hp : p ∈ K) (hq : x - p ∈ polarCone K)
    (h0 : inner ℝ (x - p) p = 0) :
    distToSetEReal x K = ((‖x - p‖ : ℝ) : EReal) ∧
      distToSetEReal x (polarCone K) = ((‖p‖ : ℝ) : EReal) := by
  constructor
  · apply le_antisymm (RW36_dist_le hp)
    apply RW36_le_dist
    intro a ha
    have h1 : inner ℝ (x - p) a ≤ 0 := hq a ha
    have h2 : ‖x - a‖ ^ 2 = ‖x - p‖ ^ 2 + 2 * inner ℝ (x - p) (p - a) + ‖p - a‖ ^ 2 := by
      rw [← norm_add_sq_real, sub_add_sub_cancel]
    have h3 : inner ℝ (x - p) (p - a) = inner ℝ (x - p) p - inner ℝ (x - p) a :=
      inner_sub_right _ _ _
    have h4 : ‖x - p‖ ^ 2 ≤ ‖x - a‖ ^ 2 := by nlinarith [sq_nonneg ‖p - a‖]
    nlinarith [norm_nonneg (x - a), norm_nonneg (x - p)]
  · apply le_antisymm
    · have := RW36_dist_le (x := x) hq
      simpa using this
    · apply RW36_le_dist
      intro s hs
      have h1 : inner ℝ s p ≤ 0 := hs p hp
      have h2 : ‖x - s‖ ^ 2 = ‖p‖ ^ 2 + 2 * inner ℝ p (x - p - s) + ‖x - p - s‖ ^ 2 := by
        rw [← norm_add_sq_real, show p + (x - p - s) = x - s by abel]
      have h3 : inner ℝ p (x - p - s) = inner ℝ (x - p) p - inner ℝ s p := by
        rw [inner_sub_right, real_inner_comm p (x - p), real_inner_comm p s]
      have h4 : ‖p‖ ^ 2 ≤ ‖x - s‖ ^ 2 := by nlinarith [sq_nonneg ‖x - p - s‖]
      nlinarith [norm_nonneg (x - s), norm_nonneg p]

lemma RW36_ereal {a b c d : ℝ} (h : a - b ≤ c - d) :
    ((a : ℝ) : EReal) - ((b : ℝ) : EReal) ≤ ((c : ℝ) : EReal) - ((d : ℝ) : EReal) := by
  rw [← EReal.coe_sub, ← EReal.coe_sub]
  exact EReal.coe_le_coe_iff.2 h

lemma RW36_key₁ {K₁ K₂ : Set E} (h₁ : IsClosed K₁) (h₂ : IsClosed K₂)
    (c₁ : IsPointedCone K₁) (c₂ : IsPointedCone K₂) (v₁ : Convex ℝ K₁) (v₂ : Convex ℝ K₂)
    {ρ : ℝ} {x : E} (hx : ‖x‖ ≤ ρ) :
    ∃ u : E, ‖u‖ ≤ ρ ∧ distToSetEReal x K₂ - distToSetEReal x K₁ ≤
      distToSetEReal u (polarCone K₁) - distToSetEReal u (polarCone K₂) := by
  obtain ⟨p₁, hp₁, hq₁, h0₁⟩ := RW36_moreau h₁ c₁ v₁ x
  obtain ⟨p₂, hp₂, hq₂, h0₂⟩ := RW36_moreau h₂ c₂ v₂ x
  rw [(RW36_moreau_dist hp₁ hq₁ h0₁).1, (RW36_moreau_dist hp₂ hq₂ h0₂).1]
  by_cases hq : x - p₂ = 0
  · refine ⟨0, by simpa using (norm_nonneg x).trans hx, ?_⟩
    rw [RW36_dist_self (RW36_polar_zero K₁), RW36_dist_self (RW36_polar_zero K₂)]
    apply RW36_ereal
    rw [hq, norm_zero]
    linarith [norm_nonneg (x - p₁)]
  · have hqpos : 0 < ‖x - p₂‖ := norm_pos_iff.2 hq
    have hn₂ := RW36_moreau_norm h0₂
    have hqx : ‖x - p₂‖ ≤ ‖x‖ := by
      nlinarith [norm_nonneg x, norm_nonneg (x - p₂), sq_nonneg ‖p₂‖]
    have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hqpos hqx
    have hc : 0 ≤ ‖x‖ / ‖x - p₂‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hu₂ : (‖x‖ / ‖x - p₂‖) • (x - p₂) ∈ polarCone K₂ := RW36_polar_smul hq₂ hc
    have hunorm : ‖(‖x‖ / ‖x - p₂‖) • (x - p₂)‖ = ‖x‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      field_simp
    obtain ⟨p, hp, hs, h0⟩ := RW36_moreau h₁ c₁ v₁ ((‖x‖ / ‖x - p₂‖) • (x - p₂))
    refine ⟨(‖x‖ / ‖x - p₂‖) • (x - p₂), by rw [hunorm]; exact hx, ?_⟩
    rw [(RW36_moreau_dist hp hs h0).2, RW36_dist_self hu₂]
    apply RW36_ereal
    generalize hu : (‖x‖ / ‖x - p₂‖) • (x - p₂) = u at hunorm hs h0
    have hn := RW36_moreau_norm h0
    have hsu : ‖u - p‖ ≤ ‖u‖ := by
      nlinarith [norm_nonneg u, norm_nonneg (u - p), sq_nonneg ‖p‖]
    have e0 : inner ℝ (x - p₂) x = ‖x - p₂‖ ^ 2 := by
      have : inner ℝ (x - p₂) x = inner ℝ (x - p₂) (x - p₂) + inner ℝ (x - p₂) p₂ := by
        rw [← inner_add_right, sub_add_cancel]
      rw [this, h0₂, real_inner_self_eq_norm_sq]
      ring
    have e1 : inner ℝ u x = ‖x‖ * ‖x - p₂‖ := by
      rw [← hu, real_inner_smul_left, e0]
      field_simp
    have a1 : inner ℝ u x = inner ℝ p x + inner ℝ (u - p) x := by
      rw [← inner_add_left, add_sub_cancel]
    have a2 : inner ℝ (u - p) x = inner ℝ (u - p) (x - p₁) + inner ℝ (u - p) p₁ := by
      rw [← inner_add_right, sub_add_cancel]
    have b1 : inner ℝ p x ≤ ‖p‖ * ‖x‖ := real_inner_le_norm p x
    have b2 : inner ℝ (u - p) (x - p₁) ≤ ‖u - p‖ * ‖x - p₁‖ := real_inner_le_norm _ _
    have b3 : inner ℝ (u - p) p₁ ≤ 0 := hs p₁ hp₁
    have b4 : ‖u - p‖ * ‖x - p₁‖ ≤ ‖x‖ * ‖x - p₁‖ :=
      mul_le_mul_of_nonneg_right (hunorm ▸ hsu) (norm_nonneg _)
    have b5 : ‖x‖ * ‖x - p₂‖ ≤ ‖x‖ * (‖p‖ + ‖x - p₁‖) := by nlinarith
    have b6 := le_of_mul_le_mul_left b5 hxpos
    linarith

lemma RW36_key₂ {K₁ K₂ : Set E} (h₁ : IsClosed K₁) (h₂ : IsClosed K₂)
    (c₁ : IsPointedCone K₁) (c₂ : IsPointedCone K₂) (v₁ : Convex ℝ K₁) (v₂ : Convex ℝ K₂)
    {ρ : ℝ} {u : E} (hu : ‖u‖ ≤ ρ) :
    ∃ x : E, ‖x‖ ≤ ρ ∧ distToSetEReal u (polarCone K₂) - distToSetEReal u (polarCone K₁) ≤
      distToSetEReal x K₁ - distToSetEReal x K₂ := by
  obtain ⟨p₁, hp₁, hq₁, h0₁⟩ := RW36_moreau h₁ c₁ v₁ u
  obtain ⟨p₂, hp₂, hq₂, h0₂⟩ := RW36_moreau h₂ c₂ v₂ u
  rw [(RW36_moreau_dist hp₁ hq₁ h0₁).2, (RW36_moreau_dist hp₂ hq₂ h0₂).2]
  by_cases hp : p₂ = 0
  · refine ⟨0, by simpa using (norm_nonneg u).trans hu, ?_⟩
    rw [RW36_dist_self c₁.1, RW36_dist_self c₂.1]
    apply RW36_ereal
    rw [hp, norm_zero]
    linarith [norm_nonneg p₁]
  · have hppos : 0 < ‖p₂‖ := norm_pos_iff.2 hp
    have hn₂ := RW36_moreau_norm h0₂
    have hpu : ‖p₂‖ ≤ ‖u‖ := by
      nlinarith [norm_nonneg u, norm_nonneg p₂, sq_nonneg ‖u - p₂‖]
    have hupos : 0 < ‖u‖ := lt_of_lt_of_le hppos hpu
    have hc : 0 ≤ ‖u‖ / ‖p₂‖ := div_nonneg (norm_nonneg _) (norm_nonneg _)
    have hx₂ : (‖u‖ / ‖p₂‖) • p₂ ∈ K₂ := c₂.2 p₂ hp₂ _ hc
    have hxnorm : ‖(‖u‖ / ‖p₂‖) • p₂‖ = ‖u‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc]
      field_simp
    obtain ⟨p, hp', hs, h0⟩ := RW36_moreau h₁ c₁ v₁ ((‖u‖ / ‖p₂‖) • p₂)
    refine ⟨(‖u‖ / ‖p₂‖) • p₂, by rw [hxnorm]; exact hu, ?_⟩
    rw [(RW36_moreau_dist hp' hs h0).1, RW36_dist_self hx₂]
    apply RW36_ereal
    generalize hx : (‖u‖ / ‖p₂‖) • p₂ = x at hxnorm hs h0
    have hn := RW36_moreau_norm h0
    have hpx : ‖p‖ ≤ ‖x‖ := by
      nlinarith [norm_nonneg x, norm_nonneg p, sq_nonneg ‖x - p‖]
    have e0 : inner ℝ p₂ u = ‖p₂‖ ^ 2 := by
      have : inner ℝ p₂ u = inner ℝ p₂ p₂ + inner ℝ p₂ (u - p₂) := by
        rw [← inner_add_right, add_sub_cancel]
      rw [this, real_inner_comm (u - p₂) p₂, h0₂, real_inner_self_eq_norm_sq]
      ring
    have e1 : inner ℝ x u = ‖u‖ * ‖p₂‖ := by
      rw [← hx, real_inner_smul_left, e0]
      field_simp
    have a1 : inner ℝ x u = inner ℝ p u + inner ℝ (x - p) u := by
      rw [← inner_add_left, add_sub_cancel]
    have a2 : inner ℝ p u = inner ℝ p p₁ + inner ℝ p (u - p₁) := by
      rw [← inner_add_right, add_sub_cancel]
    have b1 : inner ℝ (x - p) u ≤ ‖x - p‖ * ‖u‖ := real_inner_le_norm _ _
    have b2 : inner ℝ p p₁ ≤ ‖p‖ * ‖p₁‖ := real_inner_le_norm _ _
    have b3 : inner ℝ p (u - p₁) ≤ 0 := by
      rw [real_inner_comm]
      exact hq₁ p hp'
    have b4 : ‖p‖ * ‖p₁‖ ≤ ‖u‖ * ‖p₁‖ :=
      mul_le_mul_of_nonneg_right (hxnorm ▸ hpx) (norm_nonneg _)
    have b5 : ‖u‖ * ‖p₂‖ ≤ ‖u‖ * (‖p₁‖ + ‖x - p‖) := by nlinarith
    have b6 := le_of_mul_le_mul_left b5 hupos
    linarith

theorem RW_chap_11_36
    (K₁ K₂ : Set E)
    (hK₁_closed : IsClosed K₁)
    (hK₂_closed : IsClosed K₂)
    (hK₁_cone : IsPointedCone K₁)
    (hK₂_cone : IsPointedCone K₂)
    (hK₁_convex : Convex ℝ K₁)
    (hK₂_convex : Convex ℝ K₂) :
    integratedSetDistance K₁ K₂ =
      integratedSetDistance (polarCone K₁) (polarCone K₂) := by
  have key : ∀ ρ : ℝ, pompeiuHausdorffDistOn ρ K₁ K₂ =
      pompeiuHausdorffDistOn ρ (polarCone K₁) (polarCone K₂) := by
    intro ρ
    unfold pompeiuHausdorffDistOn
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, hx, rfl⟩
      rw [Metric.mem_closedBall, _root_.dist_zero_right] at hx
      apply max_le
      · obtain ⟨u, hu, h⟩ := RW36_key₁ hK₂_closed hK₁_closed hK₂_cone hK₁_cone
          hK₂_convex hK₁_convex hx
        refine le_sSup_of_le ⟨u, ?_, rfl⟩ (h.trans (le_max_right _ _))
        rwa [Metric.mem_closedBall, _root_.dist_zero_right]
      · obtain ⟨u, hu, h⟩ := RW36_key₁ hK₁_closed hK₂_closed hK₁_cone hK₂_cone
          hK₁_convex hK₂_convex hx
        refine le_sSup_of_le ⟨u, ?_, rfl⟩ (h.trans (le_max_left _ _))
        rwa [Metric.mem_closedBall, _root_.dist_zero_right]
    · apply sSup_le
      rintro _ ⟨u, hu, rfl⟩
      rw [Metric.mem_closedBall, _root_.dist_zero_right] at hu
      apply max_le
      · obtain ⟨x, hx, h⟩ := RW36_key₂ hK₂_closed hK₁_closed hK₂_cone hK₁_cone
          hK₂_convex hK₁_convex hu
        refine le_sSup_of_le ⟨x, ?_, rfl⟩ (h.trans (le_max_right _ _))
        rwa [Metric.mem_closedBall, _root_.dist_zero_right]
      · obtain ⟨x, hx, h⟩ := RW36_key₂ hK₁_closed hK₂_closed hK₁_cone hK₂_cone
          hK₁_convex hK₂_convex hu
        refine le_sSup_of_le ⟨x, ?_, rfl⟩ (h.trans (le_max_left _ _))
        rwa [Metric.mem_closedBall, _root_.dist_zero_right]
  unfold integratedSetDistance
  simp only [key]

end RW_chap_11_36
