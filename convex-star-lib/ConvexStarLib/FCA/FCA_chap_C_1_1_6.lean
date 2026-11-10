import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_1_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_1_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_1_6`, so the main result is `FCA_chap_C_1_1_6.FCA_chap_C_1_1_6`.
-/

namespace FCA_chap_C_1_1_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_1_6
  {m : ℕ}
  (σ : E → EReal)
  (x : ℕ → E)
  (hσ : IsSublinear σ)
  (h_eq_0 : ∀ j ∈ Finset.range m, σ (x j) + σ (-1 • (x j)) = 0)
  (hm : 0 < m) :
  let 𝓧 := {v | InSubspaceSpanVec m x v}
  (IsLinearOn 𝓧 σ) := by
  intro 𝓧
  obtain ⟨⟨hbot, -, hconv⟩, hhom⟩ := hσ
  -- subadditivity with real upper bounds
  have sub : ∀ u v : E, ∀ a b : ℝ, σ u ≤ (a : EReal) → σ v ≤ (b : EReal) →
      σ (u + v) ≤ ((a + b : ℝ) : EReal) := by
    intro u v a b hu hv
    have h1 : ((1/2 : ℝ) • u + (1/2 : ℝ) • v, (1/2 : ℝ) * a + (1/2 : ℝ) * b) ∈ epigraph σ := by
      have := hconv (show (u, a) ∈ epigraph σ from hu) (show (v, b) ∈ epigraph σ from hv)
        (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
      simpa [Prod.smul_mk, Prod.mk_add_mk] using this
    have h2 : σ (u + v) = ((2:ℝ) : EReal) * σ ((1/2 : ℝ) • u + (1/2 : ℝ) • v) := by
      rw [← hhom _ 2 (by norm_num)]
      congr 1
      rw [smul_add, smul_smul, smul_smul]
      norm_num
    rw [h2]
    have hw : σ ((1/2 : ℝ) • u + (1/2 : ℝ) • v) ≤ (((1/2 : ℝ) * a + (1/2 : ℝ) * b : ℝ) : EReal) := h1
    have hne_bot : σ ((1/2 : ℝ) • u + (1/2 : ℝ) • v) ≠ ⊥ := ne_of_gt (hbot _)
    have hne_top : σ ((1/2 : ℝ) • u + (1/2 : ℝ) • v) ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hw
    rw [← EReal.coe_toReal hne_top hne_bot] at hw ⊢
    rw [← EReal.coe_mul]
    rw [EReal.coe_le_coe_iff] at hw ⊢
    linarith
  -- a real upper bound and the lower bound ⊥ < σ give a real value
  have real_of_le : ∀ w : E, ∀ a : ℝ, σ w ≤ (a : EReal) → ∃ c : ℝ, σ w = (c : EReal) ∧ c ≤ a := by
    intro w a hw
    have hne_bot : σ w ≠ ⊥ := ne_of_gt (hbot _)
    have hne_top : σ w ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) hw
    refine ⟨(σ w).toReal, (EReal.coe_toReal hne_top hne_bot).symm, ?_⟩
    rw [← EReal.coe_toReal hne_top hne_bot] at hw
    exact EReal.coe_le_coe_iff.mp hw
  -- the predicate: σ is "linear" at v with value c
  let P : E → ℝ → Prop := fun v c => σ v = (c : EReal) ∧ σ (-v) = ((-c : ℝ) : EReal)
  -- base case
  have base : ∀ j ∈ Finset.range m, ∃ c, P (x j) c := by
    intro j hj
    have h := h_eq_0 j hj
    rw [neg_one_zsmul] at h
    have hb1 : σ (x j) ≠ ⊥ := ne_of_gt (hbot _)
    have hb2 : σ (-x j) ≠ ⊥ := ne_of_gt (hbot _)
    have ht1 : σ (x j) ≠ ⊤ := by
      intro h'
      rw [h', EReal.top_add_of_ne_bot hb2] at h
      exact EReal.top_ne_zero h
    have ht2 : σ (-x j) ≠ ⊤ := by
      intro h'
      rw [h', EReal.add_top_of_ne_bot hb1] at h
      exact EReal.top_ne_zero h
    refine ⟨(σ (x j)).toReal, (EReal.coe_toReal ht1 hb1).symm, ?_⟩
    rw [← EReal.coe_toReal ht1 hb1, ← EReal.coe_toReal ht2 hb2, ← EReal.coe_add] at h
    have h' : (σ (x j)).toReal + (σ (-x j)).toReal = 0 := by exact_mod_cast h
    rw [← EReal.coe_toReal ht2 hb2]
    congr 1
    linarith
  -- σ 0 = 0
  have hzero : σ 0 = 0 := by
    obtain ⟨c, hc1, hc2⟩ := base 0 (Finset.mem_range.mpr hm)
    have h1 := sub (x 0) (-x 0) c (-c) hc1.le hc2.le
    rw [add_neg_cancel] at h1
    obtain ⟨d, hd, -⟩ := real_of_le 0 _ h1
    have h2 := hhom 0 2 (by norm_num)
    rw [smul_zero, hd, ← EReal.coe_mul] at h2
    have h3 : d = 2 * d := by exact_mod_cast h2
    rw [hd]
    have : d = 0 := by linarith
    rw [this]
    rfl
  -- closure under addition
  have hadd : ∀ u v a b, P u a → P v b → P (u + v) (a + b) := by
    intro u v a b ⟨hu1, hu2⟩ ⟨hv1, hv2⟩
    have h1 := sub u v a b hu1.le hv1.le
    have h2 := sub (-u) (-v) (-a) (-b) hu2.le hv2.le
    rw [← neg_add] at h2
    obtain ⟨c, hc, hca⟩ := real_of_le _ _ h1
    obtain ⟨d, hd, hdb⟩ := real_of_le _ _ h2
    have h3 := sub (u + v) (-(u + v)) c d hc.le hd.le
    rw [add_neg_cancel, hzero] at h3
    have h4 : (0:ℝ) ≤ c + d := by exact_mod_cast h3
    have hc' : c = a + b := by linarith
    have hd' : d = -(a + b) := by linarith
    exact ⟨by rw [hc, hc'], by rw [hd, hd']⟩
  -- closure under scalar multiplication
  have hsmul : ∀ v c (t : ℝ), P v c → P (t • v) (t * c) := by
    intro v c t ⟨hv1, hv2⟩
    rcases lt_trichotomy t 0 with ht | ht | ht
    · constructor
      · have : t • v = (-t) • (-v) := by rw [neg_smul_neg]
        rw [this, hhom _ _ (by linarith), hv2, ← EReal.coe_mul]
        congr 1
        ring
      · have : -(t • v) = (-t) • v := by rw [neg_smul]
        rw [this, hhom _ _ (by linarith), hv1, ← EReal.coe_mul]
        congr 1
        ring
    · subst ht
      refine ⟨?_, ?_⟩
      · rw [zero_smul, zero_mul, hzero, EReal.coe_zero]
      · rw [zero_smul, neg_zero, zero_mul, neg_zero, hzero, EReal.coe_zero]
    · constructor
      · rw [hhom _ _ ht, hv1, ← EReal.coe_mul]
      · rw [← smul_neg, hhom _ _ ht, hv2, ← EReal.coe_mul]
        congr 1
        ring
  -- every element of 𝓧 satisfies P
  have hmem : ∀ v ∈ 𝓧, ∃ c, P v c := by
    intro v hv
    obtain ⟨z, s, hz, rfl⟩ := hv
    apply Finset.sum_induction _ (fun w => ∃ c, P w c)
    · intro a b ⟨ca, ha⟩ ⟨cb, hb⟩
      exact ⟨ca + cb, hadd a b ca cb ha hb⟩
    · exact ⟨0, hzero, by rw [neg_zero, hzero]; simp⟩
    · intro i hi
      obtain ⟨j, hj, hzj⟩ := hz i hi
      obtain ⟨c, hc⟩ := base j hj
      rw [hzj]
      exact ⟨s i * c, hsmul _ _ _ hc⟩
  -- conclusion
  intro x₁ x₂ t₁ t₂ hx₁ hx₂ _
  obtain ⟨c₁, hc₁⟩ := hmem x₁ hx₁
  obtain ⟨c₂, hc₂⟩ := hmem x₂ hx₂
  have h := hadd _ _ _ _ (hsmul _ _ t₁ hc₁) (hsmul _ _ t₂ hc₂)
  rw [h.1, hc₁.1, hc₂.1, EReal.coe_add, EReal.coe_mul, EReal.coe_mul]

end FCA_chap_C_1_1_6
