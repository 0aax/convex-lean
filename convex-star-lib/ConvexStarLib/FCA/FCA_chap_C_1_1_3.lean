import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_1_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_1_3`, so the main result is `FCA_chap_C_1_1_3.FCA_chap_C_1_1_3`.
-/

namespace FCA_chap_C_1_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem FCA_chap_C_1_1_3
  (σ : E → EReal)
  (hσbot : ∀ x, σ x ≠ ⊥) :
  let epigraph := epigraph σ
  IsSublinear σ ↔
    (Set.Nonempty epigraph ∧ Convex ℝ epigraph ∧ IsCone epigraph) := by
  intro epi
  have hmem : ∀ p : E × ℝ, p ∈ epi ↔ σ p.1 ≤ (p.2 : EReal) := fun p => Iff.rfl
  constructor
  · rintro ⟨⟨_hbot, ⟨x0, hx0⟩, hconv⟩, hhom⟩
    refine ⟨⟨(x0, (σ x0).toReal), ?_⟩, hconv, ?_⟩
    · rw [hmem]
      exact EReal.le_coe_toReal hx0.ne
    · rintro ⟨x, r⟩ hp s hs
      rw [hmem] at hp
      rw [hmem]
      simp only [Prod.smul_mk, smul_eq_mul]
      rw [hhom x s hs]
      have hne_top : σ x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top r) hp
      obtain ⟨a, ha⟩ : ∃ a : ℝ, σ x = a :=
        ⟨(σ x).toReal, (EReal.coe_toReal hne_top (hσbot x)).symm⟩
      rw [ha] at hp ⊢
      rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
      exact mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.mp hp) hs.le
  · rintro ⟨⟨p, hp⟩, hconv, hcone⟩
    refine ⟨⟨fun x => bot_lt_iff_ne_bot.mpr (hσbot x), ⟨p.1, ?_⟩, hconv⟩, ?_⟩
    · exact lt_of_le_of_lt hp (EReal.coe_lt_top _)
    · intro x t ht
      have key : ∀ y : E, ∀ r : ℝ, ∀ s : ℝ, s > 0 → σ y ≤ r →
          σ (s • y) ≤ ((s * r : ℝ) : EReal) := by
        intro y r s hs hyr
        exact hcone (y, r) hyr s hs
      have hx_inv : (t⁻¹) • (t • x) = x := by
        rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul]
      by_cases htop : σ x = ⊤
      · rw [htop, EReal.coe_mul_top_of_pos ht]
        by_contra hne
        obtain ⟨b, hb⟩ : ∃ b : ℝ, σ (t • x) = b :=
          ⟨(σ (t • x)).toReal, (EReal.coe_toReal hne (hσbot _)).symm⟩
        have h2 := key (t • x) b t⁻¹ (inv_pos.mpr ht) hb.le
        rw [hx_inv, htop] at h2
        exact absurd h2 (not_le.mpr (EReal.coe_lt_top _))
      · obtain ⟨a, ha⟩ : ∃ a : ℝ, σ x = a :=
          ⟨(σ x).toReal, (EReal.coe_toReal htop (hσbot x)).symm⟩
        rw [ha]
        have h1 : σ (t • x) ≤ ((t * a : ℝ) : EReal) := key x a t ht ha.le
        apply le_antisymm
        · rw [← EReal.coe_mul]
          exact h1
        · have hne : σ (t • x) ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
          obtain ⟨b, hb⟩ : ∃ b : ℝ, σ (t • x) = b :=
            ⟨(σ (t • x)).toReal, (EReal.coe_toReal hne (hσbot _)).symm⟩
          have h2 := key (t • x) b t⁻¹ (inv_pos.mpr ht) hb.le
          rw [hx_inv, ha, EReal.coe_le_coe_iff] at h2
          rw [hb, ← EReal.coe_mul, EReal.coe_le_coe_iff]
          have h3 := mul_le_mul_of_nonneg_left h2 ht.le
          rwa [← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul] at h3

end FCA_chap_C_1_1_3
