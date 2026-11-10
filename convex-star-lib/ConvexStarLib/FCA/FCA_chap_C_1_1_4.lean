import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_1_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_1_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_1_4`, so the main result is `FCA_chap_C_1_1_4.FCA_chap_C_1_1_4`.
-/

namespace FCA_chap_C_1_1_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_1_4
  (σ : E → EReal)
  (hσ : ∃ x, σ x ≠ ⊤)
  (hσbot : ∀ x, σ x ≠ ⊥) :
  (IsSublinear σ) ↔
  ((IsERealPosHomogeneous σ) ∧ (IsSubadditive σ)) := by
  constructor
  · rintro ⟨⟨_, _, hconv⟩, hhom⟩
    refine ⟨hhom, ?_⟩
    intro x₁ x₂
    by_cases h1 : σ x₁ = ⊤
    · rw [h1, EReal.top_add_of_ne_bot (hσbot x₂)]
      exact le_top
    by_cases h2 : σ x₂ = ⊤
    · rw [h2, EReal.add_top_of_ne_bot (hσbot x₁)]
      exact le_top
    obtain ⟨a, ha⟩ : ∃ a : ℝ, σ x₁ = a :=
      ⟨(σ x₁).toReal, (EReal.coe_toReal h1 (hσbot x₁)).symm⟩
    obtain ⟨b, hb⟩ : ∃ b : ℝ, σ x₂ = b :=
      ⟨(σ x₂).toReal, (EReal.coe_toReal h2 (hσbot x₂)).symm⟩
    have hm1 : (x₁, a) ∈ epigraph σ := by
      show σ x₁ ≤ a
      rw [ha]
    have hm2 : (x₂, b) ∈ epigraph σ := by
      show σ x₂ ≤ b
      rw [hb]
    have hmid := hconv hm1 hm2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have hmid' : σ ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂)
        ≤ (((1/2 : ℝ) * a + (1/2 : ℝ) * b : ℝ) : EReal) := hmid
    have hsum : x₁ + x₂ = (2 : ℝ) • ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂) := by
      rw [smul_add, smul_smul, smul_smul]
      norm_num
    rw [hsum, hhom _ 2 (by norm_num), ha, hb]
    have hmtop : σ ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂) ≠ ⊤ := by
      intro h
      rw [h] at hmid'
      exact (not_le.mpr (EReal.coe_lt_top _)) hmid'
    obtain ⟨c, hc⟩ : ∃ c : ℝ, σ ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂) = c :=
      ⟨_, (EReal.coe_toReal hmtop (hσbot _)).symm⟩
    rw [hc] at hmid' ⊢
    rw [EReal.coe_le_coe_iff] at hmid'
    rw [← EReal.coe_mul, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  · rintro ⟨hhom, hadd⟩
    refine ⟨⟨fun x => (hσbot x).bot_lt, ?_, ?_⟩, hhom⟩
    · obtain ⟨x, hx⟩ := hσ
      exact ⟨x, hx.lt_top⟩
    · rintro ⟨x, r⟩ hp ⟨y, s⟩ hq a b ha hb hab
      change σ x ≤ r at hp
      change σ y ≤ s at hq
      change σ (a • x + b • y) ≤ ((a * r + b * s : ℝ) : EReal)
      have hxtop : σ x ≠ ⊤ := fun h => by rw [h] at hp; exact (not_le.mpr (EReal.coe_lt_top _)) hp
      have hytop : σ y ≠ ⊤ := fun h => by rw [h] at hq; exact (not_le.mpr (EReal.coe_lt_top _)) hq
      obtain ⟨u, hu⟩ : ∃ u : ℝ, σ x = u := ⟨_, (EReal.coe_toReal hxtop (hσbot x)).symm⟩
      obtain ⟨v, hv⟩ : ∃ v : ℝ, σ y = v := ⟨_, (EReal.coe_toReal hytop (hσbot y)).symm⟩
      rw [hu, EReal.coe_le_coe_iff] at hp
      rw [hv, EReal.coe_le_coe_iff] at hq
      rcases ha.lt_or_eq with ha' | ha'
      · rcases hb.lt_or_eq with hb' | hb'
        · calc σ (a • x + b • y) ≤ σ (a • x) + σ (b • y) := hadd _ _
            _ = ((a * u + b * v : ℝ) : EReal) := by
              rw [hhom x a ha', hhom y b hb', hu, hv, EReal.coe_add, EReal.coe_mul,
                EReal.coe_mul]
            _ ≤ ((a * r + b * s : ℝ) : EReal) := by
              rw [EReal.coe_le_coe_iff]
              nlinarith
        · subst hb'
          have : a = 1 := by linarith
          subst this
          simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul]
          rw [hu, EReal.coe_le_coe_iff]
          exact hp
      · subst ha'
        have : b = 1 := by linarith
        subst this
        simp only [one_smul, zero_smul, zero_add, one_mul, zero_mul]
        rw [hv, EReal.coe_le_coe_iff]
        exact hq

end FCA_chap_C_1_1_4
