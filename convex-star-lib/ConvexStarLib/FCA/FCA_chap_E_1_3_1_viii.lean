import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_1_viii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_1_viii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_1_viii`, so the main result is `FCA_chap_E_1_3_1_viii.FCA_chap_E_1_3_1_viii`.
-/

namespace FCA_chap_E_1_3_1_viii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_3_1_viii
  (f₁ : E → EReal) (f₂ : E → EReal) (α : ℝ)
  (hf_nondegenerate : IsNondegenerate f₁ ∧ IsNondegenerate f₂) :
  Set.Nonempty (effDom f₁ ∩ effDom f₂) →
  α ∈ Set.Ioo 0 1 →
  Minorizes
    (conjugate (fun x => α * (f₁) x + (1 - α) * (f₂) x))
    (fun s => α * conjugate f₁ s
              + (1 - α) * conjugate f₂ s) := by
  intro _ hα s
  obtain ⟨hα0, hα1⟩ := hα
  have hc₁ : (0 : EReal) ≤ (α : EReal) := EReal.coe_nonneg.2 hα0.le
  have hc₂ : (0 : EReal) ≤ ((1 - α : ℝ) : EReal) := EReal.coe_nonneg.2 (sub_pos.2 hα1).le
  obtain ⟨⟨_, s₁, b₁, h₁⟩, ⟨_, s₂, b₂, h₂⟩⟩ := hf_nondegenerate
  have hsub : (1 : EReal) - (α : EReal) = ((1 - α : ℝ) : EReal) := by
    rw [EReal.coe_sub, EReal.coe_one]
  -- a nonnegative real multiple of a value bounded below by a real is not `⊥`
  have hne : ∀ (c : ℝ) (y : EReal) (r : ℝ), (0 : EReal) ≤ c → (r : EReal) ≤ y →
      (c : EReal) * y ≠ ⊥ := by
    intro c y r hc hr h
    have := mul_le_mul_of_nonneg_left hr hc
    rw [h, le_bot_iff, ← EReal.coe_mul] at this
    exact EReal.coe_ne_bot _ this
  have hl₁ : ∀ x, ((inner ℝ s₁ x - b₁ : ℝ) : EReal) ≤ f₁ x := fun x => by
    rw [EReal.coe_sub]; exact h₁ x
  have hl₂ : ∀ x, ((inner ℝ s₂ x - b₂ : ℝ) : EReal) ≤ f₂ x := fun x => by
    rw [EReal.coe_sub]; exact h₂ x
  simp only [conjugate, hsub]
  apply sSup_le
  rintro _ ⟨x, -, rfl⟩
  simp only
  have hb1 : f₁ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hl₁ x)
  have hb2 : f₂ x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) (hl₂ x)
  by_cases ht1 : f₁ x = ⊤
  · rw [ht1, EReal.coe_mul_top_of_pos hα0, EReal.top_add_of_ne_bot (hne _ _ _ hc₂ (hl₂ x)),
      EReal.sub_top]
    exact bot_le
  by_cases ht2 : f₂ x = ⊤
  · rw [ht2, EReal.coe_mul_top_of_pos (sub_pos.2 hα1),
      EReal.add_top_of_ne_bot (hne _ _ _ hc₁ (hl₁ x)), EReal.sub_top]
    exact bot_le
  obtain ⟨a₁, ha₁⟩ : ∃ a : ℝ, f₁ x = a := ⟨(f₁ x).toReal, (EReal.coe_toReal ht1 hb1).symm⟩
  obtain ⟨a₂, ha₂⟩ : ∃ a : ℝ, f₂ x = a := ⟨(f₂ x).toReal, (EReal.coe_toReal ht2 hb2).symm⟩
  have k₁ : ((inner ℝ s x - a₁ : ℝ) : EReal) ≤
      sSup ((fun y => ((inner ℝ s y : ℝ) : EReal) - f₁ y) '' Set.univ) :=
    le_sSup ⟨x, Set.mem_univ _, by dsimp only; rw [ha₁, EReal.coe_sub]⟩
  have k₂ : ((inner ℝ s x - a₂ : ℝ) : EReal) ≤
      sSup ((fun y => ((inner ℝ s y : ℝ) : EReal) - f₂ y) '' Set.univ) :=
    le_sSup ⟨x, Set.mem_univ _, by dsimp only; rw [ha₂, EReal.coe_sub]⟩
  have key : ((inner ℝ s x : ℝ) : EReal) - ((α : EReal) * f₁ x + ((1 - α : ℝ) : EReal) * f₂ x)
      = (α : EReal) * ((inner ℝ s x - a₁ : ℝ) : EReal)
        + ((1 - α : ℝ) : EReal) * ((inner ℝ s x - a₂ : ℝ) : EReal) := by
    rw [ha₁, ha₂, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_sub,
      ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add]
    congr 1
    ring
  rw [key]
  exact add_le_add (mul_le_mul_of_nonneg_left k₁ hc₁) (mul_le_mul_of_nonneg_left k₂ hc₂)

end FCA_chap_E_1_3_1_viii
