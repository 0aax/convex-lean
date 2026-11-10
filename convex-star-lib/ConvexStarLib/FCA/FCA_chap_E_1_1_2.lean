import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_1_2`, so the main result is `FCA_chap_E_1_1_2.FCA_chap_E_1_1_2`.
-/

namespace FCA_chap_E_1_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_1_2
  (f : E → EReal)
  (hf_nondegenerate : IsNondegenerate f) :
  InClosedConvRn (conjugate f) := by
  obtain ⟨⟨x₀, hx₀⟩, ⟨s, b, hsb⟩⟩ := hf_nondegenerate
  -- f never takes the value ⊥
  have hbot : ∀ x, f x ≠ ⊥ := by
    intro x h
    have := hsb x
    rw [h] at this
    exact absurd this (by simp [← EReal.coe_sub])
  -- every value of f is either ⊤ or real
  have hcases : ∀ x, f x = ⊤ ∨ ∃ c : ℝ, f x = c := by
    intro x
    by_cases ht : f x = ⊤
    · exact Or.inl ht
    · exact Or.inr ⟨(f x).toReal, (EReal.coe_toReal ht (hbot x)).symm⟩
  -- each affine minorant `⟪v, x⟫ - f x` lies below `conjugate f v`
  have hle : ∀ v x, ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v := fun v x =>
    le_sSup (Set.mem_image_of_mem (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) (Set.mem_univ x))
  have h1 : ∀ v, ⊥ < conjugate f v := by
    intro v
    obtain ⟨c, hc⟩ : ∃ c : ℝ, f x₀ = c := (hcases x₀).resolve_left hx₀
    calc (⊥ : EReal) < ((inner ℝ v x₀ - c : ℝ) : EReal) := EReal.bot_lt_coe _
      _ = ((inner ℝ v x₀ : ℝ) : EReal) - f x₀ := by rw [hc, EReal.coe_sub]
      _ ≤ conjugate f v := hle v x₀
  have h2 : ∃ v, conjugate f v < ⊤ := by
    refine ⟨s, lt_of_le_of_lt (b := (b : EReal)) ?_ (EReal.coe_lt_top b)⟩
    apply sSup_le
    rintro y ⟨x, -, rfl⟩
    show ((inner ℝ s x : ℝ) : EReal) - f x ≤ b
    rcases hcases x with h | ⟨c, hc⟩
    · simp [h]
    · have := hsb x
      rw [hc] at this ⊢
      rw [← EReal.coe_sub] at *
      norm_cast at *
      linarith
  have h3 : ConvexEReal (conjugate f) := by
    intro p hp q hq a b' ha hb hab
    show conjugate f (a • p + b' • q).1 ≤ ((a • p + b' • q).2 : EReal)
    apply sSup_le
    rintro y ⟨x, -, rfl⟩
    show ((inner ℝ (a • p + b' • q).1 x : ℝ) : EReal) - f x ≤ ((a • p + b' • q).2 : EReal)
    have hpx : ((inner ℝ p.1 x : ℝ) : EReal) - f x ≤ p.2 := le_trans (hle p.1 x) hp
    have hqx : ((inner ℝ q.1 x : ℝ) : EReal) - f x ≤ q.2 := le_trans (hle q.1 x) hq
    rcases hcases x with h | ⟨c, hc⟩
    · simp [h]
    · rw [hc] at hpx hqx ⊢
      rw [← EReal.coe_sub] at hpx hqx ⊢
      norm_cast at hpx hqx ⊢
      simp only [Prod.fst_add, Prod.smul_fst, Prod.snd_add, Prod.smul_snd, smul_eq_mul,
        inner_add_left, real_inner_smul_left]
      have hc' : c = a * c + b' * c := by rw [← add_mul, hab, one_mul]
      linarith [mul_le_mul_of_nonneg_left hpx ha, mul_le_mul_of_nonneg_left hqx hb]
  have h4 : LowerSemicontinuous (conjugate f) := by
    have : conjugate f = fun v => ⨆ x, ((inner ℝ v x : ℝ) : EReal) - f x := by
      funext v
      simp only [conjugate, Set.image_univ, sSup_range]
    rw [this]
    apply lowerSemicontinuous_iSup
    intro x
    apply Continuous.lowerSemicontinuous
    rcases hcases x with h | ⟨c, hc⟩
    · simp only [h, EReal.sub_top]
      exact continuous_const
    · simp only [hc]
      simp_rw [← EReal.coe_sub]
      exact continuous_coe_real_ereal.comp (by fun_prop)
  exact ⟨⟨h1, h2, h3⟩, h4⟩

end FCA_chap_E_1_1_2
