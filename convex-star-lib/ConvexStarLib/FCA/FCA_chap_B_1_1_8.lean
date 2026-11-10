import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_1_8`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_1_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_1_8`, so the main result is `FCA_chap_B_1_1_8.FCA_chap_B_1_1_8`.
-/

namespace FCA_chap_B_1_1_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_1_1_8
  {n : ℕ}
  (k : ℕ)
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hC_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ (x : Fin k → EuclideanSpace ℝ (Fin n)), ∀ (α : EuclideanSpace ℝ (Fin k)),
  α.ofLp ∈ probSimplex k → (f (∑ i, (α i) • (x i))) ≤ ∑ i, ((α i) * (f (x i))) := by
  intro x α hα
  obtain ⟨hα0, hα1⟩ := hα
  have hconv : Convex ℝ (epigraph f) := hC_convex.2.2
  by_cases hcase : ∃ j, α j ≠ 0 ∧ f (x j) = ⊤
  · -- some point with positive weight has value `⊤`, so the right-hand side is `⊤`
    obtain ⟨j, hj0, hjtop⟩ := hcase
    have hjpos : 0 < α j := lt_of_le_of_ne (hα0 j) (Ne.symm hj0)
    have hne : ∀ i, ((α i : EReal) * f (x i)) ≠ ⊥ := by
      intro i
      rw [EReal.mul_ne_bot]
      have h1 : f (x i) ≠ ⊥ := (f_ne_bot (x i)).ne'
      have h2 : (0 : EReal) ≤ (α i : EReal) := EReal.coe_nonneg.mpr (hα0 i)
      refine ⟨Or.inl (EReal.coe_ne_bot _), Or.inr h1, Or.inl (EReal.coe_ne_top _), Or.inl h2⟩
    have hsum : ∑ i, ((α i : EReal) * f (x i)) = ⊤ := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), hjtop, EReal.coe_mul_top_of_pos hjpos]
      apply EReal.top_add_of_ne_bot
      apply Finset.sum_induction _ (fun y : EReal => y ≠ ⊥)
      · intro a b ha hb
        exact EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩
      · exact EReal.zero_ne_bot
      · intro i _
        exact hne i
    rw [hsum]
    exact le_top
  · -- every point with positive weight has a finite value
    push_neg at hcase
    have hfin : ∀ i, α i ≠ 0 → f (x i) = ((f (x i)).toReal : EReal) := fun i hi =>
      (EReal.coe_toReal (hcase i hi) (f_ne_bot (x i)).ne').symm
    have hterm : ∀ i, ((α i : EReal) * f (x i)) = ((α i * (f (x i)).toReal : ℝ) : EReal) := by
      intro i
      by_cases h : α i = 0
      · simp [h]
      · rw [EReal.coe_mul, ← hfin i h]
    have hcoe : ∀ (s : Finset (Fin k)) (g : Fin k → ℝ),
        ((∑ i ∈ s, g i : ℝ) : EReal) = ∑ i ∈ s, (g i : EReal) := fun s g =>
      map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g s
    rw [Finset.sum_congr rfl (fun i _ => hterm i), ← hcoe]
    have hmem := hconv.sum_mem (t := Finset.univ.filter (fun i => α i ≠ 0))
      (w := fun i => α i) (z := fun i => (x i, (f (x i)).toReal)) ?_ ?_ ?_
    · simp only [epigraph, Set.mem_setOf_eq, Prod.fst_sum, Prod.snd_sum, Prod.smul_fst,
        Prod.smul_snd, smul_eq_mul] at hmem
      rw [Finset.sum_filter_of_ne, Finset.sum_filter_of_ne] at hmem
      · exact hmem
      · intro i _ hi h
        exact hi (by rw [h, zero_mul])
      · intro i _ hi h
        exact hi (by rw [h, zero_smul])
    · intro i _
      exact hα0 i
    · rw [Finset.sum_filter_ne_zero]
      exact hα1
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      show f (x i) ≤ (((f (x i)).toReal : ℝ) : EReal)
      rw [← hfin i hi]

end FCA_chap_B_1_1_8
