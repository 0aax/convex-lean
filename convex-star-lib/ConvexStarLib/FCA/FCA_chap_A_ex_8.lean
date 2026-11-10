import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_8`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_8`, so the main result is `FCA_chap_A_ex_8.FCA_chap_A_ex_8`.
-/

namespace FCA_chap_A_ex_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


set_option linter.unusedVariables false in
theorem FCA_chap_A_ex_8 {n : ℕ} (m : ℕ) (hm : m ≤ n) :
  let Pi_m : Set (EuclideanSpace ℝ (Fin n)) :=
    {α | (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ ∑ i, α i = (m : ℝ)}
  Set.extremePoints ℝ Pi_m =
    {α : EuclideanSpace ℝ (Fin n) | (∀ i, α i = 0 ∨ α i = 1) ∧ ∑ i, α i = (m : ℝ)} := by
  intro Pi_m
  ext α
  rw [mem_extremePoints]
  constructor
  · rintro ⟨⟨hbox, hsum⟩, hext⟩
    refine ⟨?_, hsum⟩
    by_contra hcon
    push_neg at hcon
    obtain ⟨i, hi0, hi1⟩ := hcon
    have hi0' : 0 < α i := lt_of_le_of_ne (hbox i).1 (Ne.symm hi0)
    have hi1' : α i < 1 := lt_of_le_of_ne (hbox i).2 hi1
    -- find j ≠ i with 0 < α j < 1
    have hj : ∃ j, j ≠ i ∧ 0 < α j ∧ α j < 1 := by
      by_contra hno
      push_neg at hno
      have h01 : ∀ j, j ≠ i → α j = 0 ∨ α j = 1 := by
        intro j hj
        rcases (hbox j).1.lt_or_eq with h | h
        · right
          exact le_antisymm (hbox j).2 (hno j hj h)
        · left
          exact h.symm
      have hsplit : ∑ k, α k = α i + ∑ k ∈ Finset.univ.erase i, α k := by
        rw [Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      have hN : ∑ k ∈ Finset.univ.erase i, α k
          = ((∑ k ∈ Finset.univ.erase i, if α k = 1 then 1 else 0 : ℕ) : ℝ) := by
        push_cast
        apply Finset.sum_congr rfl
        intro k hk
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        rcases h01 k hki with h | h
        · simp [h]
        · simp [h]
      set N := (∑ k ∈ Finset.univ.erase i, if α k = 1 then 1 else 0 : ℕ) with hNdef
      have h1 : ((0 : ℤ) : ℝ) < (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) := by push_cast; linarith
      have h2 : (((m : ℤ) - (N : ℤ) : ℤ) : ℝ) < ((1 : ℤ) : ℝ) := by push_cast; linarith
      have h1' := Int.cast_lt.mp h1
      have h2' := Int.cast_lt.mp h2
      omega
    obtain ⟨j, hji, hj0, hj1⟩ := hj
    set ε := min (min (α i) (1 - α i)) (min (α j) (1 - α j)) with hεdef
    have hε : 0 < ε := by
      simp only [hεdef, lt_min_iff]
      refine ⟨⟨hi0', by linarith⟩, ⟨hj0, by linarith⟩⟩
    have hε1 : ε ≤ α i := le_trans (min_le_left _ _) (min_le_left _ _)
    have hε2 : ε ≤ 1 - α i := le_trans (min_le_left _ _) (min_le_right _ _)
    have hε3 : ε ≤ α j := le_trans (min_le_right _ _) (min_le_left _ _)
    have hε4 : ε ≤ 1 - α j := le_trans (min_le_right _ _) (min_le_right _ _)
    set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single i ε - EuclideanSpace.single j ε
      with hvdef
    have hvi : v i = ε := by simp [hvdef, hji.symm]
    have hvj : v j = -ε := by simp [hvdef, hji]
    have hvk : ∀ k, k ≠ i → k ≠ j → v k = 0 := by
      intro k hki hkj
      simp [hvdef, hki, hkj]
    have hvsum : ∑ k, v k = 0 := by
      simp [hvdef, Finset.sum_sub_distrib]
    have hmem : ∀ s : ℝ, (s = 1 ∨ s = -1) → α + s • v ∈ Pi_m := by
      intro s hs
      refine ⟨fun k => ?_, ?_⟩
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
        by_cases hki : k = i
        · subst hki
          rw [hvi]
          rcases hs with hs | hs <;> subst hs <;> constructor <;> linarith
        · by_cases hkj : k = j
          · subst hkj
            rw [hvj]
            rcases hs with hs | hs <;> subst hs <;> constructor <;> linarith
          · rw [hvk k hki hkj, mul_zero, add_zero]
            exact hbox k
      · simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
          ← Finset.mul_sum, hvsum, mul_zero, add_zero]
        exact hsum
    have hseg : α ∈ openSegment ℝ (α + (1 : ℝ) • v) (α + (-1 : ℝ) • v) := by
      refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
      ext k
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
      ring
    have := (hext _ (hmem 1 (Or.inl rfl)) _ (hmem (-1) (Or.inr rfl)) hseg).1
    have hk := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i) this
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hvi] at hk
    linarith
  · rintro ⟨h01, hsum⟩
    refine ⟨⟨fun i => ?_, hsum⟩, ?_⟩
    · rcases h01 i with h | h <;> simp [h]
    · rintro x ⟨hxbox, hxsum⟩ y ⟨hybox, hysum⟩ ⟨a, b, ha, hb, hab, hxy⟩
      have key : ∀ i, x i = α i ∧ y i = α i := by
        intro i
        have hi := congrArg (fun w : EuclideanSpace ℝ (Fin n) => w i) hxy
        simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] at hi
        obtain ⟨hx0, hx1⟩ := hxbox i
        obtain ⟨hy0, hy1⟩ := hybox i
        rcases h01 i with h | h
        · rw [h] at hi ⊢
          constructor <;> nlinarith
        · rw [h] at hi ⊢
          constructor <;> nlinarith
      constructor
      · ext i
        exact (key i).1
      · ext i
        exact (key i).2

end FCA_chap_A_ex_8
