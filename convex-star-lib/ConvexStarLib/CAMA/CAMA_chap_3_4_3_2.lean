import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_3_2`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_3_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_3_2`, so the main result is `CAMA_chap_3_4_3_2.CAMA_chap_3_4_3_2`.
-/

namespace CAMA_chap_3_4_3_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_3_2 {m n : ℕ}
  (b : EuclideanSpace ℝ (Fin n))
  (s : Fin m → EuclideanSpace ℝ (Fin n)) :
  let P := b ∈ cone s
  let Q := ∃ (x : EuclideanSpace ℝ (Fin n)), (inner ℝ b x > 0) ∧ (∀ j, inner ℝ (s j) x ≤ 0)
  (P ∨ Q) ∧ ¬(P ∧ Q) := by
  intro P Q
  -- Farkas–Bartl, by induction on the number of generators
  have key : ∀ (k : ℕ) (t : Fin k → EuclideanSpace ℝ (Fin n)) (c : EuclideanSpace ℝ (Fin n)),
      (∀ x, (∀ i, 0 ≤ inner ℝ (t i) x) → 0 ≤ inner ℝ c x) →
      ∃ α : Fin k → ℝ, (∀ i, 0 ≤ α i) ∧ c = ∑ i, α i • t i := by
    intro k
    induction k with
    | zero =>
      intro t c h
      refine ⟨fun _ => 0, fun _ => le_rfl, ?_⟩
      have h1 := h (-c) (fun i => i.elim0)
      rw [inner_neg_right, real_inner_self_eq_norm_sq] at h1
      have : ‖c‖ = 0 := by nlinarith [norm_nonneg c]
      simp [norm_eq_zero.mp this]
    | succ k ih =>
      intro t c h
      by_cases h' : ∀ x, (∀ i : Fin k, 0 ≤ inner ℝ (t (Fin.castSucc i)) x) → 0 ≤ inner ℝ c x
      · obtain ⟨α, hα, hc⟩ := ih (fun i => t (Fin.castSucc i)) c h'
        refine ⟨Fin.snoc α 0, ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simp
          · simp [hα j]
        · rw [Fin.sum_univ_castSucc]
          simp [hc]
      · push_neg at h'
        obtain ⟨x', hx'1, hx'2⟩ := h'
        set d := inner ℝ (t (Fin.last k)) x' with hd
        have hdneg : d < 0 := by
          by_contra hcon
          push_neg at hcon
          have := h x' (fun i => by
            refine Fin.lastCases ?_ (fun j => ?_) i
            · exact hcon
            · exact hx'1 j)
          linarith
        have hdne : d ≠ 0 := hdneg.ne
        let t' : Fin k → EuclideanSpace ℝ (Fin n) := fun i =>
          t (Fin.castSucc i) - (inner ℝ (t (Fin.castSucc i)) x' / d) • t (Fin.last k)
        let c' : EuclideanSpace ℝ (Fin n) := c - (inner ℝ c x' / d) • t (Fin.last k)
        have h'' : ∀ x, (∀ i, 0 ≤ inner ℝ (t' i) x) → 0 ≤ inner ℝ c' x := by
          intro x hx
          have hzi : ∀ i, 0 ≤ inner ℝ (t i) (x - (inner ℝ (t (Fin.last k)) x / d) • x') := by
            intro i
            refine Fin.lastCases ?_ (fun j => ?_) i
            · rw [inner_sub_right, real_inner_smul_right, ← hd]
              field_simp
              simp
            · have := hx j
              simp only [t', inner_sub_left, real_inner_smul_left] at this
              rw [inner_sub_right, real_inner_smul_right]
              have e : inner ℝ (t (Fin.last k)) x / d * inner ℝ (t (Fin.castSucc j)) x'
                  = inner ℝ (t (Fin.castSucc j)) x' / d * inner ℝ (t (Fin.last k)) x := by ring
              linarith
          have := h _ hzi
          simp only [c', inner_sub_left, real_inner_smul_left]
          rw [inner_sub_right, real_inner_smul_right] at this
          have e : inner ℝ (t (Fin.last k)) x / d * inner ℝ c x'
              = inner ℝ c x' / d * inner ℝ (t (Fin.last k)) x := by ring
          linarith
        obtain ⟨α, hα, hc⟩ := ih t' c' h''
        have hcoef : 0 ≤ inner ℝ c x' / d - ∑ i, α i * (inner ℝ (t (Fin.castSucc i)) x' / d) := by
          have h1 : 0 ≤ inner ℝ c x' / d := (div_pos_of_neg_of_neg hx'2 hdneg).le
          have h2 : ∑ i, α i * (inner ℝ (t (Fin.castSucc i)) x' / d) ≤ 0 := by
            apply Finset.sum_nonpos
            intro i _
            exact mul_nonpos_of_nonneg_of_nonpos (hα i) (div_nonpos_of_nonneg_of_nonpos (hx'1 i) hdneg.le)
          linarith
        refine ⟨Fin.snoc α (inner ℝ c x' / d - ∑ i, α i * (inner ℝ (t (Fin.castSucc i)) x' / d)), ?_, ?_⟩
        · intro i
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa using hcoef
          · simpa using hα j
        · rw [Fin.sum_univ_castSucc]
          simp only [Fin.snoc_castSucc, Fin.snoc_last]
          have hc2 : c = c' + (inner ℝ c x' / d) • t (Fin.last k) := by
            simp [c']
          calc c = c' + (inner ℝ c x' / d) • t (Fin.last k) := hc2
            _ = (∑ i, α i • t' i) + (inner ℝ c x' / d) • t (Fin.last k) := by rw [hc]
            _ = _ := by
              simp only [t', smul_sub, Finset.sum_sub_distrib, sub_smul, Finset.sum_smul, smul_smul]
              abel
  refine ⟨?_, ?_⟩
  · by_cases hQ : Q
    · exact Or.inr hQ
    · left
      have hQ' : ∀ x, (∀ i, 0 ≤ inner ℝ (s i) x) → 0 ≤ inner ℝ b x := by
        intro x hx
        by_contra hneg
        push_neg at hneg
        apply hQ
        refine ⟨-x, ?_, ?_⟩
        · rw [inner_neg_right]; linarith
        · intro j
          rw [inner_neg_right]
          linarith [hx j]
      obtain ⟨α, hα, hb⟩ := key m s b hQ'
      exact ⟨α, hα, hb⟩
  · rintro ⟨⟨α, hα, hb⟩, ⟨x, hx1, hx2⟩⟩
    have : inner ℝ b x = ∑ i, α i * inner ℝ (s i) x := by
      rw [hb, sum_inner]
      simp [real_inner_smul_left]
    have h2 : ∑ i, α i * inner ℝ (s i) x ≤ 0 := by
      apply Finset.sum_nonpos
      intro i _
      exact mul_nonpos_of_nonneg_of_nonpos (hα i) (hx2 i)
    linarith

end CAMA_chap_3_4_3_2
