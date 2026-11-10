import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_3_1`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_3_1`, so the main result is `CAMA_chap_3_4_3_1.CAMA_chap_3_4_3_1`.
-/

namespace CAMA_chap_3_4_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_3_1 {m : ℕ}
  (b : E)
  (s : Fin m → E) :
  {x : E | ∀ j, inner ℝ (s j) x ≤ 0} ⊆
  {x | inner ℝ b x ≤ 0} ↔ b ∈ cone s := by
  constructor
  · intro h
    have key : ∀ (n : ℕ) (t : Fin n → E) (c : E),
        (∀ x : E, (∀ j, inner ℝ (t j) x ≤ 0) → inner ℝ c x ≤ 0) →
        ∃ α : Fin n → ℝ, (∀ i, 0 ≤ α i) ∧ c = ∑ i, α i • t i := by
      intro n
      induction n with
      | zero =>
        intro t c H
        have hc : inner ℝ c c ≤ (0 : ℝ) := H c (fun j => j.elim0)
        have hc0 : c = 0 := real_inner_self_nonpos.mp hc
        exact ⟨fun _ => 0, fun _ => le_refl _, by simp [hc0]⟩
      | succ n ih =>
        intro t c H
        by_cases hcase : ∀ x : E, (∀ j : Fin n, inner ℝ (t j.succ) x ≤ 0) → inner ℝ c x ≤ 0
        · obtain ⟨β, hβ, hc⟩ := ih (fun j => t j.succ) c hcase
          refine ⟨Fin.cons 0 β, ?_, ?_⟩
          · intro i
            refine Fin.cases ?_ ?_ i
            · simp
            · intro j; simpa using hβ j
          · rw [Fin.sum_univ_succ]
            simpa using hc
        · push_neg at hcase
          obtain ⟨x', hx'1, hx'2⟩ := hcase
          have hpos : 0 < inner ℝ (t 0) x' := by
            by_contra hneg
            push_neg at hneg
            have := H x' (fun i => Fin.cases hneg hx'1 i)
            linarith
          set γ := inner ℝ (t 0) x' with hγ
          set t'' : Fin n → E := fun j => t j.succ - (inner ℝ (t j.succ) x' / γ) • t 0 with ht''
          set c' : E := c - (inner ℝ c x' / γ) • t 0 with hc'
          have H' : ∀ x : E, (∀ j, inner ℝ (t'' j) x ≤ 0) → inner ℝ c' x ≤ 0 := by
            intro x hx
            set z := x - (inner ℝ (t 0) x / γ) • x' with hz
            have hz0 : inner ℝ (t 0) z = 0 := by
              rw [hz, inner_sub_right, real_inner_smul_right, ← hγ]
              field_simp
              ring
            have hzj : ∀ j, inner ℝ (t j.succ) z = inner ℝ (t'' j) x := by
              intro j
              rw [hz, ht'', inner_sub_right, real_inner_smul_right, inner_sub_left,
                real_inner_smul_left]
              ring
            have hzc : inner ℝ c z = inner ℝ c' x := by
              rw [hz, hc', inner_sub_right, real_inner_smul_right, inner_sub_left,
                real_inner_smul_left]
              ring
            have := H z (fun i => Fin.cases (le_of_eq hz0) (fun j => by rw [hzj]; exact hx j) i)
            rwa [hzc] at this
          obtain ⟨β, hβ, hcβ⟩ := ih t'' c' H'
          refine ⟨Fin.cons (inner ℝ c x' / γ - ∑ j, β j * (inner ℝ (t j.succ) x' / γ)) β, ?_, ?_⟩
          · intro i
            refine Fin.cases ?_ ?_ i
            · simp only [Fin.cons_zero]
              have h1 : 0 < inner ℝ c x' / γ := div_pos hx'2 hpos
              have h2 : ∑ j, β j * (inner ℝ (t j.succ) x' / γ) ≤ 0 := by
                apply Finset.sum_nonpos
                intro j _
                exact mul_nonpos_of_nonneg_of_nonpos (hβ j) (div_nonpos_of_nonpos_of_nonneg (hx'1 j) hpos.le)
              linarith
            · intro j; simpa using hβ j
          · rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            have hc_eq : c = c' + (inner ℝ c x' / γ) • t 0 := by simp [hc']
            conv_lhs => rw [hc_eq, hcβ]
            simp only [ht'', smul_sub, Finset.sum_sub_distrib, smul_smul, ← Finset.sum_smul, sub_smul]
            abel
    obtain ⟨α, hα, hb⟩ := key m s b (fun x hx => h hx)
    exact ⟨α, hα, hb⟩
  · rintro ⟨α, hα, rfl⟩ x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [sum_inner]
    apply Finset.sum_nonpos
    intro i _
    rw [real_inner_smul_left]
    exact mul_nonpos_of_nonneg_of_nonpos (hα i) (hx i)

end CAMA_chap_3_4_3_1
