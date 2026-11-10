import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex5`, so the main result is `FCA_chap_E_ex5.FCA_chap_E_ex5`.
-/

namespace FCA_chap_E_ex5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_ex5 {k : ℕ}
  (s : ℕ → E)
  (b : ℕ → ℝ) :
  let P := {x : E | ∀ i ∈ Finset.range k, inner ℝ (s i) x ≤ (b i)}
  (P ≠ ∅) ↔
    (∀ (α : ℕ → ℝ),
      ((∀ i ∈ Finset.range k, α i ≥ 0) ∧
      (∑ i ∈ Finset.range k, (α i) • (s i) = 0)) →
        (∑ i ∈ Finset.range k, (α i) • (b i) ≥ 0)) := by
  intro P
  -- Farkas' lemma (Gale's form), proved by induction on the number of constraints:
  -- an infeasible system `⟪t i, x⟫ ≤ c i` (`i < n`) has a certificate of infeasibility.
  have farkas : ∀ (n : ℕ) (t : ℕ → E) (c : ℕ → ℝ),
      (¬ ∃ x : E, ∀ i ∈ Finset.range n, inner ℝ (t i) x ≤ c i) →
      ∃ α : ℕ → ℝ, (∀ i ∈ Finset.range n, 0 ≤ α i) ∧
        (∑ i ∈ Finset.range n, α i • t i = 0) ∧ (∑ i ∈ Finset.range n, α i * c i < 0) := by
    intro n
    induction n with
    | zero =>
      intro t c h
      exact absurd ⟨0, by simp⟩ h
    | succ n ih =>
      intro t c h
      -- build a certificate for `n + 1` constraints from one for the first `n` and a weight `a`
      have key : ∀ (γ : ℕ → ℝ) (a : ℝ), (∀ i ∈ Finset.range n, 0 ≤ γ i) → 0 ≤ a →
          (∑ i ∈ Finset.range n, γ i • t i) + a • t n = 0 →
          (∑ i ∈ Finset.range n, γ i * c i) + a * c n < 0 →
          ∃ α : ℕ → ℝ, (∀ i ∈ Finset.range (n + 1), 0 ≤ α i) ∧
            (∑ i ∈ Finset.range (n + 1), α i • t i = 0) ∧
            (∑ i ∈ Finset.range (n + 1), α i * c i < 0) := by
        intro γ a hγ ha hs hb
        refine ⟨fun i => if i = n then a else γ i, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hin : i = n
          · simp [hin, ha]
          · have : i < n := by
              have := Finset.mem_range.1 hi; omega
            simp [hin, hγ i (Finset.mem_range.2 this)]
        · simp only [Finset.sum_range_succ, ↓reduceIte]
          rw [← hs]
          congr 1
          apply Finset.sum_congr rfl
          intro i hi
          simp [(Finset.mem_range.1 hi).ne]
        · simp only [Finset.sum_range_succ, ↓reduceIte]
          calc _ = (∑ i ∈ Finset.range n, γ i * c i) + a * c n := by
                congr 1
                apply Finset.sum_congr rfl
                intro i hi
                simp [(Finset.mem_range.1 hi).ne]
            _ < 0 := hb
      by_cases h0 : ∃ x : E, ∀ i ∈ Finset.range n, inner ℝ (t i) x ≤ c i
      · obtain ⟨x₀, hx₀⟩ := h0
        -- `x₀` satisfies the first `n` constraints, so it violates the last one
        have hv : c n < inner ℝ (t n) x₀ := by
          by_contra hcon
          push_neg at hcon
          apply h
          refine ⟨x₀, fun i hi => ?_⟩
          rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hi) with hlt | heq
          · exact hx₀ i (Finset.mem_range.2 hlt)
          · subst heq; exact hcon
        by_cases htn : t n = 0
        · -- the last constraint reads `0 ≤ c n` with `c n < 0`
          apply key (fun _ => 0) 1 (fun _ _ => le_refl 0) zero_le_one
          · simp [htn]
          · rw [htn, inner_zero_left] at hv
            simp
            linarith
        · -- restrict the first `n` constraints to the hyperplane `⟪v, x⟫ = β`
          set v := t n with hv_def
          set β := c n with hβ_def
          have hvv : inner ℝ v v ≠ 0 := by
            rwa [inner_self_ne_zero]
          set μ : ℕ → ℝ := fun i => inner ℝ (t i) v / inner ℝ v v with hμ
          have hproj : ¬ ∃ y : E, ∀ i ∈ Finset.range n,
              inner ℝ (t i - μ i • v) y ≤ c i - μ i * β := by
            rintro ⟨y, hy⟩
            apply h
            refine ⟨y + ((β - inner ℝ v y) / inner ℝ v v) • v, fun i hi => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 (Finset.mem_range.1 hi) with hlt | heq
            · have := hy i (Finset.mem_range.2 hlt)
              rw [inner_sub_left, real_inner_smul_left] at this
              rw [inner_add_right, real_inner_smul_right]
              have e1 : (β - inner ℝ v y) / inner ℝ v v * inner ℝ (t i) v
                  = μ i * (β - inner ℝ v y) := by
                simp only [hμ]; ring
              rw [e1]
              linarith
            · subst heq
              rw [inner_add_right, real_inner_smul_right]
              field_simp
              linarith
          obtain ⟨γ, hγ0, hγs, hγb⟩ :=
            ih (fun i => t i - μ i • v) (fun i => c i - μ i * β) hproj
          set C := ∑ i ∈ Finset.range n, γ i * μ i with hC
          have hsC : ∑ i ∈ Finset.range n, γ i • t i = C • v := by
            have : ∑ i ∈ Finset.range n, γ i • (t i - μ i • v)
                = ∑ i ∈ Finset.range n, γ i • t i - C • v := by
              rw [hC, Finset.sum_smul, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              rw [smul_sub, smul_smul]
            rw [this, sub_eq_zero] at hγs
            exact hγs
          have hbC : ∑ i ∈ Finset.range n, γ i * c i - C * β < 0 := by
            have : ∑ i ∈ Finset.range n, γ i * (c i - μ i * β)
                = ∑ i ∈ Finset.range n, γ i * c i - C * β := by
              rw [hC, Finset.sum_mul, ← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
            rw [← this]; exact hγb
          by_cases hCpos : 0 < C
          · -- impossible: evaluating at `x₀` gives `C * β < C * ⟪v, x₀⟫ ≤ ∑ γ i * c i`
            exfalso
            have h1 : ∑ i ∈ Finset.range n, γ i * inner ℝ (t i) x₀
                ≤ ∑ i ∈ Finset.range n, γ i * c i := by
              apply Finset.sum_le_sum
              intro i hi
              exact mul_le_mul_of_nonneg_left (hx₀ i hi) (hγ0 i hi)
            have h2 : ∑ i ∈ Finset.range n, γ i * inner ℝ (t i) x₀ = C * inner ℝ v x₀ := by
              rw [← real_inner_smul_left, ← hsC, sum_inner]
              apply Finset.sum_congr rfl
              intro i _
              rw [real_inner_smul_left]
            have h3 : C * β < C * inner ℝ v x₀ := mul_lt_mul_of_pos_left hv hCpos
            linarith
          · push_neg at hCpos
            apply key γ (-C) hγ0 (by linarith)
            · rw [hsC, neg_smul, add_neg_cancel]
            · linarith
      · obtain ⟨γ, hγ0, hγs, hγb⟩ := ih t c h0
        apply key γ 0 hγ0 le_rfl
        · simp [hγs]
        · simp [hγb]
  constructor
  · -- a feasible point `x` gives `∑ α i * b i ≥ ⟪∑ α i • s i, x⟫ = 0`
    intro hP α ⟨hα0, hαs⟩
    obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.2 hP
    have h1 : ∑ i ∈ Finset.range k, α i * inner ℝ (s i) x
        ≤ ∑ i ∈ Finset.range k, α i * b i := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hx i hi) (hα0 i hi)
    have h2 : ∑ i ∈ Finset.range k, α i * inner ℝ (s i) x = 0 := by
      have : inner ℝ (∑ i ∈ Finset.range k, α i • s i) x = 0 := by
        rw [hαs, inner_zero_left]
      rw [sum_inner] at this
      rw [← this]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_left]
    simp only [smul_eq_mul]
    linarith
  · -- otherwise Farkas' lemma yields a certificate contradicting the hypothesis
    intro h hP
    obtain ⟨α, hα0, hαs, hαb⟩ := farkas k s b (by
      rintro ⟨x, hx⟩
      have : x ∈ P := hx
      rw [hP] at this
      exact this)
    have := h α ⟨fun i hi => hα0 i hi, hαs⟩
    simp only [smul_eq_mul] at this
    linarith

end FCA_chap_E_ex5
