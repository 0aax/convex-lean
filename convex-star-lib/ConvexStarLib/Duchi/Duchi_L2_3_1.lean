import ConvexStarLib.Defs

/-!
# `Duchi_L2_3_1`

Source: Duchi, EE364m Convex Optimization (exercise sets).

Statement from the `convex-eval-v28-2h/Duchi_L2_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace Duchi_L2_3_1`, so the main result is `Duchi_L2_3_1.Duchi_L2_3_1`.
-/

namespace Duchi_L2_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


theorem Duchi_L2_3_1 {n : ℕ}
    (x y : Fin n → ℝ)
    (hx_sorted : Antitone x)
    (hy_sorted : Antitone y)
    (σ : Equiv.Perm (Fin n)) :
    ((∑ i, x i * (y ∘ σ) i) ≤ ∑ i, x i * y i) ∧
      ((∑ i, x i * (y ∘ σ) i) = ∑ i, x i * y i ↔
        ∃ τ : Equiv.Perm (Fin n), x ∘ τ = x ∧ (y ∘ σ) ∘ τ = y) := by
  have hmv : Monovary x y := hx_sorted.monovary hy_sorted
  refine ⟨?_, ?_⟩
  · exact hmv.sum_mul_comp_perm_le_sum_mul
  constructor
  · intro heq
    have hmv' : Monovary x (y ∘ σ) := (hmv.sum_mul_comp_perm_eq_sum_mul_iff).1 heq
    set z : Fin n → ℝ := y ∘ σ with hz
    let w : Fin n → ℝ ×ₗ ℝ := fun i => toLex (-x i, -z i)
    set p := Tuple.sort w with hp
    have hmono : Monotone (w ∘ p) := Tuple.monotone_sort w
    have key : ∀ i j, i ≤ j → x (p j) < x (p i) ∨ (x (p j) = x (p i) ∧ z (p j) ≤ z (p i)) := by
      intro i j hij
      have := hmono hij
      simp only [Function.comp, w, Prod.Lex.toLex_le_toLex] at this
      rcases this with h | ⟨h1, h2⟩
      · left; linarith
      · right; constructor <;> linarith
    have hxanti : Antitone (x ∘ p) := by
      intro i j hij
      rcases key i j hij with h | ⟨h1, h2⟩
      · exact h.le
      · exact h1.le
    have hzanti : Antitone (z ∘ p) := by
      intro i j hij
      rcases key i j hij with h | ⟨h1, h2⟩
      · by_contra hcon
        push_neg at hcon
        have := hmv' hcon
        linarith
      · exact h2
    refine ⟨p, ?_, ?_⟩
    · have := Tuple.unique_antitone (f := x) (σ := p) (τ := 1) hxanti (by simpa using hx_sorted)
      simpa using this
    · have h1 : Antitone (y ∘ ⇑(σ * p)) := by
        simpa [Equiv.Perm.coe_mul, Function.comp_assoc] using hzanti
      have := Tuple.unique_antitone (f := y) (σ := σ * p) (τ := 1) h1 (by simpa using hy_sorted)
      simpa [Equiv.Perm.coe_mul, Function.comp_assoc] using this
  · rintro ⟨τ, hxτ, hyτ⟩
    calc ∑ i, x i * (y ∘ σ) i = ∑ i, x (τ i) * (y ∘ σ) (τ i) :=
          (Equiv.sum_comp τ (fun i => x i * (y ∘ σ) i)).symm
      _ = ∑ i, x i * y i := by
        congr 1
        ext i
        have h1 := congrFun hxτ i
        have h2 := congrFun hyτ i
        simp only [Function.comp] at h1 h2 ⊢
        rw [h1, h2]

end Duchi_L2_3_1
