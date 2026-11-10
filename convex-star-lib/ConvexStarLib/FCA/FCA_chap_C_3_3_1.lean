import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_3_1`, so the main result is `FCA_chap_C_3_3_1.FCA_chap_C_3_3_1`.
-/

namespace FCA_chap_C_3_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_3_3_1
  (S₁ S₂ : Set E)
  (hS_nonempty : Set.Nonempty S₁ ∧ Set.Nonempty S₂)
  (hS_closed : IsClosed S₁ ∧ IsClosed S₂)
  (hS_convex : Convex ℝ S₁ ∧ Convex ℝ S₂) :
  let σ₁ := supportFunction S₁
  let σ₂ := supportFunction S₂
  S₁ ⊆ S₂ ↔ ∀ d, σ₁ d ≤ σ₂ d := by
  intro σ₁ σ₂
  constructor
  · intro h d
    exact sSup_le_sSup (Set.image_mono h)
  · intro h x hx
    by_contra hx2
    obtain ⟨f, u, hfu, hux⟩ := geometric_hahn_banach_closed_point hS_convex.2 hS_closed.2 hx2
    set d : E := (InnerProductSpace.toDual ℝ E).symm f with hd
    have key : ∀ v : E, (inner ℝ v d : ℝ) = f v := by
      intro v
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have h1 : σ₂ d ≤ (u : EReal) := by
      apply sSup_le
      rintro _ ⟨a, ha, rfl⟩
      simp only
      rw [key]
      exact_mod_cast (hfu a ha).le
    have h2 : ((f x : ℝ) : EReal) ≤ σ₁ d := by
      apply le_sSup
      exact ⟨x, hx, by simp only; rw [key]⟩
    have h3 : ((f x : ℝ) : EReal) ≤ (u : EReal) := h2.trans ((h d).trans h1)
    have h4 : f x ≤ u := by exact_mod_cast h3
    linarith

end FCA_chap_C_3_3_1
