import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_4_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_4_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_4_3`, so the main result is `FCA_chap_E_1_4_3.FCA_chap_E_1_4_3`.
-/

namespace FCA_chap_E_1_4_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_4_3
  (f : E → EReal)
  (g : E → EReal)
  (x s : E)
  (hf_nondegenerate : IsNondegenerate f)
  (hf_convex : InConvRn f)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (Set.Nonempty (convexSubdifferential f x) → biconjugate f x = f x) ∧
  ((Minorizes (biconjugate f) g) ∧ (Minorizes g f) ∧ (g x = f x) →
  (convexSubdifferential g x) = (convexSubdifferential f x)) ∧
  (s ∈ convexSubdifferential f x → x ∈ convexSubdifferential (conjugate f) s) := by
  obtain ⟨hbot, ⟨x0, hx0⟩, _⟩ := hf_convex
  -- Fenchel–Young inequality: `⟪v, y⟫ - f y ≤ f* v`
  have fy : ∀ v y, ((inner ℝ v y : ℝ) : EReal) - f y ≤ conjugate f v := by
    intro v y
    exact le_sSup ⟨y, Set.mem_univ _, rfl⟩
  -- the same inequality for the biconjugate: `⟪y, v⟫ - f* v ≤ f** y`
  have fy2 : ∀ v y, ((inner ℝ y v : ℝ) : EReal) - conjugate f v ≤ biconjugate f y := by
    intro v y
    exact le_sSup ⟨v, Set.mem_univ _, rfl⟩
  -- if `t ∈ ∂f(x)`, then `f x` is finite and `f* t = ⟪t, x⟫ - f x`
  have key : ∀ t ∈ convexSubdifferential f x, ∃ r : ℝ, f x = (r : EReal) ∧
      conjugate f t = ((inner ℝ t x - r : ℝ) : EReal) := by
    intro t ht
    have hfx_ne_top : f x ≠ ⊤ := by
      intro h
      have h1 : f x0 ≥ f x + ((inner ℝ t (x0 - x) : ℝ) : EReal) := ht x0
      rw [h, EReal.top_add_coe] at h1
      exact absurd hx0 (not_lt.mpr h1)
    have hfx_ne_bot : f x ≠ ⊥ := (hbot x).ne'
    have hr : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm
    refine ⟨(f x).toReal, hr, le_antisymm ?_ ?_⟩
    · apply sSup_le
      rintro _ ⟨y, -, rfl⟩
      dsimp only
      have hy : f y ≥ f x + ((inner ℝ t (y - x) : ℝ) : EReal) := ht y
      rw [hr] at hy
      have hyb := hbot y
      generalize f y = a at hy hyb ⊢
      induction a using EReal.rec with
      | bot => exact absurd hyb (lt_irrefl _)
      | top => simp
      | coe b =>
        rw [ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right] at hy
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        linarith
    · have h1 := fy t x
      rw [hr, ← EReal.coe_sub] at h1
      exact h1
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨t, ht⟩
    obtain ⟨r, hr, hct⟩ := key t ht
    rw [hr]
    apply le_antisymm
    · -- `f** x ≤ f x`
      apply sSup_le
      rintro _ ⟨v, -, rfl⟩
      dsimp only
      have h1 := fy v x
      rw [hr, ← EReal.coe_sub] at h1
      generalize conjugate f v = a at h1 ⊢
      induction a using EReal.rec with
      | bot => exact absurd h1 (not_le.mpr (EReal.bot_lt_coe _))
      | top => simp
      | coe b =>
        rw [EReal.coe_le_coe_iff] at h1
        rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
        have hc := real_inner_comm v x
        linarith
    · -- `f x ≤ f** x`
      have h2 := fy2 t x
      rw [hct, ← EReal.coe_sub] at h2
      refine le_trans ?_ h2
      rw [EReal.coe_le_coe_iff]
      have hc := real_inner_comm t x
      linarith
  · rintro ⟨hfg, hgf, hgx⟩
    ext t
    constructor
    · intro ht y
      have h1 : g y ≥ g x + ((inner ℝ t (y - x) : ℝ) : EReal) := ht y
      show f y ≥ f x + ((inner ℝ t (y - x) : ℝ) : EReal)
      rw [← hgx]
      exact le_trans h1 (hgf y)
    · intro ht y
      obtain ⟨r, hr, hct⟩ := key t ht
      have h2 := fy2 t y
      rw [hct, ← EReal.coe_sub] at h2
      show g y ≥ g x + ((inner ℝ t (y - x) : ℝ) : EReal)
      rw [hgx, hr, ← EReal.coe_add]
      refine le_trans ?_ (le_trans h2 (hfg y))
      rw [EReal.coe_le_coe_iff, inner_sub_right]
      have hc := real_inner_comm t y
      linarith
  · intro ht v
    obtain ⟨r, hr, hct⟩ := key s ht
    have h1 := fy v x
    rw [hr, ← EReal.coe_sub] at h1
    show conjugate f v ≥ conjugate f s + ((inner ℝ x (v - s) : ℝ) : EReal)
    rw [hct, ← EReal.coe_add]
    refine le_trans ?_ h1
    rw [EReal.coe_le_coe_iff, inner_sub_right]
    have hc1 := real_inner_comm v x
    have hc2 := real_inner_comm s x
    linarith

end FCA_chap_E_1_4_3
