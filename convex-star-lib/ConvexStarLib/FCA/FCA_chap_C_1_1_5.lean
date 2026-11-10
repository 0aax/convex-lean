import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_1_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_1_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_1_5`, so the main result is `FCA_chap_C_1_1_5.FCA_chap_C_1_1_5`.
-/

namespace FCA_chap_C_1_1_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_1_5
  (σ : E → EReal) :
  (IsSublinear σ) →
  (∀ (x : E), σ x + σ (-x) ≥ 0) := by
  rintro ⟨⟨hbot, _, hconv⟩, hhom⟩ x
  -- σ 0 ≥ 0, from σ 0 = 2 * σ 0 and σ 0 ≠ ⊥
  have h0 : (0 : EReal) ≤ σ 0 := by
    have h2 := hhom 0 2 (by norm_num)
    rw [smul_zero] at h2
    by_cases htop : σ 0 = ⊤
    · rw [htop]; exact le_top
    obtain ⟨c, hc⟩ : ∃ c : ℝ, σ 0 = c :=
      ⟨(σ 0).toReal, (EReal.coe_toReal htop (hbot 0).ne').symm⟩
    rw [hc] at h2 ⊢
    have hc2 : c = 2 * c := by exact_mod_cast h2
    exact_mod_cast (by linarith : (0:ℝ) ≤ c)
  by_cases hx : σ x = ⊤
  · rw [hx, EReal.top_add_of_ne_bot (hbot (-x)).ne']
    exact le_top
  by_cases hnx : σ (-x) = ⊤
  · rw [hnx, EReal.add_top_of_ne_bot (hbot x).ne']
    exact le_top
  obtain ⟨a, ha⟩ : ∃ a : ℝ, σ x = a :=
    ⟨(σ x).toReal, (EReal.coe_toReal hx (hbot x).ne').symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, σ (-x) = b :=
    ⟨(σ (-x)).toReal, (EReal.coe_toReal hnx (hbot (-x)).ne').symm⟩
  have hmem1 : (x, a) ∈ epigraph σ := by
    show σ x ≤ (a : EReal)
    rw [ha]
  have hmem2 : (-x, b) ∈ epigraph σ := by
    show σ (-x) ≤ (b : EReal)
    rw [hb]
  have hmid := hconv hmem1 hmem2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  have hmid' : σ 0 ≤ (((1/2 : ℝ) * a + (1/2) * b : ℝ) : EReal) := by
    have heq : (1/2 : ℝ) • (x, a) + (1/2 : ℝ) • (-x, b) = ((0:E), (1/2 : ℝ) * a + (1/2) * b) := by
      ext
      · simp [smul_neg]
      · simp [smul_eq_mul]
    rw [heq] at hmid
    exact hmid
  have hab : (0:ℝ) ≤ (1/2 : ℝ) * a + (1/2) * b := by
    have := h0.trans hmid'
    exact_mod_cast this
  rw [ha, hb]
  have hsum : (0:ℝ) ≤ a + b := by linarith
  exact_mod_cast hsum

end FCA_chap_C_1_1_5
