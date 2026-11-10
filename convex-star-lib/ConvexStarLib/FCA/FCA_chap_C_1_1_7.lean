import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_1_7`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_1_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_1_7`, so the main result is `FCA_chap_C_1_1_7.FCA_chap_C_1_1_7`.
-/

namespace FCA_chap_C_1_1_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_1_1_7
  {m : ℕ}
  (σ : E → EReal)
  (x : E)
  (hσ : IsSublinear σ) :
  (σ x + σ (-1 • x) = 0) →
  ∀ (y : E), σ (x + y) = σ x + σ y := by
  intro hx y
  obtain ⟨⟨hbot, _, hconv⟩, hhom⟩ := hσ
  -- subadditivity: σ (a + b) ≤ σ a + σ b
  have hsub : ∀ a b : E, σ (a + b) ≤ σ a + σ b := by
    intro a b
    by_cases ha : σ a = ⊤
    · rw [ha, EReal.top_add_of_ne_bot (hbot b).ne']
      exact le_top
    by_cases hb : σ b = ⊤
    · rw [hb, EReal.add_top_of_ne_bot (hbot a).ne']
      exact le_top
    obtain ⟨ra, hra⟩ : ∃ r : ℝ, σ a = r :=
      ⟨(σ a).toReal, (EReal.coe_toReal ha (hbot a).ne').symm⟩
    obtain ⟨rb, hrb⟩ : ∃ r : ℝ, σ b = r :=
      ⟨(σ b).toReal, (EReal.coe_toReal hb (hbot b).ne').symm⟩
    have hmema : (a, ra) ∈ epigraph σ := by
      show σ a ≤ (ra : EReal)
      rw [hra]
    have hmemb : (b, rb) ∈ epigraph σ := by
      show σ b ≤ (rb : EReal)
      rw [hrb]
    have hmid := hconv hmema hmemb (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
      (by norm_num)
    have hmid' : σ ((1/2 : ℝ) • a + (1/2 : ℝ) • b)
        ≤ (((1/2:ℝ) * ra + (1/2:ℝ) * rb : ℝ) : EReal) := hmid
    have hctop : σ ((1/2 : ℝ) • a + (1/2 : ℝ) • b) ≠ ⊤ :=
      ne_top_of_le_ne_top (EReal.coe_ne_top _) hmid'
    obtain ⟨c, hc⟩ : ∃ r : ℝ, σ ((1/2 : ℝ) • a + (1/2 : ℝ) • b) = r :=
      ⟨_, (EReal.coe_toReal hctop (hbot _).ne').symm⟩
    rw [hc] at hmid'
    have hc' : c ≤ (1/2:ℝ) * ra + (1/2:ℝ) * rb := EReal.coe_le_coe_iff.mp hmid'
    have heq : a + b = (2:ℝ) • ((1/2 : ℝ) • a + (1/2 : ℝ) • b) := by
      rw [smul_add, smul_smul, smul_smul]; norm_num
    rw [heq, hhom _ 2 (by norm_num), hc, hra, hrb]
    have : (2:ℝ) * c ≤ ra + rb := by linarith
    exact_mod_cast this
  have hneg : (-1 • x : E) = -x := by simp
  rw [hneg] at hx
  -- both σ x and σ (-x) are finite
  have hxtop : σ x ≠ ⊤ := by
    intro h
    rw [h, EReal.top_add_of_ne_bot (hbot _).ne'] at hx
    exact EReal.top_ne_zero hx
  have hnxtop : σ (-x) ≠ ⊤ := by
    intro h
    rw [h, EReal.add_top_of_ne_bot (hbot _).ne'] at hx
    exact EReal.top_ne_zero hx
  have h1 := hsub x y
  have h2 := hsub (x + y) (-x)
  rw [show x + y + -x = y by abel] at h2
  obtain ⟨r, hr⟩ : ∃ r : ℝ, σ x = r := ⟨(σ x).toReal, (EReal.coe_toReal hxtop (hbot x).ne').symm⟩
  obtain ⟨s, hs⟩ : ∃ s : ℝ, σ (-x) = s := ⟨_, (EReal.coe_toReal hnxtop (hbot _).ne').symm⟩
  rw [hr, hs] at hx
  have hrs : r + s = 0 := by exact_mod_cast hx
  rw [hr] at h1 ⊢
  rw [hs] at h2
  apply le_antisymm h1
  calc (r : EReal) + σ y ≤ (r : EReal) + (σ (x + y) + s) := by gcongr
    _ = σ (x + y) + ((r : EReal) + s) := add_left_comm _ _ _
    _ = σ (x + y) := by rw [← EReal.coe_add, hrs, EReal.coe_zero, add_zero]

end FCA_chap_C_1_1_7
