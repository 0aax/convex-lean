import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_3_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_3_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_3_3`, so the main result is `FCA_chap_B_2_3_3.FCA_chap_B_2_3_3`.
-/

namespace FCA_chap_B_2_3_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_3_3
  (f₁ : E → EReal)
  (f₂ : E → EReal)
  (hf_convex : InConvRn f₁ ∧ InConvRn f₂)
  (h_common_affine_minorant : ∃ (s : E) (b : ℝ),
    (∀ x, f₁ x ≥ (inner ℝ s x) - b) ∧
    (∀ x, f₂ x ≥ (inner ℝ s x) - b)) :
  InConvRn (infimalConv f₁ f₂) := by
  obtain ⟨⟨hb₁, ⟨x₁, hx₁⟩, hc₁⟩, ⟨hb₂, ⟨x₂, hx₂⟩, hc₂⟩⟩ := hf_convex
  obtain ⟨s, b, hs₁, hs₂⟩ := h_common_affine_minorant
  have hc₁' : Convex ℝ (epigraph f₁) := hc₁
  have hc₂' : Convex ℝ (epigraph f₂) := hc₂
  -- every split gives an upper bound
  have hle : ∀ x y, infimalConv f₁ f₂ x ≤ f₁ y + f₂ (x - y) := fun x y => sInf_le ⟨y, rfl⟩
  -- a value strictly below a real number is approximated by a finite split
  have key : ∀ x (r : ℝ), infimalConv f₁ f₂ x < r →
      ∃ y, ∃ u v : ℝ, f₁ y = u ∧ f₂ (x - y) = v ∧ u + v < r := by
    intro x r h
    obtain ⟨_, ⟨y, rfl⟩, hy⟩ := sInf_lt_iff.mp h
    have hne : f₁ y + f₂ (x - y) ≠ ⊤ := ne_top_of_lt hy
    rw [EReal.add_ne_top_iff_ne_top₂ (hb₁ y).ne' (hb₂ (x - y)).ne'] at hne
    have e1 := EReal.coe_toReal hne.1 (hb₁ y).ne'
    have e2 := EReal.coe_toReal hne.2 (hb₂ (x - y)).ne'
    refine ⟨y, (f₁ y).toReal, (f₂ (x - y)).toReal, e1.symm, e2.symm, ?_⟩
    rw [← EReal.coe_lt_coe_iff, EReal.coe_add, e1, e2]
    exact hy
  refine ⟨?_, ?_, ?_⟩
  · intro x
    have hlow : ((inner ℝ s x - 2 * b : ℝ) : EReal) ≤ infimalConv f₁ f₂ x := by
      apply le_sInf
      rintro z ⟨y, rfl⟩
      calc ((inner ℝ s x - 2 * b : ℝ) : EReal)
          = ((inner ℝ s y : ℝ) - (b : EReal)) + ((inner ℝ s (x - y) : ℝ) - (b : EReal)) := by
            rw [inner_sub_right, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_add]
            congr 1
            ring
        _ ≤ f₁ y + f₂ (x - y) := add_le_add (hs₁ y) (hs₂ (x - y))
    exact lt_of_lt_of_le (EReal.bot_lt_coe _) hlow
  · refine ⟨x₁ + x₂, ?_⟩
    calc infimalConv f₁ f₂ (x₁ + x₂) ≤ f₁ x₁ + f₂ (x₁ + x₂ - x₁) := hle _ _
      _ = f₁ x₁ + f₂ x₂ := by rw [add_sub_cancel_left]
      _ < ⊤ := EReal.add_lt_top hx₁.ne hx₂.ne
  · show Convex ℝ (epigraph (infimalConv f₁ f₂))
    rintro ⟨x, r⟩ hp ⟨x', r'⟩ hq a c ha hc hac
    simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hp hq ⊢
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : a * r + c * r' < z := EReal.coe_lt_coe_iff.mp hz
    set δ := z - (a * r + c * r') with hδ
    have hδpos : 0 < δ := by linarith
    obtain ⟨y, u, v, hu, hv, huv⟩ :=
      key x (r + δ) (lt_of_le_of_lt hp (EReal.coe_lt_coe_iff.mpr (by linarith)))
    obtain ⟨y', u', v', hu', hv', huv'⟩ :=
      key x' (r' + δ) (lt_of_le_of_lt hq (EReal.coe_lt_coe_iff.mpr (by linarith)))
    have h1 : f₁ (a • y + c • y') ≤ ((a * u + c * u' : ℝ) : EReal) := by
      have hm : (y, u) ∈ epigraph f₁ := by simp [epigraph, hu]
      have hm' : (y', u') ∈ epigraph f₁ := by simp [epigraph, hu']
      have := hc₁' hm hm' ha hc hac
      simpa [epigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
    have h2 : f₂ (a • (x - y) + c • (x' - y')) ≤ ((a * v + c * v' : ℝ) : EReal) := by
      have hm : (x - y, v) ∈ epigraph f₂ := by simp [epigraph, hv]
      have hm' : (x' - y', v') ∈ epigraph f₂ := by simp [epigraph, hv']
      have := hc₂' hm hm' ha hc hac
      simpa [epigraph, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] using this
    have heq : a • x + c • x' - (a • y + c • y') = a • (x - y) + c • (x' - y') := by
      simp only [smul_sub]; abel
    have hfin : a * u + c * u' + (a * v + c * v') ≤ z := by
      have e1 : a * (u + v) ≤ a * (r + δ) := mul_le_mul_of_nonneg_left huv.le ha
      have e2 : c * (u' + v') ≤ c * (r' + δ) := mul_le_mul_of_nonneg_left huv'.le hc
      have e3 : a * (r + δ) + c * (r' + δ) = a * r + c * r' + (a + c) * δ := by ring
      rw [hac, one_mul] at e3
      nlinarith
    calc infimalConv f₁ f₂ (a • x + c • x')
        ≤ f₁ (a • y + c • y') + f₂ (a • x + c • x' - (a • y + c • y')) := hle _ _
      _ = f₁ (a • y + c • y') + f₂ (a • (x - y) + c • (x' - y')) := by rw [heq]
      _ ≤ ((a * u + c * u' : ℝ) : EReal) + ((a * v + c * v' : ℝ) : EReal) := add_le_add h1 h2
      _ = ((a * u + c * u' + (a * v + c * v') : ℝ) : EReal) := (EReal.coe_add _ _).symm
      _ ≤ (z : EReal) := EReal.coe_le_coe_iff.mpr hfin

end FCA_chap_B_2_3_3
