import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_1_1`, so the main result is `FCA_chap_B_3_1_1.FCA_chap_B_3_1_1`.
-/

namespace FCA_chap_B_3_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_3_1_1
  (f : E → EReal)
  (x₀ : E)
  (δ m M : ℝ)
  (hf_convex : InConvRn f)
  (hf_bound : ∀ x ∈ Metric.ball x₀ (2 * δ), (m : EReal) ≤ f x ∧ f x ≤ M) :
  ∀ y ∈ Metric.ball x₀ δ, ∀ y' ∈ Metric.ball x₀ δ,
  |(f y).toReal - (f y').toReal| ≤ ((M - m) / δ) * ‖y - y'‖ := by
  intro y hy y' hy'
  have hδ : 0 < δ := lt_of_le_of_lt dist_nonneg (Metric.mem_ball.1 hy)
  -- on the big ball, `f` is finite and its real part lies in `[m, M]`
  have hfin : ∀ x ∈ Metric.ball x₀ (2 * δ),
      f x = (((f x).toReal : ℝ) : EReal) ∧ m ≤ (f x).toReal ∧ (f x).toReal ≤ M := by
    intro x hx
    obtain ⟨h1, h2⟩ := hf_bound x hx
    have hne_top : f x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top M) h2
    have hne_bot : f x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot m) h1
    refine ⟨(EReal.coe_toReal hne_top hne_bot).symm, ?_, ?_⟩
    · simpa using EReal.toReal_le_toReal h1 (EReal.coe_ne_bot m) hne_top
    · simpa using EReal.toReal_le_toReal h2 hne_bot (EReal.coe_ne_top M)
  have hmM : m ≤ M := by
    obtain ⟨_, h1, h2⟩ := hfin x₀ (Metric.mem_ball_self (by linarith))
    linarith
  set g : E → ℝ := fun x => (f x).toReal - (M + m) / 2 with hg
  have hgconv : ConvexOn ℝ (Metric.ball x₀ (2 * δ)) g := by
    refine ⟨convex_ball x₀ (2 * δ), ?_⟩
    intro x hx z hz a b ha hb hab
    have hxe : (x, (f x).toReal) ∈ epigraph f := by
      show f x ≤ (((f x).toReal : ℝ) : EReal)
      rw [← (hfin x hx).1]
    have hze : (z, (f z).toReal) ∈ epigraph f := by
      show f z ≤ (((f z).toReal : ℝ) : EReal)
      rw [← (hfin z hz).1]
    have hmem := hf_convex.2.2 hxe hze ha hb hab
    have hc : a • x + b • z ∈ Metric.ball x₀ (2 * δ) := (convex_ball x₀ (2 * δ)) hx hz ha hb hab
    have h3 : f (a • x + b • z) ≤ ((a * (f x).toReal + b * (f z).toReal : ℝ) : EReal) := by
      simpa [epigraph] using hmem
    rw [(hfin _ hc).1] at h3
    have h4 : (f (a • x + b • z)).toReal ≤ a * (f x).toReal + b * (f z).toReal :=
      EReal.coe_le_coe_iff.1 h3
    simp only [hg, smul_eq_mul]
    have : (M + m) / 2 = a * ((M + m) / 2) + b * ((M + m) / 2) := by
      rw [← add_mul, hab, one_mul]
    linarith
  have hgbound : ∀ a, dist a x₀ < 2 * δ → |g a| ≤ (M - m) / 2 := by
    intro a ha
    obtain ⟨_, h1, h2⟩ := hfin a (Metric.mem_ball.2 ha)
    rw [abs_le]
    constructor <;> simp only [hg] <;> linarith
  have hlip := hgconv.lipschitzOnWith_of_abs_le hδ hgbound
  rw [show 2 * δ - δ = δ by ring] at hlip
  have key := hlip.dist_le_mul y hy y' hy'
  have hK : ((2 * ((M - m) / 2) / δ).toNNReal : ℝ) = (M - m) / δ := by
    rw [Real.coe_toNNReal _ (div_nonneg (by linarith) hδ.le)]
    ring
  rw [hK, dist_eq_norm, Real.norm_eq_abs] at key
  simp only [hg] at key
  rw [dist_eq_norm] at key
  calc |(f y).toReal - (f y').toReal|
      = |(f y).toReal - (M + m) / 2 - ((f y').toReal - (M + m) / 2)| := by ring_nf
    _ ≤ (M - m) / δ * ‖y - y'‖ := key

end FCA_chap_B_3_1_1
