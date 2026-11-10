import ConvexStarLib.Defs

/-!
# `FCA_chap_B_ex_26`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_ex_26` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_ex_26`, so the main result is `FCA_chap_B_ex_26.FCA_chap_B_ex_26`.
-/

namespace FCA_chap_B_ex_26

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_26 (f : E → ℝ) (L : ℝ) (hL_pos : L > 0)
    (hf_convex : ConvexOn ℝ Set.univ f) (hf_diff : Differentiable ℝ f) :
    List.TFAE [
      ∀ (x x' : E), ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖,
      ∀ (x x' : E),
        f x' ≥ f x + inner ℝ (gradient f x) (x' - x) +
          1 / (2 * L) * ‖gradient f x - gradient f x'‖ ^ 2,
      ∀ (x x' : E),
        inner ℝ (gradient f x - gradient f x') (x - x') ≥
          1 / L * ‖gradient f x - gradient f x'‖ ^ 2] := by
  -- derivative of `f` along a line
  have hline : ∀ (x v : E) (t : ℝ),
      HasDerivAt (fun s : ℝ => f (x + s • v)) (inner ℝ (gradient f (x + t • v)) v) t := by
    intro x v t
    have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    have h2 := (hf_diff (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
    rw [inner_gradient_left (hf_diff _)]
    exact h2
  -- first-order characterization of convexity
  have hfo : ∀ x y : E, f x + inner ℝ (gradient f x) (y - x) ≤ f y := by
    intro x y
    have hφc : ConvexOn ℝ Set.univ (fun s : ℝ => f (x + s • (y - x))) := by
      refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
      have key := hf_convex.2 (Set.mem_univ (x + a • (y - x))) (Set.mem_univ (x + b • (y - x)))
        hμ hν hμν
      have e : x + (μ • a + ν • b) • (y - x) = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
        calc x + (μ • a + ν • b) • (y - x) = (μ + ν) • x + (μ • a + ν • b) • (y - x) := by
              rw [hμν, one_smul]
          _ = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
              simp only [smul_eq_mul, smul_add, add_smul, mul_smul]
              abel
      simp only
      rw [e]
      exact key
    have := hφc.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one
      (hline x (y - x) 0)
    simp [slope] at this
    linarith
  -- descent lemma
  have hdesc : (∀ (x x' : E), ‖gradient f x - gradient f x'‖ ≤ L * ‖x - x'‖) →
      ∀ x y : E, f y ≤ f x + inner ℝ (gradient f x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
    intro hlip x y
    set v := y - x with hv
    set h : ℝ → ℝ := fun s =>
      f (x + s • v) - s * inner ℝ (gradient f x) v - L / 2 * s ^ 2 * ‖v‖ ^ 2 with hh_def
    have hh : ∀ s, HasDerivAt h
        (inner ℝ (gradient f (x + s • v)) v - inner ℝ (gradient f x) v - L * s * ‖v‖ ^ 2) s := by
      intro s
      have h1 := hline x v s
      have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient f x) v)
          (inner ℝ (gradient f x) v) s := by
        simpa using (hasDerivAt_id s).mul_const (inner ℝ (gradient f x) v)
      have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖v‖ ^ 2) (L * s * ‖v‖ ^ 2) s := by
        have := ((hasDerivAt_pow 2 s).const_mul (L / 2)).mul_const (‖v‖ ^ 2)
        convert this using 1
        push_cast
        ring
      exact (h1.sub h2).sub h3
    have hcont : Continuous h := continuous_iff_continuousAt.2 fun s => (hh s).continuousAt
    obtain ⟨c, hc, hc'⟩ :=
      exists_hasDerivAt_eq_slope h _ zero_lt_one hcont.continuousOn (fun s _ => hh s)
    have hneg : inner ℝ (gradient f (x + c • v)) v - inner ℝ (gradient f x) v
        - L * c * ‖v‖ ^ 2 ≤ 0 := by
      rw [← inner_sub_left]
      have hcs := real_inner_le_norm (gradient f (x + c • v) - gradient f x) v
      have hl := hlip (x + c • v) x
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hc.1] at hl
      have := mul_le_mul_of_nonneg_right hl (norm_nonneg v)
      nlinarith
    have h10 : h 1 - h 0 ≤ 0 := by
      rw [sub_zero, div_one] at hc'
      linarith
    simp only [hh_def, one_smul, zero_smul, add_zero, one_pow, zero_mul, mul_one, sub_zero,
      zero_pow two_ne_zero, mul_zero] at h10
    rw [hv, add_sub_cancel] at h10
    linarith
  tfae_have 1 → 2 := by
    intro hlip x x'
    set g := gradient f x with hg
    set g' := gradient f x' with hg'
    set z := x' - (1 / L) • (g' - g) with hz
    have hA := hfo x z
    have hB := hdesc hlip x' z
    have e1 : z - x' = -(1 / L) • (g' - g) := by rw [hz]; simp [neg_smul]
    have e2 : z - x = (x' - x) - (1 / L) • (g' - g) := by rw [hz]; abel
    rw [e1] at hB
    rw [e2] at hA
    rw [inner_sub_right, inner_smul_right] at hA
    rw [inner_smul_right, norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos (by positivity)] at hB
    have e3 : ‖g - g'‖ = ‖g' - g‖ := norm_sub_rev g g'
    have e4 : inner ℝ (g' - g) (g' - g) = ‖g' - g‖ ^ 2 := real_inner_self_eq_norm_sq _
    have e5 : inner ℝ g' (g' - g) - inner ℝ g (g' - g) = ‖g' - g‖ ^ 2 := by
      rw [← inner_sub_left, e4]
    have k1 : L / 2 * (1 / L * ‖g' - g‖) ^ 2 = 1 / (2 * L) * ‖g' - g‖ ^ 2 := by
      field_simp
    have k2 : 1 / L * inner ℝ g' (g' - g) - 1 / L * inner ℝ g (g' - g)
        = 2 * (1 / (2 * L) * ‖g' - g‖ ^ 2) := by
      rw [← mul_sub, e5]
      field_simp
    rw [e3]
    linarith
  tfae_have 2 → 3 := by
    intro h2 x x'
    have a := h2 x x'
    have b := h2 x' x
    rw [norm_sub_rev (gradient f x') (gradient f x)] at b
    have e : inner ℝ (gradient f x) (x' - x) = - inner ℝ (gradient f x) (x - x') := by
      rw [← inner_neg_right, neg_sub]
    have k : 1 / L * ‖gradient f x - gradient f x'‖ ^ 2
        = 2 * (1 / (2 * L) * ‖gradient f x - gradient f x'‖ ^ 2) := by
      field_simp
    rw [inner_sub_left]
    linarith
  tfae_have 3 → 1 := by
    intro h3 x x'
    have h := h3 x x'
    have hcs := real_inner_le_norm (gradient f x - gradient f x') (x - x')
    have hn : 0 ≤ ‖gradient f x - gradient f x'‖ := norm_nonneg _
    have hm : 0 ≤ ‖x - x'‖ := norm_nonneg _
    have key : ‖gradient f x - gradient f x'‖ ^ 2
        ≤ L * (‖gradient f x - gradient f x'‖ * ‖x - x'‖) := by
      have h' := mul_le_mul_of_nonneg_left (le_trans h hcs) hL_pos.le
      rwa [← mul_assoc, mul_one_div_cancel hL_pos.ne', one_mul] at h'
    rcases hn.eq_or_lt with h0 | hpos
    · rw [← h0]
      positivity
    · nlinarith
  tfae_finish

end FCA_chap_B_ex_26
