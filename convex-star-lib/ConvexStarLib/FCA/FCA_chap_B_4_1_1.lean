import ConvexStarLib.Defs

/-!
# `FCA_chap_B_4_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_4_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_4_1_1`, so the main result is `FCA_chap_B_4_1_1.FCA_chap_B_4_1_1`.
-/

namespace FCA_chap_B_4_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 800000 in
theorem FCA_chap_B_4_1_1
  (f : E → ℝ)
  (Ω : Set E)
  (C : Set E)
  (c : ℝ)
  (hΩ_open : IsOpen Ω)
  (hC_convex : Convex ℝ C)
  (hC_subset : C ⊆ Ω)
  (hf_differentiable : DifferentiableOn ℝ f Ω) :
  (ConvexOn ℝ C f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C, f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀)) ∧
  (StrictConvexOn ℝ C f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C,
  (f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀)) ∧
  ((x ≠ x₀) → f x > f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀))) ∧
  (StrongConvexOn C c f ↔
  ∀ x₀ ∈ C, ∀ x ∈ C,
  f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀) + 1/2 * c * ‖x - x₀‖^2) := by
  -- the inner product with the gradient is the Fréchet derivative
  have hgrad : ∀ x₀ v : E, @inner ℝ _ _ (gradient f x₀) v = fderiv ℝ f x₀ v := by
    intro x₀ v
    simp only [gradient, InnerProductSpace.toDual_symm_apply]
  have hderiv : ∀ x₀ ∈ C, HasFDerivAt f (fderiv ℝ f x₀) x₀ := fun x₀ hx₀ =>
    ((hf_differentiable x₀ (hC_subset hx₀)).differentiableAt
      (hΩ_open.mem_nhds (hC_subset hx₀))).hasFDerivAt
  -- limit of difference quotients along a segment
  have key : ∀ x₀ ∈ C, ∀ v : E, ∀ K L : ℝ,
      (∀ t : ℝ, 0 < t → t ≤ 1 → f (x₀ + t • v) ≤ f x₀ + t * (K - (1 - t) * L)) →
      fderiv ℝ f x₀ v ≤ K - L := by
    intro x₀ hx₀ v K L h
    have h1 := ((hderiv x₀ hx₀).hasLineDerivAt v).tendsto_slope_zero_right
    have h2 : Filter.Tendsto (fun t : ℝ => K - (1 - t) * L) (𝓝[>] 0) (𝓝 (K - L)) := by
      have hc : Continuous (fun t : ℝ => K - (1 - t) * L) := by fun_prop
      have := hc.tendsto 0
      simp only [sub_zero, one_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [Ioc_mem_nhdsGT (zero_lt_one' ℝ)] with t ht
    have := h t ht.1 ht.2
    rw [smul_eq_mul, inv_mul_le_iff₀ ht.1]
    linarith
  -- the strongly convex case, for an arbitrary modulus
  have hstrong : ∀ m : ℝ, StrongConvexOn C m f ↔ ∀ x₀ ∈ C, ∀ x ∈ C,
      f x ≥ f x₀ + @inner ℝ _ _ (gradient f x₀) (x - x₀) + 1/2 * m * ‖x - x₀‖^2 := by
    intro m
    constructor
    · intro hs x₀ hx₀ x hx
      rw [hgrad]
      have := key x₀ hx₀ (x - x₀) (f x - f x₀) (m / 2 * ‖x - x₀‖ ^ 2) (by
        intro t ht0 ht1
        have h := hs.2 hx₀ hx (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (show (1 - t) + t = 1 by ring)
        have e : x₀ + t • (x - x₀) = (1 - t) • x₀ + t • x := by module
        rw [e]
        rw [norm_sub_rev] at h
        simp only [smul_eq_mul] at h
        linarith)
      linarith
    · intro h
      refine ⟨hC_convex, fun x hx y hy a b ha hb hab => ?_⟩
      have hz : a • x + b • y ∈ C := hC_convex hx hy ha hb hab
      obtain rfl : b = 1 - a := by linarith
      have hxz : x - (a • x + (1 - a) • y) = (1 - a) • (x - y) := by module
      have hyz : y - (a • x + (1 - a) • y) = a • (y - x) := by module
      have h1 := h _ hz x hx
      have h2 := h _ hz y hy
      rw [hgrad, hxz, map_smul, norm_smul, smul_eq_mul, Real.norm_of_nonneg hb] at h1
      rw [hgrad, hyz, map_smul, norm_smul, smul_eq_mul, Real.norm_of_nonneg ha,
        norm_sub_rev] at h2
      have e : fderiv ℝ f (a • x + (1 - a) • y) (y - x)
          = - fderiv ℝ f (a • x + (1 - a) • y) (x - y) := by
        rw [← map_neg, neg_sub]
      rw [e] at h2
      have e1 := mul_le_mul_of_nonneg_left h1 ha
      have e2 := mul_le_mul_of_nonneg_left h2 hb
      simp only [smul_eq_mul]
      linarith
  have hconv := hstrong 0
  rw [strongConvexOn_zero] at hconv
  simp only [mul_zero, zero_mul, add_zero] at hconv
  refine ⟨hconv, ?_, hstrong c⟩
  constructor
  · intro hsc x₀ hx₀ x hx
    have hc := hsc.convexOn
    refine ⟨hconv.1 hc x₀ hx₀ x hx, fun hne => ?_⟩
    have hm := hsc.2 hx₀ hx (Ne.symm hne) (show (0:ℝ) < 1/2 by norm_num)
      (show (0:ℝ) < 1/2 by norm_num) (by norm_num)
    have hmC : (1/2 : ℝ) • x₀ + (1/2 : ℝ) • x ∈ C :=
      hC_convex hx₀ hx (by norm_num) (by norm_num) (by norm_num)
    have h1 := hconv.1 hc x₀ hx₀ _ hmC
    have e : (1/2 : ℝ) • x₀ + (1/2 : ℝ) • x - x₀ = (1/2 : ℝ) • (x - x₀) := by module
    rw [e, hgrad, map_smul, smul_eq_mul] at h1
    rw [hgrad]
    simp only [smul_eq_mul] at hm
    linarith
  · intro h
    refine ⟨hC_convex, fun x hx y hy hxy a b ha hb hab => ?_⟩
    have hz : a • x + b • y ∈ C := hC_convex hx hy ha.le hb.le hab
    obtain rfl : b = 1 - a := by linarith
    have hxz : x - (a • x + (1 - a) • y) = (1 - a) • (x - y) := by module
    have hyz : y - (a • x + (1 - a) • y) = a • (y - x) := by module
    have hne1 : x ≠ a • x + (1 - a) • y := by
      intro heq
      have h0 : x - (a • x + (1 - a) • y) = 0 := by rw [← heq, sub_self]
      rw [hxz] at h0
      exact (smul_ne_zero hb.ne' (sub_ne_zero.mpr hxy)) h0
    have hne2 : y ≠ a • x + (1 - a) • y := by
      intro heq
      have h0 : y - (a • x + (1 - a) • y) = 0 := by rw [← heq, sub_self]
      rw [hyz] at h0
      exact (smul_ne_zero ha.ne' (sub_ne_zero.mpr hxy.symm)) h0
    have h1 := (h _ hz x hx).2 hne1
    have h2 := (h _ hz y hy).2 hne2
    rw [hgrad, hxz, map_smul, smul_eq_mul] at h1
    rw [hgrad, hyz, map_smul, smul_eq_mul] at h2
    have e : fderiv ℝ f (a • x + (1 - a) • y) (y - x)
        = - fderiv ℝ f (a • x + (1 - a) • y) (x - y) := by
      rw [← map_neg, neg_sub]
    rw [e] at h2
    have e1 := mul_lt_mul_of_pos_left h1 ha
    have e2 := mul_lt_mul_of_pos_left h2 hb
    simp only [smul_eq_mul]
    linarith

end FCA_chap_B_4_1_1
