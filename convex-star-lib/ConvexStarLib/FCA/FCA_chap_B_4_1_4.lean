import ConvexStarLib.Defs

/-!
# `FCA_chap_B_4_1_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_4_1_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_4_1_4`, so the main result is `FCA_chap_B_4_1_4.FCA_chap_B_4_1_4`.
-/

namespace FCA_chap_B_4_1_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_4_1_4
    (f : E → ℝ) (Ω C : Set E) (c : ℝ)
    (hΩ_open : IsOpen Ω) (hC_convex : Convex ℝ C) (hC_subset : C ⊆ Ω)
    (hf_differentiable : DifferentiableOn ℝ f Ω) (hc_pos : c > 0) :
    ((ConvexOn ℝ C f) ↔ IsMonotone (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
      ((StrictConvexOn ℝ C f) ↔ IsStrictMonotone (fun x => {v | x ∈ C ∧ v = gradient f x})) ∧
      ((StrongConvexOn C c f) ↔ IsStronglyMonotone (fun x => {v | x ∈ C ∧ v = gradient f x}) c) := by
  -- Derivative of `f` along the segment `t ↦ lineMap x₀ x₁ t`.
  have line_hasDerivAt : ∀ {F : E → ℝ} {g x₀ x₁ : E} {t : ℝ},
      HasGradientAt F g (AffineMap.lineMap x₀ x₁ t) →
        HasDerivAt (F ∘ AffineMap.lineMap x₀ x₁) (inner ℝ g (x₁ - x₀)) t :=
    fun h => h.hasFDerivAt.comp_hasDerivAt _ AffineMap.hasDerivAt_lineMap
  have lineMap_sub : ∀ (x y : E) (s t : ℝ),
      AffineMap.lineMap x y t - AffineMap.lineMap x y s = (t - s) • (y - x) := by
    intro x y s t
    simp only [AffineMap.lineMap_apply_module', sub_smul]
    abel
  -- Convexity is equivalent to monotonicity of the gradient.
  have convex_iff : ∀ (F : E → ℝ) (D : E → E), (∀ x ∈ C, HasGradientAt F (D x) x) →
      (ConvexOn ℝ C F ↔ ∀ x ∈ C, ∀ y ∈ C, 0 ≤ inner ℝ (D y - D x) (y - x)) := by
    intro F D hD
    have hderiv : ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt (F ∘ AffineMap.lineMap x y)
          (inner ℝ (D (AffineMap.lineMap x y t)) (y - x)) t := fun x hx y hy t ht =>
      line_hasDerivAt (hD _ (hC_convex.lineMap_mem hx hy ht))
    constructor
    · intro hF x hx y hy
      have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (F ∘ AffineMap.lineMap x y) :=
        (hF.comp_affineMap (AffineMap.lineMap x y)).subset
          (fun t ht => hC_convex.lineMap_mem hx hy ht) (convex_Icc 0 1)
      have h0 := hderiv x hx y hy 0 (by simp)
      have h1 := hderiv x hx y hy 1 (by simp)
      simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h0 h1
      have := (hφ.le_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one h0).trans
        (hφ.slope_le_of_hasDerivAt (by simp) (by simp) zero_lt_one h1)
      rw [inner_sub_left]
      linarith
    · intro hmono
      refine ⟨hC_convex, fun x hx y hy a b ha hb hab => ?_⟩
      have hφ : ConvexOn ℝ (Set.Icc (0:ℝ) 1) (F ∘ AffineMap.lineMap x y) := by
        apply MonotoneOn.convexOn_of_deriv (convex_Icc 0 1)
        · intro t ht
          exact (hderiv x hx y hy t ht).continuousAt.continuousWithinAt
        · rw [interior_Icc]
          intro t ht
          exact (hderiv x hx y hy t
            (Set.Ioo_subset_Icc_self ht)).differentiableAt.differentiableWithinAt
        · rw [interior_Icc]
          intro s hs t ht hst
          rw [(hderiv x hx y hy s (Set.Ioo_subset_Icc_self hs)).deriv,
            (hderiv x hx y hy t (Set.Ioo_subset_Icc_self ht)).deriv]
          rcases hst.eq_or_lt with rfl | hst
          · exact le_rfl
          have key := hmono _ (hC_convex.lineMap_mem hx hy (Set.Ioo_subset_Icc_self hs))
            _ (hC_convex.lineMap_mem hx hy (Set.Ioo_subset_Icc_self ht))
          rw [lineMap_sub, real_inner_smul_right,
            mul_nonneg_iff_of_pos_left (sub_pos.mpr hst), inner_sub_left] at key
          linarith
      have := hφ.2 (x := 0) (y := 1) (by simp) (by simp) ha hb hab
      rw [Function.comp_apply, Convex.combo_affine_apply hab] at this
      simpa only [Function.comp_apply, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using this
  -- Strict convexity is equivalent to strict monotonicity of the gradient.
  have strictConvex_iff : ∀ (F : E → ℝ) (D : E → E), (∀ x ∈ C, HasGradientAt F (D x) x) →
      (StrictConvexOn ℝ C F ↔ ∀ x ∈ C, ∀ y ∈ C, x ≠ y → 0 < inner ℝ (D y - D x) (y - x)) := by
    intro F D hD
    have hderiv : ∀ x ∈ C, ∀ y ∈ C, ∀ t ∈ Set.Icc (0:ℝ) 1,
        HasDerivAt (F ∘ AffineMap.lineMap x y)
          (inner ℝ (D (AffineMap.lineMap x y t)) (y - x)) t := fun x hx y hy t ht =>
      line_hasDerivAt (hD _ (hC_convex.lineMap_mem hx hy ht))
    constructor
    · intro hF x hx y hy hxy
      have hφ : StrictConvexOn ℝ (Set.Icc (0:ℝ) 1) (F ∘ AffineMap.lineMap x y) := by
        refine ⟨convex_Icc 0 1, fun s hs t ht hst a b ha hb hab => ?_⟩
        have hne : AffineMap.lineMap x y s ≠ AffineMap.lineMap x y t :=
          fun h => hst (AffineMap.lineMap_injective ℝ hxy h)
        have := hF.2 (hC_convex.lineMap_mem hx hy hs) (hC_convex.lineMap_mem hx hy ht)
          hne ha hb hab
        rw [Function.comp_apply, Convex.combo_affine_apply hab]
        exact this
      have h0 := hderiv x hx y hy 0 (by simp)
      have h1 := hderiv x hx y hy 1 (by simp)
      simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at h0 h1
      have := (hφ.lt_slope_of_hasDerivAt (by simp) (by simp) zero_lt_one h0).trans
        (hφ.slope_lt_of_hasDerivAt (by simp) (by simp) zero_lt_one h1)
      rw [inner_sub_left]
      linarith
    · intro hmono
      refine ⟨hC_convex, fun x hx y hy hxy a b ha hb hab => ?_⟩
      have hφ : StrictConvexOn ℝ (Set.Icc (0:ℝ) 1) (F ∘ AffineMap.lineMap x y) := by
        apply StrictMonoOn.strictConvexOn_of_deriv (convex_Icc 0 1)
        · intro t ht
          exact (hderiv x hx y hy t ht).continuousAt.continuousWithinAt
        · rw [interior_Icc]
          intro s hs t ht hst
          rw [(hderiv x hx y hy s (Set.Ioo_subset_Icc_self hs)).deriv,
            (hderiv x hx y hy t (Set.Ioo_subset_Icc_self ht)).deriv]
          have hne : AffineMap.lineMap x y s ≠ AffineMap.lineMap x y t :=
            fun h => hst.ne (AffineMap.lineMap_injective ℝ hxy h)
          have key := hmono _ (hC_convex.lineMap_mem hx hy (Set.Ioo_subset_Icc_self hs))
            _ (hC_convex.lineMap_mem hx hy (Set.Ioo_subset_Icc_self ht)) hne
          rw [lineMap_sub, real_inner_smul_right,
            mul_pos_iff_of_pos_left (sub_pos.mpr hst), inner_sub_left] at key
          linarith
      have := hφ.2 (x := 0) (y := 1) (by simp) (by simp) zero_ne_one ha hb hab
      rw [Function.comp_apply, Convex.combo_affine_apply hab] at this
      simpa only [Function.comp_apply, AffineMap.lineMap_apply_zero,
        AffineMap.lineMap_apply_one] using this
  -- Gradients of `f` and of `f - c/2 ‖·‖²` on `C`.
  have hgrad : ∀ x ∈ C, HasGradientAt f (gradient f x) x := fun x hx =>
    (hf_differentiable.differentiableAt (hΩ_open.mem_nhds (hC_subset hx))).hasGradientAt
  have hgrad' : ∀ x ∈ C, HasGradientAt (fun x => f x - c / 2 * ‖x‖ ^ 2)
      (gradient f x - c • x) x := by
    intro x hx
    have h1 := (hgrad x hx).hasFDerivAt
    have h2 := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt).const_mul (c / 2)
    rw [hasGradientAt_iff_hasFDerivAt]
    convert h1.sub h2 using 1
    ext v
    simp [InnerProductSpace.toDual_apply_apply]
    ring
  refine ⟨?_, ?_, ?_⟩
  · rw [convex_iff f (gradient f) hgrad]
    constructor
    · rintro h x₀ x₁ v₀ v₁ ⟨hx₀, rfl⟩ ⟨hx₁, rfl⟩
      exact h x₀ hx₀ x₁ hx₁
    · intro h x hx y hy
      exact h x y _ _ ⟨hx, rfl⟩ ⟨hy, rfl⟩
  · rw [strictConvex_iff f (gradient f) hgrad]
    constructor
    · rintro h x₀ x₁ v₀ v₁ hne ⟨hx₀, rfl⟩ ⟨hx₁, rfl⟩
      exact h x₀ hx₀ x₁ hx₁ hne
    · intro h x hx y hy hne
      exact h x y _ _ hne ⟨hx, rfl⟩ ⟨hy, rfl⟩
  · rw [strongConvexOn_iff_convex, convex_iff _ (fun x => gradient f x - c • x) hgrad']
    have key : ∀ x y : E, inner ℝ ((gradient f y - c • y) - (gradient f x - c • x)) (y - x) =
        inner ℝ (gradient f y - gradient f x) (y - x) - c * ‖y - x‖ ^ 2 := by
      intro x y
      rw [show (gradient f y - c • y) - (gradient f x - c • x) =
          (gradient f y - gradient f x) - c • (y - x) by rw [smul_sub]; abel,
        inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    constructor
    · rintro h x₀ x₁ v₀ v₁ ⟨hx₀, rfl⟩ ⟨hx₁, rfl⟩
      have := h x₀ hx₀ x₁ hx₁
      rw [key] at this
      linarith
    · intro h x hx y hy
      have := h x y _ _ ⟨hx, rfl⟩ ⟨hy, rfl⟩
      rw [key]
      linarith

end FCA_chap_B_4_1_4
