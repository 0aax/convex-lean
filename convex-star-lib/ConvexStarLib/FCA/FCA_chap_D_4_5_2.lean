import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_5_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_5_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_5_2`, so the main result is `FCA_chap_D_4_5_2.FCA_chap_D_4_5_2`.
-/

namespace FCA_chap_D_4_5_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_D_4_5_2
    (g : E → ℝ)
    (A : E →ₗ[ℝ] F)
    (x : F)
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_bounded : BddBelow (Set.image g {y | A y = x}))
    (hA_surjective : Function.Surjective A) :
    let Ag := fun x => sInf (Set.image g {y | A y = x})
    let Yx := {y | (A y = x) ∧ (g y = Ag x)}
    (Set.Nonempty Yx) → (∃ y ∈ Yx, DifferentiableAt ℝ g y) →
    (DifferentiableAt ℝ Ag x) := by
  intro Ag Yx _ hex
  obtain ⟨y₀, ⟨hy₀A, hy₀g⟩, hdiff⟩ := hex
  set L : E →L[ℝ] ℝ := fderiv ℝ g y₀ with hL
  have hgL : HasFDerivAt g L y₀ := hdiff.hasFDerivAt
  -- subgradient inequality
  have subgrad : ∀ y, g y₀ + L (y - y₀) ≤ g y := by
    intro y
    have hphic : ConvexOn ℝ Set.univ (g ∘ (AffineMap.lineMap y₀ y : ℝ →ᵃ[ℝ] E)) := by
      simpa using hg_convex.comp_affineMap (AffineMap.lineMap y₀ y : ℝ →ᵃ[ℝ] E)
    have hphid : HasDerivAt (g ∘ (AffineMap.lineMap y₀ y : ℝ →ᵃ[ℝ] E)) (L (y - y₀)) 0 := by
      have h1 : HasFDerivAt g L ((AffineMap.lineMap y₀ y : ℝ →ᵃ[ℝ] E) (0:ℝ)) := by simpa using hgL
      exact h1.comp_hasDerivAt (0:ℝ) AffineMap.hasDerivAt_lineMap
    have := hphic.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hphid
    simp only [slope_def_field, Function.comp_apply, AffineMap.lineMap_apply_one,
      AffineMap.lineMap_apply_zero, sub_zero, div_one] at this
    linarith
  -- L vanishes on ker A
  have hker : ∀ z, A z = 0 → L z = 0 := by
    intro z hz
    have hpsimin : IsLocalMin (fun t : ℝ => g (y₀ + t • z)) 0 := by
      refine Filter.Eventually.of_forall fun t => ?_
      show g (y₀ + (0:ℝ) • z) ≤ g (y₀ + t • z)
      rw [zero_smul, add_zero, hy₀g]
      apply csInf_le hg_bounded
      refine ⟨y₀ + t • z, ?_, rfl⟩
      show A (y₀ + t • z) = x
      rw [map_add, map_smul, hz, smul_zero, add_zero, hy₀A]
    have hpsid : HasDerivAt (fun t : ℝ => g (y₀ + t • z)) (L z) 0 := by
      have h1 : HasFDerivAt g L (y₀ + (0:ℝ) • z) := by simpa using hgL
      have h2 : HasDerivAt (fun t : ℝ => y₀ + t • z) z 0 := by
        simpa using ((hasDerivAt_id (0:ℝ)).smul_const z).const_add y₀
      exact h1.comp_hasDerivAt (0:ℝ) h2
    exact hpsimin.hasDerivAt_eq_zero hpsid
  obtain ⟨B, hB⟩ := LinearMap.exists_rightInverse_of_surjective A (LinearMap.range_eq_top.mpr hA_surjective)
  have hAB : ∀ h, A (B h) = h := fun h => LinearMap.congr_fun hB h
  let Bc : F →L[ℝ] E := LinearMap.toContinuousLinearMap B
  have hBc : ∀ h, Bc h = B h := fun h => rfl
  let ℓ : F →L[ℝ] ℝ := L.comp Bc
  have hℓ : ∀ y, ℓ (A y) = L y := by
    intro y
    have h1 : A (B (A y) - y) = 0 := by
      rw [map_sub, hAB, sub_self]
    have h2 := hker _ h1
    rw [map_sub, sub_eq_zero] at h2
    simpa [ℓ, Bc] using h2
  -- lower bound
  have lower_mem : ∀ h, ∀ y, A y = x + h → Ag x + ℓ h ≤ g y := by
    intro h y hy
    have h1 := subgrad y
    have h2 : L (y - y₀) = ℓ h := by
      rw [← hℓ, map_sub, hy, hy₀A]; congr 1; abel
    rw [← hy₀g]
    linarith
  have bdd : ∀ h, BddBelow (g '' {y | A y = x + h}) := by
    intro h
    refine ⟨Ag x + ℓ h, ?_⟩
    rintro _ ⟨y, hy, rfl⟩
    exact lower_mem h y hy
  have lower : ∀ h, Ag x + ℓ h ≤ Ag (x + h) := by
    intro h
    apply le_csInf
    · obtain ⟨y, hy⟩ := hA_surjective (x + h)
      exact ⟨g y, y, hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact lower_mem h y hy
  have upper : ∀ h, Ag (x + h) ≤ g (y₀ + Bc h) := by
    intro h
    apply csInf_le (bdd h)
    refine ⟨y₀ + Bc h, ?_, rfl⟩
    show A (y₀ + B h) = x + h
    rw [map_add, hAB, hy₀A]
  -- conclude
  have hpsi : HasFDerivAt (fun h => g (y₀ + Bc h)) ℓ 0 := by
    have h1 : HasFDerivAt (fun h => y₀ + Bc h) Bc 0 := Bc.hasFDerivAt.const_add y₀
    have h2 : HasFDerivAt g L (y₀ + Bc 0) := by simpa using hgL
    exact h2.comp 0 h1
  refine ⟨ℓ, ?_⟩
  rw [hasFDerivAt_iff_isLittleO_nhds_zero] at hpsi ⊢
  refine Asymptotics.IsBigO.trans_isLittleO ?_ hpsi
  refine Asymptotics.IsBigO.of_bound 1 (Filter.Eventually.of_forall fun h => ?_)
  have e1 := lower h
  have e2 := upper h
  simp only [map_zero, add_zero, zero_add, one_mul, Real.norm_eq_abs]
  rw [hy₀g]
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
  linarith

end FCA_chap_D_4_5_2
