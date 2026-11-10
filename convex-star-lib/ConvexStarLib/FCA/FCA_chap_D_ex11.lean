import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex11`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex11` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex11`, so the main result is `FCA_chap_D_ex11.FCA_chap_D_ex11`.
-/

namespace FCA_chap_D_ex11

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_ex11
  (α : ℝ)
  (hα : α ∈ Set.Ioo 0 1) :
  let f₁ := fun (x : EuclideanSpace ℝ (Fin 2)) => (x 0) ^ 2
  let f₂ := fun (x : EuclideanSpace ℝ (Fin 2)) => α * (x 0) ^2 + (x 1)
  let f : EuclideanSpace ℝ (Fin 2) → EReal := fun x => max (f₁ x) (f₂ x)
  let q2 := fun (h : EuclideanSpace ℝ (Fin 2)) => ((f h) - (f 0) - (directionalDeriv f 0 h)) * ((1/2) * (‖h‖ ^ 2 : ℝ))⁻¹
  let q2_lim := fun (d : EuclideanSpace ℝ (Fin 2)) =>
    if 0 < d 1 then
      2 * α * (d 0) ^ 2 / ((d 0) ^ 2 + (d 1) ^ 2)
    else
      2 * (d 0) ^ 2 / ((d 0) ^ 2 + (d 1) ^ 2)
  (0 ∈ directionalSubdifferential f 0) ∧
  (∀ d, directionalDeriv f 0 d = (supportFunction (directionalSubdifferential f 0) d)) ∧
  (∀ d, (d ≠ 0) → (∃ (L : ℝ), (L = q2_lim d) ∧ (Filter.Tendsto (fun (t : ℝ) => q2 (t • d)) (𝓝[>] 0) (𝓝 L)))) := by
  intro f₁ f₂ f q2 q2_lim
  obtain ⟨hα0, hα1⟩ := hα
  -- `f` is the coercion of a real-valued function
  have hf : ∀ x, f x = ((max (x 0 ^ 2) (α * x 0 ^ 2 + x 1) : ℝ) : EReal) := by
    intro x
    exact (EReal.coe_strictMono.monotone.map_max).symm
  have hf0 : f 0 = ((0 : ℝ) : EReal) := by
    rw [hf]; simp
  -- the directional derivative at `0`
  have hdd : ∀ d, directionalDeriv f 0 d = ((max 0 (d 1) : ℝ) : EReal) := by
    intro d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have key : ∀ t : ℝ, 0 < t → differenceQuotient f 0 d t
        = ((max (t * d 0 ^ 2) (α * t * d 0 ^ 2 + d 1) : ℝ) : EReal) := by
      intro t ht
      unfold differenceQuotient
      rw [hf, hf0, zero_add, ← EReal.coe_sub, ← EReal.coe_div, EReal.coe_eq_coe_iff]
      simp only [PiLp.smul_apply, smul_eq_mul, sub_zero]
      rw [← max_div_div_right ht.le]
      congr 1
      · field_simp
      · field_simp
    have hcont : Filter.Tendsto
        (fun t : ℝ => ((max (t * d 0 ^ 2) (α * t * d 0 ^ 2 + d 1) : ℝ) : EReal))
        (𝓝[>] 0) (𝓝 ((max 0 (d 1) : ℝ) : EReal)) := by
      apply (continuous_coe_real_ereal.tendsto _).comp
      apply tendsto_nhdsWithin_of_tendsto_nhds
      have : Continuous (fun t : ℝ => max (t * d 0 ^ 2) (α * t * d 0 ^ 2 + d 1)) := by
        fun_prop
      convert this.tendsto 0 using 2
      simp
    apply hcont.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (key t ht).symm
  have hsub : ∀ s : EuclideanSpace ℝ (Fin 2), s ∈ directionalSubdifferential f 0 ↔
      ∀ d, ((inner ℝ s d : ℝ) : EReal) ≤ ((max 0 (d 1) : ℝ) : EReal) := by
    intro s
    simp only [directionalSubdifferential, Set.mem_setOf_eq, hdd]
  have h0mem : (0 : EuclideanSpace ℝ (Fin 2)) ∈ directionalSubdifferential f 0 := by
    rw [hsub]
    intro d
    simp
  have h1mem : (EuclideanSpace.single 1 1 : EuclideanSpace ℝ (Fin 2)) ∈
      directionalSubdifferential f 0 := by
    rw [hsub]
    intro d
    rw [EuclideanSpace.inner_single_left, EReal.coe_le_coe_iff]
    simp
  refine ⟨h0mem, ?_, ?_⟩
  · intro d
    rw [hdd]
    unfold supportFunction
    apply le_antisymm
    · by_cases hd : 0 < d 1
      · apply le_sSup
        refine ⟨EuclideanSpace.single 1 1, h1mem, ?_⟩
        dsimp only
        rw [EuclideanSpace.inner_single_left, EReal.coe_eq_coe_iff]
        simp [max_eq_right hd.le]
      · apply le_sSup
        refine ⟨0, h0mem, ?_⟩
        dsimp only
        rw [EReal.coe_eq_coe_iff]
        simp [max_eq_left (not_lt.mp hd)]
    · apply sSup_le
      rintro b ⟨s, hs, rfl⟩
      exact (hsub s).1 hs d
  · intro d hd
    refine ⟨q2_lim d, rfl, ?_⟩
    have hnd : ‖d‖ ^ 2 = d 0 ^ 2 + d 1 ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_two, Real.norm_eq_abs, Real.norm_eq_abs,
        sq_abs, sq_abs]
    have hnd0 : 0 < d 0 ^ 2 + d 1 ^ 2 := by
      rw [← hnd]
      have := norm_pos_iff.mpr hd
      positivity
    have hq2 : ∀ t : ℝ, 0 < t → q2 (t • d) = ((max (t ^ 2 * d 0 ^ 2) (α * t ^ 2 * d 0 ^ 2 + t * d 1)
        - max 0 (t * d 1)) * (1 / 2 * (t ^ 2 * (d 0 ^ 2 + d 1 ^ 2)))⁻¹ : ℝ) := by
      intro t ht
      simp only [q2]
      rw [hf, hf0, hdd, ← EReal.coe_sub, ← EReal.coe_sub, ← EReal.coe_mul, EReal.coe_eq_coe_iff]
      rw [norm_smul, mul_pow, hnd, Real.norm_eq_abs, abs_of_pos ht]
      simp only [PiLp.smul_apply, smul_eq_mul, sub_zero]
      ring_nf
    apply tendsto_const_nhds.congr'
    by_cases hd1 : 0 < d 1
    · filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < d 1 / (d 0 ^ 2 + 1) by positivity)]
        with t ht
      obtain ⟨ht0, ht1⟩ := ht
      rw [hq2 t ht0, EReal.coe_eq_coe_iff]
      have hlt : t * (d 0 ^ 2 + 1) < d 1 := by
        rwa [lt_div_iff₀ (by positivity)] at ht1
      have h1 : t ^ 2 * d 0 ^ 2 ≤ α * t ^ 2 * d 0 ^ 2 + t * d 1 := by
        nlinarith [mul_lt_mul_of_pos_left hlt ht0, sq_nonneg t,
          mul_nonneg (mul_nonneg hα0.le (sq_nonneg t)) (sq_nonneg (d 0))]
      rw [max_eq_right h1, max_eq_right (by positivity)]
      simp only [q2_lim, if_pos hd1]
      field_simp
      ring
    · filter_upwards [self_mem_nhdsWithin] with t ht
      have ht0 : 0 < t := ht
      rw [hq2 t ht0, EReal.coe_eq_coe_iff]
      have hd1' : d 1 ≤ 0 := not_lt.mp hd1
      have h1 : α * t ^ 2 * d 0 ^ 2 + t * d 1 ≤ t ^ 2 * d 0 ^ 2 := by
        nlinarith [sq_nonneg (d 0), sq_nonneg t, mul_nonneg (sq_nonneg t) (sq_nonneg (d 0)),
          mul_nonpos_of_nonneg_of_nonpos ht0.le hd1']
      rw [max_eq_left h1, max_eq_left (mul_nonpos_of_nonneg_of_nonpos ht0.le hd1')]
      simp only [q2_lim, if_neg hd1]
      field_simp
      ring

end FCA_chap_D_ex11
