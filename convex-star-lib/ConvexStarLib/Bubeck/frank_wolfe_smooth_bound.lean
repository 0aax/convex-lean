import ConvexStarLib.Defs

/-!
# `frank_wolfe_smooth_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/frank_wolfe_smooth_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace frank_wolfe_smooth_bound`, so the main result is `frank_wolfe_smooth_bound.frank_wolfe_smooth_bound`.
-/

namespace frank_wolfe_smooth_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem frank_wolfe_smooth_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {t : ℕ}
  (𝓧 : Set E)
  (f : E → ℝ)
  (x : ℕ → E)
  (y : ℕ → E)
  (β : ℝ) (x_star : E)
  (hβ_pos : β > 0) (ht_pos : t ≥ 1)
  (hx_init : x 0 ∈ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (hf_convex : ConvexOn ℝ 𝓧 f)
  (hf_differentiable : DifferentiableOn ℝ f 𝓧)
  (hf_beta_smooth : IsSmoothOn 𝓧 f β)
  (h_fw_seq : IsFrankWolfeSequence 𝓧 f x y (fun s => 2 / (s + 2)))
  (hx_star_mem : x_star ∈ 𝓧)
  (hx_star : IsMinOn f 𝓧 x_star) :
  let R := sSup {v | ∃ a ∈ 𝓧, ∃ b ∈ 𝓧, v = ‖a - b‖}
  f (x t) - f x_star ≤ (2 * β * R^2) / (t + 2) := by
  intro R
  obtain ⟨hxmem, hymem, hγ, hstep, hdiff, hmin⟩ := h_fw_seq
  -- diameter bound
  have hbdd : BddAbove {v | ∃ a ∈ 𝓧, ∃ b ∈ 𝓧, v = ‖a - b‖} := by
    obtain ⟨M, hM⟩ := h𝓧_compact.isBounded.exists_norm_le
    refine ⟨M + M, ?_⟩
    rintro v ⟨a, ha, b, hb, rfl⟩
    calc ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
      _ ≤ M + M := add_le_add (hM a ha) (hM b hb)
  have hR : ∀ a ∈ 𝓧, ∀ b ∈ 𝓧, ‖a - b‖ ≤ R := fun a ha b hb =>
    le_csSup hbdd ⟨a, ha, b, hb, rfl⟩
  -- derivative along a segment
  have hpath : ∀ a b : E, ∀ τ : ℝ, a + τ • (b - a) ∈ 𝓧 →
      HasDerivAt (fun τ : ℝ => f (a + τ • (b - a))) (fderiv ℝ f (a + τ • (b - a)) (b - a)) τ := by
    intro a b τ hτ
    have h1 : HasDerivAt (fun τ : ℝ => a + τ • (b - a)) (b - a) τ := by
      simpa using ((hasDerivAt_id τ).smul_const (b - a)).const_add a
    exact (hdiff _ hτ).hasFDerivAt.comp_hasDerivAt τ h1
  -- descent lemma
  have descent : ∀ a ∈ 𝓧, ∀ b ∈ 𝓧,
      f b ≤ f a + fderiv ℝ f a (b - a) + β / 2 * ‖b - a‖ ^ 2 := by
    intro a ha b hb
    set g : ℝ → ℝ := fun τ => f (a + τ • (b - a)) - τ * fderiv ℝ f a (b - a)
      - β / 2 * τ ^ 2 * ‖b - a‖ ^ 2 with hg
    have hmemI : ∀ τ ∈ Set.Icc (0:ℝ) 1, a + τ • (b - a) ∈ 𝓧 := fun τ hτ =>
      h𝓧_convex.add_smul_sub_mem ha hb hτ
    have hgd : ∀ τ ∈ Set.Icc (0:ℝ) 1, HasDerivAt g
        (fderiv ℝ f (a + τ • (b - a)) (b - a) - fderiv ℝ f a (b - a)
          - β * τ * ‖b - a‖ ^ 2) τ := by
      intro τ hτ
      have h1 := hpath a b τ (hmemI τ hτ)
      have h2 : HasDerivAt (fun τ : ℝ => τ * fderiv ℝ f a (b - a)) (fderiv ℝ f a (b - a)) τ := by
        simpa using (hasDerivAt_id τ).mul_const (fderiv ℝ f a (b - a))
      have h3 : HasDerivAt (fun τ : ℝ => β / 2 * τ ^ 2 * ‖b - a‖ ^ 2)
          (β * τ * ‖b - a‖ ^ 2) τ := by
        have := ((hasDerivAt_pow 2 τ).const_mul (β / 2)).mul_const (‖b - a‖ ^ 2)
        convert this using 1
        push_cast
        ring
      exact (h1.sub h2).sub h3
    have hanti : AntitoneOn g (Set.Icc 0 1) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1)
      · intro τ hτ
        exact (hgd τ hτ).continuousAt.continuousWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        exact (hgd τ (Set.Ioo_subset_Icc_self hτ)).hasDerivWithinAt
      · intro τ hτ
        rw [interior_Icc] at hτ
        have hτ0 : 0 ≤ τ := hτ.1.le
        have key : fderiv ℝ f (a + τ • (b - a)) (b - a) - fderiv ℝ f a (b - a)
            ≤ β * τ * ‖b - a‖ ^ 2 := by
          have hz := hmemI τ (Set.Ioo_subset_Icc_self hτ)
          calc fderiv ℝ f (a + τ • (b - a)) (b - a) - fderiv ℝ f a (b - a)
              = (fderiv ℝ f (a + τ • (b - a)) - fderiv ℝ f a) (b - a) := by simp
            _ ≤ ‖(fderiv ℝ f (a + τ • (b - a)) - fderiv ℝ f a) (b - a)‖ :=
                (le_abs_self _).trans (le_of_eq (Real.norm_eq_abs _).symm)
            _ ≤ ‖fderiv ℝ f (a + τ • (b - a)) - fderiv ℝ f a‖ * ‖b - a‖ :=
                ContinuousLinearMap.le_opNorm _ _
            _ ≤ β * ‖(a + τ • (b - a)) - a‖ * ‖b - a‖ := by
                gcongr
                exact hf_beta_smooth _ hz _ ha
            _ = β * τ * ‖b - a‖ ^ 2 := by
                rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0]
                ring
        linarith
    have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one) zero_le_one
    simp [g] at this
    rw [map_sub]
    linarith
  -- first-order convexity
  have foc : ∀ a ∈ 𝓧, ∀ b ∈ 𝓧, f a + fderiv ℝ f a (b - a) ≤ f b := by
    intro a ha b hb
    let L : ℝ →ᵃ[ℝ] E := AffineMap.lineMap a b
    have hL : ∀ τ : ℝ, L τ = a + τ • (b - a) := by
      intro τ
      simp [L, AffineMap.lineMap_apply]
      abel
    have hmaps : Set.MapsTo L (Set.Icc 0 1) 𝓧 := by
      intro τ hτ
      rw [hL]
      exact h𝓧_convex.add_smul_sub_mem ha hb hτ
    have hconv : ConvexOn ℝ (Set.Icc 0 1) (f ∘ L) :=
      (hf_convex.comp_affineMap L).subset hmaps (convex_Icc 0 1)
    have hd : HasDerivAt (f ∘ L) (fderiv ℝ f a (b - a)) 0 := by
      have := hpath a b 0 (by simpa using ha)
      have heq : (f ∘ L) = fun τ : ℝ => f (a + τ • (b - a)) := by
        funext τ; simp [hL]
      rw [heq]
      simpa using this
    have := hconv.le_slope_of_hasDerivAt (Set.left_mem_Icc.2 zero_le_one)
      (Set.right_mem_Icc.2 zero_le_one) zero_lt_one hd
    rw [slope_def_field] at this
    simp [hL] at this
    rw [map_sub]
    linarith
  -- one-step recurrence
  have hrec : ∀ s : ℕ, f (x (s+1)) - f x_star ≤
      (1 - 2 / ((s:ℝ) + 2)) * (f (x s) - f x_star) + β / 2 * (2 / ((s:ℝ) + 2))^2 * R^2 := by
    intro s
    set γ : ℝ := 2 / ((s:ℝ) + 2) with hγdef
    have hγ0 : 0 ≤ γ := by positivity
    have hxs := hxmem s
    have hys := hymem s
    have hxs1 := hxmem (s+1)
    have hx1 : x (s+1) - x s = γ • (y s - x s) := by
      rw [hstep s]
      simp only [frankWolfeStep]
      rw [smul_sub, sub_smul, one_smul]
      abel
    have hd := descent (x s) hxs (x (s+1)) hxs1
    rw [hx1, map_smul, smul_eq_mul, norm_smul, Real.norm_of_nonneg hγ0] at hd
    have hlin : fderiv ℝ f (x s) (y s - x s) ≤ fderiv ℝ f (x s) (x_star - x s) := by
      have := hmin s hx_star_mem
      simp only [map_sub]
      simp at this
      linarith
    have hfoc := foc (x s) hxs x_star hx_star_mem
    have hRs : ‖y s - x s‖ ≤ R := hR _ hys _ hxs
    have hn0 : 0 ≤ ‖y s - x s‖ := norm_nonneg _
    have hsq : ‖y s - x s‖^2 ≤ R^2 := pow_le_pow_left₀ hn0 hRs 2
    have h1 : γ * fderiv ℝ f (x s) (y s - x s) ≤ γ * (f x_star - f (x s)) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ0
    have h2 : (γ * ‖y s - x s‖) ^ 2 ≤ γ^2 * R^2 := by
      rw [mul_pow]; exact mul_le_mul_of_nonneg_left hsq (sq_nonneg γ)
    have h3 : β / 2 * (γ * ‖y s - x s‖) ^ 2 ≤ β / 2 * (γ^2 * R^2) :=
      mul_le_mul_of_nonneg_left h2 (by linarith)
    nlinarith
  -- induction
  have main : ∀ s : ℕ, f (x (s+1)) - f x_star ≤ 2 * β * R^2 / ((s:ℝ) + 3) := by
    intro s
    induction s with
    | zero =>
      have := hrec 0
      norm_num at this
      have hR2 : 0 ≤ β * R^2 := by positivity
      norm_num
      linarith
    | succ n ih =>
      have h := hrec (n+1)
      push_cast at h
      have hc : 0 ≤ β * R^2 := by positivity
      have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
      have e1 : (1 - 2 / ((n:ℝ) + 1 + 2)) = ((n:ℝ) + 1) / ((n:ℝ) + 3) := by
        field_simp; ring
      have e1nn : 0 ≤ ((n:ℝ) + 1) / ((n:ℝ) + 3) := by positivity
      rw [e1] at h
      have h' := mul_le_mul_of_nonneg_left ih e1nn
      have key : ((n:ℝ) + 1) / ((n:ℝ) + 3) * (2 * β * R^2 / ((n:ℝ) + 3))
          + β / 2 * (2 / ((n:ℝ) + 1 + 2))^2 * R^2
          = 2 * (β * R^2) * ((n:ℝ) + 2) / ((n:ℝ) + 3)^2 := by
        field_simp; ring
      have key2 : 2 * (β * R^2) * ((n:ℝ) + 2) / ((n:ℝ) + 3)^2 ≤ 2 * β * R^2 / ((n:ℝ) + 4) := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      push_cast
      have e2 : (n:ℝ) + 1 + 3 = (n:ℝ) + 4 := by ring
      rw [e2]
      linarith
  obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
  have := main s
  push_cast
  have e : (s:ℝ) + 1 + 2 = (s:ℝ) + 3 := by ring
  rw [e]
  exact this

end frank_wolfe_smooth_bound
