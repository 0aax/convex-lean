import ConvexStarLib.Defs

/-!
# `FISTA_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/FISTA_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FISTA_bound`, so the main result is `FISTA_bound.FISTA_bound`.
-/

namespace FISTA_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FISTA_bound
  {n t : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → ℝ)
  (g : EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → EuclideanSpace ℝ (Fin n))
  (y : ℕ → EuclideanSpace ℝ (Fin n))
  (lambda : ℕ → ℝ)
  (β : ℝ)
  (x_star : EuclideanSpace ℝ (Fin n))
  (hβ_pos : β > 0)
  (ht_one : t ≥ 1)
  (hg_convex : ConvexOn ℝ Set.univ g)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_differentiable : Differentiable ℝ f)
  (hf_beta_smooth : LipschitzWith (Real.toNNReal β) (gradient f))
  (h_ista_seq : IsFISTASequence f g x y lambda β)
  (hx_star : IsMinOn (f + g) Set.univ x_star) :
  f (y (t + 1)) + g (y (t + 1)) - (f x_star + g x_star)
  ≤ (2 * β) * ‖x 0 - x_star‖ ^ 2 / (t + 1 : ℝ) ^ 2 := by
  -- elementary real arithmetic used at the very end
  have final_arith : ∀ (d l N : ℝ) (k : ℕ), ((k : ℝ) + 2) / 2 ≤ l →
      l ^ 2 * d ≤ β / 2 * N ^ 2 → d ≤ 2 * β * N ^ 2 / (((k + 1 : ℕ) : ℝ) + 1) ^ 2 := by
    intro d l N k h2 hD0
    have hc : ((k + 1 : ℕ) : ℝ) + 1 = (k : ℝ) + 2 := by push_cast; ring
    rw [hc]
    rcases le_or_gt 0 d with hpos | hneg
    · rw [le_div_iff₀ (by positivity)]
      have h3 := mul_le_mul h2 h2 (by positivity)
        ((div_nonneg (by positivity) zero_le_two).trans h2)
      have h4 : ((k : ℝ) + 2) ^ 2 ≤ 4 * l ^ 2 := by linear_combination 4 * h3
      calc d * ((k : ℝ) + 2) ^ 2 ≤ d * (4 * l ^ 2) := mul_le_mul_of_nonneg_left h4 hpos
        _ = 4 * (l ^ 2 * d) := by ring
        _ ≤ 4 * (β / 2 * N ^ 2) := by linear_combination 4 * hD0
        _ = 2 * β * N ^ 2 := by ring
    · exact hneg.le.trans (by positivity)
  -- first-order characterization of convexity for a differentiable function
  have conv_first_order : ∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [CompleteSpace F] (f : F → ℝ), ConvexOn ℝ Set.univ f → Differentiable ℝ f →
      ∀ x z : F, f x + ⟪gradient f x, z - x⟫_ℝ ≤ f z := by
    intro F _ _ _ f hf hd x z
    have hphi : ConvexOn ℝ Set.univ (f ∘ (AffineMap.lineMap x z : ℝ →ᵃ[ℝ] F)) := by
      have := hf.comp_affineMap (AffineMap.lineMap x z : ℝ →ᵃ[ℝ] F)
      simpa only [Set.preimage_univ] using this
    have hder : HasDerivAt (f ∘ (AffineMap.lineMap x z : ℝ →ᵃ[ℝ] F))
        (fderiv ℝ f x (z - x)) 0 := by
      have h1 : HasFDerivAt f (fderiv ℝ f (AffineMap.lineMap x z (0:ℝ)))
          (AffineMap.lineMap x z (0:ℝ)) :=
        (hd _).hasFDerivAt
      have h2 := h1.comp_hasDerivAt (0:ℝ)
        (AffineMap.hasDerivAt_lineMap (a := x) (b := z) (x := (0:ℝ)))
      simpa only [AffineMap.lineMap_apply_zero] using h2
    have := hphi.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
    rw [slope_def_field] at this
    simp only [Function.comp_apply, AffineMap.lineMap_apply_one, AffineMap.lineMap_apply_zero,
      sub_zero, div_one] at this
    rw [inner_gradient_left (hd x)]
    linear_combination this
  -- descent lemma for a function with `β`-Lipschitz gradient
  have descent_lemma : ∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [CompleteSpace F] (f : F → ℝ), Differentiable ℝ f →
      LipschitzWith (Real.toNNReal β) (gradient f) →
      ∀ x y : F, f y ≤ f x + ⟪gradient f x, y - x⟫_ℝ + β / 2 * ‖y - x‖ ^ 2 := by
    intro F _ _ _ f hd hL x y
    set d := y - x with hd_def
    let phi : ℝ → ℝ := fun s =>
      f (x + s • d) - s * ⟪gradient f x, d⟫_ℝ - β / 2 * s ^ 2 * ‖d‖ ^ 2
    have hphid : ∀ s, HasDerivAt phi
        (⟪gradient f (x + s • d), d⟫_ℝ - ⟪gradient f x, d⟫_ℝ - β * s * ‖d‖ ^ 2) s := by
      intro s
      have h1 : HasDerivAt (fun s : ℝ => x + s • d) d s := by
        simpa only [one_smul] using ((hasDerivAt_id' s).smul_const d).const_add x
      have h2 : HasDerivAt (fun s => f (x + s • d)) (fderiv ℝ f (x + s • d) d) s :=
        (hd _).hasFDerivAt.comp_hasDerivAt s h1
      rw [← inner_gradient_left (hd _)] at h2
      have h3 : HasDerivAt (fun s : ℝ => s * ⟪gradient f x, d⟫_ℝ)
          ⟪gradient f x, d⟫_ℝ s := by
        simpa using (hasDerivAt_id s).mul_const ⟪gradient f x, d⟫_ℝ
      have h4 : HasDerivAt (fun s : ℝ => β / 2 * s ^ 2 * ‖d‖ ^ 2)
          (β * s * ‖d‖ ^ 2) s := by
        have := ((hasDerivAt_pow 2 s).const_mul (β / 2)).mul_const (‖d‖ ^ 2)
        convert this using 1
        push_cast
        ring
      exact (h2.sub h3).sub h4
    have hanti : AntitoneOn phi (Set.Icc 0 1) := by
      apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1)
      · exact fun s _ => (hphid s).continuousAt.continuousWithinAt
      · intro s _
        exact (hphid s).differentiableAt.differentiableWithinAt
      · intro s hs
        rw [interior_Icc] at hs
        rw [(hphid s).deriv]
        have hs0 : 0 ≤ s := hs.1.le
        have hlip :
            ‖gradient f (x + s • d) - gradient f x‖ ≤ β * ‖(x + s • d) - x‖ := by
          have := hL.norm_sub_le (x + s • d) x
          rwa [Real.coe_toNNReal _ hβ_pos.le] at this
        have hnorm : ‖(x + s • d) - x‖ = s * ‖d‖ := by
          rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hs0]
        have hinner : ⟪gradient f (x + s • d) - gradient f x, d⟫_ℝ ≤
            ‖gradient f (x + s • d) - gradient f x‖ * ‖d‖ :=
          real_inner_le_norm _ _
        rw [inner_sub_left] at hinner
        rw [hnorm] at hlip
        have := mul_le_mul_of_nonneg_right hlip (norm_nonneg d)
        linarith
    have := hanti (Set.left_mem_Icc.2 zero_le_one) (Set.right_mem_Icc.2 zero_le_one)
      zero_le_one
    simp only [phi] at this
    simp only [one_smul, zero_smul, add_zero, one_mul, zero_mul, one_pow, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, sub_zero, mul_one] at this
    rw [hd_def, add_sub_cancel] at this
    linarith
  -- optimality condition for a proximal step of a convex function
  have prox_opt : ∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (g : F → ℝ), ConvexOn ℝ Set.univ g → ∀ v p : F,
      (∀ z, g p + β / 2 * ‖p - v‖ ^ 2 ≤ g z + β / 2 * ‖z - v‖ ^ 2) →
      ∀ z, g p + β * ⟪v - p, z - p⟫_ℝ ≤ g z := by
    intro F _ _ g hg v p hp z
    set A := g z - g p - β * ⟪v - p, z - p⟫_ℝ with hA
    set B := β / 2 * ‖z - p‖ ^ 2 with hB
    have hB0 : 0 ≤ B := by positivity
    have key : ∀ s : ℝ, 0 < s → s ≤ 1 → 0 ≤ A + s * B := by
      intro s hs0 hs1
      have hconv := hg.2 (Set.mem_univ p) (Set.mem_univ z) (sub_nonneg.mpr hs1) hs0.le
        (sub_add_cancel 1 s)
      have h1 := hp ((1 - s) • p + s • z)
      have hw : (1 - s) • p + s • z - v = (p - v) + s • (z - p) := by
        simp only [sub_smul, one_smul, smul_sub]; abel
      rw [hw, norm_add_sq_real, norm_smul, real_inner_smul_right,
        Real.norm_of_nonneg hs0.le] at h1
      simp only [smul_eq_mul] at hconv
      have hneg : ⟪v - p, z - p⟫_ℝ = - ⟪p - v, z - p⟫_ℝ := by rw [← inner_neg_left, neg_sub]
      have : 0 ≤ s * (A + s * B) := by
        rw [hA, hB, hneg]
        linear_combination h1 + hconv
      exact (mul_nonneg_iff_of_pos_left hs0).mp this
    by_contra hcon
    push_neg at hcon
    have hAneg : A < 0 := by rw [hA]; linarith
    have hBA : 0 < B - A := sub_pos.mpr (hAneg.trans_le hB0)
    have hs0 : 0 < -A / (B - A) := div_pos (neg_pos.mpr hAneg) hBA
    have hs1 : -A / (B - A) ≤ 1 := (div_le_one hBA).mpr (by linear_combination hB0)
    have h := key _ hs0 hs1
    have e : (A + -A / (B - A) * B) * (B - A) = -A ^ 2 := by
      field_simp; ring
    have h' := mul_nonneg h hBA.le
    rw [e] at h'
    have := pow_pos (neg_pos.mpr hAneg) 2
    rw [neg_sq] at this
    exact (not_le.mpr (neg_lt_zero.mpr this)) h'
  -- the fundamental inequality of a proximal gradient step
  have key_ineq : ∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      [CompleteSpace F] (f g : F → ℝ), ConvexOn ℝ Set.univ g → ConvexOn ℝ Set.univ f →
      Differentiable ℝ f →
      LipschitzWith (Real.toNNReal β) (gradient f) → ∀ x p : F,
      (∀ w, g p + β / 2 * ‖p - (x - (1 / β) • gradient f x)‖ ^ 2 ≤
        g w + β / 2 * ‖w - (x - (1 / β) • gradient f x)‖ ^ 2) →
      ∀ z, f p + g p - (f z + g z) ≤ β * ⟪x - p, x - z⟫_ℝ - β / 2 * ‖x - p‖ ^ 2 := by
    intro F _ _ _ f g hg hf hd hL x p hprox z
    have h1 := prox_opt g hg _ p hprox z
    have h2 := descent_lemma f hd hL x p
    have h3 := conv_first_order f hf hd x z
    have e1 : x - (1 / β) • gradient f x - p = (x - p) - (1 / β) • gradient f x := by
      abel
    have e2 : z - p = (x - p) - (x - z) := by abel
    have e3 : p - x = -(x - p) := by abel
    have e4 : z - x = -(x - z) := by abel
    have i1 : ⟪x - p, (x - p) - (x - z)⟫_ℝ = ‖x - p‖ ^ 2 - ⟪x - p, x - z⟫_ℝ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]
    have i2 : ⟪gradient f x, (x - p) - (x - z)⟫_ℝ =
        ⟪gradient f x, x - p⟫_ℝ - ⟪gradient f x, x - z⟫_ℝ := by
      rw [inner_sub_right]
    rw [e1, e2, inner_sub_left, real_inner_smul_left, i1, i2] at h1
    rw [e3, inner_neg_right, norm_neg] at h2
    rw [e4, inner_neg_right] at h3
    have hb : β * (1 / β) = 1 := by field_simp
    linear_combination
      h1 + h2 + h3 + (⟪gradient f x, x - p⟫_ℝ - ⟪gradient f x, x - z⟫_ℝ) * hb
  -- the proximal steps, read off in real arithmetic
  have hprox_all : ∀ t w,
      g (y (t + 1)) + β / 2 * ‖y (t + 1) - (x t - (1 / β) • gradient f (x t))‖ ^ 2 ≤
        g w + β / 2 * ‖w - (x t - (1 / β) • gradient f (x t))‖ ^ 2 := by
    intro t w
    have h := (h_ista_seq.2.2.2.1 t).2 w
    have hc : (2 * (1 / β))⁻¹ = β / 2 := by field_simp
    simp only [hc] at h
    exact_mod_cast h
  obtain ⟨hl0, hxy0, hlrec, -, hxrec⟩ := h_ista_seq
  simp only at hxrec
  -- facts about the sequence `lambda`
  have hlnn : ∀ s, 0 ≤ lambda s := by
    intro s
    cases s with
    | zero => rw [hl0]
    | succ s => rw [hlrec s]; positivity
  have hlstep : ∀ s, lambda s + 1 / 2 ≤ lambda (s + 1) := by
    intro s
    rw [hlrec s]
    have h1 : 2 * lambda s ≤ √(1 + 4 * lambda s ^ 2) := by
      rw [show 2 * lambda s = √((2 * lambda s) ^ 2) from
        (Real.sqrt_sq (by linarith [hlnn s])).symm]
      exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (lambda s), mul_pow 2 (lambda s) 2])
    linarith
  have hl1 : lambda 1 = 1 := by
    rw [hlrec 0, hl0]; norm_num
  have hlge1 : ∀ s, 1 ≤ lambda (s + 1) := by
    intro s
    induction s with
    | zero => rw [hl1]
    | succ k ih => linarith [hlstep (k + 1)]
  have hlge : ∀ s : ℕ, ((s : ℝ) + 2) / 2 ≤ lambda (s + 1) := by
    intro s
    induction s with
    | zero => rw [hl1]; norm_num
    | succ k ih => have := hlstep (k + 1); push_cast; linarith
  have hlsq : ∀ s, lambda (s + 1) ^ 2 - lambda (s + 1) = lambda s ^ 2 := by
    intro s
    rw [hlrec s]
    have h := Real.sq_sqrt (show (0:ℝ) ≤ 1 + 4 * lambda s ^ 2 by positivity)
    linear_combination h / 4
  -- the Lyapunov argument, in an arbitrary real inner product space
  have lyap : ∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
      (Φ : F → ℝ) (x y : ℕ → F) (x_star : F), x 0 = y 0 →
      (∀ s, x (s + 1) = (1 - (1 - lambda s) / lambda (s + 1)) • y (s + 1) +
        ((1 - lambda s) / lambda (s + 1)) • y s) →
      (∀ s z, Φ (y (s + 1 + 1)) - Φ z ≤
        β * ⟪x (s + 1) - y (s + 1 + 1), x (s + 1) - z⟫_ℝ -
          β / 2 * ‖x (s + 1) - y (s + 1 + 1)‖ ^ 2) →
      ∀ s, lambda s ^ 2 * (Φ (y (s + 1)) - Φ x_star) ≤ β / 2 * ‖x 0 - x_star‖ ^ 2 := by
    intro F _ _ Φ x y x_star hxy0 hxrec hkey
    -- the momentum step rewritten
    have hupd : ∀ s, lambda (s + 1) • x (s + 1) - (lambda (s + 1) - 1) • y (s + 1) =
        lambda s • y (s + 1) - (lambda s - 1) • y s := by
      intro s
      have hpos : lambda (s + 1) ≠ 0 := by linarith [hlge1 s]
      rw [hxrec s]
      have c1 : lambda (s + 1) * (1 - (1 - lambda s) / lambda (s + 1)) =
          lambda (s + 1) - 1 + lambda s := by
        field_simp; ring
      have c2 : lambda (s + 1) * ((1 - lambda s) / lambda (s + 1)) = 1 - lambda s := by
        field_simp
      rw [smul_add, smul_smul, smul_smul, c1, c2]
      module
    have hx1 : x 1 = x 0 := by
      rw [hxrec 0, hl0, hl1, hxy0]; norm_num
    -- Lyapunov quantities
    set D := fun s => Φ (y s) - Φ x_star with hD
    set u := fun s => lambda s • x s - (lambda s - 1) • y s - x_star with hu
    have hstep : ∀ s, lambda (s + 1) ^ 2 * D (s + 1 + 1) + β / 2 * ‖u (s + 1 + 1)‖ ^ 2 ≤
        lambda s ^ 2 * D (s + 1) + β / 2 * ‖u (s + 1)‖ ^ 2 := by
      intro s
      have ha := hkey s (y (s + 1))
      have hb := hkey s x_star
      have hsq := hlsq s
      have hL1 : 1 ≤ lambda (s + 1) := hlge1 s
      set L := lambda (s + 1) with hL
      set a := x (s + 1) - y (s + 1 + 1) with ha_def
      have hu2 : u (s + 1 + 1) = u (s + 1) - L • a := by
        simp only [hu]
        rw [hupd (s + 1)]
        module
      have hu1 : u (s + 1) = (L - 1) • (x (s + 1) - y (s + 1)) + (x (s + 1) - x_star) := by
        simp only [hu]; module
      have hL0 : 0 ≤ L := zero_le_one.trans hL1
      have hnorm : ‖u (s + 1 + 1)‖ ^ 2 =
          ‖u (s + 1)‖ ^ 2 - 2 * L * ⟪a, u (s + 1)⟫_ℝ + L ^ 2 * ‖a‖ ^ 2 := by
        rw [hu2, norm_sub_sq_real, real_inner_smul_right, norm_smul,
          Real.norm_of_nonneg hL0, real_inner_comm]
        ring
      have hinner : ⟪a, u (s + 1)⟫_ℝ =
          (L - 1) * ⟪a, x (s + 1) - y (s + 1)⟫_ℝ + ⟪a, x (s + 1) - x_star⟫_ℝ := by
        rw [hu1, inner_add_right, real_inner_smul_right]
      rw [hnorm, hinner, ← hsq]
      have m1 := mul_le_mul_of_nonneg_left ha (mul_nonneg hL0 (sub_nonneg.mpr hL1))
      have m2 := mul_le_mul_of_nonneg_left hb hL0
      simp only [hD]
      linear_combination m1 + m2
    have htel : ∀ s, lambda s ^ 2 * D (s + 1) + β / 2 * ‖u (s + 1)‖ ^ 2 ≤
        β / 2 * ‖x 0 - x_star‖ ^ 2 := by
      intro s
      induction s with
      | zero =>
        have : u (0 + 1) = x 0 - x_star := by
          simp only [hu, Nat.zero_add]; rw [hl1, hx1]; simp
        rw [hl0, this]; simp
      | succ k ih => exact (hstep k).trans ih
    intro s
    have : 0 ≤ β / 2 * ‖u (s + 1)‖ ^ 2 := by positivity
    exact (le_add_of_nonneg_right this).trans (htel s)
  have hkey : ∀ s z, (fun w => f w + g w) (y (s + 1 + 1)) - (fun w => f w + g w) z ≤
      β * ⟪x (s + 1) - y (s + 1 + 1), x (s + 1) - z⟫_ℝ -
        β / 2 * ‖x (s + 1) - y (s + 1 + 1)‖ ^ 2 := fun s z =>
    key_ineq f g hg_convex hf_convex hf_differentiable hf_beta_smooth
      (x (s + 1)) (y (s + 1 + 1)) (hprox_all (s + 1)) z
  obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
  exact final_arith _ (lambda (k + 1)) ‖x 0 - x_star‖ k (hlge k)
    (lyap (fun w => f w + g w) x y x_star hxy0 hxrec hkey (k + 1))

end FISTA_bound
