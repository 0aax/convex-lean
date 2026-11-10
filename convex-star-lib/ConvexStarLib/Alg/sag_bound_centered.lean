import ConvexStarLib.Defs

/-!
# `sag_bound_centered`

Source: Schmidt, Le Roux & Bach, 'Minimizing Finite Sums with the Stochastic Average Gradient' (2013), as stated in Tibshirani, Modern Stochastic Methods (10-725).

Statement from the `convex-eval-v28-2h/sag_bound_centered` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace sag_bound_centered`, so the main result is `sag_bound_centered.sag_bound_centered`.
-/

namespace sag_bound_centered

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


/-! ## Analytic lemmas -/
section Analytic
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

lemma sag_line_hasDerivAt {Φ : E → ℝ} {G : E → E} (hG : ∀ x, HasGradientAt Φ (G x) x)
    (x v : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Φ (x + s • v)) (inner ℝ (G (x + t • v)) v) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := (hG (x + t • v)).hasFDerivAt
  have h3 := h2.comp_hasDerivAt t h1
  simpa [InnerProductSpace.toDual_apply_apply] using h3

omit [CompleteSpace E] in
lemma sag_line_convex {Φ : E → ℝ} (hconv : ConvexOn ℝ Set.univ Φ) (x v : E) :
    ConvexOn ℝ Set.univ (fun s : ℝ => Φ (x + s • v)) := by
  refine ⟨convex_univ, ?_⟩
  intro a _ b _ μ ν hμ hν hμν
  have heq : x + (μ • a + ν • b) • v = μ • (x + a • v) + ν • (x + b • v) := by
    obtain rfl : ν = 1 - μ := by linarith
    simp only [smul_eq_mul]
    module
  simp only
  rw [heq]
  exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν

lemma sag_first_order {Φ : E → ℝ} {G : E → E} (hconv : ConvexOn ℝ Set.univ Φ)
    (hG : ∀ x, HasGradientAt Φ (G x) x) (x y : E) :
    Φ x + inner ℝ (G x) (y - x) ≤ Φ y := by
  have hd := sag_line_hasDerivAt hG x (y - x) 0
  have h := (sag_line_convex hconv x (y - x)).le_slope_of_hasDerivAt (Set.mem_univ 0)
    (Set.mem_univ 1) zero_lt_one hd
  simp only [zero_smul, add_zero, one_smul, slope_def_field, sub_zero, div_one,
    add_sub_cancel] at h
  linarith

lemma sag_descent {Φ : E → ℝ} {G : E → E} {K : ℝ≥0} (hG : ∀ x, HasGradientAt Φ (G x) x)
    (hL : LipschitzWith K G) (x y : E) :
    Φ y ≤ Φ x + inner ℝ (G x) (y - x) + ((K : ℝ) / 2) * ‖y - x‖ ^ 2 := by
  let ψ : ℝ → ℝ := fun t => Φ (x + t • (y - x)) - t * inner ℝ (G x) (y - x)
    - ((K : ℝ) / 2) * t ^ 2 * ‖y - x‖ ^ 2
  let ψ' : ℝ → ℝ := fun t => inner ℝ (G (x + t • (y - x))) (y - x) - inner ℝ (G x) (y - x)
    - (K : ℝ) * t * ‖y - x‖ ^ 2
  have hψ : ∀ t, HasDerivAt ψ (ψ' t) t := by
    intro t
    have h1 := sag_line_hasDerivAt hG x (y - x) t
    have h2 : HasDerivAt (fun t : ℝ => t * inner ℝ (G x) (y - x)) (inner ℝ (G x) (y - x)) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (G x) (y - x))
    have h3 : HasDerivAt (fun t : ℝ => ((K : ℝ) / 2) * t ^ 2 * ‖y - x‖ ^ 2)
        ((K : ℝ) * t * ‖y - x‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul ((K : ℝ) / 2)).mul_const (‖y - x‖ ^ 2)
      convert this using 1
      push_cast
      ring
    exact (h1.sub h2).sub h3
  have hψ'_nonpos : ∀ t, 0 ≤ t → ψ' t ≤ 0 := by
    intro t ht
    have hc : inner ℝ (G (x + t • (y - x)) - G x) (y - x)
        ≤ ‖G (x + t • (y - x)) - G x‖ * ‖y - x‖ := real_inner_le_norm _ _
    have hl : ‖G (x + t • (y - x)) - G x‖ ≤ (K : ℝ) * ‖(x + t • (y - x)) - x‖ := by
      have := hL.dist_le_mul (x + t • (y - x)) x
      simpa only [dist_eq_norm] using this
    have hn : ‖(x + t • (y - x)) - x‖ = t * ‖y - x‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht]
    rw [inner_sub_left] at hc
    have h4 : ‖G (x + t • (y - x)) - G x‖ * ‖y - x‖ ≤ (K : ℝ) * (t * ‖y - x‖) * ‖y - x‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [← hn]; exact hl
    simp only [ψ']
    nlinarith
  have hanti : AntitoneOn ψ (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici 0) (f' := ψ')
    · exact fun t _ => (hψ t).continuousAt.continuousWithinAt
    · intro t _; exact (hψ t).hasDerivWithinAt
    · intro t ht; rw [interior_Ici] at ht; exact hψ'_nonpos t (le_of_lt ht)
  have h01 := hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr zero_le_one) zero_le_one
  simp only [ψ, zero_smul, add_zero, one_smul, zero_mul, sub_zero, one_mul, add_sub_cancel,
    one_pow, mul_one] at h01
  simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul,
    sub_zero] at h01
  linarith

lemma sag_cocoercive {Φ : E → ℝ} {G : E → E} {β : ℝ} (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ Φ)
    (hG : ∀ x, HasGradientAt Φ (G x) x) (hL : LipschitzWith (Real.toNNReal β) G) (x y : E) :
    Φ x + inner ℝ (G x) (y - x) + (1 / (2 * β)) * ‖G y - G x‖ ^ 2 ≤ Φ y := by
  have hβ' : ((Real.toNNReal β : ℝ≥0) : ℝ) = β := Real.coe_toNNReal _ hβ.le
  have h1 := sag_first_order hconv hG x (y - (1 / β) • (G y - G x))
  have h2 := sag_descent hG hL y (y - (1 / β) • (G y - G x))
  rw [hβ'] at h2
  have e1 : y - (1 / β) • (G y - G x) - x = (y - x) - (1 / β) • (G y - G x) := by abel
  have e2 : y - (1 / β) • (G y - G x) - y = -((1 / β) • (G y - G x)) := by abel
  rw [e1, inner_sub_right, inner_smul_right] at h1
  rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity)] at h2
  have e3 : inner ℝ (G y) (G y - G x) - inner ℝ (G x) (G y - G x) = ‖G y - G x‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have key : (1 / β) * inner ℝ (G y) (G y - G x) - (1 / β) * inner ℝ (G x) (G y - G x)
      = (1 / β) * ‖G y - G x‖ ^ 2 := by rw [← mul_sub, e3]
  have e4 : β / 2 * (1 / β * ‖G y - G x‖) ^ 2 = (1 / (2 * β)) * ‖G y - G x‖ ^ 2 := by
    field_simp
  have e5 : (1 / β) * ‖G y - G x‖ ^ 2 - (1 / (2 * β)) * ‖G y - G x‖ ^ 2
      = (1 / (2 * β)) * ‖G y - G x‖ ^ 2 := by
    field_simp; ring
  linarith

end Analytic

/-! ## Deterministic one-step Lyapunov inequality -/
section Step
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Lyapunov function for SAG. -/
noncomputable def sagLyap {m : ℕ} (α : ℝ) (xs : E) (c : Fin m → E) (fs : ℝ)
    (x : E) (y : Fin m → E) (fx : ℝ) : ℝ :=
  ‖x - (((m : ℝ) - 1) * α) • ((1 / (m : ℝ)) • ∑ i, y i) - xs‖ ^ 2
  + (17 / 8 * (m : ℝ) * α) * (fx - fs)
  + 3 * α ^ 2 * ∑ i, ‖y i - c i‖ ^ 2
  + ((m : ℝ) ^ 2 * α ^ 2 / 16) * ‖(1 / (m : ℝ)) • ∑ i, y i‖ ^ 2

omit [InnerProductSpace ℝ E] in
lemma sag_sum_update {m : ℕ} (y : Fin m → E) (j : Fin m) (v : E) :
    ∑ i, Function.update y j v i = ∑ i, y i + (v - y j) := by
  rw [Finset.sum_update_of_mem (Finset.mem_univ j),
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j) y]
  abel

omit [InnerProductSpace ℝ E] in
lemma sag_sum_update_norm {m : ℕ} (y c : Fin m → E) (j : Fin m) (v : E) :
    ∑ i, ‖Function.update y j v i - c i‖ ^ 2
      = ∑ i, ‖y i - c i‖ ^ 2 - ‖y j - c j‖ ^ 2 + ‖v - c j‖ ^ 2 := by
  rw [Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j),
    Finset.sum_eq_add_sum_diff_singleton (Finset.mem_univ j) (fun i => ‖y i - c i‖ ^ 2)]
  rw [Function.update_self]
  have : ∑ i ∈ Finset.univ \ {j}, ‖Function.update y j v i - c i‖ ^ 2
      = ∑ i ∈ Finset.univ \ {j}, ‖y i - c i‖ ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hij : i ≠ j := by simpa using hi
    rw [Function.update_of_ne hij]
  rw [this]; ring

lemma sag_exp_norm_add (u z : E) (t : ℝ) :
    ‖u + t • z‖ ^ 2 = ‖u‖ ^ 2 + 2 * t * inner ℝ u z + t ^ 2 * ‖z‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  ring

lemma sag_exp_norm_sub (A u z : E) (a t : ℝ) :
    ‖A - a • (u + t • z)‖ ^ 2 = ‖A‖ ^ 2 - 2 * a * (inner ℝ A u + t * inner ℝ A z)
      + a ^ 2 * (‖u‖ ^ 2 + 2 * t * inner ℝ u z + t ^ 2 * ‖z‖ ^ 2) := by
  rw [norm_sub_sq_real, inner_smul_right, inner_add_right, inner_smul_right, norm_smul,
    mul_pow, Real.norm_eq_abs, sq_abs, sag_exp_norm_add]
  ring

lemma sag_scalar_final (M t α nA Ay Ag yy gy gg Z Ss Ds F : ℝ)
    (hM : 1 ≤ M) (ht : t * M = 1) (hα : 0 < α)
    (hyy : 0 ≤ yy) (hgg : 0 ≤ gg) (hZ : 0 ≤ Z) (hSs : 0 ≤ Ss) (hDs : 0 ≤ Ds)
    (hgy : 2 * gy ≤ gg + yy) (hZb : Z ≤ 2 * Ss + 2 * Ds)
    (hco : F - Ag + 8 * α * (t * Ss) ≤ 0) :
    (nA - 2 * M * α * Ay + M ^ 2 * α ^ 2 * yy
      + 17 / 8 * M * α * (F - α * gy + α / 32 * yy) + 3 * α ^ 2 * Ds + M ^ 2 * α ^ 2 / 16 * yy)
    + (-2 * α) * (Ag - Ay) + (-(17 / 8) * α ^ 2) * (gg - gy)
    + (2 * M * α ^ 2 + 17 / 128 * α ^ 2 + M * α ^ 2 / 8) * (gy - yy)
    + (α ^ 2 + 17 / 256 * α ^ 2 * t + α ^ 2 / 16) * (t * Z) + 3 * α ^ 2 * (t * (Ss - Ds))
    ≤ (nA - 2 * ((M - 1) * α) * Ay + ((M - 1) * α) ^ 2 * yy) + 17 / 8 * M * α * F
      + 3 * α ^ 2 * Ds + M ^ 2 * α ^ 2 / 16 * yy - 2 * α * F := by
  have ht0 : 0 < t := by
    by_contra h; push_neg at h; nlinarith
  have ht1 : t ≤ 1 := by nlinarith
  have hα2 : 0 < α ^ 2 := by positivity
  have h1 : 0 ≤ α * (Ag - F - 8 * α * (t * Ss)) := mul_nonneg hα.le (by linarith)
  have h2 : 0 ≤ α ^ 2 * (gg + yy - 2 * gy) := mul_nonneg hα2.le (by linarith)
  have h3 : 0 ≤ α ^ 2 * t * (2 * Ss + 2 * Ds - Z) := mul_nonneg (by positivity) (by linarith)
  have h4 : 0 ≤ α ^ 2 * (t * Z) * (1 - t) := mul_nonneg (by positivity) (by linarith)
  have h5 : 0 ≤ α ^ 2 * M * yy := by positivity
  have h6 : 0 ≤ α ^ 2 * yy := by positivity
  have h7 : 0 ≤ α ^ 2 * gg := by positivity
  have h8 : 0 ≤ α ^ 2 * (t * Ss) := by positivity
  have h9 : 0 ≤ α ^ 2 * (t * Ds) := by positivity
  nlinarith

lemma sag_step_det {m : ℕ} (hm : 0 < m) {α : ℝ} (hα : 0 < α)
    (xs x : E) (y G c : Fin m → E) (fs fx : ℝ) (fnew : Fin m → ℝ)
    (hdesc : ∀ j, fnew j ≤ fx + inner ℝ ((1 / (m : ℝ)) • ∑ i, G i)
        ((x - α • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i)) - x)
        + (1 / (32 * α)) * ‖(x - α • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i)) - x‖ ^ 2)
    (hcoco : fx + inner ℝ ((1 / (m : ℝ)) • ∑ i, G i) (xs - x)
        + 8 * α * ((1 / (m : ℝ)) * ∑ i, ‖G i - c i‖ ^ 2) ≤ fs) :
    (1 / (m : ℝ)) * ∑ j, sagLyap α xs c fs
        (x - α • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i))
        (Function.update y j (G j)) (fnew j)
      ≤ sagLyap α xs c fs x y fx - 2 * α * (fx - fs) := by
  have hM1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hM0 : (0 : ℝ) < (m : ℝ) := by linarith
  have htM : (1 / (m : ℝ)) * (m : ℝ) = 1 := by field_simp
  obtain ⟨yb, hyb⟩ : ∃ v : E, v = (1 / (m : ℝ)) • ∑ i, y i := ⟨_, rfl⟩
  obtain ⟨gb, hgb⟩ : ∃ v : E, v = (1 / (m : ℝ)) • ∑ i, G i := ⟨_, rfl⟩
  rw [← hgb] at hdesc hcoco
  have hv : ∀ j, (1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i
      = yb + (1 / (m : ℝ)) • (G j - y j) := by
    intro j; rw [sag_sum_update, smul_add, hyb]
  have hper : ∀ j, sagLyap α xs c fs
      (x - α • ((1 / (m : ℝ)) • ∑ i, Function.update y j (G j) i))
      (Function.update y j (G j)) (fnew j)
      ≤ (‖x - xs‖ ^ 2 - 2 * ((m : ℝ) * α) * inner ℝ (x - xs) yb + ((m : ℝ) * α) ^ 2 * ‖yb‖ ^ 2
          + 17 / 8 * (m : ℝ) * α * (fx - α * inner ℝ gb yb + α / 32 * ‖yb‖ ^ 2 - fs)
          + 3 * α ^ 2 * ∑ i, ‖y i - c i‖ ^ 2 + (m : ℝ) ^ 2 * α ^ 2 / 16 * ‖yb‖ ^ 2)
        + (-2 * ((m : ℝ) * α) * (1 / (m : ℝ))) * inner ℝ (x - xs) (G j - y j)
        + (-(17 / 8) * (m : ℝ) * α ^ 2 * (1 / (m : ℝ))) * inner ℝ gb (G j - y j)
        + (((m : ℝ) * α) ^ 2 * 2 * (1 / (m : ℝ))
            + 17 / 8 * (m : ℝ) * α * (α / 32) * 2 * (1 / (m : ℝ))
            + (m : ℝ) ^ 2 * α ^ 2 / 16 * 2 * (1 / (m : ℝ))) * inner ℝ yb (G j - y j)
        + (((m : ℝ) * α) ^ 2 * (1 / (m : ℝ)) ^ 2
            + 17 / 8 * (m : ℝ) * α * (α / 32) * (1 / (m : ℝ)) ^ 2
            + (m : ℝ) ^ 2 * α ^ 2 / 16 * (1 / (m : ℝ)) ^ 2) * ‖G j - y j‖ ^ 2
        + 3 * α ^ 2 * (‖G j - c j‖ ^ 2 - ‖y j - c j‖ ^ 2) := by
    intro j
    have hd := hdesc j
    rw [hv j] at hd
    have e5 : x - α • (yb + (1 / (m : ℝ)) • (G j - y j)) - x
        = -(α • (yb + (1 / (m : ℝ)) • (G j - y j))) := by abel
    rw [e5, inner_neg_right, inner_smul_right, inner_add_right, inner_smul_right, norm_neg,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, sag_exp_norm_add] at hd
    have e6 : 1 / (32 * α) * (α ^ 2 * (‖yb‖ ^ 2 + 2 * (1 / (m : ℝ)) * inner ℝ yb (G j - y j)
        + (1 / (m : ℝ)) ^ 2 * ‖G j - y j‖ ^ 2))
        = α / 32 * (‖yb‖ ^ 2 + 2 * (1 / (m : ℝ)) * inner ℝ yb (G j - y j)
        + (1 / (m : ℝ)) ^ 2 * ‖G j - y j‖ ^ 2) := by
      field_simp
    rw [e6] at hd
    unfold sagLyap
    rw [hv j, sag_sum_update_norm]
    have e0 : x - α • (yb + (1 / (m : ℝ)) • (G j - y j))
        - (((m : ℝ) - 1) * α) • (yb + (1 / (m : ℝ)) • (G j - y j)) - xs
        = (x - xs) - ((m : ℝ) * α) • (yb + (1 / (m : ℝ)) • (G j - y j)) := by module
    rw [e0, sag_exp_norm_sub, sag_exp_norm_add]
    have hd' := mul_le_mul_of_nonneg_left hd (by positivity : (0 : ℝ) ≤ 17 / 8 * (m : ℝ) * α)
    linarith [hd']
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper j)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum, ← inner_sum, Finset.sum_sub_distrib] at hsum
  have hGY : ∑ i, G i - ∑ i, y i = (m : ℝ) • (gb - yb) := by
    rw [hgb, hyb, ← smul_sub, smul_smul, mul_one_div_cancel hM0.ne', one_smul]
  rw [hGY, inner_smul_right, inner_smul_right, inner_smul_right, inner_sub_right,
    inner_sub_right, inner_sub_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm gb yb] at hsum
  -- old Lyapunov value
  have hold : sagLyap α xs c fs x y fx
      = (‖x - xs‖ ^ 2 - 2 * (((m : ℝ) - 1) * α) * inner ℝ (x - xs) yb
          + (((m : ℝ) - 1) * α) ^ 2 * ‖yb‖ ^ 2)
        + 17 / 8 * (m : ℝ) * α * (fx - fs) + 3 * α ^ 2 * ∑ i, ‖y i - c i‖ ^ 2
        + (m : ℝ) ^ 2 * α ^ 2 / 16 * ‖yb‖ ^ 2 := by
    unfold sagLyap
    rw [← hyb]
    have e : x - (((m : ℝ) - 1) * α) • yb - xs = (x - xs) - (((m : ℝ) - 1) * α) • yb := by abel
    rw [e, norm_sub_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    ring
  rw [hold]
  -- auxiliary facts
  have hgy : 2 * inner ℝ gb yb ≤ ‖gb‖ ^ 2 + ‖yb‖ ^ 2 := by
    have := norm_sub_sq_real gb yb
    nlinarith [sq_nonneg ‖gb - yb‖]
  have hZb : ∑ i, ‖G i - y i‖ ^ 2 ≤ 2 * ∑ i, ‖G i - c i‖ ^ 2 + 2 * ∑ i, ‖y i - c i‖ ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    have e : G i - y i = (G i - c i) - (y i - c i) := by abel
    rw [e]
    have h1 := norm_sub_sq_real (G i - c i) (y i - c i)
    have h2 := norm_add_sq_real (G i - c i) (y i - c i)
    nlinarith [sq_nonneg ‖(G i - c i) + (y i - c i)‖]
  have hco : (fx - fs) - inner ℝ (x - xs) gb + 8 * α * (1 / (m : ℝ) * ∑ i, ‖G i - c i‖ ^ 2) ≤ 0 := by
    have e : inner ℝ gb (xs - x) = - inner ℝ (x - xs) gb := by
      rw [← neg_sub x xs, inner_neg_right, real_inner_comm]
    rw [e] at hcoco
    linarith
  have key := sag_scalar_final (m : ℝ) (1 / (m : ℝ)) α (‖x - xs‖ ^ 2) (inner ℝ (x - xs) yb)
    (inner ℝ (x - xs) gb) (‖yb‖ ^ 2) (inner ℝ gb yb) (‖gb‖ ^ 2) (∑ i, ‖G i - y i‖ ^ 2)
    (∑ i, ‖G i - c i‖ ^ 2) (∑ i, ‖y i - c i‖ ^ 2) (fx - fs) hM1 htM hα (by positivity)
    (by positivity) (Finset.sum_nonneg (fun i _ => by positivity))
    (Finset.sum_nonneg (fun i _ => by positivity)) (Finset.sum_nonneg (fun i _ => by positivity))
    hgy hZb hco
  refine le_trans (mul_le_mul_of_nonneg_left hsum (by positivity)) (le_trans (le_of_eq ?_) key)
  field_simp
  ring

end Step

/-! ## Probabilistic lemmas -/
section Prob

lemma sag_expect_indep {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m : ℕ} (_hm : 0 < m) {Z : Type*} [MeasurableSpace Z] (Zt : Ω → Z) (It : Ω → Fin m)
    (hZ : Measurable Zt) (hI : Measurable It) (hind : ProbabilityTheory.IndepFun It Zt μ)
    (hunif : ∀ i, μ (It ⁻¹' {i}) = (m : ℝ≥0∞)⁻¹) (Ψ : Z → Fin m → ℝ)
    (hΨ : ∀ j, Measurable (fun z => Ψ z j))
    (hΨint : ∀ j, Integrable (fun ω => Ψ (Zt ω) j) μ) :
    ∫ ω, Ψ (Zt ω) (It ω) ∂μ = (1 / (m : ℝ)) * ∑ j, ∫ ω, Ψ (Zt ω) j ∂μ := by
  classical
  have hpt : (fun ω => Ψ (Zt ω) (It ω)) =
      fun ω => ∑ j, (fun i : Fin m => if i = j then (1:ℝ) else 0) (It ω) * Ψ (Zt ω) j := by
    funext ω
    simp
  rw [hpt, integral_finset_sum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hind.integral_fun_comp_mul_comp (f := fun i : Fin m => if i = j then (1:ℝ) else 0)
      (g := fun z => Ψ z j) hI.aemeasurable hZ.aemeasurable
      (measurable_of_finite _).aestronglyMeasurable (hΨ j).aestronglyMeasurable]
    congr 1
    have hind1 : (fun ω => (fun i : Fin m => if i = j then (1:ℝ) else 0) (It ω)) =
        (It ⁻¹' {j}).indicator 1 := by
      funext ω
      simp [Set.indicator_apply]
    rw [hind1, integral_indicator_one (hI (measurableSet_singleton j)), measureReal_def, hunif j,
      ENNReal.toReal_inv, ENNReal.toReal_natCast, one_div]
  · intro j _
    refine (hΨint j).bdd_mul (c := 1) ?_ ?_
    · exact ((measurable_of_finite (fun i : Fin m => if i = j then (1:ℝ) else 0)).comp
        hI).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun ω => ?_)
      by_cases h : It ω = j <;> simp [h]

lemma sag_integrable_of_bdd {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {Z : Type*} [NormedAddCommGroup Z] [ProperSpace Z] [MeasurableSpace Z] [BorelSpace Z]
    {Φ : Z → ℝ} (hΦ : Continuous Φ) {F : Ω → Z} (hF : Measurable F) (R : ℝ)
    (hR : ∀ ω, ‖F ω‖ ≤ R) :
    Integrable (fun ω => Φ (F ω)) μ := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : Z) R).exists_bound_of_continuousOn hΦ.continuousOn
  refine Integrable.of_bound (hΦ.measurable.comp hF).aestronglyMeasurable C ?_
  refine Filter.Eventually.of_forall (fun ω => ?_)
  exact hC (F ω) (by simpa [Metric.mem_closedBall, dist_zero_right] using hR ω)

end Prob

/-! ## Boundedness of the iterates -/
lemma sag_bounded {m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
    (I : ℕ → Ω → Fin m) (η : ℝ) (x0 : EuclideanSpace ℝ (Fin n)) (hx0 : ∀ ω, x 0 ω = x0)
    (hsag : IsCenteredSAGIterates f x g I η) (β : ℝ)
    (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i))) :
    ∀ t, ∃ R, ∀ ω, ‖x t ω‖ ≤ R ∧ ∀ i, ‖g t i ω‖ ≤ R := by
  obtain ⟨hg0, hgI, hgne, hx⟩ := hsag
  generalize hK : Real.toNNReal β = K at hf_smooth
  have hK0 : (0:ℝ) ≤ (K : ℝ) := NNReal.coe_nonneg _
  have hgrad : ∀ i z, ‖gradient (f i) z‖ ≤ ‖gradient (f i) 0‖ + (K : ℝ) * ‖z‖ := by
    intro i z
    have h1 := (hf_smooth i).dist_le_mul z 0
    rw [dist_eq_norm, dist_eq_norm, sub_zero] at h1
    have h2 := norm_sub_norm_le (gradient (f i) z) (gradient (f i) 0)
    linarith
  obtain ⟨G, hG0, hGi⟩ : ∃ G : ℝ, 0 ≤ G ∧ ∀ i, ‖gradient (f i) 0‖ ≤ G :=
    ⟨∑ i, ‖gradient (f i) 0‖, Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i =>
      Finset.single_le_sum (f := fun j => ‖gradient (f j) 0‖) (fun j _ => norm_nonneg _)
        (Finset.mem_univ i)⟩
  have hm : (1 / (m : ℝ)) * m ≤ 1 := by
    rcases Nat.eq_zero_or_pos m with h | h
    · simp [h]
    · rw [one_div_mul_cancel]
      exact_mod_cast h.ne'
  intro t
  induction t with
  | zero =>
    obtain ⟨C, hC0, hCi⟩ : ∃ C : ℝ, 0 ≤ C ∧
        ∀ i, ‖gradient (f i) x0 - gradient (finiteSumObjective f) x0‖ ≤ C :=
      ⟨∑ i, ‖gradient (f i) x0 - gradient (finiteSumObjective f) x0‖,
        Finset.sum_nonneg (fun i _ => norm_nonneg _), fun i =>
        Finset.single_le_sum
          (f := fun j => ‖gradient (f j) x0 - gradient (finiteSumObjective f) x0‖)
          (fun j _ => norm_nonneg _) (Finset.mem_univ i)⟩
    refine ⟨‖x0‖ + C, fun ω => ⟨?_, fun i => ?_⟩⟩
    · rw [hx0 ω]
      linarith
    · rw [hg0 i ω, hx0 ω]
      have := hCi i
      have := norm_nonneg x0
      linarith
  | succ t ih =>
    obtain ⟨R, hR⟩ := ih
    refine ⟨(R + G + (K : ℝ) * R) + |η| * (R + G + (K : ℝ) * R), fun ω => ?_⟩
    have hR0 : 0 ≤ R := le_trans (norm_nonneg _) (hR ω).1
    have hKR : 0 ≤ (K : ℝ) * R := mul_nonneg hK0 hR0
    have hB0 : 0 ≤ R + G + (K : ℝ) * R := by linarith
    have hηB : 0 ≤ |η| * (R + G + (K : ℝ) * R) := mul_nonneg (abs_nonneg η) hB0
    have hgB : ∀ i, ‖g (t + 1) i ω‖ ≤ R + G + (K : ℝ) * R := by
      intro i
      by_cases hi : i = I t ω
      · subst hi
        rw [hgI t ω]
        have h1 := hgrad (I t ω) (x t ω)
        have h2 := hGi (I t ω)
        have h3 : (K : ℝ) * ‖x t ω‖ ≤ (K : ℝ) * R := mul_le_mul_of_nonneg_left (hR ω).1 hK0
        linarith
      · rw [hgne t i ω hi]
        have := (hR ω).2 i
        linarith
    refine ⟨?_, fun i => le_trans (hgB i) (by linarith)⟩
    rw [hx t ω]
    have hS : ‖∑ i, g (t + 1) i ω‖ ≤ m * (R + G + (K : ℝ) * R) := by
      calc ‖∑ i, g (t + 1) i ω‖ ≤ ∑ i, ‖g (t + 1) i ω‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin m, (R + G + (K : ℝ) * R) := Finset.sum_le_sum (fun i _ => hgB i)
        _ = m * (R + G + (K : ℝ) * R) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have hA : ‖(1 / (m : ℝ)) • ∑ i, g (t + 1) i ω‖ ≤ R + G + (K : ℝ) * R := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      calc 1 / (m : ℝ) * ‖∑ i, g (t + 1) i ω‖
          ≤ 1 / (m : ℝ) * (m * (R + G + (K : ℝ) * R)) :=
            mul_le_mul_of_nonneg_left hS (by positivity)
        _ = (1 / (m : ℝ) * m) * (R + G + (K : ℝ) * R) := by ring
        _ ≤ 1 * (R + G + (K : ℝ) * R) := mul_le_mul_of_nonneg_right hm hB0
        _ = R + G + (K : ℝ) * R := one_mul _
    calc ‖x t ω - η • ((1 / (m : ℝ)) • ∑ i, g (t + 1) i ω)‖
        ≤ ‖x t ω‖ + ‖η • ((1 / (m : ℝ)) • ∑ i, g (t + 1) i ω)‖ := norm_sub_le _ _
      _ = ‖x t ω‖ + |η| * ‖(1 / (m : ℝ)) • ∑ i, g (t + 1) i ω‖ := by
          rw [norm_smul, Real.norm_eq_abs]
      _ ≤ R + |η| * (R + G + (K : ℝ) * R) := by
          have := mul_le_mul_of_nonneg_left hA (abs_nonneg η)
          linarith [(hR ω).1]
      _ ≤ (R + G + (K : ℝ) * R) + |η| * (R + G + (K : ℝ) * R) := by
          linarith

/-! ## Helpers for the main proof -/
lemma sag_hasGradient_sum {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : ∀ i, Differentiable ℝ (f i)) (z : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (finiteSumObjective f) ((1 / (m : ℝ)) • ∑ i, gradient (f i) z) z := by
  rw [hasGradientAt_iff_hasFDerivAt]
  have h : HasFDerivAt (fun w => ∑ i, f i w) (∑ i, fderiv ℝ (f i) z) z :=
    HasFDerivAt.fun_sum (fun i _ => (hf i z).hasFDerivAt)
  have h2 := h.const_mul (1 / (m : ℝ))
  convert h2 using 1
  rw [map_smul, map_sum]
  simp [gradient]

lemma sag_jensen {m n k : ℕ} (hk : 0 < k) (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i)) (p : ℕ → EuclideanSpace ℝ (Fin n)) :
    finiteSumObjective f ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
      ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, finiteSumObjective f (p t) := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hw : ∑ t ∈ Finset.range k, (1 / (k : ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp
  have hJ : ∀ i, f i ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
      ≤ ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * f i (p t) := by
    intro i
    have := (hf_convex i).map_sum_le (t := Finset.range k) (w := fun _ => 1 / (k : ℝ)) (p := p)
      (fun _ _ => by positivity) hw (fun _ _ => Set.mem_univ _)
    simpa [Finset.smul_sum] using this
  unfold finiteSumObjective
  calc (1 / (m : ℝ)) * ∑ i, f i ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
      ≤ (1 / (m : ℝ)) * ∑ i, ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * f i (p t) := by
        apply mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hJ i)) (by positivity)
    _ = (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, (1 / (m : ℝ)) * ∑ i, f i (p t) := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => by ring))

theorem sag_bound_centered {k m n : ℕ} {Ω : Type*} [MeasurableSpace Ω]
  (μ : Measure Ω) [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (x : ℕ → Ω → EuclideanSpace ℝ (Fin n))
  (g : ℕ → Fin m → Ω → EuclideanSpace ℝ (Fin n))
  (I : ℕ → Ω → Fin m)
  (β : ℝ)
  (x0 : EuclideanSpace ℝ (Fin n))
  (x_star : EuclideanSpace ℝ (Fin n))
  (hx0 : ∀ ω, x 0 ω = x0)
  (hβ_pos : β > 0)
  (hm_pos : m > 0)
  (hk_pos : k > 0)
  (h_sag_seq : IsSAGSequence μ f x g I (1 / (16 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hx_star : IsMinOn (finiteSumObjective f) Set.univ x_star)
  (hf_sum_x_int : ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ)
  (hf_xbar_int : Integrable
    (fun ω => finiteSumObjective f (sagAverageIterate x k ω)) μ) :
  let f_sum := finiteSumObjective f
  ∫ ω, f_sum (sagAverageIterate x k ω) ∂μ - f_sum x_star ≤
    ((48 * (m : ℝ)) / (k : ℝ)) * (f_sum x0 - f_sum x_star) +
      ((128 * β) / (k : ℝ)) * ‖x0 - x_star‖ ^ 2 := by
  intro f_sum
  obtain ⟨hxm, hgm, hIm, hsag, _hiind, hind, hunif⟩ := h_sag_seq
  have hbdd := sag_bounded f x g I (1 / (16 * β)) x0 hx0 hsag β hf_smooth
  obtain ⟨hg0, hgsel, hgoth, hxupd⟩ := hsag
  have hβ' : ((Real.toNNReal β : ℝ≥0) : ℝ) = β := Real.coe_toNNReal β hβ_pos.le
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk_pos
  set α : ℝ := 1 / (16 * β) with hα_def
  have hα : 0 < α := by positivity
  have hβα : β = 1 / (16 * α) := by rw [hα_def]; field_simp
  -- gradient facts
  have hG : ∀ i z, HasGradientAt (f i) (gradient (f i) z) z :=
    fun i z => (hf_differentiable i z).hasGradientAt
  have hFgrad : ∀ z, HasGradientAt f_sum ((1 / (m : ℝ)) • ∑ i, gradient (f i) z) z :=
    sag_hasGradient_sum f hf_differentiable
  have hFgrad_eq : ∀ z, gradient f_sum z = (1 / (m : ℝ)) • ∑ i, gradient (f i) z :=
    fun z => (hFgrad z).gradient
  -- minimizer facts
  set fs := f_sum x_star with hfs_def
  have hmin : ∀ z, fs ≤ f_sum z := fun z => hx_star (Set.mem_univ z)
  set c : Fin m → EuclideanSpace ℝ (Fin n) := fun i => gradient (f i) x_star with hc_def
  have hsum_c : ∑ i, c i = 0 := by
    have hloc : IsLocalMin f_sum x_star := hx_star.isLocalMin Filter.univ_mem
    have h0 := hloc.hasFDerivAt_eq_zero ((hasGradientAt_iff_hasFDerivAt).1 (hFgrad x_star))
    rw [LinearIsometryEquiv.map_eq_zero_iff] at h0
    rcases smul_eq_zero.1 h0 with h | h
    · exact absurd h (one_div_pos.2 hm').ne'
    · exact h
  have hfsum_eq : ∀ z, ∑ i, f i z = (m : ℝ) * f_sum z := by
    intro z; simp only [f_sum, finiteSumObjective]; field_simp
  -- descent for f_sum
  have hdesc_sum : ∀ z w, f_sum w ≤ f_sum z
      + inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) z) (w - z)
      + (1 / (32 * α)) * ‖w - z‖ ^ 2 := by
    intro z w
    have h : ∀ i, f i w ≤ f i z + inner ℝ (gradient (f i) z) (w - z) + (β / 2) * ‖w - z‖ ^ 2 := by
      intro i
      have := sag_descent (hG i) (hf_smooth i) z w
      rwa [hβ'] at this
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hfsum_eq, hfsum_eq] at hs
    rw [real_inner_smul_left]
    have h32 : 1 / (32 * α) = β / 2 := by rw [hβα]; field_simp; ring
    rw [h32]
    have hmm : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    have key : (m : ℝ) * f_sum w ≤ (m : ℝ) * (f_sum z + 1 / (m : ℝ) *
        inner ℝ (∑ i, gradient (f i) z) (w - z) + β / 2 * ‖w - z‖ ^ 2) := by
      have e : (m : ℝ) * (f_sum z + 1 / (m : ℝ) * inner ℝ (∑ i, gradient (f i) z) (w - z)
          + β / 2 * ‖w - z‖ ^ 2) = (m : ℝ) * f_sum z + inner ℝ (∑ i, gradient (f i) z) (w - z)
          + (m : ℝ) * (β / 2 * ‖w - z‖ ^ 2) := by
        linear_combination (inner ℝ (∑ i, gradient (f i) z) (w - z)) * hmm
      rw [e]; linarith
    exact le_of_mul_le_mul_left key hm'
  -- cocoercivity averaged at (z, x_star)
  have hcoco_sum : ∀ z, f_sum z + inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) z) (x_star - z)
      + 8 * α * ((1 / (m : ℝ)) * ∑ i, ‖gradient (f i) z - c i‖ ^ 2) ≤ fs := by
    intro z
    have h8 : 1 / (2 * β) = 8 * α := by rw [hβα]; field_simp; ring
    have h : ∀ i, f i z + inner ℝ (gradient (f i) z) (x_star - z)
        + 8 * α * ‖gradient (f i) z - c i‖ ^ 2 ≤ f i x_star := by
      intro i
      have := sag_cocoercive hβ_pos (hf_convex i) (hG i) (hf_smooth i) z x_star
      rw [h8, norm_sub_rev] at this
      exact this
    have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => h i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, ← Finset.mul_sum,
      hfsum_eq, hfsum_eq] at hs
    rw [real_inner_smul_left]
    have hmm : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
    have key : (m : ℝ) * (f_sum z + 1 / (m : ℝ) * inner ℝ (∑ i, gradient (f i) z) (x_star - z)
        + 8 * α * (1 / (m : ℝ) * ∑ i, ‖gradient (f i) z - c i‖ ^ 2)) ≤ (m : ℝ) * fs := by
      have e : (m : ℝ) * (f_sum z + 1 / (m : ℝ) * inner ℝ (∑ i, gradient (f i) z) (x_star - z)
          + 8 * α * (1 / (m : ℝ) * ∑ i, ‖gradient (f i) z - c i‖ ^ 2))
          = (m : ℝ) * f_sum z + inner ℝ (∑ i, gradient (f i) z) (x_star - z)
            + 8 * α * ∑ i, ‖gradient (f i) z - c i‖ ^ 2 := by
        linear_combination (inner ℝ (∑ i, gradient (f i) z) (x_star - z)
          + 8 * α * ∑ i, ‖gradient (f i) z - c i‖ ^ 2) * hmm
      rw [e]; linarith
    exact le_of_mul_le_mul_left key hm'
  -- Lyapunov machinery
  let W : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → ℝ :=
    fun z => sagLyap α x_star c fs z.1 z.2 (f_sum z.1)
  let newy : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → Fin m →
      Fin m → EuclideanSpace ℝ (Fin n) :=
    fun z j => Function.update z.2 j (gradient (f j) z.1)
  let newx : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → Fin m →
      EuclideanSpace ℝ (Fin n) :=
    fun z j => z.1 - α • ((1 / (m : ℝ)) • ∑ i, newy z j i)
  let Ψ : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → Fin m → ℝ :=
    fun z j => W (newx z j, newy z j)
  let Zt : ℕ → Ω → EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) :=
    fun t ω => (x t ω, fun i => g t i ω)
  have hstep_id : ∀ t ω, W (Zt (t + 1) ω) = Ψ (Zt t ω) (I t ω) := by
    intro t ω
    have hy : (fun i => g (t + 1) i ω) = newy (Zt t ω) (I t ω) := by
      funext i
      show g (t + 1) i ω = Function.update (fun i => g t i ω) (I t ω) (gradient (f (I t ω)) (x t ω)) i
      by_cases hi : i = I t ω
      · rw [hi, Function.update_self]; exact hgsel t ω
      · rw [Function.update_of_ne hi]; exact hgoth t i ω hi
    have hx : x (t + 1) ω = newx (Zt t ω) (I t ω) := by
      rw [hxupd t ω]
      show x t ω - α • ((1 / (m : ℝ)) • ∑ i, g (t + 1) i ω)
        = x t ω - α • ((1 / (m : ℝ)) • ∑ i, newy (Zt t ω) (I t ω) i)
      rw [← hy]
    show W (x (t + 1) ω, fun i => g (t + 1) i ω) = W (newx (Zt t ω) (I t ω), newy (Zt t ω) (I t ω))
    rw [hx, hy]
  have hdet : ∀ z, (1 / (m : ℝ)) * ∑ j, Ψ z j ≤ W z - 2 * α * (f_sum z.1 - fs) := by
    intro z
    exact sag_step_det hm_pos hα x_star z.1 z.2 (fun i => gradient (f i) z.1) c fs (f_sum z.1)
      (fun j => f_sum (newx z j)) (fun j => hdesc_sum z.1 (newx z j)) (hcoco_sum z.1)
  have hW_nonneg : ∀ z, 0 ≤ W z := by
    intro z
    have h1 : 0 ≤ f_sum z.1 - fs := sub_nonneg.mpr (hmin z.1)
    simp only [W, sagLyap]
    have h2 : 0 ≤ (17 / 8 * (m : ℝ) * α) * (f_sum z.1 - fs) := mul_nonneg (by positivity) h1
    have h3 : 0 ≤ 3 * α ^ 2 * ∑ i, ‖z.2 i - c i‖ ^ 2 :=
      mul_nonneg (by positivity) (Finset.sum_nonneg (fun i _ => by positivity))
    have h4 : 0 ≤ ((m : ℝ) ^ 2 * α ^ 2 / 16) * ‖(1 / (m : ℝ)) • ∑ i, z.2 i‖ ^ 2 := by positivity
    have h5 : 0 ≤ ‖z.1 - (((m : ℝ) - 1) * α) • ((1 / (m : ℝ)) • ∑ i, z.2 i) - x_star‖ ^ 2 := by
      positivity
    linarith
  -- continuity
  have hfc : Continuous f_sum := by
    show Continuous (fun z => (1 / (m : ℝ)) * ∑ i, f i z)
    exact continuous_const.mul
      (continuous_finset_sum _ fun i _ => (hf_differentiable i).continuous)
  have hW_cont : Continuous W := by
    simp only [W, sagLyap]
    fun_prop
  have hΨ_cont : ∀ j, Continuous (fun z => Ψ z j) := by
    intro j
    have hgc : Continuous (gradient (f j)) := (hf_smooth j).continuous
    have hny : Continuous (fun z : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) =>
        newy z j) :=
      continuous_snd.update j (hgc.comp continuous_fst)
    have hnx : Continuous (fun z : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) =>
        newx z j) :=
      continuous_fst.sub (continuous_const.smul (continuous_const.smul
        (continuous_finset_sum _ fun i _ => (continuous_apply i).comp hny)))
    exact hW_cont.comp (hnx.prodMk hny)
  -- measurability & boundedness
  have hZm : ∀ t, Measurable (Zt t) := fun t =>
    (hxm t).prodMk (measurable_pi_lambda _ (fun i => hgm t i))
  have hZb : ∀ t, ∃ R, ∀ ω, ‖Zt t ω‖ ≤ R := by
    intro t
    obtain ⟨R, hR⟩ := hbdd t
    refine ⟨R, fun ω => ?_⟩
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hR ω).1
    rw [norm_prod_le_iff]
    exact ⟨(hR ω).1, (pi_norm_le_iff_of_nonneg hR0).mpr (fun i => (hR ω).2 i)⟩
  have hW_int : ∀ t, Integrable (fun ω => W (Zt t ω)) μ := by
    intro t
    obtain ⟨R, hR⟩ := hZb t
    exact sag_integrable_of_bdd μ hW_cont (hZm t) R hR
  have hΨ_int : ∀ t j, Integrable (fun ω => Ψ (Zt t ω) j) μ := by
    intro t j
    obtain ⟨R, hR⟩ := hZb t
    exact sag_integrable_of_bdd μ (hΨ_cont j) (hZm t) R hR
  -- expectation step
  have hE : ∀ t, ∫ ω, W (Zt (t + 1) ω) ∂μ ≤ ∫ ω, W (Zt t ω) ∂μ
      - 2 * α * (∫ ω, f_sum (x t ω) ∂μ - fs) := by
    intro t
    have h1 : ∫ ω, W (Zt (t + 1) ω) ∂μ = ∫ ω, Ψ (Zt t ω) (I t ω) ∂μ := by
      congr 1; funext ω; exact hstep_id t ω
    have h2 := sag_expect_indep μ hm_pos (Zt t) (I t) (hZm t) (hIm t) (hind t) (hunif t) Ψ
      (fun j => (hΨ_cont j).measurable) (hΨ_int t)
    have h3 : (1 / (m : ℝ)) * ∑ j, ∫ ω, Ψ (Zt t ω) j ∂μ
        = ∫ ω, (1 / (m : ℝ)) * ∑ j, Ψ (Zt t ω) j ∂μ := by
      rw [integral_const_mul, integral_finset_sum]
      intro j _; exact hΨ_int t j
    have hint2 : Integrable (fun ω => W (Zt t ω) - 2 * α * (f_sum (x t ω) - fs)) μ :=
      (hW_int t).sub (((hf_sum_x_int t).sub (integrable_const fs)).const_mul (2 * α))
    have h4 : ∫ ω, (1 / (m : ℝ)) * ∑ j, Ψ (Zt t ω) j ∂μ
        ≤ ∫ ω, (W (Zt t ω) - 2 * α * (f_sum (x t ω) - fs)) ∂μ := by
      apply integral_mono
      · exact (integrable_finset_sum _ (fun j _ => hΨ_int t j)).const_mul _
      · exact hint2
      · intro ω; exact hdet (Zt t ω)
    have h5 : ∫ ω, (W (Zt t ω) - 2 * α * (f_sum (x t ω) - fs)) ∂μ
        = ∫ ω, W (Zt t ω) ∂μ - 2 * α * (∫ ω, f_sum (x t ω) ∂μ - fs) := by
      have hi1 : Integrable (fun ω => 2 * α * (f_sum (x t ω) - fs)) μ :=
        ((hf_sum_x_int t).sub (integrable_const fs)).const_mul (2 * α)
      have hi2 : Integrable (fun ω => f_sum (x t ω)) μ := hf_sum_x_int t
      rw [integral_sub (hW_int t) hi1, integral_const_mul, integral_sub hi2 (integrable_const fs)]
      simp
    rw [h1, h2, h3]; linarith [h4, h5]
  -- telescoping
  have htel : ∀ K, ∫ ω, W (Zt K ω) ∂μ + 2 * α * ∑ t ∈ Finset.range K, (∫ ω, f_sum (x t ω) ∂μ - fs)
      ≤ ∫ ω, W (Zt 0 ω) ∂μ := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [Finset.sum_range_succ]
      have := hE K
      nlinarith
  -- initial value
  have hW0 : ∫ ω, W (Zt 0 ω) ∂μ ≤ ‖x0 - x_star‖ ^ 2 + 5 / 2 * (m : ℝ) * α * (f_sum x0 - fs) := by
    obtain ⟨G, hG_def⟩ : ∃ G : Fin m → EuclideanSpace ℝ (Fin n),
        G = fun i => gradient (f i) x0 := ⟨_, rfl⟩
    obtain ⟨y0, hy0_def⟩ : ∃ y0 : Fin m → EuclideanSpace ℝ (Fin n),
        y0 = fun i => G i - (1 / (m : ℝ)) • ∑ j, G j := ⟨_, rfl⟩
    have hZ0 : ∀ ω, Zt 0 ω = (x0, y0) := by
      intro ω
      refine Prod.ext (hx0 ω) (funext fun i => ?_)
      show g 0 i ω = y0 i
      rw [hg0 i ω, hx0 ω, hy0_def, hG_def]
      show gradient (f i) x0 - gradient f_sum x0 = _
      rw [hFgrad_eq x0]
    have hint : ∫ ω, W (Zt 0 ω) ∂μ = W (x0, y0) := by
      have hfun : (fun ω => W (Zt 0 ω)) = fun _ => W (x0, y0) :=
        funext fun ω => by rw [hZ0 ω]
      rw [hfun, integral_const, probReal_univ, one_smul]
    have hsy : ∑ i, y0 i = 0 := by
      rw [hy0_def, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_one_div_cancel hm'.ne', one_smul, sub_self]
    -- memory term
    have hsumGc : ∑ i, (G i - c i) = ∑ j, G j := by
      rw [Finset.sum_sub_distrib, hsum_c, sub_zero]
    have hmem : ∑ i, ‖y0 i - c i‖ ^ 2 ≤ ∑ i, ‖G i - c i‖ ^ 2 := by
      obtain ⟨T, hT_def⟩ : ∃ T : EuclideanSpace ℝ (Fin n), T = (1 / (m : ℝ)) • ∑ j, G j :=
        ⟨_, rfl⟩
      have hST : ∑ j, G j = (m : ℝ) • T := by
        rw [hT_def, smul_smul, mul_one_div_cancel hm'.ne', one_smul]
      have e0 : ∀ i, y0 i - c i = (G i - c i) - T := by
        intro i; rw [hy0_def, hT_def]; dsimp only; abel
      have e : ∀ i, ‖y0 i - c i‖ ^ 2
          = ‖G i - c i‖ ^ 2 - 2 * inner ℝ (G i - c i) T + ‖T‖ ^ 2 := by
        intro i
        rw [e0 i, norm_sub_sq_real]
      rw [Finset.sum_congr rfl (fun i _ => e i), Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← sum_inner, hsumGc, hST, real_inner_smul_left,
        real_inner_self_eq_norm_sq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hT2 := mul_nonneg hm'.le (sq_nonneg ‖T‖)
      linarith
    -- cocoercivity summed
    have hco : ∀ i, f i x_star + inner ℝ (c i) (x0 - x_star)
        + (1 / (2 * β)) * ‖G i - c i‖ ^ 2 ≤ f i x0 := by
      intro i
      rw [hG_def]
      exact sag_cocoercive hβ_pos (hf_convex i) (hG i) (hf_smooth i) x_star x0
    have hco_sum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hco i)
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← sum_inner, hsum_c, inner_zero_left,
      ← Finset.mul_sum, hfsum_eq, hfsum_eq] at hco_sum
    have h2β : 1 / (2 * β) = 8 * α := by rw [hβα]; field_simp; ring
    rw [h2β] at hco_sum
    have hfx : 0 ≤ f_sum x0 - fs := sub_nonneg.2 (hmin x0)
    rw [hint]
    show sagLyap α x_star c fs x0 y0 (f_sum x0) ≤ _
    unfold sagLyap
    simp only [hsy, smul_zero, sub_zero, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero]
    have h1 := mul_le_mul_of_nonneg_left hmem (by positivity : (0 : ℝ) ≤ 3 * α ^ 2)
    have h2 := mul_le_mul_of_nonneg_left hco_sum hα.le
    linarith
  -- Jensen
  have hJ : ∫ ω, f_sum (sagAverageIterate x k ω) ∂μ
      ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, ∫ ω, f_sum (x t ω) ∂μ := by
    rw [← integral_finset_sum _ (fun t _ => hf_sum_x_int t), ← integral_const_mul]
    apply integral_mono hf_xbar_int
    · exact (integrable_finset_sum _ (fun t _ => hf_sum_x_int t)).const_mul _
    · intro ω
      exact sag_jensen hk_pos f hf_convex (fun t => x t ω)
  have hF0 : 0 ≤ f_sum x0 - fs := sub_nonneg.mpr (hmin x0)
  have hN : 0 ≤ ‖x0 - x_star‖ ^ 2 := by positivity
  have hWk : 0 ≤ ∫ ω, W (Zt k ω) ∂μ := integral_nonneg (fun ω => hW_nonneg _)
  have htk := htel k
  have hsumsub : ∑ t ∈ Finset.range k, (∫ ω, f_sum (x t ω) ∂μ - fs)
      = (∑ t ∈ Finset.range k, ∫ ω, f_sum (x t ω) ∂μ) - k * fs := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hsumsub] at htk
  have h1 : (k : ℝ) * (∫ ω, f_sum (sagAverageIterate x k ω) ∂μ - fs)
      ≤ (∑ t ∈ Finset.range k, ∫ ω, f_sum (x t ω) ∂μ) - k * fs := by
    have := mul_le_mul_of_nonneg_left hJ hk'.le
    rw [← mul_assoc, mul_one_div_cancel hk'.ne', one_mul] at this
    linarith
  have e2 : 2 * α * (8 * β) = 1 := by rw [hβα]; field_simp; ring
  have h3 : (k : ℝ) * (∫ ω, f_sum (sagAverageIterate x k ω) ∂μ - fs)
      ≤ 8 * β * ‖x0 - x_star‖ ^ 2 + 5 / 4 * (m : ℝ) * (f_sum x0 - fs) := by
    have h2a := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2 * α)
    have : 2 * α * ((k : ℝ) * (∫ ω, f_sum (sagAverageIterate x k ω) ∂μ - fs))
        ≤ 2 * α * (8 * β * ‖x0 - x_star‖ ^ 2 + 5 / 4 * (m : ℝ) * (f_sum x0 - fs)) := by
      have e3 : 2 * α * (8 * β * ‖x0 - x_star‖ ^ 2 + 5 / 4 * (m : ℝ) * (f_sum x0 - fs))
          = ‖x0 - x_star‖ ^ 2 + 5 / 2 * (m : ℝ) * α * (f_sum x0 - fs) := by
        linear_combination ‖x0 - x_star‖ ^ 2 * e2
      rw [e3]; linarith
    exact le_of_mul_le_mul_left this (by positivity)
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, le_div_iff₀ hk']
  nlinarith [mul_nonneg hβ_pos.le hN, mul_nonneg hm'.le hF0]

end sag_bound_centered
