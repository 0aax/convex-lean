import ConvexStarLib.Defs

/-!
# `subgradient_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/subgradient_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace subgradient_bound`, so the main result is `subgradient_bound.subgradient_bound`.
-/

namespace subgradient_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {n : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem subgradient_bound {t : ℕ}
    (𝓧 : Set (EuclideanSpace ℝ (Fin n))) (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (g : ℕ → EuclideanSpace ℝ (Fin n))
    (R L : ℝ) (x_star : EuclideanSpace ℝ (Fin n))
    (hx_init : x 0 ∈ 𝓧)
    (h𝓧_nonempty : Set.Nonempty 𝓧)
    (h𝓧_compact : IsCompact 𝓧)
    (h𝓧_convex : Convex ℝ 𝓧)
    (h𝓧_contained : 𝓧 ⊆ Metric.ball (x 0) R)
    (hR : R > 0) (hL : L > 0) (ht : t > 0)
    (hf_convex : ConvexOn ℝ 𝓧 f)
    (hf_exists_subgrad : ∀ x ∈ 𝓧, ∃ w, InDomIsSubgradientAt 𝓧 f x w)
    (hg_bounded : ∀ s, ‖g s‖ ≤ L)
    (h_ps_seq : IsProjectedSubgradientSequence 𝓧 f x g (fun _ => R / (L * Real.sqrt t))
      h𝓧_nonempty h𝓧_compact h𝓧_convex)
    (hx_star_mem : x_star ∈ 𝓧)
    (hx_star : IsMinOn f 𝓧 x_star) :
    f ((1 / (t : ℝ)) • (∑ i ∈ Finset.range t, x i)) - f x_star ≤
      (R * L) / Real.sqrt t := by
  obtain ⟨h_step, h_sub⟩ := h_ps_seq
  have ht_pos : (0 : ℝ) < t := by exact_mod_cast ht
  have hsqrt_pos : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht_pos
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht_pos.le
  set η : ℝ := R / (L * Real.sqrt t) with hη_def
  have hη_pos : 0 < η := div_pos hR (mul_pos hL hsqrt_pos)
  -- the projection onto 𝓧 lands in 𝓧 and does not increase distances to points of 𝓧
  have hproj : ∀ y : EuclideanSpace ℝ (Fin n),
      pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty ∈ 𝓧 ∧
      ∀ z ∈ 𝓧, ‖pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty - z‖ ^ 2 ≤ ‖y - z‖ ^ 2 := by
    intro y
    have hspec := Classical.choose_spec (exists_norm_eq_iInf_of_complete_convex h𝓧_nonempty
      h𝓧_compact.isClosed.isComplete h𝓧_convex y)
    have hp_mem : pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty ∈ 𝓧 := hspec.1
    have hp_eq : ‖y - pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty‖ = ⨅ w : 𝓧, ‖y - w‖ :=
      hspec.2
    refine ⟨hp_mem, fun z hz => ?_⟩
    set p := pC y 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty with hp
    have hineq := (norm_eq_iInf_iff_real_inner_le_zero h𝓧_convex hp_mem).mp hp_eq z hz
    have h1 : ‖y - z‖ ^ 2 = ‖y - p‖ ^ 2 - 2 * inner ℝ (y - p) (z - p) + ‖z - p‖ ^ 2 := by
      have : y - z = (y - p) - (z - p) := by abel
      rw [this, norm_sub_sq_real]
    rw [norm_sub_rev p z, h1]
    nlinarith [sq_nonneg ‖y - p‖]
  have hx_succ : ∀ i, x (i + 1) = pC (x i - η • g i) 𝓧 h𝓧_compact.isClosed h𝓧_convex h𝓧_nonempty :=
    fun i => h_step i
  have hmem : ∀ i, x i ∈ 𝓧 := by
    intro i
    induction i with
    | zero => exact hx_init
    | succ k _ => rw [hx_succ k]; exact (hproj _).1
  -- one step of the standard analysis
  have hstep_ineq : ∀ i, ‖x (i + 1) - x_star‖ ^ 2 ≤
      ‖x i - x_star‖ ^ 2 - 2 * η * inner ℝ (x i - x_star) (g i) + η ^ 2 * L ^ 2 := by
    intro i
    have h1 : ‖x (i + 1) - x_star‖ ^ 2 ≤ ‖(x i - η • g i) - x_star‖ ^ 2 := by
      rw [hx_succ i]
      exact (hproj (x i - η • g i)).2 x_star hx_star_mem
    have h2 : ‖(x i - η • g i) - x_star‖ ^ 2 =
        ‖x i - x_star‖ ^ 2 - 2 * η * inner ℝ (x i - x_star) (g i) + η ^ 2 * ‖g i‖ ^ 2 := by
      have : (x i - η • g i) - x_star = (x i - x_star) - η • g i := by abel
      rw [this, norm_sub_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hη_pos]
      ring
    have h3 : ‖g i‖ ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hg_bounded i) 2
    have h4 : η ^ 2 * ‖g i‖ ^ 2 ≤ η ^ 2 * L ^ 2 := mul_le_mul_of_nonneg_left h3 (sq_nonneg η)
    linarith
  have key : ∀ i, 2 * η * (f (x i) - f x_star) ≤
      (‖x i - x_star‖ ^ 2 - ‖x (i + 1) - x_star‖ ^ 2) + η ^ 2 * L ^ 2 := by
    intro i
    have hs := h_sub i x_star hx_star_mem
    have hinner : inner ℝ (x_star - x i) (g i) = - inner ℝ (x i - x_star) (g i) := by
      rw [← inner_neg_left, neg_sub]
    have hfi : f (x i) - f x_star ≤ inner ℝ (x i - x_star) (g i) := by
      rw [hinner] at hs
      linarith
    have := hstep_ineq i
    have h2η : 2 * η * (f (x i) - f x_star) ≤ 2 * η * inner ℝ (x i - x_star) (g i) :=
      mul_le_mul_of_nonneg_left hfi (by positivity)
    linarith
  have hsum : 2 * η * ∑ i ∈ Finset.range t, (f (x i) - f x_star) ≤
      ‖x 0 - x_star‖ ^ 2 - ‖x t - x_star‖ ^ 2 + t * (η ^ 2 * L ^ 2) := by
    calc 2 * η * ∑ i ∈ Finset.range t, (f (x i) - f x_star)
        = ∑ i ∈ Finset.range t, 2 * η * (f (x i) - f x_star) := by rw [Finset.mul_sum]
      _ ≤ ∑ i ∈ Finset.range t,
            ((‖x i - x_star‖ ^ 2 - ‖x (i + 1) - x_star‖ ^ 2) + η ^ 2 * L ^ 2) :=
          Finset.sum_le_sum (fun i _ => key i)
      _ = ‖x 0 - x_star‖ ^ 2 - ‖x t - x_star‖ ^ 2 + t * (η ^ 2 * L ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.sum_range_sub' (fun i => ‖x i - x_star‖ ^ 2),
            Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hD : ‖x 0 - x_star‖ ^ 2 ≤ R ^ 2 := by
    have hball := h𝓧_contained hx_star_mem
    rw [Metric.mem_ball, dist_eq_norm] at hball
    rw [norm_sub_rev]
    exact pow_le_pow_left₀ (norm_nonneg _) hball.le 2
  have hjensen : f ((1 / (t : ℝ)) • (∑ i ∈ Finset.range t, x i)) ≤
      (1 / (t : ℝ)) * ∑ i ∈ Finset.range t, f (x i) := by
    rw [Finset.smul_sum, Finset.mul_sum]
    have := hf_convex.map_sum_le (t := Finset.range t) (w := fun _ => 1 / (t : ℝ)) (p := x)
      (fun i _ => by positivity)
      (by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; field_simp)
      (fun i _ => hmem i)
    simpa [smul_eq_mul] using this
  have hS : ∑ i ∈ Finset.range t, (f (x i) - f x_star) =
      ∑ i ∈ Finset.range t, f (x i) - t * f x_star := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [hS] at hsum
  have hηt : t * (η ^ 2 * L ^ 2) = R ^ 2 := by
    rw [hη_def, div_pow, mul_pow, hsq]
    field_simp
  set S := ∑ i ∈ Finset.range t, f (x i) with hS_def
  -- from hsum: η * (S - t f*) ≤ R²
  have hmain : η * (S - t * f x_star) ≤ R ^ 2 := by
    nlinarith [sq_nonneg ‖x t - x_star‖]
  -- goal
  have hgoal : (1 / (t : ℝ)) * S - f x_star ≤ R * L / Real.sqrt t := by
    have hrw : (1 / (t : ℝ)) * S - f x_star = (S - t * f x_star) / t := by
      field_simp
    rw [hrw, div_le_div_iff₀ ht_pos hsqrt_pos]
    rw [hη_def, div_mul_eq_mul_div, div_le_iff₀ (mul_pos hL hsqrt_pos)] at hmain
    have h1 : S - t * f x_star ≤ R * L * Real.sqrt t := by
      have h' : R * (S - t * f x_star) ≤ R * (R * L * Real.sqrt t) := by linarith
      exact le_of_mul_le_mul_left h' hR
    calc (S - t * f x_star) * Real.sqrt t ≤ (R * L * Real.sqrt t) * Real.sqrt t :=
          mul_le_mul_of_nonneg_right h1 hsqrt_pos.le
      _ = R * L * t := by rw [mul_assoc, Real.mul_self_sqrt ht_pos.le]
  linarith

end subgradient_bound
