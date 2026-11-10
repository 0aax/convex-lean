import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_9`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_9` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_9`, so the main result is `FCA_chap_E_1_3_9.FCA_chap_E_1_3_9`.
-/

namespace FCA_chap_E_1_3_9

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_9
  (f : E → EReal)
  (x₀ : E)
  (hf_nondegenerate : IsNondegenerate f)
  (hf_convex : InConvRn f) :
  (x₀ ∈ interior (effDom f) →
  IsLevelBounded (fun x => conjugate f x - inner ℝ x₀ x)) ∧
  ((∀ x, f x ≠ ⊤) → IsOneCoerciveFun (conjugate f)) := by
  classical
  have hbot : ∀ x, ⊥ < f x := hf_convex.1
  -- basic inequality defining the conjugate
  have hconj : ∀ v x : E, ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v := by
    intro v x
    exact le_sSup ⟨x, Set.mem_univ _, rfl⟩
  set b := stdOrthonormalBasis ℝ E with hb
  set n : ℕ := Module.finrank ℝ E with hn
  -- the norm is bounded by the sum of the absolute values of the coordinates
  have hnorm : ∀ v : E, ‖v‖ ≤ ∑ i, |inner ℝ v (b i)| := by
    intro v
    calc ‖v‖ = ‖∑ i, inner ℝ (b i) v • b i‖ := by rw [b.sum_repr' v]
      _ ≤ ∑ i, ‖inner ℝ (b i) v • b i‖ := norm_sum_le _ _
      _ = ∑ i, |inner ℝ v (b i)| := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, real_inner_comm]
  -- key estimate
  have key : ∀ (y : E) (R : ℝ), 0 < R → (∀ i, f (y + R • b i) ≠ ⊤) →
      (∀ i, f (y - R • b i) ≠ ⊤) →
      ∃ M : ℝ, ∀ (v : E) (t : ℝ), conjugate f v - ((inner ℝ y v : ℝ) : EReal) ≤ (t : EReal) →
        R * ‖v‖ ≤ n * t + M := by
    intro y R hR hp hm
    set a : Fin n → ℝ := fun i => (f (y + R • b i)).toReal with ha
    set c : Fin n → ℝ := fun i => (f (y - R • b i)).toReal with hc
    have ha' : ∀ i, f (y + R • b i) = (a i : EReal) := fun i =>
      (EReal.coe_toReal (hp i) (hbot _).ne').symm
    have hc' : ∀ i, f (y - R • b i) = (c i : EReal) := fun i =>
      (EReal.coe_toReal (hm i) (hbot _).ne').symm
    refine ⟨∑ i, (|a i| + |c i|), ?_⟩
    intro v t hvt
    have step : ∀ (x : E) (m : ℝ), f x = (m : EReal) → inner ℝ v x - m - inner ℝ y v ≤ t := by
      intro x m hm
      have h1 := hconj v x
      rw [hm, ← EReal.coe_sub] at h1
      have h2 := EReal.sub_le_sub h1 (le_refl ((inner ℝ y v : ℝ) : EReal))
      have h3 := h2.trans hvt
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h3
      exact h3
    have hi : ∀ i, R * |inner ℝ v (b i)| ≤ t + (|a i| + |c i|) := by
      intro i
      have e1 := step _ _ (ha' i)
      have e2 := step _ _ (hc' i)
      rw [inner_add_right, inner_smul_right] at e1
      rw [inner_sub_right, inner_smul_right] at e2
      rcases abs_cases (inner ℝ v (b i)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
        linarith [abs_nonneg (a i), abs_nonneg (c i), le_abs_self (a i), le_abs_self (c i),
          real_inner_comm y v]
    calc R * ‖v‖ ≤ R * ∑ i, |inner ℝ v (b i)| := mul_le_mul_of_nonneg_left (hnorm v) hR.le
      _ = ∑ i, R * |inner ℝ v (b i)| := Finset.mul_sum _ _ _
      _ ≤ ∑ i, (t + (|a i| + |c i|)) := Finset.sum_le_sum (fun i _ => hi i)
      _ = n * t + ∑ i, (|a i| + |c i|) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
  constructor
  · intro hx₀ α
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hx₀
    obtain ⟨δ, hδ, hball⟩ := hx₀
    have hR : 0 < δ / 2 := half_pos hδ
    have hin : ∀ z : E, ‖z - x₀‖ = δ / 2 → f z ≠ ⊤ := by
      intro z hz
      have : z ∈ Metric.ball x₀ δ := by
        rw [Metric.mem_ball, dist_eq_norm, hz]; linarith
      exact (hball this).ne
    have hbn : ∀ i, ‖(δ / 2) • b i‖ = δ / 2 := by
      intro i
      rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs, abs_of_pos hR]
    obtain ⟨M, hM⟩ := key x₀ (δ / 2) hR
      (fun i => hin _ (by rw [add_sub_cancel_left, hbn i]))
      (fun i => hin _ (by rw [sub_sub_cancel_left, norm_neg, hbn i]))
    refine isBounded_iff_forall_norm_le.2 ⟨(n * α + M) / (δ / 2), fun v hv => ?_⟩
    have hv' : conjugate f v - ((inner ℝ x₀ v : ℝ) : EReal) ≤ (α : EReal) := hv
    have := hM v α hv'
    rw [le_div_iff₀ hR]
    linarith
  · intro hfin C
    have hR : (0:ℝ) < n * |C| + 1 := by positivity
    obtain ⟨M, hM⟩ := key 0 (n * |C| + 1) hR (fun i => hfin _) (fun i => hfin _)
    have hbot' : ∀ v, conjugate f v ≠ ⊥ := by
      intro v h
      have h1 := hconj v 0
      rw [h] at h1
      have h2 : f 0 = ((f 0).toReal : EReal) := (EReal.coe_toReal (hfin 0) (hbot 0).ne').symm
      rw [h2, ← EReal.coe_sub] at h1
      exact EReal.coe_ne_bot _ (le_bot_iff.1 h1)
    rw [Filter.eventually_comap, Filter.eventually_atTop]
    refine ⟨|M| + 1, fun r hr v hv => ?_⟩
    subst hv
    have hpos : 0 < ‖v‖ := by linarith [abs_nonneg M]
    by_cases htop : conjugate f v = ⊤
    · rw [htop, EReal.coe_mul_top_of_pos (inv_pos.2 hpos)]
      exact le_top
    · set t := (conjugate f v).toReal with ht_def
      have ht : conjugate f v = (t : EReal) := (EReal.coe_toReal htop (hbot' v)).symm
      have hk := hM v t (by rw [ht, inner_zero_left, EReal.coe_zero, sub_zero])
      rw [ht, ← EReal.coe_mul, EReal.coe_le_coe_iff, le_inv_mul_iff₀ hpos]
      by_contra hcon
      push_neg at hcon
      have h1 : (n:ℝ) * t ≤ n * (‖v‖ * C) := mul_le_mul_of_nonneg_left hcon.le (Nat.cast_nonneg n)
      have h2 : ‖v‖ * C ≤ ‖v‖ * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) hpos.le
      have h3 : (n:ℝ) * (‖v‖ * C) ≤ n * (‖v‖ * |C|) :=
        mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg n)
      nlinarith [le_abs_self M]

end FCA_chap_E_1_3_9
