import ConvexStarLib.Defs

/-!
# `saga_convex_average_bound`

Source: Defazio, Bach & Lacoste-Julien, 'SAGA: A Fast Incremental Gradient Method With Support for Non-Strongly Convex Composite Objectives' (NIPS 2014).

Statement from the `convex-eval-v28-2h/saga_convex_average_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace saga_convex_average_bound`, so the main result is `saga_convex_average_bound.saga_convex_average_bound`.
-/

namespace saga_convex_average_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section SagaAux

open InnerProductSpace

lemma saga_aux_lim {a b : ℝ} (h : ∀ t : ℝ, 0 < t → t < 1 → 0 ≤ a + t * b) : 0 ≤ a := by
  by_contra hneg
  push_neg at hneg
  have hb1 : 0 < |b| + 1 := by positivity
  have ht0 : 0 < min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) :=
    lt_min (by norm_num) (div_pos (by linarith) (by positivity))
  have ht1 : min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) < 1 :=
    lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have ht2 : min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) ≤ -a / (2 * (|b| + 1)) := min_le_right _ _
  have key := h _ ht0 ht1
  have htb := mul_le_mul_of_nonneg_left (le_abs_self b) ht0.le
  have h3 : min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) * (|b| + 1) ≤ -a / 2 := by
    calc min (1 / 2 : ℝ) (-a / (2 * (|b| + 1))) * (|b| + 1)
        ≤ (-a / (2 * (|b| + 1))) * (|b| + 1) := mul_le_mul_of_nonneg_right ht2 hb1.le
      _ = -a / 2 := by field_simp
  nlinarith

lemma sagaA_hasDerivAt_line {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hd : Differentiable ℝ ψ)
    (x v : EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => ψ (x + s • v)) (inner ℝ (gradient ψ (x + t • v)) v) t := by
  have h1 : HasDerivAt (fun s : ℝ => x + s • v) v t := by
    simpa using ((hasDerivAt_id t).smul_const v).const_add x
  have h2 := (hd (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
  rw [inner_gradient_left (hd _)]
  exact h2

lemma saga_aux_descent {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 ≤ L)
    (hd : Differentiable ℝ ψ)
    (hlip : ∀ a b, ‖gradient ψ a - gradient ψ b‖ ≤ L * ‖a - b‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ψ y ≤ ψ x + inner ℝ (gradient ψ x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hderiv : ∀ t : ℝ, HasDerivAt
      (fun s : ℝ => ψ (x + s • (y - x)) - s * inner ℝ (gradient ψ x) (y - x)
        - L / 2 * s ^ 2 * ‖y - x‖ ^ 2)
      (inner ℝ (gradient ψ (x + t • (y - x))) (y - x) - inner ℝ (gradient ψ x) (y - x)
        - L * t * ‖y - x‖ ^ 2) t := by
    intro t
    have h1 := sagaA_hasDerivAt_line hd x (y - x) t
    have h2 : HasDerivAt (fun s : ℝ => s * inner ℝ (gradient ψ x) (y - x))
        (inner ℝ (gradient ψ x) (y - x)) t := by
      simpa using (hasDerivAt_id t).mul_const (inner ℝ (gradient ψ x) (y - x))
    have h3 : HasDerivAt (fun s : ℝ => L / 2 * s ^ 2 * ‖y - x‖ ^ 2) (L * t * ‖y - x‖ ^ 2) t := by
      have := ((hasDerivAt_pow 2 t).const_mul (L / 2)).mul_const (‖y - x‖ ^ 2)
      convert this using 1
      push_cast
      ring
    exact (h1.sub h2).sub h3
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope _ _ zero_lt_one
    (fun t _ => (hderiv t).continuousAt.continuousWithinAt) (fun t _ => hderiv t)
  have hc0 : 0 < c := hc.1
  have e2 : inner ℝ (gradient ψ (x + c • (y - x)) - gradient ψ x) (y - x)
      ≤ ‖gradient ψ (x + c • (y - x)) - gradient ψ x‖ * ‖y - x‖ := real_inner_le_norm _ _
  have e3 : ‖gradient ψ (x + c • (y - x)) - gradient ψ x‖ ≤ L * (c * ‖y - x‖) := by
    have := hlip (x + c • (y - x)) x
    rwa [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hc0.le] at this
  have e4 : 0 ≤ ‖y - x‖ := norm_nonneg _
  have e5 := mul_le_mul_of_nonneg_right e3 e4
  have e6 : 0 ≤ L * c := mul_nonneg hL hc0.le
  rw [inner_sub_left] at e2
  have hneg : (inner ℝ (gradient ψ (x + c • (y - x))) (y - x) - inner ℝ (gradient ψ x) (y - x)
        - L * c * ‖y - x‖ ^ 2) ≤ 0 := by nlinarith [e6]
  rw [hcd] at hneg
  simp only [sub_zero, div_one, one_smul, zero_smul, add_zero, one_mul, one_pow, mul_one,
    zero_mul, zero_pow two_ne_zero, mul_zero, add_sub_cancel] at hneg
  linarith

lemma saga_aux_convex_grad {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} (hd : Differentiable ℝ ψ)
    (hc : ConvexOn ℝ Set.univ ψ) (x y : EuclideanSpace ℝ (Fin n)) :
    ψ x + inner ℝ (gradient ψ x) (y - x) ≤ ψ y := by
  have hconv : ConvexOn ℝ Set.univ (fun t : ℝ => ψ (x + t • (y - x))) := by
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ μ ν hμ hν hμν
    have e : x + (μ • a + ν • b) • (y - x) = μ • (x + a • (y - x)) + ν • (x + b • (y - x)) := by
      calc x + (μ • a + ν • b) • (y - x) = (μ + ν) • x + (μ • a + ν • b) • (y - x) := by
            rw [hμν, one_smul]
        _ = _ := by simp only [smul_add, add_smul, smul_eq_mul, mul_smul]; abel
    simp only [e]
    exact hc.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν
  have hder := sagaA_hasDerivAt_line hd x (y - x) 0
  rw [zero_smul, add_zero] at hder
  have := hconv.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hder
  rw [slope_def_field] at this
  simp only [sub_zero, div_one, one_smul, zero_smul, add_zero, add_sub_cancel] at this
  linarith

lemma saga_aux_cocoercive {n : ℕ} {ψ : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 < L)
    (hd : Differentiable ℝ ψ) (hc : ConvexOn ℝ Set.univ ψ)
    (hlip : ∀ a b, ‖gradient ψ a - gradient ψ b‖ ≤ L * ‖a - b‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    ψ x + inner ℝ (gradient ψ x) (y - x) + 1 / (2 * L) * ‖gradient ψ y - gradient ψ x‖ ^ 2
      ≤ ψ y := by
  have h3 := saga_aux_convex_grad hd hc x (y - (1 / L) • (gradient ψ y - gradient ψ x))
  have h2 := saga_aux_descent hL.le hd hlip y (y - (1 / L) • (gradient ψ y - gradient ψ x))
  have e1 : y - (1 / L) • (gradient ψ y - gradient ψ x) - x
      = (y - x) - (1 / L) • (gradient ψ y - gradient ψ x) := by abel
  have e2 : y - (1 / L) • (gradient ψ y - gradient ψ x) - y
      = -((1 / L) • (gradient ψ y - gradient ψ x)) := by abel
  rw [e1, inner_sub_right, inner_smul_right] at h3
  rw [e2, inner_neg_right, inner_smul_right, norm_neg, norm_smul,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 / L)] at h2
  have e3 : inner ℝ (gradient ψ y) (gradient ψ y - gradient ψ x)
      - inner ℝ (gradient ψ x) (gradient ψ y - gradient ψ x)
      = ‖gradient ψ y - gradient ψ x‖ ^ 2 := by
    rw [← inner_sub_left, real_inner_self_eq_norm_sq]
  have key : 1 / (2 * L) * ‖gradient ψ y - gradient ψ x‖ ^ 2
      = 1 / L * (inner ℝ (gradient ψ y) (gradient ψ y - gradient ψ x)
          - inner ℝ (gradient ψ x) (gradient ψ y - gradient ψ x))
        - L / 2 * (1 / L * ‖gradient ψ y - gradient ψ x‖) ^ 2 := by
    rw [e3]; field_simp; ring
  linarith [key]

lemma saga_aux_prox_real {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ} {η : ℝ}
    {w p : EuclideanSpace ℝ (Fin n)}
    (hp : p ∈ proximalMapping (liftRealtoEReal h) η w) (z : EuclideanSpace ℝ (Fin n)) :
    h p + (2 * η)⁻¹ * ‖p - w‖ ^ 2 ≤ h z + (2 * η)⁻¹ * ‖z - w‖ ^ 2 := by
  unfold proximalMapping liftRealtoEReal at hp
  have h1 := hp.2 z
  rw [← EReal.coe_pow, ← EReal.coe_pow, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at h1
  exact h1

lemma saga_aux_prox_subgrad {n : ℕ} {h : EuclideanSpace ℝ (Fin n) → ℝ}
    (hh : ConvexOn ℝ Set.univ h) {c : ℝ} (hc : 0 < c) {w p : EuclideanSpace ℝ (Fin n)}
    (hp : ∀ z, h p + c * ‖p - w‖ ^ 2 ≤ h z + c * ‖z - w‖ ^ 2) (z : EuclideanSpace ℝ (Fin n)) :
    h p + 2 * c * inner ℝ (w - p) (z - p) ≤ h z := by
  have _hc : 0 ≤ c := hc.le  -- (positivity of `c` is not actually needed)
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ (h z - h p - 2 * c * inner ℝ (w - p) (z - p)) + t * (c * ‖z - p‖ ^ 2) := by
    intro t ht0 ht1
    have hconv := hh.2 (Set.mem_univ p) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul] at hconv
    have hzt : (1 - t) • p + t • z = p + t • (z - p) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hzt] at hconv
    have h2 := hp (p + t • (z - p))
    have hnorm : ‖p + t • (z - p) - w‖ ^ 2
        = ‖p - w‖ ^ 2 + 2 * t * inner ℝ (p - w) (z - p) + t ^ 2 * ‖z - p‖ ^ 2 := by
      have : p + t • (z - p) - w = (p - w) + t • (z - p) := by abel
      rw [this, norm_add_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
        sq_abs]
      ring
    rw [hnorm] at h2
    have hinner : inner ℝ (w - p) (z - p) = - inner ℝ (p - w) (z - p) := by
      rw [← inner_neg_left, neg_sub]
    rw [hinner]
    have h3 : 0 ≤ t * ((h z - h p - 2 * c * -inner ℝ (p - w) (z - p)) + t * (c * ‖z - p‖ ^ 2)) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right h3 ht0
  have := saga_aux_lim key
  linarith

lemma saga_aux_avg_descent {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hL : 0 ≤ L) (hm : 0 < m) (hd : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    finiteSumObjective f y ≤ finiteSumObjective f x
      + inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) x) (y - x) + L / 2 * ‖y - x‖ ^ 2 := by
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : ∑ i, f i y
      ≤ ∑ i, (f i x + inner ℝ (gradient (f i) x) (y - x) + L / 2 * ‖y - x‖ ^ 2) :=
    Finset.sum_le_sum (fun i _ => saga_aux_descent hL (hd i) (hlip i) x y)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] at hsum
  unfold finiteSumObjective
  rw [real_inner_smul_left, sum_inner]
  have h2 := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hmpos))
  calc _ ≤ _ := h2
    _ = _ := by
      rw [mul_add, mul_add, ← mul_assoc, one_div_mul_cancel hmpos.ne', one_mul]

lemma saga_aux_avg_cocoercive {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hd : ∀ i, Differentiable ℝ (f i))
    (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (x y : EuclideanSpace ℝ (Fin n)) :
    finiteSumObjective f x + inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) x) (y - x)
      + 1 / (2 * L) * ((1 / (m : ℝ)) * ∑ i, ‖gradient (f i) y - gradient (f i) x‖ ^ 2)
      ≤ finiteSumObjective f y := by
  have hmpos : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hsum : ∑ i, (f i x + inner ℝ (gradient (f i) x) (y - x)
      + 1 / (2 * L) * ‖gradient (f i) y - gradient (f i) x‖ ^ 2) ≤ ∑ i, f i y :=
    Finset.sum_le_sum (fun i _ => saga_aux_cocoercive hL (hd i) (hc i) (hlip i) x y)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  unfold finiteSumObjective
  rw [real_inner_smul_left, sum_inner]
  have h2 := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.mpr hmpos))
  calc _ = (1 / (m:ℝ)) * (∑ i, f i x + ∑ i, inner ℝ (gradient (f i) x) (y - x)
        + 1 / (2 * L) * ∑ i, ‖gradient (f i) y - gradient (f i) x‖ ^ 2) := by ring
    _ ≤ _ := h2

lemma saga_aux_opt {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 ≤ L) (hm : 0 < m)
    (hd : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (hh : ConvexOn ℝ Set.univ h) {xs : EuclideanSpace ℝ (Fin n)}
    (hxs : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ xs)
    (z : EuclideanSpace ℝ (Fin n)) :
    h xs - inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) xs) (z - xs) ≤ h z := by
  set G := (1 / (m : ℝ)) • ∑ i, gradient (f i) xs with hG
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      0 ≤ (h z - h xs + inner ℝ G (z - xs)) + t * (L / 2 * ‖z - xs‖ ^ 2) := by
    intro t ht0 ht1
    have hmin := isMinOn_iff.mp hxs (xs + t • (z - xs)) (Set.mem_univ _)
    simp only at hmin
    have hdesc := saga_aux_avg_descent hL hm hd hlip xs (xs + t • (z - xs))
    have hsub : xs + t • (z - xs) - xs = t • (z - xs) := by abel
    rw [hsub, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hdesc
    have hconv := hh.2 (Set.mem_univ xs) (Set.mem_univ z) (by linarith : (0:ℝ) ≤ 1 - t) ht0.le
      (by ring : (1 - t) + t = 1)
    simp only [smul_eq_mul] at hconv
    have hzt : (1 - t) • xs + t • z = xs + t • (z - xs) := by
      rw [smul_sub, sub_smul, one_smul]; abel
    rw [hzt] at hconv
    have h3 : 0 ≤ t * ((h z - h xs + inner ℝ G (z - xs)) + t * (L / 2 * ‖z - xs‖ ^ 2)) := by
      nlinarith
    exact nonneg_of_mul_nonneg_right h3 ht0
  have := saga_aux_lim key
  linarith

lemma saga_aux_grad_sum {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    (hd : ∀ i, Differentiable ℝ (f i)) (x v : EuclideanSpace ℝ (Fin n)) :
    inner ℝ (gradient (finiteSumObjective f) x) v
      = inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) x) v := by
  have hF : HasFDerivAt (finiteSumObjective f) ((1 / (m:ℝ)) • ∑ i, fderiv ℝ (f i) x) x := by
    unfold finiteSumObjective
    have := HasFDerivAt.fun_sum (u := Finset.univ) (fun i _ => (hd i x).hasFDerivAt)
    exact this.const_mul (1 / (m:ℝ))
  rw [inner_gradient_left hF.differentiableAt, hF.fderiv, real_inner_smul_left, sum_inner]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sum_apply, smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [inner_gradient_left (hd i x)]

noncomputable def sagaKabs {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}
    (L : ℝ) (d : V) (A B : Fin m → V) (j : Fin m) : ℝ :=
  3 * L / 2 * ‖d‖ ^ 2
    + inner ℝ ((1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i) d
    + 1 / (4 * L) * ‖(1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
    - 1 / (2 * L) * ((1 / (m : ℝ)) * ∑ i, ‖A i‖ ^ 2)
    + 9 * L / 4 * ‖d - (1 / (3 * L)) • (A j - B j + (1 / (m : ℝ)) • ∑ i, B i)‖ ^ 2
    + 1 / L * (∑ i, ‖B i‖ ^ 2 - ‖B j‖ ^ 2 + ‖A j‖ ^ 2)

lemma sagaC_sq_sub_le {V : Type*} [NormedAddCommGroup V] (a b : V) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 := norm_sub_le a b
  have h2 := norm_nonneg (a - b)
  nlinarith [sq_nonneg (‖a‖ - ‖b‖), norm_nonneg a, norm_nonneg b]

lemma sagaC_var_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}
    (hm : 0 < m) (c : Fin m → V) :
    ∑ j, ‖c j - (1 / (m : ℝ)) • ∑ i, c i‖ ^ 2 ≤ ∑ j, ‖c j‖ ^ 2 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  obtain ⟨cb, hcb⟩ : ∃ cb : V, (1 / (m : ℝ)) • ∑ i, c i = cb := ⟨_, rfl⟩
  have hsum : ∑ i, c i = (m : ℝ) • cb := by
    rw [← hcb, smul_smul, mul_one_div_cancel hm'.ne', one_smul]
  rw [hcb]
  simp_rw [norm_sub_sq_real]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have : 0 ≤ (m:ℝ) * ‖cb‖ ^ 2 := by positivity
  linarith

lemma sagaC_expand {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {L : ℝ}
    (hL : 0 < L) (d u : V) :
    9 * L / 4 * ‖d - (1 / (3 * L)) • u‖ ^ 2
      = 9 * L / 4 * ‖d‖ ^ 2 - 3 / 2 * inner ℝ u d + 1 / (4 * L) * ‖u‖ ^ 2 := by
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ) < 1 / (3 * L)), real_inner_comm]
  field_simp
  ring

lemma sagaKabs_avg {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {m : ℕ}
    (hm : 0 < m) {L : ℝ} (hL : 0 < L) (d : V) (A B : Fin m → V)
    (hco : ∀ i, 1 / L * ‖A i‖ ^ 2 ≤ inner ℝ (A i) d) :
    (1 / (m : ℝ)) * ∑ j, sagaKabs L d A B j ≤ 15 * L / 4 * ‖d‖ ^ 2 + 1 / L * ∑ i, ‖B i‖ ^ 2 := by
  have hm' : (0:ℝ) < m := by exact_mod_cast hm
  have hXc : ∀ j, ‖(1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i‖
      = ‖(A j - B j) - (1 / (m : ℝ)) • ∑ i, (A i - B i)‖ := by
    intro j
    rw [Finset.sum_sub_distrib, smul_sub, ← norm_neg]
    congr 1; abel
  have hX : ∑ j, ‖(1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
      ≤ 2 * ∑ i, ‖A i‖ ^ 2 + 2 * ∑ i, ‖B i‖ ^ 2 := by
    simp_rw [hXc]
    calc _ ≤ ∑ j, ‖A j - B j‖ ^ 2 := sagaC_var_le hm (fun i => A i - B i)
      _ ≤ ∑ j, (2 * ‖A j‖ ^ 2 + 2 * ‖B j‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => sagaC_sq_sub_le _ _)
      _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hZ : ∑ j, ‖A j - B j + (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
      ≤ 2 * ∑ i, ‖A i‖ ^ 2 + 2 * ∑ i, ‖B i‖ ^ 2 := by
    have h1 : ∀ j, ‖A j - B j + (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
        ≤ 2 * ‖A j‖ ^ 2 + 2 * ‖B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2 := by
      intro j
      have e : A j - B j + (1 / (m : ℝ)) • ∑ i, B i
          = A j - (B j - (1 / (m : ℝ)) • ∑ i, B i) := by abel
      rw [e]
      exact sagaC_sq_sub_le _ _
    calc _ ≤ ∑ j, (2 * ‖A j‖ ^ 2 + 2 * ‖B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2) :=
          Finset.sum_le_sum (fun j _ => h1 j)
      _ = 2 * ∑ i, ‖A i‖ ^ 2 + 2 * ∑ j, ‖B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2 := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ _ := by have := sagaC_var_le hm B; linarith
  have hY : 1 / L * ∑ i, ‖A i‖ ^ 2 ≤ ∑ j, inner ℝ (A j - B j + (1 / (m : ℝ)) • ∑ i, B i) d := by
    have e : ∑ j, inner ℝ (A j - B j + (1 / (m : ℝ)) • ∑ i, B i) d = ∑ j, inner ℝ (A j) d := by
      simp only [inner_add_left, inner_sub_left, Finset.sum_add_distrib, Finset.sum_sub_distrib,
        Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, real_inner_smul_left,
        ← sum_inner]
      field_simp
      ring
    rw [e, Finset.mul_sum]
    exact Finset.sum_le_sum (fun i _ => hco i)
  have hW : ∑ j, inner ℝ ((1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i) d
      = 0 := by
    simp only [inner_add_left, inner_sub_left, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, real_inner_smul_left,
      ← sum_inner]
    field_simp
    ring
  have hsum : ∑ j, sagaKabs L d A B j = (m:ℝ) * (15 * L / 4 * ‖d‖ ^ 2)
      + ∑ j, inner ℝ ((1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i) d
      + 1 / (4 * L) * ∑ j, ‖(1 / (m : ℝ)) • ∑ i, A i - A j + B j - (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
      - 1 / (2 * L) * ∑ i, ‖A i‖ ^ 2
      - 3 / 2 * ∑ j, inner ℝ (A j - B j + (1 / (m : ℝ)) • ∑ i, B i) d
      + 1 / (4 * L) * ∑ j, ‖A j - B j + (1 / (m : ℝ)) • ∑ i, B i‖ ^ 2
      + 1 / L * ((m:ℝ) * ∑ i, ‖B i‖ ^ 2 - ∑ i, ‖B i‖ ^ 2 + ∑ i, ‖A i‖ ^ 2) := by
    simp only [sagaKabs, sagaC_expand hL]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← Finset.mul_sum]
    field_simp
    ring
  rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ hm', hsum, hW]
  have e4 : 1 / (4 * L) = 1 / 4 * (1 / L) := by ring
  have e2 : 1 / (2 * L) = 1 / 2 * (1 / L) := by ring
  rw [e4, e2]
  have hL' : 0 ≤ 1 / L := by positivity
  have hX' := mul_le_mul_of_nonneg_left hX hL'
  have hZ' := mul_le_mul_of_nonneg_left hZ hL'
  linarith

noncomputable def sagaPhi {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) : ℝ :=
  15 * L / 4 * ‖y.1 - xs‖ ^ 2 + 1 / L * ∑ i, ‖y.2 i - gradient (f i) xs‖ ^ 2

noncomputable def sagaK {m n : ℕ} (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ) (L : ℝ)
    (xs : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) (j : Fin m) : ℝ :=
  sagaKabs L (y.1 - xs) (fun i => gradient (f i) y.1 - gradient (f i) xs)
    (fun i => y.2 i - gradient (f i) xs) j

lemma sagaK_avg {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hL : 0 < L) (hm : 0 < m) (hd : ∀ i, Differentiable ℝ (f i))
    (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (xs : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) :
    (1 / (m : ℝ)) * ∑ j, sagaK f L xs y j ≤ sagaPhi f L xs y := by
  have hco : ∀ i, 1 / L * ‖gradient (f i) y.1 - gradient (f i) xs‖ ^ 2
      ≤ inner ℝ (gradient (f i) y.1 - gradient (f i) xs) (y.1 - xs) := by
    intro i
    have h1 := saga_aux_cocoercive hL (hd i) (hc i) (hlip i) y.1 xs
    have h2 := saga_aux_cocoercive hL (hd i) (hc i) (hlip i) xs y.1
    rw [norm_sub_rev (gradient (f i) xs)] at h1
    have e1 : inner ℝ (gradient (f i) y.1) (xs - y.1)
        = - inner ℝ (gradient (f i) y.1) (y.1 - xs) := by
      rw [← inner_neg_right, neg_sub]
    rw [e1] at h1
    rw [inner_sub_left]
    have e3 : 1 / L = 2 * (1 / (2 * L)) := by field_simp
    rw [e3]
    linarith
  have key := sagaKabs_avg hm hL (y.1 - xs) (fun i => gradient (f i) y.1 - gradient (f i) xs)
    (fun i => y.2 i - gradient (f i) xs) hco
  unfold sagaK sagaPhi
  exact key

lemma sagaPhi_nonneg {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hL : 0 < L) (xs : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))) :
    0 ≤ sagaPhi f L xs y := by
  unfold sagaPhi
  positivity

lemma sagaK_continuous {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (hg : ∀ i, Continuous (gradient (f i))) (xs : EuclideanSpace ℝ (Fin n)) (j : Fin m) :
    Continuous (fun y => sagaK f L xs y j) := by
  unfold sagaK sagaKabs
  fun_prop

lemma sagaPhi_continuous {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ}
    (xs : EuclideanSpace ℝ (Fin n)) :
    Continuous (fun y => sagaPhi f L xs y) := by
  unfold sagaPhi
  fun_prop

/-- nonexpansiveness-type bound (B) -/
lemma saga_stepB {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 < L) (hm : 0 < m)
    (hd : ∀ i, Differentiable ℝ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (hh : ConvexOn ℝ Set.univ h) {xs : EuclideanSpace ℝ (Fin n)}
    (hxs : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ xs)
    (x xp v : EuclideanSpace ℝ (Fin n))
    (hxp : xp ∈ proximalMapping (liftRealtoEReal h) (1 / (3 * L)) (x - (1 / (3 * L)) • v)) :
    ‖xp - xs‖ ^ 2
      ≤ ‖x - xs - (1 / (3 * L)) • (v - (1 / (m : ℝ)) • ∑ i, gradient (f i) xs)‖ ^ 2 := by
  have hL3 : 0 < 3 * L := by positivity
  have hc : 0 < (2 * (1 / (3 * L)))⁻¹ := by positivity
  have h1 := saga_aux_prox_subgrad hh hc (saga_aux_prox_real hxp) xs
  have h2 := saga_aux_opt hL.le hm hd hlip hh hxs xp
  have h2c : 2 * (2 * (1 / (3 * L)))⁻¹ = 3 * L := by field_simp
  rw [h2c] at h1
  generalize hgs : (1 / (m : ℝ)) • ∑ i, gradient (f i) xs = gs at h2 ⊢
  generalize hγ : 1 / (3 * L) = γ at h1 ⊢
  have h3γ : 3 * L * γ = 1 := by rw [← hγ]; field_simp
  have hw : x - γ • v - xp = (x - xs - γ • (v - gs) - (xp - xs)) - γ • gs := by
    rw [smul_sub]; abel
  have hxsxp : xs - xp = -(xp - xs) := by abel
  rw [hw, hxsxp, inner_neg_right, inner_sub_left, real_inner_smul_left] at h1
  generalize hu : x - xs - γ • (v - gs) = u at h1 ⊢
  generalize hp : xp - xs = p at h1 h2 ⊢
  have h4 : 3 * L * (γ * inner ℝ gs p) = inner ℝ gs p := by rw [← mul_assoc, h3γ, one_mul]
  have h5 : 0 ≤ 3 * L * inner ℝ (u - p) p := by linarith
  have key : 0 ≤ inner ℝ (u - p) p := by
    by_contra hcon
    push_neg at hcon
    have := mul_neg_of_pos_of_neg hL3 hcon
    linarith
  have hnorm : ‖u‖ ^ 2 = ‖u - p‖ ^ 2 + 2 * inner ℝ (u - p) p + ‖p‖ ^ 2 := by
    rw [← norm_add_sq_real, sub_add_cancel]
  rw [hnorm]
  nlinarith [sq_nonneg ‖u - p‖]

lemma sagaD_key {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {L : ℝ}
    (hL : 0 < L) (e a : V) : inner ℝ e a - L * ‖a‖ ^ 2 ≤ 1 / (4 * L) * ‖e‖ ^ 2 := by
  have h0 : 0 ≤ ‖e - (2 * L) • a‖ ^ 2 := sq_nonneg _
  rw [norm_sub_sq_real, real_inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs] at h0
  rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ (by positivity)]
  nlinarith [h0]

lemma saga_step {m n : ℕ} {f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ}
    {h : EuclideanSpace ℝ (Fin n) → ℝ} {L : ℝ} (hL : 0 < L) (hm : 0 < m)
    (hd : ∀ i, Differentiable ℝ (f i)) (hc : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ L * ‖a - b‖)
    (hh : ConvexOn ℝ Set.univ h) {xs : EuclideanSpace ℝ (Fin n)}
    (hxs : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ xs)
    (x xp : EuclideanSpace ℝ (Fin n)) (g gp : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    (hgpj : gp j = gradient (f j) x) (hgpi : ∀ i, i ≠ j → gp i = g i)
    (hxp : xp ∈ proximalMapping (liftRealtoEReal h) (1 / (3 * L))
        (x - (1 / (3 * L)) • (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i))) :
    (finiteSumObjective f xp + h xp) - (finiteSumObjective f xs + h xs)
      + sagaPhi f L xs (xp, gp) ≤ sagaK f L xs (x, g) j := by
  -- (B)
  have hB := saga_stepB hL hm hd hlip hh hxs x xp (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i) hxp
  -- prox inequality at xs
  have hc2 : 0 < (2 * (1 / (3 * L)))⁻¹ := by positivity
  have hA1 := saga_aux_prox_subgrad hh hc2 (saga_aux_prox_real hxp) xs
  have h2c : 2 * (2 * (1 / (3 * L)))⁻¹ = 3 * L := by field_simp
  rw [h2c] at hA1
  have hA2 := saga_aux_avg_descent hL.le hm hd hlip x xp
  have hA3 := saga_aux_avg_cocoercive hL hm hd hc hlip x xs
  have hG : ∑ i, ‖gradient (f i) xs - gradient (f i) x‖ ^ 2
      = ∑ i, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2 :=
    Finset.sum_congr rfl (fun i _ => by rw [norm_sub_rev])
  rw [hG] at hA3
  -- (C) sum split
  have hsum : ∑ i, ‖gp i - gradient (f i) xs‖ ^ 2
      = ∑ i, ‖g i - gradient (f i) xs‖ ^ 2 - ‖g j - gradient (f j) xs‖ ^ 2
        + ‖gradient (f j) x - gradient (f j) xs‖ ^ 2 := by
    have e1 := Finset.add_sum_erase Finset.univ
      (fun i => ‖gp i - gradient (f i) xs‖ ^ 2) (Finset.mem_univ j)
    have e2 := Finset.add_sum_erase Finset.univ
      (fun i => ‖g i - gradient (f i) xs‖ ^ 2) (Finset.mem_univ j)
    have e3 : ∑ i ∈ Finset.univ.erase j, ‖gp i - gradient (f i) xs‖ ^ 2
        = ∑ i ∈ Finset.univ.erase j, ‖g i - gradient (f i) xs‖ ^ 2 :=
      Finset.sum_congr rfl (fun i hi => by rw [hgpi i (Finset.ne_of_mem_erase hi)])
    simp only at e1 e2
    rw [← e1, ← e2, e3, hgpj]
    ring
  -- vector identities
  have hE : (1 / (m : ℝ)) • ∑ i, (gradient (f i) x - gradient (f i) xs)
      - (gradient (f j) x - gradient (f j) xs) + (g j - gradient (f j) xs)
      - (1 / (m : ℝ)) • ∑ i, (g i - gradient (f i) xs)
      = (1 / (m : ℝ)) • ∑ i, gradient (f i) x - (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i) := by
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, smul_sub, smul_sub, hgpj]
    abel
  have hV : (gradient (f j) x - gradient (f j) xs) - (g j - gradient (f j) xs)
      + (1 / (m : ℝ)) • ∑ i, (g i - gradient (f i) xs)
      = (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i) - (1 / (m : ℝ)) • ∑ i, gradient (f i) xs := by
    rw [Finset.sum_sub_distrib, smul_sub, hgpj]
    abel
  have hK : sagaK f L xs (x, g) j = 3 * L / 2 * ‖x - xs‖ ^ 2
      + inner ℝ ((1 / (m : ℝ)) • ∑ i, gradient (f i) x
          - (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i)) (x - xs)
      + 1 / (4 * L) * ‖(1 / (m : ℝ)) • ∑ i, gradient (f i) x
          - (gp j - g j + (1 / (m : ℝ)) • ∑ i, g i)‖ ^ 2
      - 1 / (2 * L) * ((1 / (m : ℝ)) * ∑ i, ‖gradient (f i) x - gradient (f i) xs‖ ^ 2)
      + 9 * L / 4 * ‖x - xs - (1 / (3 * L)) • ((gp j - g j + (1 / (m : ℝ)) • ∑ i, g i)
          - (1 / (m : ℝ)) • ∑ i, gradient (f i) xs)‖ ^ 2
      + 1 / L * (∑ i, ‖g i - gradient (f i) xs‖ ^ 2 - ‖g j - gradient (f j) xs‖ ^ 2
          + ‖gradient (f j) x - gradient (f j) xs‖ ^ 2) := by
    simp only [sagaK, sagaKabs]
    rw [hE, hV]
  have hPhi : sagaPhi f L xs (xp, gp)
      = 15 * L / 4 * ‖xp - xs‖ ^ 2 + 1 / L * ∑ i, ‖gp i - gradient (f i) xs‖ ^ 2 := rfl
  rw [hK, hPhi, hsum]
  generalize hv : gp j - g j + (1 / (m : ℝ)) • ∑ i, g i = v at hA1 hB ⊢
  generalize hgx : (1 / (m : ℝ)) • ∑ i, gradient (f i) x = gx at hA2 hA3 ⊢
  generalize hgs : (1 / (m : ℝ)) • ∑ i, gradient (f i) xs = gs at hB ⊢
  generalize hγ : 1 / (3 * L) = γ at hA1 hB ⊢
  have h3γ : 3 * L * γ = 1 := by rw [← hγ]; field_simp
  -- expansion of the prox inner product
  have hI1 : inner ℝ (x - γ • v - xp) (xs - xp)
      = ‖xp - x‖ ^ 2 + inner ℝ (xp - x) (x - xs)
        + γ * inner ℝ v (xp - x) + γ * inner ℝ v (x - xs) := by
    have e1 : x - γ • v - xp = -((xp - x) + γ • v) := by abel
    have e2 : xs - xp = -((xp - x) + (x - xs)) := by abel
    rw [e1, e2, inner_neg_neg]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  have hA1' : h xp - h xs ≤ -(3 * L * (‖xp - x‖ ^ 2 + inner ℝ (xp - x) (x - xs)))
      - inner ℝ v (xp - x) - inner ℝ v (x - xs) := by
    rw [hI1] at hA1
    have e : 3 * L * (‖xp - x‖ ^ 2 + inner ℝ (xp - x) (x - xs)
        + γ * inner ℝ v (xp - x) + γ * inner ℝ v (x - xs))
        = 3 * L * (‖xp - x‖ ^ 2 + inner ℝ (xp - x) (x - xs))
          + inner ℝ v (xp - x) + inner ℝ v (x - xs) := by
      linear_combination (inner ℝ v (xp - x) + inner ℝ v (x - xs)) * h3γ
    linarith
  have hI3 : inner ℝ gx (xs - x) = -inner ℝ gx (x - xs) := by
    rw [← inner_neg_right, neg_sub]
  have hN : ‖xp - xs‖ ^ 2 = ‖xp - x‖ ^ 2 + 2 * inner ℝ (xp - x) (x - xs) + ‖x - xs‖ ^ 2 := by
    rw [← norm_add_sq_real, sub_add_sub_cancel]
  have hE1 : inner ℝ (gx - v) (x - xs) = inner ℝ gx (x - xs) - inner ℝ v (x - xs) :=
    inner_sub_left _ _ _
  have hE2 : inner ℝ (gx - v) (xp - x) = inner ℝ gx (xp - x) - inner ℝ v (xp - x) :=
    inner_sub_left _ _ _
  have hkey : inner ℝ (gx - v) (xp - x) - L * ‖xp - x‖ ^ 2 ≤ 1 / (4 * L) * ‖gx - v‖ ^ 2 :=
    sagaD_key hL (gx - v) (xp - x)
  have hBL : 9 * L / 4 * ‖xp - xs‖ ^ 2 ≤ 9 * L / 4 * ‖x - xs - γ • (v - gs)‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hB (by positivity)
  have hN' : L * ‖xp - xs‖ ^ 2
      = L * (‖xp - x‖ ^ 2 + 2 * inner ℝ (xp - x) (x - xs) + ‖x - xs‖ ^ 2) := by
    rw [hN]
  linarith

end SagaAux

set_option linter.unusedVariables false in
theorem saga_convex_average_bound
  {k m n : ℕ}
  {Ω : Type*}
  [MeasurableSpace Ω]
  (μ : Measure Ω)
  [IsProbabilityMeasure μ]
  (f : Fin m → EuclideanSpace ℝ (Fin n) → ℝ)
  (h : EuclideanSpace ℝ (Fin n) → ℝ)
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
  (h_saga_seq : IsSAGASequence μ f h x g I (1 / (3 * β)))
  (hf_differentiable : ∀ i, Differentiable ℝ (f i))
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_smooth : ∀ i, LipschitzWith (Real.toNNReal β) (gradient (f i)))
  (hh_convex : ConvexOn ℝ Set.univ h)
  (hx_star : IsMinOn (fun z => finiteSumObjective f z + h z) Set.univ x_star)
  (hf_sum_x_int :
    ∀ t, Integrable (fun ω => finiteSumObjective f (x t ω)) μ)
  (hF_xbar_int :
    Integrable
      (fun ω => finiteSumObjective f (sagaAverageIterate x k ω) +
        h (sagaAverageIterate x k ω)) μ) :
  let f_sum := finiteSumObjective f
  let F := fun z => f_sum z + h z
  ∫ ω, F (sagaAverageIterate x k ω) ∂μ - F x_star ≤
    ((4 * (m : ℝ)) / (k : ℝ)) *
      (((2 * β) / (m : ℝ)) * ‖x0 - x_star‖ ^ 2 +
        f_sum x0 -
          inner ℝ (gradient f_sum x_star) (x0 - x_star) -
        f_sum x_star) := by
  intro f_sum F
  obtain ⟨hx_meas, hg_meas, hI_meas, ⟨hg0, hgupd, hgsame, hprox⟩, hIindep, hIY, hIunif⟩ :=
    h_saga_seq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm_pos
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk_pos
  have hlip : ∀ i a b, ‖gradient (f i) a - gradient (f i) b‖ ≤ β * ‖a - b‖ := by
    intro i a b
    have := (hf_smooth i).dist_le_mul a b
    rwa [Real.coe_toNNReal _ hβ_pos.le, dist_eq_norm, dist_eq_norm] at this
  have hgcont : ∀ i, Continuous (gradient (f i)) := fun i => (hf_smooth i).continuous
  obtain ⟨Y, hY⟩ : ∃ Y : ℕ → Ω → EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)),
      Y = fun t ω => (x t ω, fun i => g t i ω) := ⟨_, rfl⟩
  have hYapp : ∀ t ω, Y t ω = (x t ω, fun i => g t i ω) := by intro t ω; rw [hY]
  have hY_meas : ∀ t, Measurable (Y t) := by
    intro t
    rw [hY]
    exact (hx_meas t).prodMk (measurable_pi_lambda _ fun i => hg_meas t i)
  -- one-step inequality
  have hstep : ∀ t ω, F (x (t + 1) ω) - F x_star + sagaPhi f β x_star (Y (t + 1) ω)
      ≤ sagaK f β x_star (Y t ω) (I t ω) := by
    intro t ω
    rw [hYapp, hYapp]
    exact saga_step hβ_pos hm_pos hf_differentiable hf_convex hlip hh_convex hx_star
      (x t ω) (x (t + 1) ω) (fun i => g t i ω) (fun i => g (t + 1) i ω) (I t ω)
      (hgupd t ω) (fun i hi => hgsame t i ω hi) (hprox t ω)
  -- boundedness of the state
  have hbdd : ∀ t, ∃ R, ∀ ω, ‖Y t ω‖ ≤ R := by
    intro t
    induction t with
    | zero =>
      refine ⟨‖((x0, fun i => gradient (f i) x0) :
        EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)))‖, fun ω => le_of_eq ?_⟩
      rw [hYapp, hx0]
      simp only [hg0, hx0]
    | succ t ih =>
      obtain ⟨R, hR⟩ := ih
      let gs := (1 / (m : ℝ)) • ∑ i, gradient (f i) x_star
      let Θ : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → ℝ := fun y =>
        ‖x_star‖ + ∑ j, ‖y.1 - x_star - (1 / (3 * β)) •
            ((gradient (f j) y.1 - y.2 j + (1 / (m : ℝ)) • ∑ i, y.2 i) - gs)‖
          + ∑ i, ‖gradient (f i) y.1‖ + ‖y‖
      have hΘ : Continuous Θ := by fun_prop
      obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n) ×
        (Fin m → EuclideanSpace ℝ (Fin n))) R).exists_bound_of_continuousOn hΘ.continuousOn
      refine ⟨C, fun ω => ?_⟩
      have hYt : Y t ω ∈ Metric.closedBall 0 R := by simpa using hR ω
      have hΘC : Θ (Y t ω) ≤ C := le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using hC _ hYt)
      have hs1 : 0 ≤ ∑ j, ‖(Y t ω).1 - x_star - (1 / (3 * β)) •
            ((gradient (f j) (Y t ω).1 - (Y t ω).2 j + (1 / (m : ℝ)) • ∑ i, (Y t ω).2 i) - gs)‖ :=
        Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hs2 : 0 ≤ ∑ i, ‖gradient (f i) (Y t ω).1‖ := Finset.sum_nonneg fun _ _ => norm_nonneg _
      have hnormY : ‖Y t ω‖ ≤ Θ (Y t ω) := by
        simp only [Θ]
        linarith [norm_nonneg x_star]
      have hx1 : ‖x (t + 1) ω‖ ≤ Θ (Y t ω) := by
        have hB := saga_stepB hβ_pos hm_pos hf_differentiable hlip hh_convex hx_star
          (x t ω) (x (t + 1) ω) _ (hprox t ω)
        rw [hgupd t ω] at hB
        have hB' := (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).1 hB
        have hterm : ‖x t ω - x_star - (1 / (3 * β)) • ((gradient (f (I t ω)) (x t ω) - g t (I t ω) ω
            + (1 / (m : ℝ)) • ∑ i, g t i ω) - gs)‖ ≤ ∑ j, ‖(Y t ω).1 - x_star - (1 / (3 * β)) •
            ((gradient (f j) (Y t ω).1 - (Y t ω).2 j + (1 / (m : ℝ)) • ∑ i, (Y t ω).2 i) - gs)‖ := by
          rw [hYapp]
          exact Finset.single_le_sum (f := fun j => ‖x t ω - x_star - (1 / (3 * β)) •
            ((gradient (f j) (x t ω) - g t j ω + (1 / (m : ℝ)) • ∑ i, g t i ω) - gs)‖)
            (fun _ _ => norm_nonneg _) (Finset.mem_univ (I t ω))
        have htri : ‖x (t + 1) ω‖ ≤ ‖x_star‖ + ‖x (t + 1) ω - x_star‖ := by
          have := norm_add_le x_star (x (t + 1) ω - x_star)
          simpa using this
        simp only [Θ]
        linarith [norm_nonneg (Y t ω)]
      have hg1 : ∀ i, ‖g (t + 1) i ω‖ ≤ Θ (Y t ω) := by
        intro i
        by_cases hi : i = I t ω
        · subst hi
          rw [hgupd t ω]
          have : ‖gradient (f (I t ω)) (x t ω)‖ ≤ ∑ i, ‖gradient (f i) (Y t ω).1‖ := by
            rw [hYapp]
            exact Finset.single_le_sum (f := fun i => ‖gradient (f i) (x t ω)‖)
              (fun _ _ => norm_nonneg _) (Finset.mem_univ (I t ω))
          simp only [Θ]
          linarith [norm_nonneg (Y t ω), norm_nonneg x_star]
        · rw [hgsame t i ω hi]
          have : ‖g t i ω‖ ≤ ‖Y t ω‖ := by
            rw [hYapp]
            exact (norm_le_pi_norm (fun i => g t i ω) i).trans (norm_snd_le ((x t ω, fun i => g t i ω) :
              EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n))))
          linarith
      calc ‖Y (t + 1) ω‖ ≤ Θ (Y t ω) := by
            rw [hYapp, Prod.norm_def]
            refine max_le hx1 ?_
            exact (pi_norm_le_iff_of_nonneg (le_trans (norm_nonneg _) hnormY)).2 hg1
        _ ≤ C := hΘC
  -- integrability of continuous functions of the state
  have hint : ∀ t (ψ : EuclideanSpace ℝ (Fin n) × (Fin m → EuclideanSpace ℝ (Fin n)) → ℝ),
      Continuous ψ → Integrable (fun ω => ψ (Y t ω)) μ := by
    intro t ψ hψ
    obtain ⟨R, hR⟩ := hbdd t
    obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin n) ×
        (Fin m → EuclideanSpace ℝ (Fin n))) R).exists_bound_of_continuousOn hψ.continuousOn
    exact Integrable.of_bound (hψ.measurable.comp (hY_meas t)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun ω => hC _ (by simpa using hR ω))
  have hPhiint : ∀ t, Integrable (fun ω => sagaPhi f β x_star (Y t ω)) μ :=
    fun t => hint t _ (sagaPhi_continuous x_star)
  have hKjint : ∀ t j, Integrable (fun ω => sagaK f β x_star (Y t ω) j) μ :=
    fun t j => hint t _ (sagaK_continuous hgcont x_star j)
  -- decomposition according to the value of I t
  have hdecomp : ∀ t ω, sagaK f β x_star (Y t ω) (I t ω)
      = ∑ j, (fun i => if i = j then (1 : ℝ) else 0) (I t ω) * sagaK f β x_star (Y t ω) j := by
    intro t ω
    rw [Finset.sum_eq_single (I t ω)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  have hKint : ∀ t, Integrable (fun ω => sagaK f β x_star (Y t ω) (I t ω)) μ := by
    intro t
    rw [funext (hdecomp t)]
    refine integrable_finset_sum _ (fun j _ => ?_)
    refine (hKjint t j).bdd_mul (c := 1) ?_ ?_
    · exact ((measurable_of_countable (fun i : Fin m => if i = j then (1 : ℝ) else 0)).comp
        (hI_meas t)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun ω => ?_
      by_cases hj : I t ω = j <;> simp [hj]
  have hEK : ∀ t, ∫ ω, sagaK f β x_star (Y t ω) (I t ω) ∂μ
      = ∫ ω, (1 / (m : ℝ)) * ∑ j, sagaK f β x_star (Y t ω) j ∂μ := by
    intro t
    have hind : ProbabilityTheory.IndepFun (I t) (Y t) μ := by
      have := hIY t
      rw [hY]
      exact this
    rw [integral_congr_ae (Filter.Eventually.of_forall (hdecomp t))]
    rw [integral_finset_sum _ (fun j _ => ?_)]
    · rw [integral_const_mul, integral_finset_sum _ (fun j _ => hKjint t j), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      have hmul := hind.integral_comp_mul_comp (𝕜 := ℝ)
        (f := fun i => if i = j then (1 : ℝ) else 0) (g := fun y => sagaK f β x_star y j)
        (hI_meas t).aemeasurable (hY_meas t).aemeasurable
        (measurable_of_countable _).aestronglyMeasurable
        (sagaK_continuous hgcont x_star j).aestronglyMeasurable
      simp only [Function.comp_def, Pi.mul_apply] at hmul
      rw [hmul]
      congr 1
      have hind1 : (fun ω => if I t ω = j then (1 : ℝ) else 0) = (I t ⁻¹' {j}).indicator 1 := by
        ext ω
        by_cases hj : I t ω = j <;> simp [hj]
      rw [hind1, integral_indicator_one ((hI_meas t) (measurableSet_singleton j)),
        measureReal_def, hIunif t j]
      simp [ENNReal.toReal_inv]
    · refine (hKjint t j).bdd_mul (c := 1) ?_ ?_
      · exact ((measurable_of_countable (fun i : Fin m => if i = j then (1 : ℝ) else 0)).comp
        (hI_meas t)).aestronglyMeasurable
      · refine Filter.Eventually.of_forall fun ω => ?_
        by_cases hj : I t ω = j <;> simp [hj]
  have hEK_le : ∀ t, ∫ ω, sagaK f β x_star (Y t ω) (I t ω) ∂μ
      ≤ ∫ ω, sagaPhi f β x_star (Y t ω) ∂μ := by
    intro t
    rw [hEK t]
    refine integral_mono ?_ (hPhiint t) (fun ω => sagaK_avg hβ_pos hm_pos hf_differentiable
      hf_convex hlip x_star (Y t ω))
    exact (integrable_finset_sum _ (fun j _ => hKjint t j)).const_mul _
  -- Jensen
  have hJensen : ∀ p : ℕ → EuclideanSpace ℝ (Fin n),
      F ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, F (p t) := by
    intro p
    have hw0 : ∀ t ∈ Finset.range k, (0 : ℝ) ≤ 1 / (k : ℝ) := fun _ _ => by positivity
    have hw1 : ∑ t ∈ Finset.range k, (1 / (k : ℝ)) = 1 := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      field_simp
    have hpts : ∀ t ∈ Finset.range k, p t ∈ (Set.univ : Set (EuclideanSpace ℝ (Fin n))) :=
      fun _ _ => Set.mem_univ _
    have hfi : ∀ i, f i ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        ≤ ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * f i (p t) := by
      intro i
      have := (hf_convex i).map_sum_le hw0 hw1 hpts
      simpa [Finset.smul_sum, smul_eq_mul] using this
    have hhh : h ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        ≤ ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * h (p t) := by
      have := hh_convex.map_sum_le hw0 hw1 hpts
      simpa [Finset.smul_sum, smul_eq_mul] using this
    show (1 / (m : ℝ)) * ∑ i, f i ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        + h ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, ((1 / (m : ℝ)) * ∑ i, f i (p t) + h (p t))
    calc (1 / (m : ℝ)) * ∑ i, f i ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        + h ((1 / (k : ℝ)) • ∑ t ∈ Finset.range k, p t)
        ≤ (1 / (m : ℝ)) * ∑ i, ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * f i (p t)
          + ∑ t ∈ Finset.range k, (1 / (k : ℝ)) * h (p t) := by
          gcongr with i
          · exact hfi i
      _ = (1 / (k : ℝ)) * ∑ t ∈ Finset.range k, ((1 / (m : ℝ)) * ∑ i, f i (p t) + h (p t)) := by
          rw [Finset.sum_comm]
          simp only [Finset.mul_sum, mul_add, Finset.sum_add_distrib]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => Finset.sum_congr rfl (fun i _ => ?_))
          ring
  -- pointwise bound
  have hpw : ∀ ω, F (sagaAverageIterate x k ω) - F x_star
      ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k,
          (sagaK f β x_star (Y t ω) (I t ω) - sagaPhi f β x_star (Y (t + 1) ω)) := by
    intro ω
    have hJ := hJensen (fun t => x (t + 1) ω)
    have hs : ∀ t ∈ Finset.range k, F (x (t + 1) ω) - F x_star
        ≤ sagaK f β x_star (Y t ω) (I t ω) - sagaPhi f β x_star (Y (t + 1) ω) :=
      fun t _ => by linarith [hstep t ω]
    have hsum := Finset.sum_le_sum hs
    rw [Finset.sum_sub_distrib] at hsum
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
    have hrw : sagaAverageIterate x k ω = (1 / (k : ℝ)) • ∑ t ∈ Finset.range k, x (t + 1) ω := rfl
    rw [hrw]
    have hk1 : (1 / (k : ℝ)) * ((k : ℝ) * F x_star) = F x_star := by field_simp
    have := mul_le_mul_of_nonneg_left hsum (le_of_lt (one_div_pos.2 hkR))
    rw [mul_sub, hk1] at this
    linarith
  -- integrate
  have hFint : Integrable (fun ω => F (sagaAverageIterate x k ω)) μ := hF_xbar_int
  have hdiff : ∀ t, Integrable (fun ω => sagaK f β x_star (Y t ω) (I t ω)
      - sagaPhi f β x_star (Y (t + 1) ω)) μ := fun t => (hKint t).sub (hPhiint (t + 1))
  have hRint : Integrable (fun ω => (1 / (k : ℝ)) * ∑ t ∈ Finset.range k,
      (sagaK f β x_star (Y t ω) (I t ω) - sagaPhi f β x_star (Y (t + 1) ω))) μ :=
    (integrable_finset_sum _ (fun t _ => hdiff t)).const_mul _
  have hmain : ∫ ω, F (sagaAverageIterate x k ω) ∂μ - F x_star
      ≤ (1 / (k : ℝ)) * sagaPhi f β x_star (x0, fun i => gradient (f i) x0) := by
    have h1 : ∫ ω, F (sagaAverageIterate x k ω) ∂μ - F x_star
        = ∫ ω, (F (sagaAverageIterate x k ω) - F x_star) ∂μ := by
      rw [integral_sub hFint (integrable_const _)]
      simp
    rw [h1]
    calc ∫ ω, (F (sagaAverageIterate x k ω) - F x_star) ∂μ
        ≤ ∫ ω, (1 / (k : ℝ)) * ∑ t ∈ Finset.range k,
          (sagaK f β x_star (Y t ω) (I t ω) - sagaPhi f β x_star (Y (t + 1) ω)) ∂μ :=
          integral_mono (hFint.sub (integrable_const _)) hRint hpw
      _ = (1 / (k : ℝ)) * ∑ t ∈ Finset.range k,
          (∫ ω, sagaK f β x_star (Y t ω) (I t ω) ∂μ - ∫ ω, sagaPhi f β x_star (Y (t + 1) ω) ∂μ) := by
          rw [integral_const_mul, integral_finset_sum _ (fun t _ => hdiff t)]
          congr 1
          refine Finset.sum_congr rfl (fun t _ => ?_)
          exact integral_sub (hKint t) (hPhiint (t + 1))
      _ ≤ (1 / (k : ℝ)) * ∑ t ∈ Finset.range k,
          (∫ ω, sagaPhi f β x_star (Y t ω) ∂μ - ∫ ω, sagaPhi f β x_star (Y (t + 1) ω) ∂μ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun t _ => ?_) (by positivity)
          linarith [hEK_le t]
      _ = (1 / (k : ℝ)) * (∫ ω, sagaPhi f β x_star (Y 0 ω) ∂μ
          - ∫ ω, sagaPhi f β x_star (Y k ω) ∂μ) := by
          rw [Finset.sum_range_sub' (fun t => ∫ ω, sagaPhi f β x_star (Y t ω) ∂μ)]
      _ ≤ (1 / (k : ℝ)) * sagaPhi f β x_star (x0, fun i => gradient (f i) x0) := by
          have hY0 : ∀ ω, Y 0 ω = (x0, fun i => gradient (f i) x0) := by
            intro ω
            rw [hYapp, hx0]
            simp only [hg0, hx0]
          have hnn : 0 ≤ ∫ ω, sagaPhi f β x_star (Y k ω) ∂μ :=
            integral_nonneg (fun ω => sagaPhi_nonneg hβ_pos x_star _)
          simp only [hY0, integral_const, probReal_univ, one_smul]
          gcongr
          linarith
  -- final algebra
  refine hmain.trans ?_
  have hgrad := saga_aux_grad_sum (m := m) hf_differentiable x_star (x0 - x_star)
  have hco := saga_aux_avg_cocoercive hβ_pos hm_pos hf_differentiable hf_convex hlip x_star x0
  have hS : 0 ≤ ∑ i, ‖gradient (f i) x0 - gradient (f i) x_star‖ ^ 2 :=
    Finset.sum_nonneg fun _ _ => by positivity
  have hN : 0 ≤ ‖x0 - x_star‖ ^ 2 := by positivity
  have hfin : ∀ (S N P Q R : ℝ), 0 ≤ S → 0 ≤ N → 1 / (2 * β) * ((1 / (m : ℝ)) * S) ≤ P - Q - R →
      1 / (k : ℝ) * (15 * β / 4 * N + 1 / β * S)
        ≤ 4 * (m : ℝ) / (k : ℝ) * (2 * β / (m : ℝ) * N + P - Q - R) := by
    intro S N P Q R hS hN hDS
    have hPQR : 2 * β / (m : ℝ) * N + P - Q - R = 2 * β / (m : ℝ) * N + (P - Q - R) := by ring
    rw [hPQR]
    generalize P - Q - R = D at hDS ⊢
    have hD0 : 0 ≤ D := le_trans (by positivity) hDS
    have hSD : 1 / β * S ≤ 2 * (m : ℝ) * D := by
      have h2 : 1 / β * S = 2 * (m : ℝ) * (1 / (2 * β) * ((1 / (m : ℝ)) * S)) := by
        field_simp
      rw [h2]
      exact mul_le_mul_of_nonneg_left hDS (by positivity)
    have h3 : 4 * (m : ℝ) / (k : ℝ) * (2 * β / (m : ℝ) * N + D)
        = 1 / (k : ℝ) * (8 * β * N + 4 * (m : ℝ) * D) := by
      field_simp
      ring
    rw [h3]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    nlinarith
  have hDS : 1 / (2 * β) * ((1 / (m : ℝ)) * ∑ i, ‖gradient (f i) x0 - gradient (f i) x_star‖ ^ 2)
      ≤ finiteSumObjective f x0 - inner ℝ (gradient (finiteSumObjective f) x_star) (x0 - x_star)
        - finiteSumObjective f x_star := by
    rw [hgrad]
    linarith
  exact hfin _ _ _ _ _ hS hN hDS

end saga_convex_average_bound
