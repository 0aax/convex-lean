import ConvexStarLib.Defs

/-!
# `bubeck_3_14`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/bubeck_3_14` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace bubeck_3_14`, so the main result is `bubeck_3_14.bubeck_3_14`.
-/

namespace bubeck_3_14

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal


namespace Bubeck314

/-- Standard basis vector with a natural-number index (zero when out of range). -/
noncomputable def bE (n j : ℕ) : EuclideanSpace ℝ (Fin n) :=
  if h : j < n then EuclideanSpace.single ⟨j, h⟩ (1 : ℝ) else 0

/-- `bW 0 = e₀`, `bW (j+1) = e_j - e_{j+1}`. -/
noncomputable def bW (n : ℕ) : ℕ → EuclideanSpace ℝ (Fin n)
  | 0 => bE n 0
  | j + 1 => bE n j - bE n (j + 1)

/-- The quadratic form `x₀² + ∑_{j<t} (x_j - x_{j+1})²`. -/
noncomputable def bQ (n t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  ∑ j ∈ Finset.range (t + 1), (inner ℝ x (bW n j)) ^ 2

noncomputable def bF (n t : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) : ℝ :=
  c * (bQ n t x - 2 * inner ℝ x (bE n 0))

noncomputable def bM (n t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin n) :=
  ∑ j ∈ Finset.range (t + 1), (inner ℝ x (bW n j)) • bW n j

noncomputable def bG (n t : ℕ) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    EuclideanSpace ℝ (Fin n) :=
  (2 * c) • (bM n t x - bE n 0)

noncomputable def bXs (n t : ℕ) : EuclideanSpace ℝ (Fin n) :=
  ∑ j ∈ Finset.range (t + 1), bE n j

lemma inner_bE_right {n j : ℕ} (h : j < n) (x : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x (bE n j) = x ⟨j, h⟩ := by
  simp [bE, h, EuclideanSpace.inner_single_right]

lemma inner_bE_bE_of_ne {n j k : ℕ} (h : j ≠ k) : inner ℝ (bE n j) (bE n k) = 0 := by
  by_cases hk : k < n
  · rw [inner_bE_right hk]
    by_cases hj : j < n
    · simp [bE, hj, EuclideanSpace.single_apply, Fin.ext_iff, Ne.symm h]
    · simp [bE, hj]
  · simp [bE, hk]

lemma inner_bE_self {n j : ℕ} (h : j < n) : inner ℝ (bE n j) (bE n j) = 1 := by
  rw [inner_bE_right h]
  simp [bE, h]

lemma norm_sq_eq_sum_range (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    ‖x‖ ^ 2 = ∑ j ∈ Finset.range n, (inner ℝ x (bE n j)) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Fin.sum_univ_eq_sum_range (fun j => (inner ℝ x (bE n j)) ^ 2)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [inner_bE_right i.isLt]
  simp

lemma sum_sq_le_norm_sq {n m : ℕ} (hm : m ≤ n) (x : EuclideanSpace ℝ (Fin n)) :
    ∑ j ∈ Finset.range m, (inner ℝ x (bE n j)) ^ 2 ≤ ‖x‖ ^ 2 := by
  rw [norm_sq_eq_sum_range]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hm)
    (fun _ _ _ => sq_nonneg _)

lemma bQ_eq (n t : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    bQ n t x = (inner ℝ x (bE n 0)) ^ 2 +
      ∑ j ∈ Finset.range t, (inner ℝ x (bE n j) - inner ℝ x (bE n (j + 1))) ^ 2 := by
  unfold bQ
  rw [Finset.sum_range_succ', add_comm]
  simp [bW, inner_sub_right]

lemma bQ_nonneg (n t : ℕ) (x : EuclideanSpace ℝ (Fin n)) : 0 ≤ bQ n t x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

lemma path_le (X : ℕ → ℝ) (t : ℕ) :
    X 0 ^ 2 + ∑ j ∈ Finset.range t, (X j - X (j + 1)) ^ 2 ≤
      4 * ∑ j ∈ Finset.range (t + 1), X j ^ 2 := by
  have h1 : ∑ j ∈ Finset.range (t + 1), X j ^ 2 = X 0 ^ 2 + ∑ j ∈ Finset.range t, X (j + 1) ^ 2 := by
    rw [Finset.sum_range_succ', add_comm]
  have h2 : ∑ j ∈ Finset.range (t + 1), X j ^ 2 = ∑ j ∈ Finset.range t, X j ^ 2 + X t ^ 2 := by
    rw [Finset.sum_range_succ]
  have h3 : ∑ j ∈ Finset.range t, (X j - X (j + 1)) ^ 2 ≤
      2 * ∑ j ∈ Finset.range t, X j ^ 2 + 2 * ∑ j ∈ Finset.range t, X (j + 1) ^ 2 := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun j _ => by nlinarith [sq_nonneg (X j + X (j + 1))])
  nlinarith [sq_nonneg (X 0), sq_nonneg (X t)]

lemma bQ_le {n t : ℕ} (ht : t < n) (x : EuclideanSpace ℝ (Fin n)) : bQ n t x ≤ 4 * ‖x‖ ^ 2 := by
  rw [bQ_eq]
  have h1 := path_le (fun j => inner ℝ x (bE n j)) t
  have h2 := sum_sq_le_norm_sq (Nat.succ_le_of_lt ht) x
  simp only at h1
  linarith

lemma path_lower (X : ℕ → ℝ) (t : ℕ) (ht : 0 < t) (hXt : X t = 0) :
    (t + 1 : ℝ) * (X 0 ^ 2 + ∑ j ∈ Finset.range t, (X j - X (j + 1)) ^ 2 - 2 * X 0) ≥ - t := by
  have htel : ∑ j ∈ Finset.range t, (X j - X (j + 1)) = X 0 := by
    rw [Finset.sum_range_sub']
    simp [hXt]
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range t) (f := fun j => X j - X (j + 1))
  rw [htel, Finset.card_range] at hcs
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  set D := ∑ j ∈ Finset.range t, (X j - X (j + 1)) ^ 2
  nlinarith [sq_nonneg ((t + 1) * X 0 - t), mul_le_mul_of_nonneg_left hcs (by positivity : (0:ℝ) ≤ t + 1)]

lemma inner_bM (n t : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ y (bM n t x) = ∑ j ∈ Finset.range (t + 1), inner ℝ x (bW n j) * inner ℝ y (bW n j) := by
  simp [bM, inner_sum, inner_smul_right]

lemma bF_eq (n t : ℕ) (c : ℝ) (x y : EuclideanSpace ℝ (Fin n)) :
    bF n t c y = bF n t c x + inner ℝ (y - x) (bG n t c x) + c * bQ n t (y - x) := by
  have h1 : bQ n t y - bQ n t x - 2 * inner ℝ (y - x) (bM n t x) = bQ n t (y - x) := by
    rw [inner_bM]
    simp only [bQ, inner_sub_left]
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  have h2 : inner ℝ (y - x) (bG n t c x) =
      2 * c * (inner ℝ (y - x) (bM n t x) - (inner ℝ y (bE n 0) - inner ℝ x (bE n 0))) := by
    simp only [bG, inner_smul_right, inner_sub_right, inner_sub_left]
  rw [h2]
  unfold bF
  linear_combination c * h1

lemma hasGradientAt_bF {n t : ℕ} (ht : t < n) (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    HasGradientAt (bF n t c) (bG n t c x) x := by
  rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero]
  have key : (fun h => bF n t c (x + h) - bF n t c x -
      (InnerProductSpace.toDual ℝ _ (bG n t c x)) h) = fun h => c * bQ n t h := by
    funext h
    rw [InnerProductSpace.toDual_apply_apply, bF_eq n t c x (x + h)]
    simp only [add_sub_cancel_left, real_inner_comm h]
    ring
  rw [key]
  refine Asymptotics.IsBigO.trans_isLittleO (g := fun h => ‖h‖ ^ 2) ?_
    (Asymptotics.isLittleO_norm_pow_id one_lt_two)
  refine Asymptotics.IsBigO.of_bound (|c| * 4) (Filter.Eventually.of_forall fun h => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (bQ_nonneg n t h),
    abs_of_nonneg (sq_nonneg ‖h‖)]
  have := bQ_le ht h
  nlinarith [abs_nonneg c]

lemma bM_sub (n t : ℕ) (x y : EuclideanSpace ℝ (Fin n)) :
    bM n t x - bM n t y = bM n t (x - y) := by
  simp only [bM, ← Finset.sum_sub_distrib, inner_sub_left, sub_smul]

lemma norm_bM_le {n t : ℕ} (ht : t < n) (z : EuclideanSpace ℝ (Fin n)) :
    ‖bM n t z‖ ≤ 4 * ‖z‖ := by
  have h1 := inner_bM n t z (bM n t z)
  rw [real_inner_self_eq_norm_sq] at h1
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (t + 1)) (fun j => inner ℝ z (bW n j))
    (fun j => inner ℝ (bM n t z) (bW n j))
  rw [← h1] at h2
  have hQz := bQ_le ht z
  have hQu := bQ_le ht (bM n t z)
  unfold bQ at hQz hQu
  have h4 : (‖bM n t z‖ ^ 2) ^ 2 ≤ (4 * ‖z‖ ^ 2) * (4 * ‖bM n t z‖ ^ 2) := by
    refine h2.trans ?_
    exact mul_le_mul hQz hQu (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (by positivity)
  by_cases hA : ‖bM n t z‖ = 0
  · rw [hA]; positivity
  · have hApos : 0 < ‖bM n t z‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hA)
    have hA2 : 0 < ‖bM n t z‖ ^ 2 := by positivity
    have h5 : ‖bM n t z‖ ^ 2 ≤ 16 * ‖z‖ ^ 2 := by
      by_contra hcon
      push_neg at hcon
      nlinarith
    nlinarith [norm_nonneg z]

lemma lipschitz_bG {n t : ℕ} (ht : t < n) {β : ℝ} (hβ : 0 < β) :
    LipschitzWith (Real.toNNReal β) (bG n t (β / 8)) := by
  refine LipschitzWith.of_dist_le_mul (fun x y => ?_)
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hβ.le]
  have : bG n t (β / 8) x - bG n t (β / 8) y = (2 * (β / 8)) • bM n t (x - y) := by
    simp only [bG, ← smul_sub, ← bM_sub]
    congr 1
    abel
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have := norm_bM_le ht (x - y)
  nlinarith

/-- vectors supported on the first `s` coordinates -/
def bV (n s : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin n)) where
  carrier := {z | ∀ j, s ≤ j → inner ℝ z (bE n j) = 0}
  add_mem' := by
    intro a b ha hb j hj
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [inner_add_left, ha j hj, hb j hj, add_zero]
  zero_mem' := by
    intro j hj
    simp
  smul_mem' := by
    intro r a ha j hj
    simp only [Set.mem_setOf_eq] at ha ⊢
    rw [real_inner_smul_left, ha j hj, mul_zero]

lemma mem_bV {n s : ℕ} {z : EuclideanSpace ℝ (Fin n)} :
    z ∈ bV n s ↔ ∀ j, s ≤ j → inner ℝ z (bE n j) = 0 := Iff.rfl

lemma bV_mono {n s s' : ℕ} (h : s ≤ s') : bV n s ≤ bV n s' := by
  intro z hz
  rw [mem_bV] at hz ⊢
  exact fun j hj => hz j (le_trans h hj)

lemma bG_mem {n t s : ℕ} (c : ℝ) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ bV n s) :
    bG n t c x ∈ bV n (s + 1) := by
  rw [mem_bV] at hx ⊢
  intro k hk
  simp only [bG, real_inner_smul_left, inner_sub_left, bM, sum_inner]
  rw [inner_bE_bE_of_ne (by omega : 0 ≠ k)]
  rw [Finset.sum_eq_zero]
  · ring
  intro j _
  cases j with
  | zero => simp [bW, inner_bE_bE_of_ne (by omega : 0 ≠ k)]
  | succ j =>
    by_cases hj : j < s
    · simp [bW, inner_sub_left, inner_bE_bE_of_ne (by omega : j ≠ k),
        inner_bE_bE_of_ne (by omega : j + 1 ≠ k)]
    · have h1 := hx j (by omega)
      have h2 := hx (j + 1) (by omega)
      simp [bW, inner_sub_right, h1, h2]

lemma span_mem {n t : ℕ} (c : ℝ) (x : ℕ → EuclideanSpace ℝ (Fin n))
    (hx : IsBlackBoxSpanProcedure Set.univ (bG n t c) x) : ∀ s, x s ∈ bV n s := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    cases s with
    | zero => rw [hx.1]; exact (bV n 0).zero_mem
    | succ s =>
      refine (Submodule.span_le.mpr ?_) (hx.2.2 s)
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j ≤ s := hj
      exact bV_mono (by omega) (bG_mem c _ (ih j (by omega)))

lemma bF_lower {n t : ℕ} (ht : 0 < t) (c : ℝ) (hc : 0 ≤ c) (x : EuclideanSpace ℝ (Fin n))
    (hx : x ∈ bV n t) : (t + 1 : ℝ) * bF n t c x ≥ - c * t := by
  have h := path_lower (fun j => inner ℝ x (bE n j)) t ht (hx t le_rfl)
  rw [bF, bQ_eq]
  simp only at h
  nlinarith

lemma inner_bXs {n t k : ℕ} (htn : t < n) (hk : k ≤ t) : inner ℝ (bXs n t) (bE n k) = 1 := by
  simp only [bXs, sum_inner]
  rw [Finset.sum_eq_single k]
  · exact inner_bE_self (by omega)
  · intro j _ hjk; exact inner_bE_bE_of_ne hjk
  · intro hk'; simp at hk'; omega

lemma norm_bXs_sq {n t : ℕ} (htn : t < n) : ‖bXs n t‖ ^ 2 = t + 1 := by
  rw [← real_inner_self_eq_norm_sq]
  calc inner ℝ (bXs n t) (bXs n t)
      = inner ℝ (bXs n t) (∑ j ∈ Finset.range (t + 1), bE n j) := rfl
    _ = ∑ j ∈ Finset.range (t + 1), inner ℝ (bXs n t) (bE n j) := inner_sum _ _ _
    _ = ∑ j ∈ Finset.range (t + 1), (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun j hj => inner_bXs htn ?_)
        simp at hj; omega
    _ = t + 1 := by simp

lemma bF_xs {n t : ℕ} (htn : t < n) (c : ℝ) : bF n t c (bXs n t) = -c := by
  rw [bF, bQ_eq, inner_bXs htn (Nat.zero_le _)]
  rw [Finset.sum_eq_zero (fun j hj => by
    simp at hj
    rw [inner_bXs htn (by omega), inner_bXs htn (by omega)]; ring)]
  ring

lemma bF_ge {n t : ℕ} (c : ℝ) (hc : 0 ≤ c) (y : EuclideanSpace ℝ (Fin n)) :
    -c ≤ bF n t c y := by
  rw [bF, bQ_eq]
  have := Finset.sum_nonneg (s := Finset.range t)
    (fun j _ => sq_nonneg (inner ℝ y (bE n j) - inner ℝ y (bE n (j + 1))))
  nlinarith [mul_nonneg hc (add_nonneg (sq_nonneg (inner ℝ y (bE n 0) - 1)) this)]

theorem bubeck_3_14_aux {n t : ℕ}
  (β : ℝ)
  (ht : 2 * t + 1 ≤ n)
  (ht_pos : 0 < t)
  (hβ : β > 0) :
  ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    (ConvexOn ℝ Set.univ f) ∧
    (Differentiable ℝ f) ∧
    (LipschitzWith (Real.toNNReal β) (gradient f)) ∧
    (IsMinOn f Set.univ x_star) ∧
    (‖x_star‖ > 0) ∧
    (IsSubgradientOracle Set.univ f G) ∧
    (∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
      (IsBlackBoxSpanProcedure Set.univ G x) →
        ∀ s, s < t →
          f (x s) - f x_star ≥ ((3 * β) / 32) * (‖x 0 - x_star‖ ^ 2 / (((t : ℝ) + 1) ^ 2))) := by
  have htn : t < n := by omega
  have hc : (0 : ℝ) < β / 8 := by positivity
  have hgrad : ∀ x, HasGradientAt (bF n t (β / 8)) (bG n t (β / 8) x) x :=
    hasGradientAt_bF htn _
  have hgradeq : gradient (bF n t (β / 8)) = bG n t (β / 8) :=
    funext fun x => (hgrad x).gradient
  have hsub : ∀ x y, bF n t (β / 8) y ≥ bF n t (β / 8) x + inner ℝ (y - x) (bG n t (β / 8) x) := by
    intro x y
    rw [bF_eq n t (β / 8) x y]
    have := bQ_nonneg n t (y - x)
    nlinarith
  refine ⟨bF n t (β / 8), bXs n t, bG n t (β / 8), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
    have h1 := hsub (a • x + b • y) x
    have h2 := hsub (a • x + b • y) y
    have h3 : a • (x - (a • x + b • y)) + b • (y - (a • x + b • y)) = 0 := by
      rw [smul_sub, smul_sub, sub_add_sub_comm, ← add_smul, hab, one_smul, sub_self]
    have h4 : a * inner ℝ (x - (a • x + b • y)) (bG n t (β / 8) (a • x + b • y)) +
        b * inner ℝ (y - (a • x + b • y)) (bG n t (β / 8) (a • x + b • y)) = 0 := by
      rw [← real_inner_smul_left, ← real_inner_smul_left, ← inner_add_left, h3, inner_zero_left]
    have h5 := mul_le_mul_of_nonneg_left h1 ha
    have h6 := mul_le_mul_of_nonneg_left h2 hb
    have h7 : a * bF n t (β / 8) (a • x + b • y) + b * bF n t (β / 8) (a • x + b • y) =
        bF n t (β / 8) (a • x + b • y) := by rw [← add_mul, hab, one_mul]
    simp only [smul_eq_mul]
    linarith
  · exact fun x => (hgrad x).differentiableAt
  · rw [hgradeq]; exact lipschitz_bG htn hβ
  · rw [isMinOn_univ_iff]
    intro y
    rw [bF_xs htn]
    exact bF_ge _ hc.le y
  · have h := norm_bXs_sq htn
    have h' : (0 : ℝ) < ‖bXs n t‖ ^ 2 := by rw [h]; positivity
    exact lt_of_le_of_ne (norm_nonneg _) (fun h0 => by rw [← h0] at h'; simp at h')
  · intro z _ y _
    exact hsub z y
  · intro x hx s hs
    have hxs : x s ∈ bV n t := bV_mono hs.le (span_mem _ x hx s)
    have hlow := bF_lower ht_pos (β / 8) hc.le (x s) hxs
    rw [bF_xs htn, hx.1, zero_sub, norm_neg, norm_bXs_sq htn]
    have htp : (0 : ℝ) < t + 1 := by positivity
    have e : (3 * β / 32) * (((t : ℝ) + 1) / ((t : ℝ) + 1) ^ 2) = (3 * β / 32) / ((t : ℝ) + 1) := by
      field_simp
    rw [e, ge_iff_le, div_le_iff₀ htp]
    nlinarith

end Bubeck314

theorem bubeck_3_14 {n t : ℕ}
  (β : ℝ)
  (ht : 2 * t + 1 ≤ n)
  (ht_pos : 0 < t)
  (hβ : β > 0) :
  ∃ (f : EuclideanSpace ℝ (Fin n) → ℝ) (x_star : EuclideanSpace ℝ (Fin n))
    (G : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)),
    (ConvexOn ℝ Set.univ f) ∧
    (Differentiable ℝ f) ∧
    (LipschitzWith (Real.toNNReal β) (gradient f)) ∧
    (IsMinOn f Set.univ x_star) ∧
    (‖x_star‖ > 0) ∧
    (IsSubgradientOracle Set.univ f G) ∧
    (∀ (x : ℕ → EuclideanSpace ℝ (Fin n)),
      (IsBlackBoxSpanProcedure Set.univ G x) →
        ∀ s, s < t →
          f (x s) - f x_star ≥ ((3 * β) / 32) * (‖x 0 - x_star‖ ^ 2 / (((t : ℝ) + 1) ^ 2))) := by
  exact Bubeck314.bubeck_3_14_aux β ht ht_pos hβ

end bubeck_3_14
