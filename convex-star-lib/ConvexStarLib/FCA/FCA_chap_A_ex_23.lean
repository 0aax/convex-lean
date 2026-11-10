import ConvexStarLib.Defs

/-!
# `FCA_chap_A_ex_23`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_A_ex_23` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_A_ex_23`, so the main result is `FCA_chap_A_ex_23.FCA_chap_A_ex_23`.
-/

namespace FCA_chap_A_ex_23

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA23_inner_split {n : ℕ} (hn : n ≥ 2) (x y : EuclideanSpace ℝ (Fin n)) :
    inner ℝ x y = ∑ k : Fin (n - 1), x ⟨k.val, by omega⟩ * y ⟨k.val, by omega⟩
      + x ⟨n - 1, by omega⟩ * y ⟨n - 1, by omega⟩ := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have h1 : inner ℝ x y = ∑ i, x i * y i := by simp [PiLp.inner_apply, mul_comm]
  rw [h1, Fin.sum_univ_castSucc]
  rfl

theorem FCA23_part1 {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))) :
    IsAcuteCone K ↔ K ⊆ {x | -x ∈ polarCone K} := by
  constructor
  · intro h x hx y hy
    rw [inner_neg_left]
    linarith [h x hx y hy]
  · intro h x hx y hy
    have := h hx y hy
    rw [inner_neg_left] at this
    linarith

theorem FCA23_part2 {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp : 1 < p) :
    polarCone (coneKp p hn) =
      {x : EuclideanSpace ℝ (Fin n) | -x ∈ coneKp (p / (p - 1)) hn} := by
  set q := p / (p - 1) with hq_def
  have hpq : p.HolderConjugate q := (Real.holderConjugate_iff_eq_conjExponent hp).mpr rfl
  have hq1 : 1 < q := hpq.symm.lt
  have hp0 : 0 < p := hpq.pos
  have hq0 : 0 < q := hpq.symm.pos
  have hinv : 1 / p + 1 / q = 1 := by rw [one_div, one_div]; exact hpq.inv_add_inv_eq_one
  ext s
  simp only [polarCone, coneKp, Set.mem_setOf_eq, PiLp.neg_apply, abs_neg]
  constructor
  · intro hs
    set S := ∑ k : Fin (n-1), |s ⟨k.val, by omega⟩| ^ q with hS
    have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
    -- step a: s_last ≤ 0
    have hlast : s ⟨n-1, by omega⟩ ≤ 0 := by
      have := hs (WithLp.toLp 2 (fun i : Fin n => if h : i.val < n - 1 then 0 else 1)) ?_
      · rw [FCA23_inner_split hn] at this
        simpa using this
      · simp [Real.zero_rpow hp0.ne', Real.zero_rpow (inv_ne_zero hp0.ne')]
    -- step b
    have hb : ∀ a : ℝ, ∃ b : ℝ, a * b = |a| ^ q ∧ |b| ^ p = |a| ^ q := by
      intro a
      refine ⟨if 0 ≤ a then |a| ^ (q - 1) else -(|a| ^ (q - 1)), ?_, ?_⟩
      · have e : |a| ^ q = |a| * |a| ^ (q - 1) := by
          rw [← Real.rpow_one_add' (abs_nonneg a) (by linarith)]; congr 1; ring
        split_ifs with ha
        · rw [e, abs_of_nonneg ha]
        · rw [e, abs_of_neg (not_le.mp ha)]; ring
      · have e : (|a| ^ (q - 1)) ^ p = |a| ^ q := by
          rw [← Real.rpow_mul (abs_nonneg a)]; congr 1
          linear_combination hpq.mul_eq_add
        split_ifs <;> simp [abs_neg, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg a) _), e]
    choose b hb1 hb2 using hb
    have key := hs (WithLp.toLp 2 (fun i : Fin n => if h : i.val < n - 1 then b (s ⟨i.val, by omega⟩) else S ^ (1/p))) ?_
    · rw [FCA23_inner_split hn] at key
      simp only [Fin.is_lt, dite_true, lt_irrefl, dite_false, hb1] at key
      rw [← hS] at key
      rcases hS0.eq_or_lt with h0 | hpos
      · rw [← h0, Real.zero_rpow (by positivity)]; linarith
      · have h1 : S = S^(1/p) * S^(1/q) := by rw [← Real.rpow_add hpos, hinv, Real.rpow_one]
        have h2 : 0 < S^(1/p) := Real.rpow_pos_of_pos hpos _
        nlinarith
    · simp only [Fin.is_lt, dite_true, lt_irrefl, dite_false, hb2]
      rw [← hS]
  · intro hs x hx
    rw [FCA23_inner_split hn]
    have hH := Real.inner_le_Lp_mul_Lq Finset.univ (fun k : Fin (n-1) => s ⟨k.val, by omega⟩)
      (fun k => x ⟨k.val, by omega⟩) hpq.symm
    set A := (∑ k : Fin (n-1), |s ⟨k.val, by omega⟩| ^ q) ^ (1/q) with hA_def
    set B := (∑ k : Fin (n-1), |x ⟨k.val, by omega⟩| ^ p) ^ (1/p) with hB_def
    have hA : 0 ≤ A := Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)) _
    have hB : 0 ≤ B := Real.rpow_nonneg (Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)) _
    have hx0 : 0 ≤ x ⟨n - 1, by omega⟩ := le_trans hB hx
    have h1 : A + s ⟨n - 1, by omega⟩ ≤ 0 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left hx hA, mul_le_mul_of_nonneg_right h1 hx0]

theorem FCA23_acute_of_sq_bound {n : ℕ} (hn : n ≥ 2) (K : Set (EuclideanSpace ℝ (Fin n)))
    (hK : ∀ x ∈ K, 0 ≤ x ⟨n-1, by omega⟩ ∧
      ∑ k : Fin (n-1), (x ⟨k.val, by omega⟩)^2 ≤ (x ⟨n-1, by omega⟩)^2) :
    IsAcuteCone K := by
  intro x hx y hy
  rw [FCA23_inner_split hn]
  obtain ⟨hx0, hx2⟩ := hK x hx
  obtain ⟨hy0, hy2⟩ := hK y hy
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun k : Fin (n-1) => x ⟨k.val, by omega⟩) (fun k => y ⟨k.val, by omega⟩)
  have h2 : (∑ k : Fin (n-1), x ⟨k.val, by omega⟩ * y ⟨k.val, by omega⟩)^2 ≤
      (x ⟨n-1, by omega⟩ * y ⟨n-1, by omega⟩)^2 := by
    calc _ ≤ _ := hCS
      _ ≤ (x ⟨n-1, by omega⟩)^2 * (y ⟨n-1, by omega⟩)^2 :=
          mul_le_mul hx2 hy2 (Finset.sum_nonneg (fun _ _ => sq_nonneg _)) (sq_nonneg _)
      _ = _ := by ring
  have h3 := abs_le_of_sq_le_sq h2 (mul_nonneg hx0 hy0)
  have h4 := neg_abs_le (∑ k : Fin (n-1), x ⟨k.val, by omega⟩ * y ⟨k.val, by omega⟩)
  linarith

theorem FCA23_coord_le {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp0 : 0 < p)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ coneKp p hn) (k : Fin (n-1)) :
    |x ⟨k.val, by omega⟩| ≤ x ⟨n-1, by omega⟩ := by
  simp only [coneKp, Set.mem_setOf_eq] at hx
  have h1 : |x ⟨k.val, by omega⟩| ^ p ≤ ∑ k : Fin (n-1), |x ⟨k.val, by omega⟩| ^ p :=
    Finset.single_le_sum (f := fun k : Fin (n-1) => |x ⟨k.val, by omega⟩| ^ p)
      (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ k)
  have h2 := Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1 (by positivity : (0:ℝ) ≤ 1 / p)
  rw [one_div, Real.rpow_rpow_inv (abs_nonneg _) hp0.ne', ← one_div] at h2
  linarith

theorem FCA23_sq_bound_of_le_two {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp1 : 1 ≤ p) (hp2 : p ≤ 2)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ coneKp p hn) :
    0 ≤ x ⟨n-1, by omega⟩ ∧
      ∑ k : Fin (n-1), (x ⟨k.val, by omega⟩)^2 ≤ (x ⟨n-1, by omega⟩)^2 := by
  have hp0 : 0 < p := by linarith
  have hk := FCA23_coord_le hn p hp0 x hx
  simp only [coneKp, Set.mem_setOf_eq] at hx
  set t := x ⟨n-1, by omega⟩ with ht
  set S := ∑ k : Fin (n-1), |x ⟨k.val, by omega⟩| ^ p with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hB0 : 0 ≤ S ^ (1/p) := Real.rpow_nonneg hS0 _
  have ht0 : 0 ≤ t := le_trans hB0 hx
  refine ⟨ht0, ?_⟩
  have hSt : S ≤ t ^ p := by
    have : (S^(1/p))^p ≤ t^p := Real.rpow_le_rpow hB0 hx hp0.le
    rwa [one_div, Real.rpow_inv_rpow hS0 hp0.ne'] at this
  have hk2 : ∀ k : Fin (n-1), (x ⟨k.val, by omega⟩)^2 ≤ |x ⟨k.val, by omega⟩| ^ p * t ^ (2 - p) := by
    intro k
    have e : (x ⟨k.val, by omega⟩)^2 = |x ⟨k.val, by omega⟩| ^ p * |x ⟨k.val, by omega⟩| ^ (2 - p) := by
      rw [← Real.rpow_add' (abs_nonneg _) (by ring_nf; norm_num), show p + (2 - p) = 2 by ring,
        Real.rpow_two, sq_abs]
    rw [e]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) (hk k) (by linarith))
      (Real.rpow_nonneg (abs_nonneg _) _)
  calc ∑ k : Fin (n-1), (x ⟨k.val, by omega⟩)^2
      ≤ ∑ k : Fin (n-1), |x ⟨k.val, by omega⟩| ^ p * t ^ (2 - p) := Finset.sum_le_sum (fun k _ => hk2 k)
    _ = S * t ^ (2 - p) := by rw [Finset.sum_mul]
    _ ≤ t ^ p * t ^ (2 - p) := mul_le_mul_of_nonneg_right hSt (Real.rpow_nonneg ht0 _)
    _ = t ^ 2 := by
      rw [← Real.rpow_add' ht0 (by ring_nf; norm_num), show p + (2 - p) = 2 by ring, Real.rpow_two]

theorem FCA23_sq_bound_n2 {n : ℕ} (hn : n ≥ 2) (h2 : n = 2) (p : ℝ) (hp1 : 1 ≤ p)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ coneKp p hn) :
    0 ≤ x ⟨n-1, by omega⟩ ∧
      ∑ k : Fin (n-1), (x ⟨k.val, by omega⟩)^2 ≤ (x ⟨n-1, by omega⟩)^2 := by
  have hp0 : 0 < p := by linarith
  have hk := FCA23_coord_le hn p hp0 x hx
  subst h2
  have h0 := hk ⟨0, by norm_num⟩
  have ht0 : 0 ≤ x ⟨2 - 1, by omega⟩ := le_trans (abs_nonneg _) h0
  refine ⟨ht0, ?_⟩
  haveI : Subsingleton (Fin (2 - 1)) := inferInstanceAs (Subsingleton (Fin 1))
  rw [Fintype.sum_subsingleton _ ⟨0, by norm_num⟩]
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h0 2

theorem FCA23_not_acute {n : ℕ} (hn : n ≥ 2) (h3 : n ≥ 3) (p : ℝ) (hp : 2 < p) :
    ¬ IsAcuteCone (coneKp p hn) := by
  intro hac
  have hp0 : 0 < p := by linarith
  set c : ℝ := (2:ℝ) ^ (1/p) with hc
  have hsum : ∀ a : ℝ, ∑ k : Fin (n-1), (if k.val < 2 then a else 0) = 2 * a := by
    intro a
    rw [Fin.sum_univ_eq_sum_range (fun j => if j < 2 then a else 0) (n-1)]
    obtain ⟨m, hm⟩ : ∃ m, n - 1 = 2 + m := ⟨n - 3, by omega⟩
    rw [hm, Finset.sum_range_add]
    simp [Finset.sum_range_succ]
    ring
  have hmem : ∀ e : ℝ, |e| = 1 →
      (WithLp.toLp 2 (fun i : Fin n => if i.val < 2 then e else if i.val < n - 1 then 0 else c) :
        EuclideanSpace ℝ (Fin n)) ∈ coneKp p hn := by
    intro e he
    simp only [coneKp, Set.mem_setOf_eq, Fin.is_lt, if_true, lt_irrefl, if_false]
    have h2n : ¬ (n - 1 < 2) := by omega
    rw [if_neg h2n]
    have : ∀ k : Fin (n-1), |(if k.val < 2 then e else 0)| ^ p = (if k.val < 2 then 1 else 0) := by
      intro k
      split_ifs
      · rw [he, Real.one_rpow]
      · simp [Real.zero_rpow hp0.ne']
    rw [Finset.sum_congr rfl (fun k _ => this k), hsum, mul_one]
  have hx := hmem 1 (by simp)
  have hy := hmem (-1) (by simp)
  have := hac _ hx _ hy
  rw [FCA23_inner_split hn] at this
  simp only [Fin.is_lt, if_true, lt_irrefl, if_false] at this
  have h2n : ¬ (n - 1 < 2) := by omega
  rw [if_neg h2n, if_neg h2n] at this
  have e1 : ∀ k : Fin (n-1), (if k.val < 2 then (1:ℝ) else 0) * (if k.val < 2 then (-1:ℝ) else 0)
      = (if k.val < 2 then (-1) else 0) := by
    intro k; split_ifs <;> simp
  rw [Finset.sum_congr rfl (fun k _ => e1 k), hsum] at this
  have hcc : c * c < 2 := by
    rw [hc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    calc (2:ℝ) ^ (1 / p + 1 / p) < 2 ^ (1:ℝ) := by
          apply Real.rpow_lt_rpow_of_exponent_lt (by norm_num)
          rw [← add_div, div_lt_one hp0]; linarith
      _ = 2 := Real.rpow_one 2
  linarith

set_option linter.unusedVariables false in
theorem FCA_chap_A_ex_23 :
  (∀ {n : ℕ} (K : Set (EuclideanSpace ℝ (Fin n))),
    IsAcuteCone K ↔ K ⊆ {x | -x ∈ polarCone K}) ∧
  (∀ {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp : 1 < p),
    let q := p / (p - 1)
    polarCone (coneKp p hn) =
      {x : EuclideanSpace ℝ (Fin n) | -x ∈ coneKp q hn}) ∧
  (∀ {n : ℕ} (hn : n ≥ 2) (p : ℝ) (hp : 1 ≤ p),
    (n ≥ 3 → (IsAcuteCone (coneKp p hn) ↔ p ≤ 2)) ∧
    (n = 2 → IsAcuteCone (coneKp p hn))) := by
  refine ⟨fun K => FCA23_part1 K, fun hn p hp => FCA23_part2 hn p hp,
    fun hn p hp => ⟨fun h3 => ⟨fun hac => ?_, fun h2 => ?_⟩, fun h2 => ?_⟩⟩
  · by_contra hcon
    push_neg at hcon
    exact FCA23_not_acute hn h3 p hcon hac
  · exact FCA23_acute_of_sq_bound hn _ (fun x hx => FCA23_sq_bound_of_le_two hn p hp h2 x hx)
  · exact FCA23_acute_of_sq_bound hn _ (fun x hx => FCA23_sq_bound_n2 hn h2 p hp x hx)

end FCA_chap_A_ex_23
