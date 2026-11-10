import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex7`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex7`, so the main result is `FCA_chap_E_ex7.FCA_chap_E_ex7`.
-/

namespace FCA_chap_E_ex7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex7 (m : ℕ) (p : ℝ)
  (r : ℕ → ℝ)
  (a : ℕ → ℝ)
  (f : ℕ → (EuclideanSpace ℝ (Fin 1) → EReal))
  (hp : p > 0) (hm : m > 0)
  (hr : ∀ i ∈ Finset.range m, r i > 0)
  (hf : ∀ i ∈ Finset.range m, ∀ (x : EuclideanSpace ℝ (Fin 1)),
        (f i x) = ((((p + 1) * (r i) ^ p)⁻¹ * (abs (x 0 - (a i)) ^ (p + 1)) : ℝ) : EReal))
  (f_ne_bot : ∀ x₁ x₂, ⊥ < f x₁ x₂) :
  let f_infconv := multiInfimalConv m f
  let r_sum := ∑ i ∈ Finset.range m, r i
  let a_sum := ∑ i ∈ Finset.range m, a i
  ∀ (x : EuclideanSpace ℝ (Fin 1)),
  f_infconv x = ((((p + 1) * r_sum ^ p)⁻¹ * (abs (x 0 - a_sum)) ^ (p + 1) : ℝ) : EReal) := by
  intro f_infconv r_sum a_sum x
  -- Weighted power-mean (Jensen) consequence: Radon-type inequality
  have key : ∀ (s : Finset ℕ) (r z : ℕ → ℝ), (∀ i ∈ s, 0 < r i) → s.Nonempty →
      |∑ i ∈ s, z i| ^ (p + 1) / (∑ i ∈ s, r i) ^ p ≤ ∑ i ∈ s, |z i| ^ (p + 1) / r i ^ p := by
    intro s r z hr hs
    set R := ∑ i ∈ s, r i with hRdef
    have hR : 0 < R := Finset.sum_pos hr hs
    have hq : 1 ≤ p + 1 := by linarith
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow s (fun i => r i / R) (fun i => |z i| / r i)
      (fun i hi => (div_pos (hr i hi) hR).le)
      (by rw [← Finset.sum_div]; exact div_self hR.ne')
      (fun i hi => div_nonneg (abs_nonneg _) (hr i hi).le) hq
    have hL : ∑ i ∈ s, r i / R * (|z i| / r i) = (∑ i ∈ s, |z i|) / R := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      have := (hr i hi).ne'
      field_simp
    have hRt : ∀ i ∈ s, r i / R * (|z i| / r i) ^ (p + 1) = (|z i| ^ (p + 1) / r i ^ p) / R := by
      intro i hi
      have hri := hr i hi
      rw [Real.div_rpow (abs_nonneg _) hri.le, Real.rpow_add_one hri.ne']
      have := hri.ne'
      have : r i ^ p ≠ 0 := (Real.rpow_pos_of_pos hri p).ne'
      field_simp
    simp only at hJ
    rw [hL, Finset.sum_congr rfl hRt, ← Finset.sum_div,
      Real.div_rpow (Finset.sum_nonneg (fun i _ => abs_nonneg _)) hR.le,
      Real.rpow_add_one hR.ne'] at hJ
    have h1 : |∑ i ∈ s, z i| ^ (p + 1) ≤ (∑ i ∈ s, |z i|) ^ (p + 1) :=
      Real.rpow_le_rpow (abs_nonneg _) (Finset.abs_sum_le_sum_abs _ _) (by linarith)
    have hRp : 0 < R ^ p := Real.rpow_pos_of_pos hR p
    rw [div_le_div_iff₀ (mul_pos hRp hR) hR] at hJ
    rw [div_le_iff₀ hRp]
    have h2 : (∑ i ∈ s, |z i|) ^ (p + 1) ≤ (∑ i ∈ s, |z i| ^ (p + 1) / r i ^ p) * R ^ p := by
      have : (∑ i ∈ s, |z i|) ^ (p + 1) * R
          ≤ ((∑ i ∈ s, |z i| ^ (p + 1) / r i ^ p) * R ^ p) * R := by
        rw [mul_assoc]; exact hJ
      exact le_of_mul_le_mul_right this hR
    linarith
  have hne : (Finset.range m).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  have hR : 0 < r_sum := Finset.sum_pos (fun i hi => hr i hi) hne
  have hcoe : ∀ (s : Finset ℕ) (g : ℕ → ℝ),
      (∑ i ∈ s, ((g i : ℝ) : EReal)) = ((∑ i ∈ s, g i : ℝ) : EReal) := by
    intro s g
    exact (map_sum (⟨⟨Real.toEReal, EReal.coe_zero⟩, EReal.coe_add⟩ : ℝ →+ EReal) g s).symm
  show sInf _ = _
  apply le_antisymm
  · -- the optimal decomposition y i = a i + (r i / r_sum) * (x - a_sum)
    apply sInf_le
    refine ⟨fun i => WithLp.toLp 2 (fun _ => a i + r i * (x 0 - a_sum) / r_sum), ?_, ?_⟩
    · ext j
      rw [WithLp.ofLp_sum, Finset.sum_apply]
      dsimp only
      rw [Subsingleton.elim j 0]
      rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul]
      have := hR.ne'
      field_simp
      ring
    · rw [Finset.sum_congr rfl (fun i hi => hf i hi _), hcoe]
      congr 1
      set c := x 0 - a_sum with hc
      have hterm : ∀ i ∈ Finset.range m,
          ((p + 1) * r i ^ p)⁻¹ * |(WithLp.toLp 2 (fun _ => a i + r i * c / r_sum) :
            EuclideanSpace ℝ (Fin 1)) 0 - a i| ^ (p + 1)
          = r i * (((p + 1) * r_sum ^ (p + 1))⁻¹ * |c| ^ (p + 1)) := by
        intro i hi
        have hri := hr i hi
        have h1 : (WithLp.toLp 2 (fun _ => a i + r i * c / r_sum) :
            EuclideanSpace ℝ (Fin 1)) 0 - a i = (r i / r_sum) * c := by
          dsimp only; ring
        rw [h1, abs_mul, abs_of_pos (div_pos hri hR),
          Real.mul_rpow (div_pos hri hR).le (abs_nonneg _), Real.div_rpow hri.le hR.le,
          Real.rpow_add_one hri.ne', Real.rpow_add_one hR.ne']
        have : r i ^ p ≠ 0 := (Real.rpow_pos_of_pos hri p).ne'
        have : r_sum ^ p ≠ 0 := (Real.rpow_pos_of_pos hR p).ne'
        have : p + 1 ≠ 0 := by linarith
        have := hri.ne'
        have := hR.ne'
        field_simp
      rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul, Real.rpow_add_one hR.ne']
      have : r_sum ^ p ≠ 0 := (Real.rpow_pos_of_pos hR p).ne'
      have : p + 1 ≠ 0 := by linarith
      have := hR.ne'
      field_simp
      rfl
  · -- lower bound for every decomposition, via `key`
    apply le_sInf
    rintro z ⟨y, hxy, rfl⟩
    rw [Finset.sum_congr rfl (fun i hi => hf i hi _), hcoe]
    apply EReal.coe_le_coe_iff.mpr
    have e1 : ∀ i ∈ Finset.range m, ((p + 1) * r i ^ p)⁻¹ * |y i 0 - a i| ^ (p + 1)
        = (p + 1)⁻¹ * (|y i 0 - a i| ^ (p + 1) / r i ^ p) := by
      intro i hi; rw [mul_inv]; ring
    rw [Finset.sum_congr rfl e1, ← Finset.mul_sum]
    have e2 : ((p + 1) * r_sum ^ p)⁻¹ * |x 0 - a_sum| ^ (p + 1)
        = (p + 1)⁻¹ * (|x 0 - a_sum| ^ (p + 1) / r_sum ^ p) := by rw [mul_inv]; ring
    rw [e2]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hx0 : x 0 - a_sum = ∑ i ∈ Finset.range m, (y i 0 - a i) := by
      rw [Finset.sum_sub_distrib, hxy, WithLp.ofLp_sum, Finset.sum_apply]
    rw [hx0]
    exact key (Finset.range m) r (fun i => y i 0 - a i) hr hne

end FCA_chap_E_ex7
