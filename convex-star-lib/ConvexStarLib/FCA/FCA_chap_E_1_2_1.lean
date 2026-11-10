import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_2_1`, so the main result is `FCA_chap_E_1_2_1.FCA_chap_E_1_2_1`.
-/

namespace FCA_chap_E_1_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_2_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_nondegenerate : IsNondegenerate f) :
  let f' := f
  let f_conj := fun s => conjugate f' s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) =>
    supportFunction {z | (vecHead z, vecLast z) ∈ epigraph f'}
      ((WithLp.equiv 2 _).symm (Fin.snoc s.ofLp (-u)))
  let f_dom_supportfun := fun s => supportFunction {z | z ∈ effDom f'} s
  (conjugate f' =
    fun s => sSup {z : EReal | ∃ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      (z = (((inner ℝ s x) - r : ℝ) : EReal)) ∧ ((x, r) ∈ epigraph f')}) ∧
  f_epi_supportfun = (fun s (u : ℝ) =>
    if u > 0 then (u : EReal) * f_conj (u⁻¹ • s)
    else if u = 0 then f_dom_supportfun s
    else ⊤) := by
  intro f' f_conj f_epi_supportfun f_dom_supportfun
  obtain ⟨⟨x₀, hx₀⟩, ⟨s₀, b₀, hmin⟩⟩ := hf_nondegenerate
  have hbot : ∀ x, f x ≠ ⊥ := by
    intro x h
    have := hmin x
    rw [h, ← EReal.coe_sub] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.mp this)
  -- inner product formula
  have hinner : ∀ (z : EuclideanSpace ℝ (Fin (n+1))) (s : EuclideanSpace ℝ (Fin n)) (u : ℝ),
      inner ℝ z ((WithLp.equiv 2 _).symm (Fin.snoc s.ofLp (-u)) : EuclideanSpace ℝ (Fin (n+1)))
        = inner ℝ (vecHead z) s - u * vecLast z := by
    intro z s u
    simp [PiLp.inner_apply, Fin.sum_univ_castSucc, vecHead, vecLast]
    ring
  -- every (x, r) comes from a z
  have hsurj : ∀ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ), ∃ z : EuclideanSpace ℝ (Fin (n+1)),
      vecHead z = x ∧ vecLast z = r := by
    intro x r
    refine ⟨(WithLp.equiv 2 _).symm (Fin.snoc x.ofLp r), ?_, ?_⟩
    · ext i; simp [vecHead]
    · simp [vecLast]
  -- characterization
  have hepi : ∀ s u, f_epi_supportfun s u =
      sSup {t : EReal | ∃ x r, t = ((inner ℝ x s - u * r : ℝ) : EReal) ∧ f x ≤ r} := by
    intro s u
    simp only [f_epi_supportfun, supportFunction]
    congr 1
    ext t
    simp only [Set.mem_image, Set.mem_setOf_eq, epigraph, f']
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨vecHead z, vecLast z, by rw [hinner], hz⟩
    · rintro ⟨x, r, rfl, hxr⟩
      obtain ⟨z, rfl, rfl⟩ := hsurj x r
      exact ⟨z, hxr, by rw [hinner]⟩
  constructor
  · funext s
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      cases hfx : f x with
      | bot => exact absurd hfx (hbot x)
      | top => simp [f', hfx]
      | coe a =>
        apply le_sSup
        exact ⟨x, a, by simp [f', hfx], by simp [epigraph, f', hfx]⟩
    · apply sSup_le
      rintro _ ⟨x, r, rfl, hr⟩
      refine le_sSup_of_le (Set.mem_image_of_mem _ (Set.mem_univ x)) ?_
      simp only [epigraph, Set.mem_setOf_eq, f'] at hr
      cases hfx : f x with
      | bot => exact absurd hfx (hbot x)
      | top => rw [hfx] at hr; simp at hr
      | coe a =>
        rw [hfx] at hr
        simp only [f', hfx]
        rw [← EReal.coe_sub]
        exact EReal.coe_le_coe_iff.mpr (by have := EReal.coe_le_coe_iff.mp hr; linarith)
  · funext s u
    rw [hepi]
    split_ifs with hu hu0
    · -- u > 0
      have hu' : (0 : EReal) < u := EReal.coe_pos.mpr hu
      have hutop : (u : EReal) ≠ ⊤ := EReal.coe_ne_top u
      simp only [f_conj, conjugate, f']
      apply le_antisymm
      · apply sSup_le
        rintro _ ⟨x, r, rfl, hxr⟩
        cases hfx : f x with
        | bot => exact absurd hfx (hbot x)
        | top => rw [hfx] at hxr; simp at hxr
        | coe a =>
          rw [hfx] at hxr
          have har : a ≤ r := EReal.coe_le_coe_iff.mp hxr
          calc ((inner ℝ x s - u * r : ℝ) : EReal)
              ≤ (u : EReal) * ((inner ℝ (u⁻¹ • s) x - a : ℝ) : EReal) := by
                rw [← EReal.coe_mul]
                apply EReal.coe_le_coe_iff.mpr
                rw [inner_smul_left, real_inner_comm]
                simp only [conj_trivial]
                rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hu.ne', one_mul]
                nlinarith
            _ ≤ (u : EReal) * sSup ((fun x => ((inner ℝ (u⁻¹ • s) x : ℝ) : EReal) - f x) '' Set.univ) := by
                apply mul_le_mul_of_nonneg_left _ hu'.le
                apply le_sSup
                refine ⟨x, Set.mem_univ _, ?_⟩
                simp [hfx]
      · rw [mul_comm, ← EReal.le_div_iff_mul_le hu' hutop]
        apply sSup_le
        rintro _ ⟨x, -, rfl⟩
        rw [EReal.le_div_iff_mul_le hu' hutop]
        show (((inner ℝ (u⁻¹ • s) x : ℝ) : EReal) - f x) * u ≤ _
        cases hfx : f x with
        | bot => exact absurd hfx (hbot x)
        | top => rw [EReal.sub_top, EReal.bot_mul_of_pos hu']; exact bot_le
        | coe a =>
          apply le_sSup
          refine ⟨x, a, ?_, by simp [hfx]⟩
          rw [← EReal.coe_sub, ← EReal.coe_mul]
          congr 1
          rw [inner_smul_left, real_inner_comm]
          simp only [conj_trivial]
          linear_combination (inner ℝ x s) * (inv_mul_cancel₀ hu.ne' : u⁻¹ * u = 1)
    · -- u = 0
      subst hu0
      simp only [f_dom_supportfun, supportFunction, effDom, f']
      congr 1
      ext t
      simp only [Set.mem_setOf_eq, Set.mem_image, zero_mul, sub_zero]
      constructor
      · rintro ⟨x, r, rfl, hxr⟩
        exact ⟨x, lt_of_le_of_lt hxr (EReal.coe_lt_top r), rfl⟩
      · rintro ⟨x, hx, rfl⟩
        cases hfx : f x with
        | bot => exact absurd hfx (hbot x)
        | top => rw [hfx] at hx; simp at hx
        | coe a => exact ⟨x, a, rfl, hfx.le⟩
    · -- u < 0
      have hu' : u < 0 := by push_neg at hu; exact lt_of_le_of_ne hu hu0
      rw [EReal.eq_top_iff_forall_lt]
      intro y
      cases hfx : f x₀ with
      | bot => exact absurd hfx (hbot x₀)
      | top => exact absurd hfx hx₀
      | coe a =>
        have h1 : (y - inner ℝ x₀ s) / (-u) + 1 ≤ max a ((y - inner ℝ x₀ s) / (-u) + 1) :=
          le_max_right _ _
        have h2 : (y - inner ℝ x₀ s) / (-u) * (-u) = y - inner ℝ x₀ s :=
          div_mul_cancel₀ _ (by linarith)
        refine lt_of_lt_of_le ?_ (le_sSup ⟨x₀, max a ((y - inner ℝ x₀ s) / (-u) + 1), rfl, ?_⟩)
        · apply EReal.coe_lt_coe_iff.mpr
          nlinarith
        · rw [hfx]; exact EReal.coe_le_coe_iff.mpr (le_max_left _ _)

end FCA_chap_E_1_2_1
