import ConvexStarLib.Defs

/-!
# `FCA_chap_C_2_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_2_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_2_1_2`, so the main result is `FCA_chap_C_2_1_2.FCA_chap_C_2_1_2`.
-/

namespace FCA_chap_C_2_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_2_1_2
  (S : Set E)
  (hS : Set.Nonempty S) :
  let support_fun := supportFunction S
  (IsSublinear support_fun) ∧ (LowerSemicontinuous support_fun) := by
  intro support_fun
  -- every inner product with a point of `S` is below the support function
  have hle : ∀ v ∈ S, ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction S w :=
    fun v hv w => le_sSup (Set.mem_image_of_mem _ hv)
  -- and the support function is the least such upper bound
  have hub : ∀ w (c : EReal), (∀ v ∈ S, ((inner ℝ v w : ℝ) : EReal) ≤ c) →
      supportFunction S w ≤ c := by
    intro w c h
    apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    exact h v hv
  -- one inequality of positive homogeneity
  have hhom : ∀ (x : E) (t : ℝ), 0 < t →
      supportFunction S (t • x) ≤ (t : EReal) * supportFunction S x := by
    intro x t ht
    apply hub
    intro v hv
    rw [real_inner_smul_right, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left (hle v hv x) (by exact_mod_cast ht.le)
  obtain ⟨v₀, hv₀⟩ := hS
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- the support function never takes the value `⊥`
    intro x
    exact lt_of_lt_of_le (EReal.bot_lt_coe _) (hle v₀ hv₀ x)
  · -- it is finite at `0`
    refine ⟨0, lt_of_le_of_lt (hub 0 0 fun v _ => ?_) EReal.zero_lt_top⟩
    simp
  · -- its epigraph is convex
    intro p hp q hq a b ha hb hab
    have hp' : supportFunction S p.1 ≤ (p.2 : EReal) := hp
    have hq' : supportFunction S q.1 ≤ (q.2 : EReal) := hq
    show supportFunction S (a • p.1 + b • q.1) ≤ ((a * p.2 + b * q.2 : ℝ) : EReal)
    apply hub
    intro v hv
    have h1 : inner ℝ v p.1 ≤ p.2 := by exact_mod_cast (hle v hv p.1).trans hp'
    have h2 : inner ℝ v q.1 ≤ q.2 := by exact_mod_cast (hle v hv q.1).trans hq'
    rw [EReal.coe_le_coe_iff, inner_add_right, real_inner_smul_right, real_inner_smul_right]
    exact add_le_add (mul_le_mul_of_nonneg_left h1 ha) (mul_le_mul_of_nonneg_left h2 hb)
  · -- positive homogeneity
    intro x t ht
    apply le_antisymm (hhom x t ht)
    have h2 := hhom (t • x) t⁻¹ (inv_pos.mpr ht)
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h2
    calc (t : EReal) * supportFunction S x
        ≤ (t : EReal) * (((t⁻¹ : ℝ) : EReal) * supportFunction S (t • x)) :=
          mul_le_mul_of_nonneg_left h2 (by exact_mod_cast ht.le)
      _ = supportFunction S (t • x) := by
          rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul]
  · -- lower semicontinuity: a supremum of continuous linear forms
    show LowerSemicontinuous (supportFunction S)
    have h : supportFunction S = fun w => ⨆ v ∈ S, ((inner ℝ v w : ℝ) : EReal) := by
      funext w
      exact sSup_image
    rw [h]
    exact lowerSemicontinuous_biSup fun v _ =>
      (continuous_coe_real_ereal.comp (continuous_const.inner continuous_id)).lowerSemicontinuous

end FCA_chap_C_2_1_2
