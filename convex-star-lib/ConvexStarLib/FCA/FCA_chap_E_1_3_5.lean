import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_5`, so the main result is `FCA_chap_E_1_3_5.FCA_chap_E_1_3_5`.
-/

namespace FCA_chap_E_1_3_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_3_5
  (f : E → EReal)
  (hf_nondegenerate : IsNondegenerate f) :
  epigraph ((biconjugate f)) =
  closure (convexHull ℝ (epigraph f)) := by
  classical
  obtain ⟨⟨x₀, hx₀⟩, ⟨s₀, b, hb⟩⟩ := hf_nondegenerate
  -- KF1
  have KF1 : ∀ (a c : ℝ) (y : EReal),
      ((a : EReal) - y ≤ (c : EReal)) ↔ (((a - c : ℝ) : EReal) ≤ y) := by
    intro a c y
    induction y using EReal.rec with
    | bot =>
      rw [EReal.coe_sub_bot]
      exact iff_of_false (by simp) (le_bot_iff.not.mpr (EReal.coe_ne_bot _))
    | top =>
      rw [EReal.sub_top]
      exact iff_of_true bot_le le_top
    | coe y =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro h <;> linarith
  -- KF2
  have KF2 : ∀ (z y : EReal), z ≤ y ↔ ∀ t : ℝ, y ≤ t → z ≤ t := by
    intro z y
    constructor
    · intro h t ht; exact h.trans ht
    · intro h
      induction y using EReal.rec with
      | bot =>
        induction z using EReal.rec with
        | bot => exact le_rfl
        | top => exact absurd (h 0 bot_le) (by simp)
        | coe z =>
          have := h (z - 1) bot_le
          rw [EReal.coe_le_coe_iff] at this
          linarith
      | top => exact le_top
      | coe y => exact h y le_rfl
  -- conjugate characterization
  have hconj : ∀ (v : E) (c : ℝ), conjugate f v ≤ c ↔
      ∀ x (t : ℝ), f x ≤ t → inner ℝ v x - t ≤ c := by
    intro v c
    unfold conjugate
    rw [sSup_le_iff]
    simp only [Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    apply forall_congr'
    intro x
    rw [KF1, KF2]
    apply forall_congr'
    intro t
    apply imp_congr_right
    intro _
    rw [EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith
  -- biconjugate characterization
  have hbi : ∀ (u : E) (r : ℝ), biconjugate f u ≤ r ↔
      ∀ v (c : ℝ), (∀ x (t : ℝ), f x ≤ t → inner ℝ v x - t ≤ c) → inner ℝ v u - r ≤ c := by
    intro u r
    rw [biconjugate, conjugate, sSup_le_iff]
    simp only [Set.image_univ, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
    apply forall_congr'
    intro v
    rw [KF1, KF2]
    apply forall_congr'
    intro c
    rw [hconj, EReal.coe_le_coe_iff, real_inner_comm u v]
  ext ⟨u, r⟩
  change biconjugate f u ≤ (r : EReal) ↔ _
  rw [hbi]
  constructor
  · -- (⊆)
    intro h
    by_contra hC
    obtain ⟨ℓ, β, hℓC, hℓu⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ (epigraph f)).closure isClosed_closure hC
    set α := ℓ (0, 1) with hα
    set s := (InnerProductSpace.toDual ℝ E).symm (ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ)) with hs
    have hℓ : ∀ x t, ℓ (x, t) = inner ℝ s x + t * α := by
      intro x t
      have : ((x, t) : E × ℝ) = (x, (0:ℝ)) + t • ((0:E), (1:ℝ)) := by simp
      rw [this, map_add, map_smul, smul_eq_mul, hs, InnerProductSpace.toDual_symm_apply]
      rfl
    have hepi : ∀ x (t : ℝ), f x ≤ t → ℓ (x, t) < β := fun x t hxt =>
      hℓC _ (subset_closure (subset_convexHull ℝ _ hxt))
    have hmin : ∀ x (t : ℝ), f x ≤ t → inner ℝ s₀ x - t ≤ b := by
      intro x t hxt
      have := (hb x).trans hxt
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at this
      linarith
    obtain ⟨t₀, ht₀⟩ : ∃ t₀ : ℝ, f x₀ ≤ t₀ := ⟨(f x₀).toReal, EReal.le_coe_toReal hx₀⟩
    have hα0 : α ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      obtain ⟨M, hM⟩ : ∃ M, M = β - ℓ (x₀, t₀) := ⟨_, rfl⟩
      have hA : 0 ≤ |M| / α := by positivity
      have h1 : f x₀ ≤ ((t₀ + |M| / α : ℝ) : EReal) :=
        ht₀.trans (EReal.coe_le_coe_iff.mpr (by linarith))
      have h2 := hepi x₀ _ h1
      have h2' := hℓ x₀ (t₀ + |M| / α)
      have h3 := hℓ x₀ t₀
      have h4 : (t₀ + |M| / α) * α = t₀ * α + |M| := by
        rw [add_mul, div_mul_cancel₀ _ hpos.ne']
      have := le_abs_self M
      linarith
    have hδ : 0 < ℓ (u, r) - β := by linarith
    obtain ⟨δ, hδdef⟩ : ∃ δ, δ = ℓ (u, r) - β := ⟨_, rfl⟩
    rw [← hδdef] at hδ
    obtain ⟨K, hK⟩ : ∃ K, K = b - inner ℝ s₀ u + r := ⟨_, rfl⟩
    obtain ⟨ε, hεdef⟩ : ∃ ε, ε = δ / (|K| + 1) := ⟨_, rfl⟩
    have hε : 0 < ε := by rw [hεdef]; positivity
    have hεK : ε * K < δ := by
      have h1 : ε * (|K| + 1) = δ := by
        rw [hεdef, div_mul_cancel₀]
        positivity
      have h2 := mul_le_mul_of_nonneg_left (le_abs_self K) hε.le
      linarith
    obtain ⟨μ, hμdef⟩ : ∃ μ, μ = ε - α := ⟨_, rfl⟩
    have hμ : 0 < μ := by linarith
    have key := h (μ⁻¹ • (s + ε • s₀)) (μ⁻¹ * (β + ε * b)) ?_
    · rw [real_inner_smul_left, inner_add_left, real_inner_smul_left] at key
      have hu := hℓ u r
      have key2 : inner ℝ s u + ε * inner ℝ s₀ u - μ * r ≤ β + ε * b := by
        have := mul_le_mul_of_nonneg_left key hμ.le
        rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul, one_mul] at this
        linarith
      have e1 : ε * inner ℝ s₀ u - ε * r = ε * b - ε * K := by rw [hK]; ring
      have e2 : μ * r = ε * r - α * r := by rw [hμdef]; ring
      linarith
    · intro x t hxt
      rw [real_inner_smul_left, inner_add_left, real_inner_smul_left]
      have h1 := hepi x t hxt
      rw [hℓ] at h1
      have h2 := hmin x t hxt
      rw [← mul_le_mul_iff_of_pos_left hμ]
      rw [mul_sub, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hμ.ne', one_mul, one_mul]
      have e2 : μ * t = ε * t - α * t := by rw [hμdef]; ring
      have e3 := mul_le_mul_of_nonneg_left h2 hε.le
      have e4 : ε * (inner ℝ s₀ x - t) = ε * inner ℝ s₀ x - ε * t := by ring
      linarith
  · -- (⊇)
    intro hC v c hvc
    let L : E × ℝ →L[ℝ] ℝ :=
      (innerSL ℝ v).comp (ContinuousLinearMap.fst ℝ E ℝ) - ContinuousLinearMap.snd ℝ E ℝ
    have hH : closure (convexHull ℝ (epigraph f)) ⊆ L ⁻¹' Set.Iic c := by
      apply closure_minimal _ (isClosed_Iic.preimage L.continuous)
      apply convexHull_min _ ((convex_Iic c).linear_preimage L.toLinearMap)
      rintro ⟨x, t⟩ hxt
      simp only [epigraph, Set.mem_setOf_eq] at hxt
      simp [L]
      have := hvc x t hxt
      linarith
    have := hH hC
    simpa [L] using this

end FCA_chap_E_1_3_5
