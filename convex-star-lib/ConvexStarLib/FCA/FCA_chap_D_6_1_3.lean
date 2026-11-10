import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_1_3`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_1_3`, so the main result is `FCA_chap_D_6_1_3.FCA_chap_D_6_1_3`.
-/

namespace FCA_chap_D_6_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem FCA_chap_D_6_1_3
  (f : E → ℝ)
  (C : Set E)
  (hC_convex : Convex ℝ C)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  (StrictConvexOn ℝ C f ↔
  ∀ x₁ ∈ C, ∀ x₂ ∈ C, (x₁ ≠ x₂) →
  ∀ s ∈ directionalSubdifferential (liftRealtoEReal f) x₁,
  f x₂ > f x₁ + inner ℝ s (x₂ - x₁)) ∧
  (StrictConvexOn ℝ C f ↔
  IsStrictMonotone (fun x => {s | x ∈ C ∧ s ∈ directionalSubdifferential (liftRealtoEReal f) x})) := by
  set q : E → E → ℝ → ℝ := fun x d t => (f (x + t • d) - f x) / t with hq_def
  have hline : ∀ x d : E, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
    intro x d
    refine ⟨convex_univ, ?_⟩
    intro a _ b _ μ ν hμ hν hμν
    have e : x + (μ * a + ν * b) • d = μ • (x + a • d) + ν • (x + b • d) := by
      obtain rfl : ν = 1 - μ := by linarith
      module
    simp only [smul_eq_mul]
    rw [e]
    exact hf_convex.2 (Set.mem_univ _) (Set.mem_univ _) hμ hν hμν
  have hmono : ∀ x d : E, ∀ s t : ℝ, 0 < s → s ≤ t → q x d s ≤ q x d t := by
    intro x d s t hs hst
    have h := (hline x d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ s)
      (Set.mem_univ t) hs.ne' (hs.trans_le hst).ne' hst
    simpa [q] using h
  have hbdd : ∀ x d : E, ∀ t : ℝ, 0 < t → f x - f (x - d) ≤ q x d t := by
    intro x d t ht
    have h := (hline x d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ (-1))
      (Set.mem_univ t) (by norm_num) ht.ne' (by linarith)
    have e1 : x + (-1 : ℝ) • d = x - d := by rw [neg_one_smul, ← sub_eq_add_neg]
    simp only [zero_smul, add_zero, sub_zero, e1] at h
    rw [div_neg, div_one] at h
    simp only [q]
    linarith
  have hbddB : ∀ x d : E, BddBelow (q x d '' Set.Ioi 0) := by
    intro x d
    exact ⟨f x - f (x - d), by rintro _ ⟨t, ht, rfl⟩; exact hbdd x d t ht⟩
  set N : E → E → ℝ := fun x d => sInf (q x d '' Set.Ioi 0) with hN_def
  have htend : ∀ x d : E, Filter.Tendsto (q x d) (𝓝[>] 0) (𝓝 (N x d)) := by
    intro x d
    apply MonotoneOn.tendsto_nhdsGT
    · intro s hs t ht hst
      exact hmono x d s t hs hst
    · exact hbddB x d
  have hNle : ∀ x d : E, ∀ t : ℝ, 0 < t → N x d ≤ q x d t := by
    intro x d t ht
    exact csInf_le (hbddB x d) ⟨t, ht, rfl⟩
  have hNge : ∀ x d : E, ∀ c : ℝ, (∀ t : ℝ, 0 < t → c ≤ q x d t) → c ≤ N x d := by
    intro x d c hc
    exact le_csInf ⟨q x d 1, 1, Set.mem_Ioi.mpr one_pos, rfl⟩ (by rintro _ ⟨t, ht, rfl⟩; exact hc t ht)
  have hdd : ∀ x d : E, directionalDeriv (liftRealtoEReal f) x d = ((N x d : ℝ) : EReal) := by
    intro x d
    unfold directionalDeriv
    have h1 : (fun t => differenceQuotient (liftRealtoEReal f) x d t)
        = fun t => ((q x d t : ℝ) : EReal) := by
      funext t
      simp only [differenceQuotient, liftRealtoEReal, q, EReal.coe_div, EReal.coe_sub]
    rw [h1]
    exact (EReal.tendsto_coe.mpr (htend x d)).limUnder_eq
  have hmem : ∀ x s : E, s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔
      ∀ d, inner ℝ s d ≤ N x d := by
    intro x s
    simp only [directionalSubdifferential, Set.mem_setOf_eq, hdd, EReal.coe_le_coe_iff]
  have key1 : ∀ x s : E, s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔
      ∀ y, f x + inner ℝ s (y - x) ≤ f y := by
    intro x s
    rw [hmem]
    constructor
    · intro h y
      have h1 := h (y - x)
      have h2 := hNle x (y - x) 1 one_pos
      simp only [q, one_smul, add_sub_cancel, div_one] at h2
      linarith
    · intro h d
      apply hNge
      intro t ht
      have h1 := h (x + t • d)
      rw [add_sub_cancel_left, inner_smul_right] at h1
      simp only [q]
      rw [le_div_iff₀ ht]
      linarith
  have key2 : ∀ x : E, ∃ s, s ∈ directionalSubdifferential (liftRealtoEReal f) x := by
    intro x
    have hN0 : N x 0 = 0 := by
      apply le_antisymm
      · have := hNle x 0 1 one_pos
        simpa [q] using this
      · apply hNge
        intro t ht
        simp [q]
    have hhom : ∀ c : ℝ, 0 < c → ∀ d, N x (c • d) = c * N x d := by
      intro c hc d
      apply le_antisymm
      · rw [← div_le_iff₀' hc]
        apply hNge
        intro t ht
        rw [div_le_iff₀' hc]
        have h1 := hNle x (c • d) (t / c) (div_pos ht hc)
        have h2 : q x (c • d) (t / c) = c * q x d t := by
          simp only [q, smul_smul]
          rw [div_mul_cancel₀ t hc.ne']
          field_simp
        linarith
      · apply hNge
        intro t ht
        have h1 := hNle x d (t * c) (mul_pos ht hc)
        have h2 : q x (c • d) t = c * q x d (t * c) := by
          simp only [q, smul_smul]
          field_simp
        rw [h2]
        exact mul_le_mul_of_nonneg_left h1 hc.le
    have hadd : ∀ d₁ d₂, N x (d₁ + d₂) ≤ N x d₁ + N x d₂ := by
      intro d₁ d₂
      have key : ∀ t₁ t₂ : ℝ, 0 < t₁ → 0 < t₂ → N x (d₁ + d₂) ≤ q x d₁ t₁ + q x d₂ t₂ := by
        intro t₁ t₂ h₁ h₂
        have ht : 0 < min t₁ t₂ := lt_min h₁ h₂
        have e1 := hNle x (d₁ + d₂) (min t₁ t₂ / 2) (by positivity)
        have e2 : q x (d₁ + d₂) (min t₁ t₂ / 2) ≤ q x d₁ (min t₁ t₂) + q x d₂ (min t₁ t₂) := by
          have hc := hf_convex.2 (Set.mem_univ (x + (min t₁ t₂) • d₁))
            (Set.mem_univ (x + (min t₁ t₂) • d₂)) (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
          have e : (1/2 : ℝ) • (x + (min t₁ t₂) • d₁) + (1/2 : ℝ) • (x + (min t₁ t₂) • d₂)
              = x + (min t₁ t₂ / 2) • (d₁ + d₂) := by module
          rw [e] at hc
          simp only [q, smul_eq_mul] at hc ⊢
          rw [← add_div, div_le_div_iff₀ (by positivity) ht]
          nlinarith
        have e3 := hmono x d₁ (min t₁ t₂) t₁ ht (min_le_left _ _)
        have e4 := hmono x d₂ (min t₁ t₂) t₂ ht (min_le_right _ _)
        linarith
      have k2 : ∀ t₂ : ℝ, 0 < t₂ → N x (d₁ + d₂) - q x d₂ t₂ ≤ N x d₁ := by
        intro t₂ h₂
        apply hNge
        intro t₁ h₁
        have := key t₁ t₂ h₁ h₂
        linarith
      have k3 : N x (d₁ + d₂) - N x d₁ ≤ N x d₂ := by
        apply hNge
        intro t₂ h₂
        have := k2 t₂ h₂
        linarith
      linarith
    obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear ⟨⊥, 0⟩ (N x) hhom hadd (by
      rintro ⟨y, hy⟩
      rw [Submodule.mem_bot] at hy
      subst hy
      simp [hN0])
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g), ?_⟩
    rw [hmem]
    intro d
    rw [InnerProductSpace.toDual_symm_apply]
    exact hg d
  have part1 : StrictConvexOn ℝ C f ↔ ∀ x₁ ∈ C, ∀ x₂ ∈ C, (x₁ ≠ x₂) →
      ∀ s ∈ directionalSubdifferential (liftRealtoEReal f) x₁,
      f x₂ > f x₁ + inner ℝ s (x₂ - x₁) := by
    constructor
    · intro hsc x₁ hx₁ x₂ hx₂ hne s hs
      rw [key1] at hs
      have h1 := hsc.2 hx₁ hx₂ hne (by norm_num : (0:ℝ) < 1/2) (by norm_num : (0:ℝ) < 1/2)
        (by norm_num)
      have h2 := hs ((1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂)
      have h3 : (1/2 : ℝ) • x₁ + (1/2 : ℝ) • x₂ - x₁ = (1/2 : ℝ) • (x₂ - x₁) := by module
      rw [h3, inner_smul_right] at h2
      simp only [smul_eq_mul] at h1
      linarith
    · intro H
      refine ⟨hC_convex, ?_⟩
      intro x hx y hy hxy a b ha hb hab
      obtain rfl : b = 1 - a := by linarith
      have hz : a • x + (1 - a) • y ∈ C := hC_convex hx hy ha.le hb.le hab
      obtain ⟨s, hs⟩ := key2 (a • x + (1 - a) • y)
      have hzx : a • x + (1 - a) • y ≠ x := by
        intro h
        apply hxy
        have e : (1 - a) • (y - x) = 0 := by
          calc (1 - a) • (y - x) = (a • x + (1 - a) • y) - x := by module
            _ = 0 := by rw [h, sub_self]
        rcases smul_eq_zero.mp e with h0 | h0
        · exact absurd h0 hb.ne'
        · exact (sub_eq_zero.mp h0).symm
      have hzy : a • x + (1 - a) • y ≠ y := by
        intro h
        apply hxy
        have e : a • (x - y) = 0 := by
          calc a • (x - y) = (a • x + (1 - a) • y) - y := by module
            _ = 0 := by rw [h, sub_self]
        rcases smul_eq_zero.mp e with h0 | h0
        · exact absurd h0 ha.ne'
        · exact sub_eq_zero.mp h0
      have h1 := H _ hz x hx hzx s hs
      have h2 := H _ hz y hy hzy s hs
      have h3 : a * inner ℝ s (x - (a • x + (1 - a) • y))
          + (1 - a) * inner ℝ s (y - (a • x + (1 - a) • y)) = 0 := by
        rw [← inner_smul_right, ← inner_smul_right, ← inner_add_right]
        have e : a • (x - (a • x + (1 - a) • y)) + (1 - a) • (y - (a • x + (1 - a) • y))
            = (0 : E) := by module
        rw [e, inner_zero_right]
      simp only [smul_eq_mul]
      nlinarith [mul_lt_mul_of_pos_left h1 ha, mul_lt_mul_of_pos_left h2 hb]
  refine ⟨part1, ?_⟩
  constructor
  · intro hsc x₀ x₁ v₀ v₁ hne hv₀ hv₁
    obtain ⟨hx₀, hv₀⟩ := hv₀
    obtain ⟨hx₁, hv₁⟩ := hv₁
    have h1 := part1.mp hsc x₀ hx₀ x₁ hx₁ hne v₀ hv₀
    have h2 := part1.mp hsc x₁ hx₁ x₀ hx₀ (Ne.symm hne) v₁ hv₁
    simp only [inner_sub_left, inner_sub_right] at h1 h2 ⊢
    linarith
  · intro hmon
    apply part1.mpr
    intro x₁ hx₁ x₂ hx₂ hne s hs
    by_contra hle
    push_neg at hle
    have hs' := (key1 x₁ s).mp hs
    have hs2 : s ∈ directionalSubdifferential (liftRealtoEReal f) x₂ := by
      rw [key1]
      intro y
      have h1 := hs' y
      have h2 : inner ℝ s (y - x₂) = inner ℝ s (y - x₁) - inner ℝ s (x₂ - x₁) := by
        rw [← inner_sub_right]; congr 1; abel
      linarith
    have := hmon x₁ x₂ s s hne ⟨hx₁, hs⟩ ⟨hx₂, hs2⟩
    simp at this

end FCA_chap_D_6_1_3
