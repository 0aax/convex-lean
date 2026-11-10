import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_1_2`, so the main result is `FCA_chap_D_6_1_2.FCA_chap_D_6_1_2`.
-/

namespace FCA_chap_D_6_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Set Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma dq_eq (f : E → ℝ) (x d : E) (t : ℝ) :
    differenceQuotient (liftRealtoEReal f) x d t = (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
  simp only [differenceQuotient, liftRealtoEReal]
  rw [EReal.coe_div, EReal.coe_sub]

lemma dq_mono (f : E → ℝ) (hf : ConvexOn ℝ univ f) (x d : E) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) :
    (f (x + s • d) - f x) / s ≤ (f (x + t • d) - f x) / t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have key : f (x + s • d) ≤ (1 - s / t) * f x + (s / t) * f (x + t • d) := by
    have h := hf.2 (mem_univ x) (mem_univ (x + t • d))
      (show (0:ℝ) ≤ 1 - s / t by rw [sub_nonneg, div_le_one ht]; exact hst)
      (show (0:ℝ) ≤ s / t by positivity) (show 1 - s / t + s / t = 1 by ring)
    have e : (1 - s / t) • x + (s / t) • (x + t • d) = x + s • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne']
      module
    rw [e] at h
    simpa [smul_eq_mul] using h
  rw [div_le_div_iff₀ hs ht]
  have h2 : f (x + s • d) * t ≤ (t - s) * f x + s * f (x + t • d) := by
    have := mul_le_mul_of_nonneg_right key ht.le
    calc f (x + s • d) * t ≤ ((1 - s / t) * f x + (s / t) * f (x + t • d)) * t := this
      _ = (t - s) * f x + s * f (x + t • d) := by field_simp
  nlinarith

lemma dd_tendsto (f : E → ℝ) (hf : ConvexOn ℝ univ f) (x d : E) :
    Tendsto (fun t => differenceQuotient (liftRealtoEReal f) x d t) (𝓝[>] 0)
      (𝓝 (⨅ t ∈ Ioi (0:ℝ), differenceQuotient (liftRealtoEReal f) x d t)) := by
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact lt_of_lt_of_le ha (biInf_le _ ht)
  · intro a ha
    obtain ⟨t₀, ht₀, hlt⟩ : ∃ t₀ ∈ Ioi (0:ℝ), differenceQuotient (liftRealtoEReal f) x d t₀ < a := by
      simpa only [iInf_lt_iff, exists_prop] using ha
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
    refine lt_of_le_of_lt ?_ hlt
    rw [dq_eq, dq_eq]
    exact EReal.coe_le_coe_iff.2 (dq_mono f hf x d ht.1 ht.2.le)

lemma dd_eq (f : E → ℝ) (hf : ConvexOn ℝ univ f) (x d : E) :
    directionalDeriv (liftRealtoEReal f) x d =
      ⨅ t ∈ Ioi (0:ℝ), differenceQuotient (liftRealtoEReal f) x d t :=
  (dd_tendsto f hf x d).limUnder_eq

lemma mem_dsd_iff (f : E → ℝ) (hf : ConvexOn ℝ univ f) (x s : E) :
    s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔
      ∀ y, f x + inner ℝ s (y - x) ≤ f y := by
  simp only [directionalSubdifferential, mem_setOf_eq, dd_eq f hf]
  constructor
  · intro h y
    have h1 := (h (y - x)).trans (biInf_le _ (show (1:ℝ) ∈ Ioi 0 from mem_Ioi.2 one_pos))
    rw [dq_eq] at h1
    have h2 := EReal.coe_le_coe_iff.1 h1
    simp only [one_smul, add_sub_cancel, div_one] at h2
    linarith
  · intro h d
    refine le_iInf₂ fun t ht => ?_
    rw [dq_eq]
    refine EReal.coe_le_coe_iff.2 ?_
    rw [le_div_iff₀ (show (0:ℝ) < t from ht)]
    have := h (x + t • d)
    rw [add_sub_cancel_left, inner_smul_right] at this
    linarith

lemma exists_subgrad (f : E → ℝ) (hf : ConvexOn ℝ univ f) (z : E) :
    ∃ s : E, ∀ y, f z + inner ℝ s (y - z) ≤ f y := by
  have hcont : Continuous f := hf.locallyLipschitz.continuous
  let S : Set (E × ℝ) := {p | f p.1 < p.2}
  have hS_open : IsOpen S := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hS_conv : Convex ℝ S := by
    rw [convex_iff_forall_pos]
    intro p hp q hq a b ha hb hab
    simp only [S, mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at hp hq ⊢
    have h1 := hf.2 (mem_univ p.1) (mem_univ q.1) ha.le hb.le hab
    simp only [smul_eq_mul] at h1
    nlinarith [mul_pos ha (sub_pos.2 hp), mul_pos hb (sub_pos.2 hq)]
  have hz : ((z, f z) : E × ℝ) ∉ S := by simp [S]
  obtain ⟨Φ, hΦ⟩ := geometric_hahn_banach_open_point hS_conv hS_open hz
  set α := Φ ((0 : E), (1 : ℝ)) with hα_def
  have hΦ_apply : ∀ (x : E) (t : ℝ), Φ (x, t) = Φ (x, 0) + t * α := by
    intro x t
    have e : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [e, map_add, map_smul, smul_eq_mul]
  have hα : α < 0 := by
    have h := hΦ (z, f z + 1) (by simp [S])
    rw [hΦ_apply z (f z + 1), hΦ_apply z (f z)] at h
    linarith
  have key : ∀ y, Φ (y, 0) + f y * α ≤ Φ (z, 0) + f z * α := by
    intro y
    by_contra hcon
    push_neg at hcon
    set gap := Φ (y, 0) + f y * α - (Φ (z, 0) + f z * α) with hgap_def
    have hgap : 0 < gap := by linarith
    have hmem : ((y, f y + gap / (-2 * α)) : E × ℝ) ∈ S := by
      simp only [S, mem_setOf_eq]
      have : 0 < gap / (-2 * α) := div_pos hgap (by linarith)
      linarith
    have h := hΦ _ hmem
    rw [hΦ_apply y, hΦ_apply z (f z)] at h
    have hα0 : α ≠ 0 := hα.ne
    have e : (f y + gap / (-2 * α)) * α = f y * α - gap / 2 := by
      field_simp
      ring
    linarith
  let ℓ : StrongDual ℝ E := Φ.comp (ContinuousLinearMap.inl ℝ E ℝ)
  refine ⟨(InnerProductSpace.toDual ℝ E).symm ((-α)⁻¹ • ℓ), fun y => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp',
    Function.comp_apply, ContinuousLinearMap.inl_apply, smul_eq_mul, ℓ]
  have h1 : Φ (y - z, 0) = Φ (y, 0) - Φ (z, 0) := by
    rw [← map_sub]
    simp
  rw [h1]
  have hk := key y
  have hna : 0 < -α := by linarith
  have : (-α)⁻¹ * (Φ (y, 0) - Φ (z, 0)) ≤ f y - f z := by
    rw [inv_mul_le_iff₀ hna]
    nlinarith
  linarith

lemma part1_fwd (f : E → ℝ) (C : Set E) (c : ℝ) (hsc : StrongConvexOn C c f)
    (x₁ x₂ : E) (h₁ : x₁ ∈ C) (h₂ : x₂ ∈ C) (s : E)
    (hs : ∀ y, f x₁ + inner ℝ s (y - x₁) ≤ f y) :
    f x₁ + inner ℝ s (x₂ - x₁) + c / 2 * ‖x₂ - x₁‖ ^ 2 ≤ f x₂ := by
  have key : ∀ t : ℝ, 0 < t → t < 1 →
      inner ℝ s (x₂ - x₁) ≤ f x₂ - f x₁ - (1 - t) * (c / 2 * ‖x₂ - x₁‖ ^ 2) := by
    intro t ht0 ht1
    have h := hsc.2 h₁ h₂ (show (0:ℝ) ≤ 1 - t by linarith) ht0.le (show 1 - t + t = 1 by ring)
    have hpt : (1 - t) • x₁ + t • x₂ = x₁ + t • (x₂ - x₁) := by module
    rw [hpt] at h
    have h' := hs (x₁ + t • (x₂ - x₁))
    rw [add_sub_cancel_left, inner_smul_right] at h'
    rw [norm_sub_rev] at h
    simp only [smul_eq_mul] at h
    have : t * inner ℝ s (x₂ - x₁) ≤
        t * (f x₂ - f x₁ - (1 - t) * (c / 2 * ‖x₂ - x₁‖ ^ 2)) := by nlinarith
    exact le_of_mul_le_mul_left this ht0
  have hlim : Tendsto (fun t : ℝ => f x₂ - f x₁ - (1 - t) * (c / 2 * ‖x₂ - x₁‖ ^ 2)) (𝓝[>] 0)
      (𝓝 (f x₂ - f x₁ - (1 - 0) * (c / 2 * ‖x₂ - x₁‖ ^ 2))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    exact ((continuous_const.sub ((continuous_const.sub continuous_id).mul
      continuous_const)).tendsto 0)
  have := ge_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
    exact key t ht.1 ht.2)
  linarith

lemma part1_bwd (f : E → ℝ) (hf : ConvexOn ℝ univ f) (C : Set E) (c : ℝ) (hC : Convex ℝ C)
    (H : ∀ x₁ ∈ C, ∀ x₂ ∈ C, ∀ s : E, (∀ y, f x₁ + inner ℝ s (y - x₁) ≤ f y) →
      f x₁ + inner ℝ s (x₂ - x₁) + c / 2 * ‖x₂ - x₁‖ ^ 2 ≤ f x₂) :
    StrongConvexOn C c f := by
  refine ⟨hC, fun x hx y hy a b ha hb hab => ?_⟩
  have hz : a • x + b • y ∈ C := hC hx hy ha hb hab
  obtain ⟨s, hs⟩ := exists_subgrad f hf (a • x + b • y)
  have h1 := H _ hz x hx s hs
  have h2 := H _ hz y hy s hs
  obtain rfl : a = 1 - b := by linarith
  have e1 : x - ((1 - b) • x + b • y) = b • (x - y) := by module
  have e2 : y - ((1 - b) • x + b • y) = (-(1 - b)) • (x - y) := by module
  rw [e1, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h1
  rw [e2, inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h2
  simp only [smul_eq_mul]
  nlinarith [mul_nonneg ha (sub_nonneg.2 h1), mul_nonneg hb (sub_nonneg.2 h2)]

lemma part2_bwd_aux (f : E → ℝ) (hf : ConvexOn ℝ univ f) (C : Set E) (c : ℝ) (hC : Convex ℝ C)
    (hmono : ∀ x₀ x₁ v₀ v₁ : E, x₀ ∈ C → (∀ y, f x₀ + inner ℝ v₀ (y - x₀) ≤ f y) → x₁ ∈ C →
      (∀ y, f x₁ + inner ℝ v₁ (y - x₁) ≤ f y) → c * ‖x₁ - x₀‖ ^ 2 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀))
    (x₁ x₂ : E) (h₁ : x₁ ∈ C) (h₂ : x₂ ∈ C) (s : E)
    (hs : ∀ y, f x₁ + inner ℝ s (y - x₁) ≤ f y) :
    f x₁ + inner ℝ s (x₂ - x₁) + c / 2 * ‖x₂ - x₁‖ ^ 2 ≤ f x₂ := by
  set d := x₂ - x₁ with hd
  set A := inner ℝ s d with hA
  set K := ‖d‖ ^ 2 with hK
  have hK0 : 0 ≤ K := by positivity
  have step : ∀ n : ℕ, 0 < n → ∀ m : ℕ, m ≤ n →
      (m : ℝ) / n * A + c * K * ((m : ℝ) * ((m : ℝ) - 1)) / (2 * (n : ℝ) ^ 2) ≤
        f (x₁ + ((m : ℝ) / n) • d) - f x₁ := by
    intro n hn m
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have ih := ih (by omega)
      have hmn1 : (m : ℝ) / n ≤ 1 := by
        rw [div_le_one hn']
        exact_mod_cast (show m ≤ n by omega)
      have hp : x₁ + ((m : ℝ) / n) • d ∈ C := by
        have e : x₁ + ((m : ℝ) / n) • d = (1 - (m : ℝ) / n) • x₁ + ((m : ℝ) / n) • x₂ := by
          rw [hd]; module
        rw [e]
        exact hC h₁ h₂ (by linarith) (by positivity) (by ring)
      obtain ⟨σ, hσ, hσd⟩ : ∃ σ : E, (∀ y, f (x₁ + ((m : ℝ) / n) • d) +
          inner ℝ σ (y - (x₁ + ((m : ℝ) / n) • d)) ≤ f y) ∧
          A + c * ((m : ℝ) / n) * K ≤ inner ℝ σ d := by
        rcases Nat.eq_zero_or_pos m with rfl | hm0
        · refine ⟨s, ?_, ?_⟩
          · simpa using hs
          · simp [hA]
        · obtain ⟨σ, hσ⟩ := exists_subgrad f hf (x₁ + ((m : ℝ) / n) • d)
          refine ⟨σ, hσ, ?_⟩
          have h := hmono x₁ (x₁ + ((m : ℝ) / n) • d) s σ h₁ hs hp hσ
          have hmn : (0 : ℝ) < m / n := by
            have : (0 : ℝ) < m := by exact_mod_cast hm0
            positivity
          rw [add_sub_cancel_left, norm_smul, inner_smul_right, inner_sub_left, mul_pow,
            Real.norm_eq_abs, abs_of_pos hmn] at h
          -- h : c * ((m/n)^2 * K) ≤ (m/n) * (inner σ d - A)
          have h' : (m / n : ℝ) * (A + c * ((m : ℝ) / n) * K) ≤ (m / n : ℝ) * inner ℝ σ d := by
            nlinarith
          exact le_of_mul_le_mul_left h' hmn
      have hnext := hσ (x₁ + (((m + 1 : ℕ) : ℝ) / n) • d)
      have e : x₁ + (((m + 1 : ℕ) : ℝ) / n) • d - (x₁ + ((m : ℝ) / n) • d) =
          (1 / (n : ℝ)) • d := by
        push_cast
        rw [add_div, add_smul]
        module
      rw [e, inner_smul_right] at hnext
      have key : (((m + 1 : ℕ) : ℝ)) / n * A +
          c * K * (((m + 1 : ℕ) : ℝ) * (((m + 1 : ℕ) : ℝ) - 1)) / (2 * (n : ℝ) ^ 2) =
          ((m : ℝ) / n * A + c * K * ((m : ℝ) * ((m : ℝ) - 1)) / (2 * (n : ℝ) ^ 2)) +
          1 / (n : ℝ) * (A + c * ((m : ℝ) / n) * K) := by
        push_cast
        field_simp
        ring
      rw [key]
      have h3 : 1 / (n : ℝ) * (A + c * ((m : ℝ) / n) * K) ≤ 1 / (n : ℝ) * inner ℝ σ d :=
        mul_le_mul_of_nonneg_left hσd (by positivity)
      linarith
  have final : ∀ n : ℕ, 0 < n → A + c * K * ((n : ℝ) - 1) / (2 * n) ≤ f x₂ - f x₁ := by
    intro n hn
    have h := step n hn n le_rfl
    have hn' : (n : ℝ) ≠ 0 := by positivity
    rw [div_self hn', one_smul, hd, add_sub_cancel] at h
    have e : c * K * ((n : ℝ) * ((n : ℝ) - 1)) / (2 * (n : ℝ) ^ 2) =
        c * K * ((n : ℝ) - 1) / (2 * n) := by
      field_simp
    rw [e] at h
    linarith
  by_contra hcon
  push_neg at hcon
  set gap := f x₁ + A + c / 2 * K - f x₂ with hgap_def
  have hgap : 0 < gap := by linarith
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt (c * K / (2 * gap))
  set n := n₀ + 1 with hn_def
  have hn0 : 0 < n := Nat.succ_pos n₀
  have hn : c * K / (2 * gap) < n := by
    rw [hn_def]; push_cast; linarith
  have h := final n hn0
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn0
  have e : c * K * ((n : ℝ) - 1) / (2 * n) = c / 2 * K - c * K / (2 * n) := by
    field_simp
  rw [e] at h
  have : c * K / (2 * n) < gap := by
    rw [div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hn
    nlinarith
  linarith

set_option linter.unusedVariables false in
theorem FCA_chap_D_6_1_2
  (f : E → ℝ)
  (C : Set E)
  (c : ℝ)
  (hC_convex : Convex ℝ C)
  (hc : c > 0)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  (StrongConvexOn C c f ↔
  ∀ x₁ ∈ C, ∀ x₂ ∈ C, ∀ s ∈ directionalSubdifferential (liftRealtoEReal f) x₁,
  f x₂ ≥ f x₁ + inner ℝ s (x₂ - x₁) + (c / 2) * ‖x₂ - x₁‖ ^ 2) ∧
  (StrongConvexOn C c f ↔
  IsStronglyMonotone (fun x => {s | x ∈ C ∧ s ∈ directionalSubdifferential (liftRealtoEReal f) x}) c) := by
  have hsub : ∀ x s, s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔
      ∀ y, f x + inner ℝ s (y - x) ≤ f y := fun x s => mem_dsd_iff f hf_convex x s
  refine ⟨⟨fun h x₁ h₁ x₂ h₂ s hs => part1_fwd f C c h x₁ x₂ h₁ h₂ s ((hsub x₁ s).1 hs),
    fun H => part1_bwd f hf_convex C c hC_convex
      (fun x₁ h₁ x₂ h₂ s hs => H x₁ h₁ x₂ h₂ s ((hsub x₁ s).2 hs))⟩, ⟨?_, ?_⟩⟩
  · intro h x₀ x₁ v₀ v₁ hv₀ hv₁
    obtain ⟨h₀C, h₀s⟩ := hv₀
    obtain ⟨h₁C, h₁s⟩ := hv₁
    have a1 := part1_fwd f C c h x₀ x₁ h₀C h₁C v₀ ((hsub _ _).1 h₀s)
    have a2 := part1_fwd f C c h x₁ x₀ h₁C h₀C v₁ ((hsub _ _).1 h₁s)
    rw [norm_sub_rev x₀ x₁] at a2
    have e : inner ℝ v₁ (x₀ - x₁) = - inner ℝ v₁ (x₁ - x₀) := by
      rw [← inner_neg_right, neg_sub]
    rw [e] at a2
    rw [inner_sub_left]
    linarith
  · intro hmono
    apply part1_bwd f hf_convex C c hC_convex
    intro x₁ h₁ x₂ h₂ s hs
    exact part2_bwd_aux f hf_convex C c hC_convex
      (fun x₀ x₁ v₀ v₁ h0 hv0 h1 hv1 =>
        hmono x₀ x₁ v₀ v₁ ⟨h0, (hsub _ _).2 hv0⟩ ⟨h1, (hsub _ _).2 hv1⟩)
      x₁ x₂ h₁ h₂ s hs

end FCA_chap_D_6_1_2
