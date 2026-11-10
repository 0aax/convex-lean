import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_2_8`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_2_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_2_8`, so the main result is `FCA_chap_B_1_2_8.FCA_chap_B_1_2_8`.
-/

namespace FCA_chap_B_1_2_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma FCA_aux_convex_ineq {f : E → EReal} (hf : ConvexEReal f) {x y : E} {s t : ℝ}
    (hx : f x ≤ s) (hy : f y ≤ t) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • x + b • y) ≤ ((a * s + b * t : ℝ) : EReal) := by
  have h := hf (show (x, s) ∈ epigraph f from hx) (show (y, t) ∈ epigraph f from hy) ha hb hab
  simpa [epigraph] using h

lemma FCA_aux_real {f : E → EReal} (hbot : ∀ x, ⊥ < f x) {y : E} (hy : f y ≠ ⊤) :
    f y = ((f y).toReal : EReal) :=
  (EReal.coe_toReal hy (hbot y).ne').symm

/-- Local lower bound at some point of the effective domain (uses finite dimensionality). -/
lemma FCA_aux_local_lower_bound (f : E → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    (hdom : ∃ x, f x < ⊤) :
    ∃ x₁, f x₁ < ⊤ ∧ ∃ m : ℝ, ∃ δ > 0, ∀ y, dist y x₁ < δ → (m : EReal) ≤ f y := by
  obtain ⟨x₀, hx₀⟩ := hdom
  set T : Set E := {v | f (v + x₀) < ⊤} with hT
  set V : Submodule ℝ E := Submodule.span ℝ T with hV
  set T' : Set V := ((↑) : V → E) ⁻¹' T with hT'
  have e : ∀ (v₁ v₂ : V) (a b : ℝ), a + b = 1 →
      ((a • v₁ + b • v₂ : V) : E) + x₀ = a • ((v₁ : E) + x₀) + b • ((v₂ : E) + x₀) := by
    intro v₁ v₂ a b hab
    simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
    rw [add_add_add_comm, ← add_smul, hab, one_smul]
  have hT'conv : Convex ℝ T' := by
    intro v₁ hv₁ v₂ hv₂ a b ha hb hab
    simp only [hT', hT, Set.mem_preimage, Set.mem_setOf_eq] at hv₁ hv₂ ⊢
    rw [e v₁ v₂ a b hab]
    calc f (a • ((v₁ : E) + x₀) + b • ((v₂ : E) + x₀))
        ≤ ((a * (f ((v₁ : E) + x₀)).toReal + b * (f ((v₂ : E) + x₀)).toReal : ℝ) : EReal) :=
          FCA_aux_convex_ineq hf (FCA_aux_real hbot hv₁.ne).le (FCA_aux_real hbot hv₂.ne).le
            ha hb hab
      _ < ⊤ := EReal.coe_lt_top _
  have h0 : (0 : V) ∈ T' := by simpa [hT', hT] using hx₀
  have hT'span : Submodule.span ℝ T' = ⊤ := Submodule.span_span_coe_preimage
  have hT'aff : affineSpan ℝ T' = ⊤ := by
    rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty ℝ V V ⟨0, h0⟩,
      vectorSpan_eq_span_vsub_set_right ℝ h0]
    simpa using hT'span
  obtain ⟨v₁, hv₁⟩ := (hT'conv.interior_nonempty_iff_affineSpan_eq_top).2 hT'aff
  set g : V → ℝ := fun v => (f ((v : E) + x₀)).toReal with hg
  have hgconv : ConvexOn ℝ T' g := by
    refine ⟨hT'conv, ?_⟩
    intro v₁ hv₁ v₂ hv₂ a b ha hb hab
    simp only [hT', hT, Set.mem_preimage, Set.mem_setOf_eq] at hv₁ hv₂
    simp only [hg, smul_eq_mul]
    rw [e v₁ v₂ a b hab]
    have h1 := FCA_aux_convex_ineq hf (FCA_aux_real hbot hv₁.ne).le
      (FCA_aux_real hbot hv₂.ne).le ha hb hab
    have h2 := EReal.toReal_le_toReal h1 (hbot _).ne' (EReal.coe_ne_top _)
    simpa using h2
  have hcont : ContinuousAt g v₁ :=
    (hgconv.continuousOn_interior).continuousAt (isOpen_interior.mem_nhds hv₁)
  have hev : ∀ᶠ v in 𝓝 v₁, g v₁ - 1 < g v ∧ v ∈ T' :=
    (hcont.eventually_const_lt (by linarith)).and (mem_interior_iff_mem_nhds.1 hv₁)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 hev
  have hv₁T : v₁ ∈ T' := interior_subset hv₁
  refine ⟨(v₁ : E) + x₀, hv₁T, g v₁ - 1, δ, hδ, ?_⟩
  intro y hy
  by_cases hfy : f y = ⊤
  · rw [hfy]; exact le_top
  · have hyT : y - x₀ ∈ T := by
      show f (y - x₀ + x₀) < ⊤
      rw [sub_add_cancel]; exact lt_top_iff_ne_top.2 hfy
    have hyV : y - x₀ ∈ V := Submodule.subset_span hyT
    set v : V := ⟨y - x₀, hyV⟩ with hv
    have hdist : dist v v₁ < δ := by
      rw [Subtype.dist_eq]
      calc dist (v : E) (v₁ : E) = dist y ((v₁ : E) + x₀) := by
            simp only [hv, dist_eq_norm]; congr 1; abel
        _ < δ := hy
    have h1 := (hball hdist).1
    have hgv : g v = (f y).toReal := by
      simp only [hg, hv, sub_add_cancel]
    rw [hgv] at h1
    rw [FCA_aux_real hbot hfy]
    exact_mod_cast h1.le

lemma FCA_aux_sep (f : E → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    (hdom : ∃ x, f x < ⊤) (x : E) (r : ℝ) (hr : (r : EReal) < lscHull f x) :
    ∃ (w : E) (α u : ℝ), 0 ≤ α ∧ inner ℝ w x + α * r < u ∧
      ∀ y (t : ℝ), f y ≤ t → u ≤ inner ℝ w y + α * t := by
  obtain ⟨r', hrr', hr'⟩ := EReal.lt_iff_exists_real_btwn.1 hr
  have hev : ∀ᶠ y in 𝓝 x, (r' : EReal) < f y := Filter.eventually_lt_of_lt_liminf hr'
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.1 hev
  set s : Set (E × ℝ) := Metric.ball x ε ×ˢ Set.Iio r' with hs
  have hs_conv : Convex ℝ s := (convex_ball x ε).prod (convex_Iio r')
  have hs_open : IsOpen s := Metric.isOpen_ball.prod isOpen_Iio
  have hdisj : Disjoint s (epigraph f) := by
    rw [Set.disjoint_left]
    rintro ⟨y, τ⟩ ⟨hy, hτ⟩ hyτ
    simp only [Metric.mem_ball, Set.mem_Iio] at hy hτ
    have h1 := hball hy
    have h2 : f y ≤ τ := hyτ
    have h3 : (τ : EReal) < r' := by exact_mod_cast hτ
    exact absurd (h1.trans_le (h2.trans h3.le)) (lt_irrefl _)
  obtain ⟨Φ, u, hΦs, hΦt⟩ := geometric_hahn_banach_open hs_conv hs_open hf hdisj
  set ψ : StrongDual ℝ E := Φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hψ
  set w : E := (InnerProductSpace.toDual ℝ E).symm ψ with hw
  set α : ℝ := Φ (0, 1) with hα
  have key : ∀ y (t : ℝ), Φ (y, t) = inner ℝ w y + α * t := by
    intro y t
    have e1 : (y, t) = (y, (0:ℝ)) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    have e2 : Φ (y, 0) = inner ℝ w y := by
      rw [hw, InnerProductSpace.toDual_symm_apply]; rfl
    rw [e1, map_add, map_smul, smul_eq_mul, e2, mul_comm]
  have hx : inner ℝ w x + α * r < u := by
    rw [← key]
    apply hΦs
    exact ⟨Metric.mem_ball_self hε, by exact_mod_cast hrr'⟩
  have ht : ∀ y (t : ℝ), f y ≤ t → u ≤ inner ℝ w y + α * t := by
    intro y t hyt
    rw [← key]
    exact hΦt (y, t) hyt
  refine ⟨w, α, u, ?_, hx, ht⟩
  obtain ⟨y₀, hy₀⟩ := hdom
  have hy₀t : ∀ t : ℝ, (f y₀).toReal ≤ t → u ≤ inner ℝ w y₀ + α * t := by
    intro t htt
    apply ht
    rw [FCA_aux_real hbot hy₀.ne]
    exact_mod_cast htt
  by_contra hneg
  push_neg at hneg
  have hK : 0 < inner ℝ w y₀ + α * (f y₀).toReal - u + 1 := by linarith [hy₀t _ le_rfl]
  have hpos : 0 < (inner ℝ w y₀ + α * (f y₀).toReal - u + 1) / (-α) := div_pos hK (by linarith)
  have h1 := hy₀t ((f y₀).toReal + (inner ℝ w y₀ + α * (f y₀).toReal - u + 1) / (-α))
    (by linarith)
  have e : α * ((inner ℝ w y₀ + α * (f y₀).toReal - u + 1) / (-α))
      = -(inner ℝ w y₀ + α * (f y₀).toReal - u + 1) := by
    have hαne : α ≠ 0 := hneg.ne
    field_simp
  nlinarith [e]

lemma FCA_aux_minorant (f : E → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    (hdom : ∃ x, f x < ⊤) :
    ∃ (s : E) (c : ℝ), ∀ y, ((inner ℝ s y - c : ℝ) : EReal) ≤ f y := by
  obtain ⟨x₁, hx₁, m, δ, hδ, hloc⟩ := FCA_aux_local_lower_bound f hf hbot hdom
  have hlsc : ((m - 1 : ℝ) : EReal) < lscHull f x₁ := by
    have h1 : (m : EReal) ≤ lscHull f x₁ := by
      exact Filter.le_liminf_of_le (by isBoundedDefault)
        (Metric.eventually_nhds_iff.2 ⟨δ, hδ, fun y hy => hloc y hy⟩)
    exact lt_of_lt_of_le (by exact_mod_cast (by linarith : m - 1 < m)) h1
  obtain ⟨w, α, u, hα, hx, ht⟩ := FCA_aux_sep f hf hbot hdom x₁ (m - 1) hlsc
  have h1 : u ≤ inner ℝ w x₁ + α * (f x₁).toReal := ht x₁ _ (FCA_aux_real hbot hx₁.ne).le
  have hαpos : 0 < α := by
    rcases hα.lt_or_eq with h | h
    · exact h
    · exfalso; rw [← h] at hx h1; linarith
  refine ⟨-(α⁻¹) • w, -(u / α), fun y => ?_⟩
  by_cases hfy : f y = ⊤
  · rw [hfy]; exact le_top
  · rw [FCA_aux_real hbot hfy]
    have h2 := ht y _ (FCA_aux_real hbot hfy).le
    rw [EReal.coe_le_coe_iff, real_inner_smul_left]
    have h3 : α⁻¹ * (u - inner ℝ w y) ≤ (f y).toReal := by
      rw [inv_mul_le_iff₀ hαpos]; linarith
    rw [div_eq_mul_inv]
    linarith

lemma FCA_aux_minorant_ge (f : E → EReal) (hf : ConvexEReal f) (hbot : ∀ x, ⊥ < f x)
    (hdom : ∃ x, f x < ⊤) (x : E) (r : ℝ) (hr : (r : EReal) < lscHull f x) :
    ∃ z : E × ℝ, r ≤ inner ℝ z.1 x - z.2 ∧ ∀ y, ((inner ℝ z.1 y - z.2 : ℝ) : EReal) ≤ f y := by
  obtain ⟨s₀, c₀, h₀⟩ := FCA_aux_minorant f hf hbot hdom
  by_cases hle : r ≤ inner ℝ s₀ x - c₀
  · exact ⟨(s₀, c₀), hle, h₀⟩
  push_neg at hle
  obtain ⟨w, α, u, hα, hx, ht⟩ := FCA_aux_sep f hf hbot hdom x r hr
  have hD₀pos : 0 < u - inner ℝ w x - α * (inner ℝ s₀ x - c₀) := by
    nlinarith [mul_nonneg hα (sub_nonneg.2 hle.le)]
  set D₀ := u - inner ℝ w x - α * (inner ℝ s₀ x - c₀) with hD₀
  set lam := (r - (inner ℝ s₀ x - c₀)) / D₀ with hlam
  have hlam0 : 0 ≤ lam := div_nonneg (by linarith) hD₀pos.le
  have hlamα : lam * α ≤ 1 := by
    rw [hlam, div_mul_eq_mul_div, div_le_one hD₀pos, hD₀]; nlinarith
  have hlamD : lam * D₀ = r - (inner ℝ s₀ x - c₀) := by
    rw [hlam]; field_simp
  rw [hD₀] at hlamD
  refine ⟨((1 - lam * α) • s₀ - lam • w, (1 - lam * α) * c₀ - lam * u), ?_, ?_⟩
  · simp only [inner_sub_left, real_inner_smul_left]
    nlinarith [hlamD]
  · intro y
    by_cases hfy : f y = ⊤
    · rw [hfy]; exact le_top
    · rw [FCA_aux_real hbot hfy, EReal.coe_le_coe_iff]
      have h1 : inner ℝ s₀ y - c₀ ≤ (f y).toReal := by
        have := h₀ y
        rw [FCA_aux_real hbot hfy] at this
        exact_mod_cast this
      have h2 : u ≤ inner ℝ w y + α * (f y).toReal := ht y _ (FCA_aux_real hbot hfy).le
      simp only [inner_sub_left, real_inner_smul_left]
      nlinarith [mul_nonneg hlam0 (by linarith : 0 ≤ inner ℝ w y + α * (f y).toReal - u),
        mul_nonneg (by linarith : 0 ≤ 1 - lam * α)
          (by linarith : 0 ≤ (f y).toReal - (inner ℝ s₀ y - c₀))]

set_option linter.unusedVariables false in
theorem FCA_chap_B_1_2_8
  (f : E → EReal)
  (hf_convex : InConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let cl_f := lscHull f
  ∀ x, cl_f x = sSup (affineMinorantValuesE f x) := by
  intro cl_f x
  obtain ⟨hbot, hdom, hconv⟩ := hf_convex
  apply le_antisymm
  · apply le_of_forall_lt_imp_le_of_dense
    intro a ha
    induction a using EReal.rec with
    | bot => exact bot_le
    | top => exact absurd ha (not_lt.2 le_top)
    | coe r =>
      obtain ⟨z, hzr, hz⟩ := FCA_aux_minorant_ge f hconv hbot hdom x r ha
      calc (r : EReal) ≤ ((inner ℝ z.1 x - z.2 : ℝ) : EReal) := by exact_mod_cast hzr
        _ ≤ sSup (affineMinorantValuesE f x) := by
          apply le_sSup
          refine ⟨z, rfl, fun y => ?_⟩
          have := hz y
          rw [EReal.coe_sub] at this
          exact this
  · apply sSup_le
    rintro v ⟨z, rfl, hz⟩
    have hcont : Continuous (fun y : E => ((inner ℝ z.1 y - z.2 : ℝ) : EReal)) :=
      continuous_coe_real_ereal.comp ((continuous_const.inner continuous_id).sub continuous_const)
    calc ((inner ℝ z.1 x - z.2 : ℝ) : EReal)
        = Filter.liminf (fun y : E => ((inner ℝ z.1 y - z.2 : ℝ) : EReal)) (𝓝 x) :=
          ((hcont.tendsto x).liminf_eq).symm
      _ ≤ Filter.liminf f (𝓝 x) := by
          exact Filter.liminf_le_liminf
            (Filter.Eventually.of_forall (fun y => by rw [EReal.coe_sub]; exact hz y))

end FCA_chap_B_1_2_8
