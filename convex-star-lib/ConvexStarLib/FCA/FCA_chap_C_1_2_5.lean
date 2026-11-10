import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_2_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_2_5`, so the main result is `FCA_chap_C_1_2_5.FCA_chap_C_1_2_5`.
-/

namespace FCA_chap_C_1_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace FCAGaugeAux

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

lemma gaugeFun_eq (C : Set F) (x : F) :
    gaugeFun C x = sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | 0 < r ∧ x ∈ r • C}) := by
  unfold gaugeFun
  congr 1
  ext l
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_smul_set]
  constructor
  · rintro ⟨l', rfl, hl', y, hy, rfl⟩
    exact ⟨l', ⟨hl', y, hy, rfl⟩, rfl⟩
  · rintro ⟨l', ⟨hl', y, hy, rfl⟩, rfl⟩
    exact ⟨l', rfl, hl', y, hy, rfl⟩

lemma gaugeFun_nonneg (C : Set F) (x : F) : 0 ≤ gaugeFun C x := by
  rw [gaugeFun_eq]
  apply le_sInf
  rintro _ ⟨r, ⟨hr, _⟩, rfl⟩
  exact EReal.coe_nonneg.2 hr.le

lemma gaugeFun_le_of_mem {C : Set F} {x : F} {r : ℝ} (hr : 0 < r) (hx : x ∈ r • C) :
    gaugeFun C x ≤ r := by
  rw [gaugeFun_eq]
  exact sInf_le ⟨r, ⟨hr, hx⟩, rfl⟩

lemma mem_smul_of_le {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hx : x ∈ a • C) : x ∈ b • C := by
  obtain ⟨y, hy, rfl⟩ := hx
  have hb : 0 < b := lt_of_lt_of_le ha hab
  refine ⟨(a / b) • y, hC.smul_mem_of_zero_mem h0 hy ⟨by positivity, (div_le_one hb).2 hab⟩, ?_⟩
  simp only [smul_smul]
  congr 1
  field_simp

lemma mem_smul_of_gaugeFun_lt {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} {r : ℝ}
    (h : gaugeFun C x < r) : x ∈ r • C := by
  rw [gaugeFun_eq, sInf_lt_iff] at h
  obtain ⟨_, ⟨s, ⟨hs, hxs⟩, rfl⟩, hsr⟩ := h
  have hsr' : s < r := EReal.coe_lt_coe_iff.1 hsr
  exact mem_smul_of_le hC h0 hs hsr'.le hxs

lemma gaugeFun_le_iff {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} {R : ℝ}
    (hR : 0 ≤ R) : gaugeFun C x ≤ R ↔ ∀ s : ℝ, R < s → x ∈ s • C := by
  constructor
  · intro h s hs
    exact mem_smul_of_gaugeFun_lt hC h0 (lt_of_le_of_lt h (by exact_mod_cast hs))
  · intro h
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : R < z := by exact_mod_cast hz
    exact gaugeFun_le_of_mem (lt_of_le_of_lt hR hz') (h z hz')

lemma mem_smul_of_forall_gt {C : Set F} (hCc : IsClosed C) {x : F} {R : ℝ} (hR : 0 < R)
    (h : ∀ s : ℝ, R < s → x ∈ s • C) : x ∈ R • C := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hR.ne']
  have hmem : ∀ s : ℝ, R < s → s⁻¹ • x ∈ C := fun s hs =>
    (Set.mem_smul_set_iff_inv_smul_mem₀ (by linarith : s ≠ 0) _ _).1 (h s hs)
  have ht : Filter.Tendsto (fun s : ℝ => s⁻¹ • x) (𝓝[>] R) (𝓝 (R⁻¹ • x)) :=
    (((continuousAt_inv₀ hR.ne').tendsto).mono_left nhdsWithin_le_nhds).smul_const x
  exact hCc.mem_of_tendsto ht (eventually_nhdsWithin_of_forall fun s hs => hmem s hs)

lemma gaugeFun_le_iff_mem {C : Set F} (hCc : IsClosed C) (hC : Convex ℝ C) (h0 : (0:F) ∈ C)
    {x : F} {R : ℝ} (hR : 0 < R) : gaugeFun C x ≤ R ↔ x ∈ R • C := by
  constructor
  · intro h
    exact mem_smul_of_forall_gt hCc hR ((gaugeFun_le_iff hC h0 hR.le).1 h)
  · exact gaugeFun_le_of_mem hR

lemma gaugeFun_ne_top_iff {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} :
    gaugeFun C x ≠ ⊤ ↔ ∃ s : ℝ, 0 < s ∧ x ∈ s • C := by
  constructor
  · intro h
    obtain ⟨r, hr1, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 h)
    have hr : (0:ℝ) < r := by exact_mod_cast lt_of_le_of_lt (gaugeFun_nonneg C x) hr1
    exact ⟨r, hr, mem_smul_of_gaugeFun_lt hC h0 hr1⟩
  · rintro ⟨s, hs, hx⟩
    exact ne_top_of_le_ne_top (EReal.coe_ne_top s) (gaugeFun_le_of_mem hs hx)

lemma gaugeFun_eq_coe_or_top (C : Set F) (x : F) :
    gaugeFun C x = ⊤ ∨ ∃ a : ℝ, 0 ≤ a ∧ gaugeFun C x = a := by
  have h0 := gaugeFun_nonneg C x
  rcases eq_or_ne (gaugeFun C x) ⊤ with h | h
  · exact Or.inl h
  · have hb : gaugeFun C x ≠ ⊥ := ne_bot_of_le_ne_bot (by simp) h0
    exact Or.inr ⟨(gaugeFun C x).toReal, EReal.toReal_nonneg h0, (EReal.coe_toReal h hb).symm⟩

lemma gaugeFun_smul_le {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} {t R : ℝ}
    (ht : 0 < t) (hR : 0 ≤ R) (h : gaugeFun C x ≤ R) : gaugeFun C (t • x) ≤ ((t * R : ℝ) : EReal) := by
  rw [gaugeFun_le_iff hC h0 (by positivity)]
  intro s hs
  have h1 : R < s / t := by rw [lt_div_iff₀ ht]; linarith
  have h2 := (gaugeFun_le_iff hC h0 hR).1 h (s / t) h1
  have : t • x ∈ t • (s / t) • C := Set.smul_mem_smul_set h2
  rwa [smul_smul, mul_div_cancel₀ _ ht.ne'] at this

lemma gaugeFun_smul {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) (x : F) {t : ℝ} (ht : 0 < t) :
    gaugeFun C (t • x) = (t : EReal) * gaugeFun C x := by
  rcases gaugeFun_eq_coe_or_top C x with hx | ⟨a, ha, hx⟩
  · rw [hx, EReal.coe_mul_top_of_pos ht]
    rcases gaugeFun_eq_coe_or_top C (t • x) with htx | ⟨b, hb, htx⟩
    · exact htx
    · exfalso
      have := gaugeFun_smul_le hC h0 (x := t • x) (inv_pos.2 ht) hb htx.le
      rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, hx] at this
      exact absurd (top_le_iff.1 this) (EReal.coe_ne_top _)
  · rw [hx, ← EReal.coe_mul]
    apply le_antisymm
    · exact gaugeFun_smul_le hC h0 ht ha hx.le
    · rcases gaugeFun_eq_coe_or_top C (t • x) with htx | ⟨b, hb, htx⟩
      · rw [htx]; exact le_top
      · rw [htx]
        have := gaugeFun_smul_le hC h0 (x := t • x) (inv_pos.2 ht) hb htx.le
        rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul, hx] at this
        have h' : a ≤ t⁻¹ * b := by exact_mod_cast this
        have h'' : t * a ≤ b := by
          calc t * a ≤ t * (t⁻¹ * b) := by gcongr
            _ = b := by field_simp
        exact_mod_cast h''

lemma gaugeFun_convex_epigraph {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) :
    Convex ℝ (epigraph (gaugeFun C)) := by
  rintro ⟨x₁, r₁⟩ h₁ ⟨x₂, r₂⟩ h₂ a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq] at h₁ h₂ ⊢
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  have hr₁ : 0 ≤ r₁ := by exact_mod_cast (gaugeFun_nonneg C x₁).trans h₁
  have hr₂ : 0 ≤ r₂ := by exact_mod_cast (gaugeFun_nonneg C x₂).trans h₂
  rw [gaugeFun_le_iff hC h0 (by positivity)]
  rw [gaugeFun_le_iff hC h0 hr₁] at h₁
  rw [gaugeFun_le_iff hC h0 hr₂] at h₂
  intro s hs
  obtain ⟨ε, hε, rfl⟩ : ∃ ε : ℝ, 0 < ε ∧ s = a * r₁ + b * r₂ + ε :=
    ⟨s - (a * r₁ + b * r₂), by linarith, by ring⟩
  have m₁ := h₁ (r₁ + ε) (by linarith)
  have m₂ := h₂ (r₂ + ε) (by linarith)
  have key : a • x₁ + b • x₂ ∈ (a * (r₁ + ε)) • C + (b * (r₂ + ε)) • C := by
    rw [← smul_smul, ← smul_smul]
    exact Set.add_mem_add (Set.smul_mem_smul_set m₁) (Set.smul_mem_smul_set m₂)
  rw [← hC.add_smul (by positivity) (by positivity)] at key
  convert key using 2
  linear_combination (-ε) * hab

lemma gaugeFun_lsc {C : Set F} (hCc : IsClosed C) (hC : Convex ℝ C) (h0 : (0:F) ∈ C) :
    LowerSemicontinuous (gaugeFun C) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y using EReal.rec with
  | bot =>
    convert isClosed_empty
    ext x
    simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    have := gaugeFun_nonneg C x
    rw [h] at this
    exact absurd this (by simp)
  | coe R =>
    rcases lt_or_ge R 0 with hR | hR
    · convert isClosed_empty
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_empty_iff_false, iff_false, not_le]
      exact lt_of_lt_of_le (by exact_mod_cast hR) (gaugeFun_nonneg C x)
    · have : gaugeFun C ⁻¹' Set.Iic (R : EReal) = ⋂ s ∈ Set.Ioi R, s • C := by
        ext x
        simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_iInter, Set.mem_Ioi]
        exact gaugeFun_le_iff hC h0 hR
      rw [this]
      refine isClosed_biInter fun s hs => ?_
      have hs' : (0:ℝ) < s := lt_of_le_of_lt hR hs
      exact hCc.smul_of_ne_zero hs'.ne'
  | top => simp

lemma gaugeFun_eq_zero_iff {C : Set F} (hC : Convex ℝ C) (h0 : (0:F) ∈ C) {x : F} :
    gaugeFun C x = 0 ↔ ∀ t : ℝ, 0 < t → t • x ∈ C := by
  rw [le_antisymm_iff, and_iff_left (gaugeFun_nonneg C x)]
  rw [show (0 : EReal) = ((0:ℝ) : EReal) from rfl, gaugeFun_le_iff hC h0 le_rfl]
  constructor
  · intro h t ht
    have := h t⁻¹ (inv_pos.2 ht)
    rwa [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero ht.ne'), inv_inv] at this
  · intro h s hs
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne']
    exact h s⁻¹ (inv_pos.2 hs)

lemma asymptoticConeAt_mono {C : Set F} (hCc : IsClosed C) (hC : Convex ℝ C) {z z' : F}
    (hz' : z' ∈ C) {d : F} (hd : d ∈ asymptoticConeAt C z) :
    d ∈ asymptoticConeAt C z' := by
  intro t ht
  have hmem : ∀ ε ∈ Set.Ioo (0:ℝ) 1, (1 - ε) • z' + ε • z + t • d ∈ C := by
    rintro ε ⟨hε0, hε1⟩
    have h1 : z + (t / ε) • d ∈ C := hd (t / ε) (div_pos ht hε0)
    have h2 := hC hz' h1 (by linarith : (0:ℝ) ≤ 1 - ε) hε0.le (by ring)
    convert h2 using 1
    rw [smul_add, smul_smul, mul_div_cancel₀ _ hε0.ne', add_assoc]
  have hcont : Filter.Tendsto (fun ε : ℝ => (1 - ε) • z' + ε • z + t • d) (𝓝[>] 0)
      (𝓝 (z' + t • d)) := by
    have hc : Continuous (fun ε : ℝ => (1 - ε) • z' + ε • z + t • d) := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  exact hCc.mem_of_tendsto hcont (Filter.mem_of_superset (Ioo_mem_nhdsGT one_pos) hmem)

end FCAGaugeAux

open FCAGaugeAux in
lemma FCAGaugeAux.zero_mem_interior_iff {C : Set E} (hC : Convex ℝ C) (h0 : (0:E) ∈ C) :
    (∀ x, gaugeFun C x ≠ ⊤) ↔ (0 : E) ∈ interior C := by
  constructor
  · intro h
    have habs : ∀ x : E, ∃ t : ℝ, 0 < t ∧ t • x ∈ C := by
      intro x
      obtain ⟨s, hs, hx⟩ := (gaugeFun_ne_top_iff hC h0).1 (h x)
      exact ⟨s⁻¹, inv_pos.2 hs, (Set.mem_smul_set_iff_inv_smul_mem₀ hs.ne' _ _).1 hx⟩
    have hspan : affineSpan ℝ C = ⊤ := by
      rw [eq_top_iff]
      intro x _
      obtain ⟨t, ht, htx⟩ := habs x
      have h1 : (t • x : E) ∈ affineSpan ℝ C := mem_affineSpan ℝ htx
      have h2 : (0 : E) ∈ affineSpan ℝ C := mem_affineSpan ℝ h0
      have := (affineSpan ℝ C).smul_vsub_vadd_mem t⁻¹ h1 h2 h2
      simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using this
    obtain ⟨y, hy⟩ := (hC.interior_nonempty_iff_affineSpan_eq_top).2 hspan
    obtain ⟨t, ht, hty⟩ := habs (-y)
    have := hC.combo_interior_self_mem_interior hy hty (a := t / (1 + t)) (b := 1 / (1 + t))
      (by positivity) (by positivity) (by field_simp; ring)
    convert this using 1
    rw [smul_smul, smul_neg, ← sub_eq_add_neg, ← sub_smul]
    have : t / (1 + t) - 1 / (1 + t) * t = 0 := by field_simp; ring
    rw [this, zero_smul]
  · intro h x
    have hn : C ∈ 𝓝 (0 : E) := mem_interior_iff_mem_nhds.1 h
    have ht : Filter.Tendsto (fun t : ℝ => t • x) (𝓝 0) (𝓝 0) := by
      simpa using (Filter.tendsto_id (x := 𝓝 (0:ℝ))).smul_const x
    obtain ⟨t, htC, htpos⟩ :=
      (((ht.eventually hn).filter_mono nhdsWithin_le_nhds).and
        (self_mem_nhdsWithin (s := Set.Ioi (0:ℝ)) (a := 0))).exists
    rw [gaugeFun_ne_top_iff hC h0]
    refine ⟨t⁻¹, inv_pos.2 htpos, ?_⟩
    rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero (ne_of_gt htpos)), inv_inv]
    exact htC


theorem FCA_chap_C_1_2_5
  (C : Set E)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hC_origin : 0 ∈ C) :
  let g : E → EReal := fun x => gaugeFun C x
  let rC : ℝ → Set E :=
    fun r => Set.image (fun x => r • x) C
  ((∀ x, g x ≥ 0) ∧ (IsSublinear g) ∧
    (LowerSemicontinuous g)) ∧
  ((∀ x, g x ≠ ⊤) ↔ (0 ∈ interior C)) ∧
  (∀ (r : ℝ), r > 0 → ({x | g x ≤ r} = rC r)) ∧
  (∀ (z : E),
    z ∈ C → {x | g x = 0} = asymptoticConeAt C z) := by
  intro g rC
  refine ⟨⟨fun x => FCAGaugeAux.gaugeFun_nonneg C x, ⟨⟨fun x => ?_, ⟨0, ?_⟩, ?_⟩, fun x t ht => ?_⟩, ?_⟩,
    FCAGaugeAux.zero_mem_interior_iff hC_convex hC_origin, fun r hr => ?_, fun z hz => ?_⟩
  · exact lt_of_lt_of_le (by simp) (FCAGaugeAux.gaugeFun_nonneg C x)
  · exact lt_of_le_of_lt (FCAGaugeAux.gaugeFun_le_of_mem one_pos (by simpa using hC_origin))
      (EReal.coe_lt_top 1)
  · exact FCAGaugeAux.gaugeFun_convex_epigraph hC_convex hC_origin
  · exact FCAGaugeAux.gaugeFun_smul hC_convex hC_origin x ht
  · exact FCAGaugeAux.gaugeFun_lsc hC_closed hC_convex hC_origin
  · ext x
    simp only [Set.mem_setOf_eq, rC, g, Set.image_smul]
    exact FCAGaugeAux.gaugeFun_le_iff_mem hC_closed hC_convex hC_origin hr
  · ext x
    simp only [Set.mem_setOf_eq, g]
    rw [FCAGaugeAux.gaugeFun_eq_zero_iff hC_convex hC_origin]
    constructor
    · intro h
      exact FCAGaugeAux.asymptoticConeAt_mono hC_closed hC_convex hz (z := 0)
        (fun t ht => by simpa using h t ht)
    · intro h t ht
      simpa using FCAGaugeAux.asymptoticConeAt_mono hC_closed hC_convex hC_origin h t ht

end FCA_chap_C_1_2_5
