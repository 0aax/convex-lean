import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex4`, so the main result is `FCA_chap_C_ex4.FCA_chap_C_ex4`.
-/

namespace FCA_chap_C_ex4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_C_ex4
  (C₁ C₂ : Set E)
  (hC₁_closed : IsClosed C₁) (hC₁_convex : Convex ℝ C₁) (hC₁_origin : 0 ∈ C₁)
  (hC₂_closed : IsClosed C₂) (hC₂_convex : Convex ℝ C₂) (hC₂_origin : 0 ∈ C₂)
  (hC_int_origin : 0 ∈ interior C₁ ∨ 0 ∈ interior C₂) :
  let f := gaugeFun C₁
  let g := gaugeFun C₂
  let fg := fun x => infimalConv f g x
  (∃ C : Set E,
    IsClosed C ∧ Convex ℝ C ∧ 0 ∈ C ∧
    ∀ x, fg x = (gaugeFun C x)) ∧
  ({x | fg x < (1 : EReal)} =
    convexHull ℝ ({x | f x < 1} ∪ {x | g x < 1})) := by
  intro f g fg
  -- Characterization of `gaugeFun C x < r` for real `r`
  have hgauge : ∀ (C : Set E) (x : E) (r : ℝ),
      gaugeFun C x < (r : EReal) ↔ ∃ l : ℝ, 0 < l ∧ l < r ∧ ∃ c ∈ C, x = l • c := by
    intro C x r
    unfold gaugeFun
    rw [sInf_lt_iff]
    constructor
    · rintro ⟨z, ⟨l', rfl, hl', y, hy, hxy⟩, hz⟩
      exact ⟨l', hl', EReal.coe_lt_coe_iff.mp hz, y, hy, hxy⟩
    · rintro ⟨l, hl, hlr, c, hc, hxc⟩
      exact ⟨(l : EReal), ⟨l, rfl, hl, c, hc, hxc⟩, EReal.coe_lt_coe_iff.mpr hlr⟩
  have hgauge_le : ∀ (C : Set E) (l : ℝ), 0 < l → ∀ c ∈ C, gaugeFun C (l • c) ≤ (l : EReal) := by
    intro C l hl c hc
    unfold gaugeFun
    exact sInf_le ⟨l, rfl, hl, c, hc, rfl⟩
  have hgauge_nonneg : ∀ (C : Set E) (x : E), 0 ≤ gaugeFun C x := by
    intro C x
    unfold gaugeFun
    apply le_sInf
    rintro z ⟨l', rfl, hl', _⟩
    exact EReal.coe_nonneg.mpr hl'.le
  -- Splitting a strict real upper bound on a sum of two nonnegative extended reals
  have hsplit : ∀ u v : EReal, 0 ≤ u → 0 ≤ v → ∀ r : ℝ, u + v < r →
      ∃ p q : ℝ, u < p ∧ v < q ∧ p + q < r := by
    intro u v hu hv r huv
    induction u with
    | bot => exact absurd hu (by simp)
    | top =>
      rw [EReal.top_add_of_ne_bot (by rintro rfl; simp at hv)] at huv
      exact absurd huv (by simp)
    | coe u' =>
      induction v with
      | bot => exact absurd hv (by simp)
      | top =>
        rw [EReal.add_top_of_ne_bot (by simp)] at huv
        exact absurd huv (by simp)
      | coe v' =>
        have h : u' + v' < r := by exact_mod_cast huv
        refine ⟨u' + (r - u' - v') / 3, v' + (r - u' - v') / 3, ?_, ?_, ?_⟩
        · exact EReal.coe_lt_coe_iff.mpr (by linarith)
        · exact EReal.coe_lt_coe_iff.mpr (by linarith)
        · linarith
  -- Characterization of `fg x < r` for real `r`
  have hfg : ∀ (x : E) (r : ℝ), fg x < (r : EReal) ↔
      ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a + b < r ∧ ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, x = a • c₁ + b • c₂ := by
    intro x r
    show infimalConv f g x < (r : EReal) ↔ _
    unfold infimalConv
    rw [sInf_lt_iff]
    constructor
    · rintro ⟨z, ⟨y, rfl⟩, hz⟩
      obtain ⟨p, q, hp, hq, hpq⟩ :=
        hsplit _ _ (hgauge_nonneg C₁ y) (hgauge_nonneg C₂ (x - y)) r hz
      obtain ⟨a, ha, hap, c₁, hc₁, hy⟩ := (hgauge C₁ y p).mp hp
      obtain ⟨b, hb, hbq, c₂, hc₂, hxy⟩ := (hgauge C₂ (x - y) q).mp hq
      refine ⟨a, b, ha, hb, by linarith, c₁, hc₁, c₂, hc₂, ?_⟩
      rw [← hy, ← hxy]
      abel
    · rintro ⟨a, b, ha, hb, hab, c₁, hc₁, c₂, hc₂, rfl⟩
      refine ⟨f (a • c₁) + g (a • c₁ + b • c₂ - a • c₁), ⟨a • c₁, rfl⟩, ?_⟩
      rw [add_sub_cancel_left]
      calc f (a • c₁) + g (b • c₂) ≤ (a : EReal) + (b : EReal) :=
            add_le_add (hgauge_le C₁ a ha c₁ hc₁) (hgauge_le C₂ b hb c₂ hc₂)
        _ = ((a + b : ℝ) : EReal) := by rw [EReal.coe_add]
        _ < r := EReal.coe_lt_coe_iff.mpr hab
  -- Nonnegative coefficients suffice
  have hfg_weak : ∀ (x : E) (r : ℝ), (∃ a b : ℝ, 0 ≤ a ∧ 0 ≤ b ∧ a + b < r ∧
      ∃ c₁ ∈ C₁, ∃ c₂ ∈ C₂, x = a • c₁ + b • c₂) → fg x < (r : EReal) := by
    rintro x r ⟨a, b, ha, hb, hab, c₁, hc₁, c₂, hc₂, rfl⟩
    rw [hfg]
    obtain ⟨ε, hε, hεab⟩ : ∃ ε : ℝ, 0 < ε ∧ a + b + 2 * ε < r :=
      ⟨(r - a - b) / 3, by linarith, by linarith⟩
    refine ⟨a + ε, b + ε, by linarith, by linarith, by linarith,
      (a / (a + ε)) • c₁, hC₁_convex.smul_mem_of_zero_mem hC₁_origin hc₁ ⟨?_, ?_⟩,
      (b / (b + ε)) • c₂, hC₂_convex.smul_mem_of_zero_mem hC₂_origin hc₂ ⟨?_, ?_⟩, ?_⟩
    · exact div_nonneg ha (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · exact div_nonneg hb (by linarith)
    · rw [div_le_one (by linarith)]; linarith
    · rw [smul_smul, smul_smul, mul_div_cancel₀ _ (by linarith : a + ε ≠ 0),
        mul_div_cancel₀ _ (by linarith : b + ε ≠ 0)]
  -- Combining two points of a convex set containing the origin
  have hcomb : ∀ (S : Set E), Convex ℝ S → (0 : E) ∈ S → ∀ c ∈ S, ∀ c' ∈ S, ∀ p q : ℝ,
      0 ≤ p → 0 ≤ q → ∃ d ∈ S, p • c + q • c' = (p + q) • d := by
    intro S hS hS0 c hc c' hc' p q hp hq
    rcases (add_nonneg hp hq).eq_or_lt with h | h
    · have hp0 : p = 0 := by linarith
      have hq0 : q = 0 := by linarith
      exact ⟨0, hS0, by simp [hp0, hq0]⟩
    · refine ⟨(p / (p + q)) • c + (q / (p + q)) • c',
        hS hc hc' (div_nonneg hp h.le) (div_nonneg hq h.le) ?_, ?_⟩
      · rw [← add_div]; exact div_self h.ne'
      · rw [smul_add, smul_smul, smul_smul, mul_div_cancel₀ _ h.ne', mul_div_cancel₀ _ h.ne']
  set D := convexHull ℝ (C₁ ∪ C₂) with hD
  have hD_convex : Convex ℝ D := convex_convexHull ℝ _
  have hC₁D : C₁ ⊆ D := Set.subset_union_left.trans (subset_convexHull ℝ _)
  have hC₂D : C₂ ⊆ D := Set.subset_union_right.trans (subset_convexHull ℝ _)
  have hD_int : (0 : E) ∈ interior D := by
    rcases hC_int_origin with h | h
    · exact interior_mono hC₁D h
    · exact interior_mono hC₂D h
  have hD_join : D = convexJoin ℝ C₁ C₂ :=
    hC₁_convex.convexHull_union hC₂_convex ⟨0, hC₁_origin⟩ ⟨0, hC₂_origin⟩
  -- Two extended reals with the same real strict upper bounds are equal
  have hext : ∀ u v : EReal, (∀ r : ℝ, u < r ↔ v < r) → u = v := by
    intro u v h
    by_contra hne
    rcases lt_or_gt_of_ne hne with huv | huv
    · obtain ⟨r, hur, hrv⟩ := EReal.lt_iff_exists_real_btwn.mp huv
      exact absurd ((h r).mp hur) (not_lt.mpr hrv.le)
    · obtain ⟨r, hvr, hru⟩ := EReal.lt_iff_exists_real_btwn.mp huv
      exact absurd ((h r).mpr hvr) (not_lt.mpr hru.le)
  constructor
  · refine ⟨closure D, isClosed_closure, hD_convex.closure, subset_closure (hC₁D hC₁_origin), ?_⟩
    intro x
    apply hext
    intro r
    rw [hgauge]
    constructor
    · intro h
      obtain ⟨a, b, ha, hb, hab, c₁, hc₁, c₂, hc₂, hx⟩ := (hfg x r).mp h
      obtain ⟨d, hd, hd'⟩ := hcomb D hD_convex (hC₁D hC₁_origin) c₁ (hC₁D hc₁) c₂ (hC₂D hc₂)
        a b ha.le hb.le
      exact ⟨a + b, by linarith, hab, d, subset_closure hd, hx.trans hd'⟩
    · rintro ⟨l, hl, hlr, c, hc, rfl⟩
      obtain ⟨l', hll', hl'r⟩ : ∃ l' : ℝ, l < l' ∧ l' < r := ⟨(l + r) / 2, by linarith, by linarith⟩
      have hl'_pos : 0 < l' := by linarith
      have htc : (l / l') • c ∈ D := by
        have := hD_convex.combo_interior_closure_mem_interior (a := 1 - l / l') (b := l / l')
          hD_int hc (by rw [sub_pos, div_lt_one hl'_pos]; exact hll')
          (div_nonneg hl.le hl'_pos.le) (by ring)
        rw [smul_zero, zero_add] at this
        exact interior_subset this
      rw [hD_join] at htc
      obtain ⟨c₁, hc₁, c₂, hc₂, α, β, hα, hβ, hαβ, hcomb'⟩ := mem_convexJoin.mp htc
      apply hfg_weak
      refine ⟨l' * α, l' * β, mul_nonneg hl'_pos.le hα, mul_nonneg hl'_pos.le hβ, ?_,
        c₁, hc₁, c₂, hc₂, ?_⟩
      · rw [← mul_add, hαβ, mul_one]; exact hl'r
      · rw [mul_smul, mul_smul, ← smul_add, hcomb', smul_smul, mul_div_cancel₀ _ hl'_pos.ne']
  · ext x
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h
      obtain ⟨a, b, ha, hb, hab, c₁, hc₁, c₂, hc₂, rfl⟩ := (hfg x 1).mp (by exact_mod_cast h)
      have hs : 0 < a + b := by linarith
      have h1 : (a + b) • c₁ ∈ {x | f x < 1} ∪ {x | g x < 1} := by
        left
        show f ((a + b) • c₁) < 1
        exact_mod_cast (hgauge C₁ _ 1).mpr ⟨a + b, hs, hab, c₁, hc₁, rfl⟩
      have h2 : (a + b) • c₂ ∈ {x | f x < 1} ∪ {x | g x < 1} := by
        right
        show g ((a + b) • c₂) < 1
        exact_mod_cast (hgauge C₂ _ 1).mpr ⟨a + b, hs, hab, c₂, hc₂, rfl⟩
      have h3 : a • c₁ + b • c₂ ∈ segment ℝ ((a + b) • c₁) ((a + b) • c₂) := by
        refine ⟨a / (a + b), b / (a + b), div_nonneg ha.le hs.le, div_nonneg hb.le hs.le, ?_, ?_⟩
        · rw [← add_div]; exact div_self hs.ne'
        · rw [smul_smul, smul_smul, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
      exact segment_subset_convexHull h1 h2 h3
    · intro hx
      have hconv : Convex ℝ {x | fg x < 1} := by
        intro u hu v hv t s ht hs hts
        simp only [Set.mem_setOf_eq] at hu hv ⊢
        obtain ⟨a, b, ha, hb, hab, c₁, hc₁, c₂, hc₂, rfl⟩ := (hfg u 1).mp (by exact_mod_cast hu)
        obtain ⟨a', b', ha', hb', hab', c₁', hc₁', c₂', hc₂', rfl⟩ :=
          (hfg v 1).mp (by exact_mod_cast hv)
        obtain ⟨d₁, hd₁, hd₁'⟩ := hcomb C₁ hC₁_convex hC₁_origin c₁ hc₁ c₁' hc₁'
          (t * a) (s * a') (mul_nonneg ht ha.le) (mul_nonneg hs ha'.le)
        obtain ⟨d₂, hd₂, hd₂'⟩ := hcomb C₂ hC₂_convex hC₂_origin c₂ hc₂ c₂' hc₂'
          (t * b) (s * b') (mul_nonneg ht hb.le) (mul_nonneg hs hb'.le)
        have key : t • (a • c₁ + b • c₂) + s • (a' • c₁' + b' • c₂') =
            (t * a + s * a') • d₁ + (t * b + s * b') • d₂ := by
          rw [← hd₁', ← hd₂']
          simp only [smul_add, smul_smul]
          abel
        rw [key]
        have : fg ((t * a + s * a') • d₁ + (t * b + s * b') • d₂) < ((1 : ℝ) : EReal) := by
          apply hfg_weak
          refine ⟨t * a + s * a', t * b + s * b',
            add_nonneg (mul_nonneg ht ha.le) (mul_nonneg hs ha'.le),
            add_nonneg (mul_nonneg ht hb.le) (mul_nonneg hs hb'.le), ?_, d₁, hd₁, d₂, hd₂, rfl⟩
          rcases ht.eq_or_lt with h | h
          · have : s = 1 := by linarith
            rw [← h, this]; linarith
          · nlinarith
        exact_mod_cast this
      refine convexHull_min ?_ hconv hx
      rintro y (hy | hy)
      · simp only [Set.mem_setOf_eq] at hy ⊢
        obtain ⟨l, hl, hl1, c, hc, rfl⟩ := (hgauge C₁ y 1).mp (by exact_mod_cast hy)
        have : fg (l • c) < ((1 : ℝ) : EReal) :=
          hfg_weak _ 1 ⟨l, 0, hl.le, le_refl _, by linarith, c, hc, 0, hC₂_origin, by simp⟩
        exact_mod_cast this
      · simp only [Set.mem_setOf_eq] at hy ⊢
        obtain ⟨l, hl, hl1, c, hc, rfl⟩ := (hgauge C₂ y 1).mp (by exact_mod_cast hy)
        have : fg (l • c) < ((1 : ℝ) : EReal) :=
          hfg_weak _ 1 ⟨0, l, le_refl _, hl.le, by linarith, 0, hC₁_origin, c, hc, by simp⟩
        exact_mod_cast this

end FCA_chap_C_ex4
