import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_8_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_8_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_8_i`, so the main result is `FCA_chap_B_3_2_8_i.FCA_chap_B_3_2_8_i`.
-/

namespace FCA_chap_B_3_2_8_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma sInf_coe_ub_eq_iSup {ι : Type*} (q : ι → EReal) :
    sInf ((fun r : ℝ => (r : EReal)) '' {ρ : ℝ | ∀ i, q i ≤ ρ}) = ⨆ i, q i := by
  apply le_antisymm
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    apply sInf_le
    exact ⟨z, fun i => (le_iSup q i).trans hz.le, rfl⟩
  · apply le_sInf
    rintro _ ⟨ρ, hρ, rfl⟩
    exact iSup_le hρ

lemma mem_horizonCone_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {C : Set F}
    (hconv : Convex ℝ C) (hclosed : IsClosed C) {p : F} (hp : p ∈ C) (v : F) :
    v ∈ horizonCone C ↔ ∀ s : ℝ, 0 < s → p + s • v ∈ C := by
  constructor
  · rintro ⟨xs, l, hxs, hl, hlim⟩ s hs
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hl).1
    have hlpos : ∀ᶠ k in Filter.atTop, 0 < l k := (tendsto_nhdsWithin_iff.mp hl).2
    have hsmall : ∀ᶠ k in Filter.atTop, s * l k < 1 := by
      have : Filter.Tendsto (fun k => s * l k) Filter.atTop (𝓝 0) := by
        simpa using hl0.const_mul s
      exact this.eventually (gt_mem_nhds one_pos)
    have hmem : ∀ᶠ k in Filter.atTop, p + (s * l k) • (xs k - p) ∈ C := by
      filter_upwards [hlpos, hsmall] with k hk1 hk2
      exact hconv.add_smul_sub_mem hp (hxs k) ⟨(mul_pos hs hk1).le, hk2.le⟩
    have htend : Filter.Tendsto (fun k => p + (s * l k) • (xs k - p)) Filter.atTop
        (𝓝 (p + s • v)) := by
      have h1 : ∀ k, (s * l k) • (xs k - p) = s • (l k • xs k) - (s * l k) • p := by
        intro k; rw [smul_sub, smul_smul]
      simp_rw [h1]
      have h2 : Filter.Tendsto (fun k => s • (l k • xs k) - (s * l k) • p) Filter.atTop
          (𝓝 (s • v - (s * 0) • p)) :=
        (hlim.const_smul s).sub ((hl0.const_mul s).smul_const p)
      simpa using h2.const_add p
    exact hclosed.mem_of_tendsto htend hmem
  · intro h
    refine ⟨fun k => p + ((k:ℝ) + 1) • v, fun k => 1 / ((k:ℝ) + 1),
      fun k => h _ (by positivity), ?_, ?_⟩
    · exact tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall (fun k => by simp only [Set.mem_Ioi]; positivity)⟩
    · have h1 : ∀ k : ℕ, (1 / ((k:ℝ) + 1)) • (p + ((k:ℝ) + 1) • v)
          = (1 / ((k:ℝ)+1)) • p + v := by
        intro k
        rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ (by positivity), one_smul]
      simp_rw [h1]
      have := ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const p).add_const v
      simpa using this

lemma mem_hc_epi_iff {h : E → EReal} (hconv : Convex ℝ (epigraph h))
    (hclosed : IsClosed (epigraph h)) {x : E} {c : ℝ} (hx : h x = c) (d : E) (ρ : ℝ) :
    (d, ρ) ∈ horizonCone (epigraph h) ↔
      ∀ s : ℝ, 0 < s → h (x + s • d) ≤ ((c + s * ρ : ℝ) : EReal) := by
  have hp : ((x, c) : E × ℝ) ∈ epigraph h := by simp [epigraph, hx]
  rw [mem_horizonCone_iff hconv hclosed hp]
  simp [epigraph]

lemma epi_mono {h : E → EReal} (hconv : Convex ℝ (epigraph h)) {x : E} {c : ℝ} (hx : h x = c)
    {d : E} {s s' : ℝ} (hs : 0 < s) (hss' : s ≤ s') (ρ : ℝ)
    (h' : h (x + s' • d) ≤ ((c + s' * ρ : ℝ) : EReal)) :
    h (x + s • d) ≤ ((c + s * ρ : ℝ) : EReal) := by
  have hp : ((x, c) : E × ℝ) ∈ epigraph h := by simp [epigraph, hx]
  have hq : ((x + s' • d, c + s' * ρ) : E × ℝ) ∈ epigraph h := h'
  have hs' : 0 < s' := hs.trans_le hss'
  have := hconv.add_smul_sub_mem hp hq (t := s / s') ⟨by positivity, (div_le_one hs').mpr hss'⟩
  have heq : ((x, c) : E × ℝ) + (s / s') • ((x + s' • d, c + s' * ρ) - (x, c))
      = (x + s • d, c + s * ρ) := by
    ext
    · simp [smul_smul, div_mul_cancel₀ s hs'.ne']
    · simp; field_simp
  rw [heq] at this
  exact this

lemma q_le_iff {a : EReal} {c s ρ : ℝ} (hs : 0 < s) :
    (a - c) / (s : EReal) ≤ (ρ : EReal) ↔ a ≤ ((c + s * ρ : ℝ) : EReal) := by
  rw [EReal.div_le_iff_le_mul (by exact_mod_cast hs) (EReal.coe_ne_top s),
    EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot c)) (Or.inl (EReal.coe_ne_top c))]
  rw [show ((c + s * ρ : ℝ) : EReal) = (s : EReal) * (ρ : EReal) + (c : EReal) by
    rw [EReal.coe_add, EReal.coe_mul, add_comm]]

lemma EReal_iSup_add_of_monotone {ι : Type*} [Preorder ι] [IsDirected ι (· ≤ ·)]
    {f g : ι → EReal} (hf : Monotone f) (hg : Monotone g) :
    ⨆ i, (f i + g i) = (⨆ i, f i) + (⨆ i, g i) := by
  apply le_antisymm
  · exact iSup_le fun i => add_le_add (le_iSup f i) (le_iSup g i)
  · apply EReal.add_le_of_forall_lt
    intro a ha b hb
    obtain ⟨i, hi⟩ := lt_iSup_iff.mp ha
    obtain ⟨j, hj⟩ := lt_iSup_iff.mp hb
    obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
    calc a + b ≤ f k + g k := add_le_add (hi.le.trans (hf hik)) (hj.le.trans (hg hjk))
      _ ≤ ⨆ i, (f i + g i) := le_iSup (fun i => f i + g i) k

lemma q_mono {h : E → EReal} (hconv : Convex ℝ (epigraph h)) {x : E} {c : ℝ} (hx : h x = c)
    (d : E) :
    Monotone (fun s : Set.Ioi (0:ℝ) => (h (x + (s:ℝ) • d) - c) / ((s:ℝ) : EReal)) := by
  rintro ⟨s, hs⟩ ⟨s', hs'⟩ hss'
  simp only
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  rw [q_le_iff hs]
  have := (q_le_iff (Set.mem_Ioi.mp hs')).mp hz.le
  exact epi_mono hconv hx hs hss' z this

lemma asymptoticFun_eq_iSup {h : E → EReal} (hconv : Convex ℝ (epigraph h))
    (hclosed : IsClosed (epigraph h)) {x : E} {c : ℝ} (hx : h x = c) (d : E) :
    asymptoticFun h d = ⨆ s : Set.Ioi (0:ℝ), (h (x + (s:ℝ) • d) - c) / ((s : ℝ) : EReal) := by
  rw [← sInf_coe_ub_eq_iSup]
  unfold asymptoticFun funFromSet verticalSlice
  congr 2
  ext ρ
  simp only [Set.mem_setOf_eq]
  rw [mem_hc_epi_iff hconv hclosed hx]
  constructor
  · rintro H ⟨s, hs⟩
    exact (q_le_iff hs).mpr (H s hs)
  · intro H s hs
    exact (q_le_iff hs).mp (H ⟨s, hs⟩)

lemma epi_closed_of_lsc {h : E → EReal} (hh : LowerSemicontinuous h) :
    IsClosed (epigraph h) := by
  have := hh.isClosed_epigraph
  exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))

lemma epi_convex_add {h₁ h₂ : E → EReal} (hb₁ : ∀ x, ⊥ < h₁ x) (hb₂ : ∀ x, ⊥ < h₂ x)
    (hc₁ : Convex ℝ (epigraph h₁)) (hc₂ : Convex ℝ (epigraph h₂)) :
    Convex ℝ (epigraph (fun v => h₁ v + h₂ v)) := by
  have split : ∀ y : E, ∀ r : ℝ, h₁ y + h₂ y ≤ (r : EReal) →
      ∃ u₁ u₂ : ℝ, h₁ y = u₁ ∧ h₂ y = u₂ ∧ u₁ + u₂ ≤ r := by
    intro y r hyr
    have hy₁ : h₁ y ≠ ⊤ := by
      intro hh
      rw [hh, EReal.top_add_of_ne_bot (hb₂ y).ne'] at hyr
      exact EReal.coe_ne_top r (top_le_iff.mp hyr)
    have hy₂ : h₂ y ≠ ⊤ := by
      intro hh
      rw [hh, EReal.add_top_of_ne_bot (hb₁ y).ne'] at hyr
      exact EReal.coe_ne_top r (top_le_iff.mp hyr)
    refine ⟨(h₁ y).toReal, (h₂ y).toReal, (EReal.coe_toReal hy₁ (hb₁ y).ne').symm,
      (EReal.coe_toReal hy₂ (hb₂ y).ne').symm, ?_⟩
    rw [← EReal.coe_toReal hy₁ (hb₁ y).ne', ← EReal.coe_toReal hy₂ (hb₂ y).ne',
      ← EReal.coe_add, EReal.coe_le_coe_iff] at hyr
    exact hyr
  rintro ⟨x, r⟩ hxr ⟨y, r'⟩ hyr' a b ha hb hab
  obtain ⟨u₁, u₂, ex₁, ex₂, hu⟩ := split x r hxr
  obtain ⟨v₁, v₂, ey₁, ey₂, hv⟩ := split y r' hyr'
  have H₁ := hc₁ (x := (x, u₁)) (y := (y, v₁)) (le_of_eq ex₁) (le_of_eq ey₁) ha hb hab
  have H₂ := hc₂ (x := (x, u₂)) (y := (y, v₂)) (le_of_eq ex₂) (le_of_eq ey₂) ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at H₁ H₂ ⊢
  calc h₁ (a • x + b • y) + h₂ (a • x + b • y)
      ≤ ((a * u₁ + b * v₁ : ℝ) : EReal) + ((a * u₂ + b * v₂ : ℝ) : EReal) := add_le_add H₁ H₂
    _ = ((a * (u₁ + u₂) + b * (v₁ + v₂) : ℝ) : EReal) := by
        rw [← EReal.coe_add]; congr 1; ring
    _ ≤ ((a * r + b * r' : ℝ) : EReal) := by
        rw [EReal.coe_le_coe_iff]
        nlinarith

lemma lsc_add {h₁ h₂ : E → EReal} (hb₁ : ∀ x, ⊥ < h₁ x) (hb₂ : ∀ x, ⊥ < h₂ x)
    (hl₁ : LowerSemicontinuous h₁) (hl₂ : LowerSemicontinuous h₂) :
    LowerSemicontinuous (fun v => h₁ v + h₂ v) :=
  hl₁.add' hl₂ (fun x => EReal.continuousAt_add (Or.inr (hb₂ x).ne') (Or.inl (hb₁ x).ne'))

lemma ereal_mul_le_iff {t : ℝ} (ht : 0 < t) (a : EReal) (r : ℝ) :
    (t : EReal) * a ≤ (r : EReal) ↔ a ≤ ((r / t : ℝ) : EReal) := by
  induction a with
  | bot => simp [EReal.coe_mul_bot_of_pos ht]
  | top => simp [EReal.coe_mul_top_of_pos ht]
  | coe u =>
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff, le_div_iff₀ ht, mul_comm]

lemma epi_convex_smul {h : E → EReal} {t : ℝ} (ht : 0 < t) (hc : Convex ℝ (epigraph h)) :
    Convex ℝ (epigraph (fun v => (t : EReal) * h v)) := by
  have : epigraph (fun v => (t : EReal) * h v) =
      (fun p : E × ℝ => (p.1, p.2 / t)) ⁻¹' epigraph h := by
    ext ⟨x, r⟩
    simp only [epigraph, Set.mem_setOf_eq, Set.mem_preimage]
    exact ereal_mul_le_iff ht (h x) r
  rw [this]
  refine hc.is_linear_preimage ⟨fun p q => ?_, fun c p => ?_⟩
  · simp [add_div]
  · simp [mul_div_assoc]

lemma lsc_smul {h : E → EReal} {t : ℝ} (ht : 0 < t) (hl : LowerSemicontinuous h) :
    LowerSemicontinuous (fun v => (t : EReal) * h v) := by
  have hcont : Continuous (fun a : EReal => (t : EReal) * a) := by
    rw [continuous_iff_continuousAt]
    intro a
    have h1 : ContinuousAt (fun p : EReal × EReal => p.1 * p.2) ((t : EReal), a) :=
      EReal.continuousAt_mul (Or.inl (by simp [ht.ne'])) (Or.inl (by simp [ht.ne']))
        (Or.inl (EReal.coe_ne_bot t)) (Or.inl (EReal.coe_ne_top t))
    exact h1.comp (Continuous.prodMk continuous_const continuous_id).continuousAt
  have hmono : Monotone (fun a : EReal => (t : EReal) * a) := fun a b hab =>
    mul_le_mul_of_nonneg_left hab (by exact_mod_cast ht.le)
  exact hcont.comp_lowerSemicontinuous hl hmono

lemma bot_lt_smul {t : ℝ} (ht : 0 < t) {a : EReal} (ha : ⊥ < a) : ⊥ < (t : EReal) * a := by
  induction a with
  | bot => exact absurd ha (lt_irrefl _)
  | top => rw [EReal.coe_mul_top_of_pos ht]; exact ha
  | coe u => rw [← EReal.coe_mul]; exact EReal.bot_lt_coe _

lemma epi_convex_zero : Convex ℝ (epigraph (fun _ : E => (0:EReal))) := by
  rintro ⟨x, r⟩ hxr ⟨y, r'⟩ hyr' a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, EReal.coe_nonneg, Prod.smul_mk, Prod.mk_add_mk,
    smul_eq_mul] at hxr hyr' ⊢
  positivity

lemma asymptoticFun_add {h₁ h₂ : E → EReal}
    (hb₁ : ∀ x, ⊥ < h₁ x) (hc₁ : Convex ℝ (epigraph h₁)) (hl₁ : LowerSemicontinuous h₁)
    (hb₂ : ∀ x, ⊥ < h₂ x) (hc₂ : Convex ℝ (epigraph h₂)) (hl₂ : LowerSemicontinuous h₂)
    {x : E} (hx₁ : h₁ x < ⊤) (hx₂ : h₂ x < ⊤) (d : E) :
    asymptoticFun (fun v => h₁ v + h₂ v) d = asymptoticFun h₁ d + asymptoticFun h₂ d := by
  set c₁ := (h₁ x).toReal
  set c₂ := (h₂ x).toReal
  have e₁ : h₁ x = c₁ := (EReal.coe_toReal hx₁.ne (hb₁ x).ne').symm
  have e₂ : h₂ x = c₂ := (EReal.coe_toReal hx₂.ne (hb₂ x).ne').symm
  have e : (fun v => h₁ v + h₂ v) x = ((c₁ + c₂ : ℝ) : EReal) := by
    simp only [e₁, e₂, EReal.coe_add]
  rw [asymptoticFun_eq_iSup (epi_convex_add hb₁ hb₂ hc₁ hc₂)
      (epi_closed_of_lsc (lsc_add hb₁ hb₂ hl₁ hl₂)) e,
    asymptoticFun_eq_iSup hc₁ (epi_closed_of_lsc hl₁) e₁,
    asymptoticFun_eq_iSup hc₂ (epi_closed_of_lsc hl₂) e₂]
  rw [← EReal_iSup_add_of_monotone (q_mono hc₁ e₁ d) (q_mono hc₂ e₂ d)]
  congr 1
  ext ⟨s, hs⟩
  simp only
  rw [← EReal.add_div_of_nonneg_right (by exact_mod_cast (le_of_lt hs))]
  congr 1
  rw [sub_eq_add_neg, sub_eq_add_neg, sub_eq_add_neg, ← EReal.coe_neg (c₁ + c₂),
    ← EReal.coe_neg c₁, ← EReal.coe_neg c₂, neg_add, EReal.coe_add]
  abel

lemma asymptoticFun_sum {ι : Type*} [DecidableEq ι] (s : Finset ι) (g : ι → E → EReal)
    (hb : ∀ i ∈ s, ∀ x, ⊥ < g i x) (hc : ∀ i ∈ s, Convex ℝ (epigraph (g i)))
    (hl : ∀ i ∈ s, LowerSemicontinuous (g i)) {x : E} (hx : ∀ i ∈ s, g i x < ⊤) (d : E) :
    (∀ y, ⊥ < ∑ i ∈ s, g i y) ∧ Convex ℝ (epigraph (fun v => ∑ i ∈ s, g i v)) ∧
    LowerSemicontinuous (fun v => ∑ i ∈ s, g i v) ∧ (∑ i ∈ s, g i x < ⊤) ∧
    asymptoticFun (fun v => ∑ i ∈ s, g i v) d = ∑ i ∈ s, asymptoticFun (g i) d := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    refine ⟨fun _ => EReal.bot_lt_zero, epi_convex_zero, lowerSemicontinuous_const,
      EReal.zero_lt_top, ?_⟩
    rw [asymptoticFun_eq_iSup epi_convex_zero (epi_closed_of_lsc lowerSemicontinuous_const)
      (x := x) (c := 0) (by simp)]
    simp
  | @insert a s ha ih =>
    have hb' : ∀ i ∈ s, ∀ x, ⊥ < g i x := fun i hi => hb i (Finset.mem_insert_of_mem hi)
    have hc' : ∀ i ∈ s, Convex ℝ (epigraph (g i)) := fun i hi =>
      hc i (Finset.mem_insert_of_mem hi)
    have hl' : ∀ i ∈ s, LowerSemicontinuous (g i) := fun i hi =>
      hl i (Finset.mem_insert_of_mem hi)
    have hx' : ∀ i ∈ s, g i x < ⊤ := fun i hi => hx i (Finset.mem_insert_of_mem hi)
    obtain ⟨Sb, Sc, Sl, Sx, SA⟩ := ih hb' hc' hl' hx'
    have hba := hb a (Finset.mem_insert_self a s)
    have hca := hc a (Finset.mem_insert_self a s)
    have hla := hl a (Finset.mem_insert_self a s)
    have hxa := hx a (Finset.mem_insert_self a s)
    simp only [Finset.sum_insert ha]
    refine ⟨fun y => ?_, epi_convex_add hba Sb hca Sc, lsc_add hba Sb hla Sl,
      EReal.add_lt_top hxa.ne Sx.ne, ?_⟩
    · exact Ne.bot_lt (EReal.add_ne_bot_iff.mpr ⟨(hba y).ne', (Sb y).ne'⟩)
    · rw [asymptoticFun_add hba hca hla Sb Sc Sl hxa Sx d, SA]

lemma sum_lt_top_imp {ι : Type*} (s : Finset ι) (a : ι → EReal) (hb : ∀ i ∈ s, ⊥ < a i)
    (h : ∑ i ∈ s, a i < ⊤) : ∀ i ∈ s, a i < ⊤ := by
  classical
  intro i hi
  rw [← Finset.add_sum_erase s a hi] at h
  have hne : ∑ j ∈ s.erase i, a j ≠ ⊥ := by
    apply Finset.sum_induction _ (fun y => y ≠ ⊥)
    · intro u v hu hv; exact EReal.add_ne_bot_iff.mpr ⟨hu, hv⟩
    · exact EReal.zero_ne_bot
    · intro j hj; exact (hb j (Finset.mem_of_mem_erase hj)).ne'
  by_contra hcon
  rw [not_lt, top_le_iff] at hcon
  rw [hcon, EReal.top_add_of_ne_bot hne] at h
  exact lt_irrefl _ h

set_option linter.unusedVariables false in
theorem FCA_chap_B_3_2_8_i
  {n m : ℕ}
  (fm : ℕ → (E → EReal))
  (t : ℕ → ℝ)
  (x₀ : ℕ → E)
  (hf_closed_conv : ∀ i ∈ Finset.range m, InClosedConvRn (fm i))
  (hf_finite : ∀ i ∈ Finset.range m, fm i (x₀ i) < ⊤)
  (ht_pos : ∀ i ∈ Finset.range m, t i > 0)
  (fm_ne_bot : ∀ x₁ x₂, ⊥ < fm x₁ x₂) :
  let f := fun v => ∑ i ∈ Finset.range m, (t i) * (fm i v)
  let f'_sum_infinity := fun d =>
    ∑ i ∈ Finset.range m, asymptoticFun (fun v => (t i) * (fm i v)) d
  (effDom f).Nonempty → ∀ d,
  asymptoticFun f d = f'_sum_infinity d := by
  intro f f'_sum_infinity hne d
  obtain ⟨x, hx⟩ := hne
  have hb : ∀ i ∈ Finset.range m, ∀ y, ⊥ < (fun v => (t i : EReal) * fm i v) y :=
    fun i hi y => bot_lt_smul (ht_pos i hi) (fm_ne_bot i y)
  have hc : ∀ i ∈ Finset.range m, Convex ℝ (epigraph (fun v => (t i : EReal) * fm i v)) :=
    fun i hi => epi_convex_smul (ht_pos i hi) (hf_closed_conv i hi).1.2.2
  have hl : ∀ i ∈ Finset.range m, LowerSemicontinuous (fun v => (t i : EReal) * fm i v) :=
    fun i hi => lsc_smul (ht_pos i hi) (hf_closed_conv i hi).2
  have hx' : ∑ i ∈ Finset.range m, (t i : EReal) * fm i x < ⊤ := hx
  have hxi : ∀ i ∈ Finset.range m, (fun v => (t i : EReal) * fm i v) x < ⊤ :=
    sum_lt_top_imp (Finset.range m) (fun i => (t i : EReal) * fm i x)
      (fun i hi => hb i hi x) hx'
  exact (asymptoticFun_sum (Finset.range m) (fun i v => (t i : EReal) * fm i v)
    hb hc hl hxi d).2.2.2.2

end FCA_chap_B_3_2_8_i
