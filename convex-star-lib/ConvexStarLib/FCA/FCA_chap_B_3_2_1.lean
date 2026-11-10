import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_1`, so the main result is `FCA_chap_B_3_2_1.FCA_chap_B_3_2_1`.
-/

namespace FCA_chap_B_3_2_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma horizonCone_eq_asymptoticConeAt_aux {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {C : Set F} (hC : Convex ℝ C) (hCc : IsClosed C) {x : F} (hx : x ∈ C) :
    horizonCone C = asymptoticConeAt C x := by
  ext d
  constructor
  · rintro ⟨xs, l, hxs, hl, hlim⟩ t ht
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hlpos : ∀ᶠ i in Filter.atTop, 0 < l i := (tendsto_nhdsWithin_iff.mp hl).2
    have hlim2 : Filter.Tendsto (fun i => (1 - t * l i) • x + t • (l i • xs i)) Filter.atTop
        (𝓝 ((1 - t * 0) • x + t • d)) := by
      refine Filter.Tendsto.add ?_ (hlim.const_smul t)
      exact (tendsto_const_nhds.sub (tendsto_const_nhds.mul hl0)).smul_const x
    rw [mul_zero, sub_zero, one_smul] at hlim2
    apply hCc.mem_of_tendsto hlim2
    have hsmall : ∀ᶠ i in Filter.atTop, t * l i < 1 := by
      have h1 : Filter.Tendsto (fun i => t * l i) Filter.atTop (𝓝 (t * 0)) :=
        tendsto_const_nhds.mul hl0
      rw [mul_zero] at h1
      exact h1.eventually (gt_mem_nhds one_pos)
    filter_upwards [hlpos, hsmall] with i hi1 hi2
    have := hC hx (hxs i) (by linarith : (0:ℝ) ≤ 1 - t * l i)
      (by positivity : (0:ℝ) ≤ t * l i) (by ring)
    rwa [smul_smul]
  · intro hd
    refine ⟨fun i : ℕ => x + ((i:ℝ) + 1) • d, fun i : ℕ => 1 / ((i:ℝ) + 1), ?_, ?_, ?_⟩
    · intro i; exact hd _ (by positivity)
    · apply tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun i => Set.mem_Ioi.mpr (by positivity))
    · have h1 : ∀ i : ℕ, (1 / ((i:ℝ) + 1)) • (x + ((i:ℝ) + 1) • d)
          = (1 / ((i:ℝ) + 1)) • x + d := by
        intro i
        rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ (show ((i:ℝ) + 1) ≠ 0 by positivity),
          one_smul]
      simp_rw [h1]
      have h2 : Filter.Tendsto (fun i : ℕ => (1 / ((i:ℝ) + 1)) • x + d) Filter.atTop
          (𝓝 ((0:ℝ) • x + d)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat.smul_const x).add_const d
      rwa [zero_smul, zero_add] at h2

lemma convex_asymptoticConeAt_aux {F : Type*} [AddCommGroup F] [Module ℝ F]
    {C : Set F} (hC : Convex ℝ C) (x : F) : Convex ℝ (asymptoticConeAt C x) := by
  intro u hu v hv a b ha hb hab t ht
  have := hC (hu t ht) (hv t ht) ha hb hab
  convert this using 1
  calc x + t • (a • u + b • v) = (a + b) • x + t • (a • u + b • v) := by rw [hab, one_smul]
    _ = a • (x + t • u) + b • (x + t • v) := by module

lemma isClosed_asymptoticConeAt_aux {F : Type*} [AddCommGroup F] [Module ℝ F]
    [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    {C : Set F} (hC : IsClosed C) (x : F) : IsClosed (asymptoticConeAt C x) := by
  have : asymptoticConeAt C x = ⋂ t ∈ Set.Ioi (0:ℝ), (fun d => x + t • d) ⁻¹' C := by
    ext d; simp [asymptoticConeAt]
  rw [this]
  exact isClosed_biInter (fun t _ => hC.preimage (continuous_const.add (continuous_const.smul continuous_id)))

lemma lsc_of_isClosed_epigraph_aux {α : Type*} [TopologicalSpace α] {g : α → EReal}
    (hg : IsClosed (epigraph g)) : LowerSemicontinuous g := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro y
  induction y with
  | bot =>
    have : g ⁻¹' Set.Iic ⊥ = ⋂ n : ℕ, (fun x => (x, -(n:ℝ))) ⁻¹' epigraph g := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iic, le_bot_iff, Set.mem_iInter, epigraph,
        Set.mem_setOf_eq]
      constructor
      · intro h n; rw [h]; exact bot_le
      · intro h
        rw [EReal.eq_bot_iff_forall_lt]
        intro y
        obtain ⟨n, hn⟩ := exists_nat_gt (-y)
        have hny : (-(n:ℝ)) < y := by linarith
        calc g x ≤ ((-(n:ℝ) : ℝ) : EReal) := h n
          _ < y := EReal.coe_lt_coe_iff.mpr hny
    rw [this]
    exact isClosed_iInter (fun n => hg.preimage (Continuous.prodMk_left _))
  | top => simp
  | coe r => exact hg.preimage (Continuous.prodMk_left r)

lemma EReal_sInf_coe_image_aux (M : EReal) :
    sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | M ≤ r}) = M := by
  apply le_antisymm
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    exact sInf_le ⟨z, hz.le, rfl⟩
  · apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    exact hr

lemma EReal_dq_le_iff_aux {y : EReal} {a t r : ℝ} (ht : 0 < t) :
    (y - a) / t ≤ (r : EReal) ↔ y ≤ ((a + t * r : ℝ) : EReal) := by
  have ht' : (0 : EReal) < t := by exact_mod_cast ht
  induction y with
  | bot => simp [EReal.bot_sub, EReal.bot_div_of_pos_ne_top ht' (EReal.coe_ne_top t)]
  | top =>
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top ht' (EReal.coe_ne_top t)]
    simp only [top_le_iff, EReal.coe_ne_top]
  | coe y =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      div_le_iff₀ ht]
    constructor <;> intro h <;> nlinarith

set_option linter.unusedVariables false in
theorem FCA_chap_B_3_2_1
  (f : E → EReal)
  (hf_closed_conv : InClosedConvRn f)
  (f_ne_bot : ∀ (x : E), ⊥ < f x) :
  let f'_infinity := asymptoticFun f
  (∀ (x₁ : E × ℝ), x₁ ∈ epigraph f →
    asymptoticConeAt (epigraph f) x₁ = epigraph f'_infinity) ∧
  InClosedConvRn f'_infinity ∧ (∀ (d : E), ⊥ < f'_infinity d) ∧
  (∀ (x₀ : E), x₀ ∈ effDom f → ∀ (d : E),
    f'_infinity d =
      sSup {q : EReal | ∃ (t : ℝ), 0 < t ∧ q = differenceQuotient f x₀ d t} ∧
    Filter.Tendsto (fun (t : ℝ) => differenceQuotient f x₀ d t)
      Filter.atTop (𝓝 (f'_infinity d))) := by
  intro f'_infinity
  obtain ⟨⟨hbot, ⟨x₀, hx₀⟩, hconv⟩, hlsc⟩ := hf_closed_conv
  have hconv' : Convex ℝ (epigraph f) := hconv
  have hclosed : IsClosed (epigraph f) :=
    hlsc.isClosed_epigraph.preimage
      (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  -- the horizon cone equals the asymptotic cone at any point of the epigraph
  have hK : ∀ p ∈ epigraph f, horizonCone (epigraph f) = asymptoticConeAt (epigraph f) p :=
    fun p hp => horizonCone_eq_asymptoticConeAt_aux hconv' hclosed hp
  -- points of the domain give points of the epigraph
  have hfx : ∀ x ∈ effDom f, f x = (((f x).toReal : ℝ) : EReal) := fun x hx =>
    (EReal.coe_toReal (ne_of_lt hx) (hbot x).ne').symm
  have hxepi : ∀ x ∈ effDom f, (x, (f x).toReal) ∈ epigraph f := by
    intro x hx
    show f x ≤ (((f x).toReal : ℝ) : EReal)
    rw [← hfx x hx]
  -- characterization of the horizon cone through difference quotients
  have hchar : ∀ x ∈ effDom f, ∀ d : E, ∀ r : ℝ, (d, r) ∈ horizonCone (epigraph f) ↔
      sSup {q : EReal | ∃ (t : ℝ), 0 < t ∧ q = differenceQuotient f x d t} ≤ r := by
    intro x hx d r
    rw [hK _ (hxepi x hx), sSup_le_iff]
    constructor
    · rintro h _ ⟨t, ht, rfl⟩
      have h1 : f (x + t • d) ≤ (((f x).toReal + t * r : ℝ) : EReal) := h t ht
      unfold differenceQuotient
      rw [hfx x hx, EReal_dq_le_iff_aux ht]
      exact h1
    · intro h t ht
      have h1 := h _ ⟨t, ht, rfl⟩
      unfold differenceQuotient at h1
      rw [hfx x hx, EReal_dq_le_iff_aux ht] at h1
      exact h1
  -- the asymptotic function is the supremum of the difference quotients
  have hf'eq : ∀ x ∈ effDom f, ∀ d, f'_infinity d =
      sSup {q : EReal | ∃ (t : ℝ), 0 < t ∧ q = differenceQuotient f x d t} := by
    intro x hx d
    show sInf ((fun r : ℝ => (r : EReal)) '' verticalSlice (horizonCone (epigraph f)) d) = _
    have : verticalSlice (horizonCone (epigraph f)) d = {r : ℝ |
        sSup {q : EReal | ∃ (t : ℝ), 0 < t ∧ q = differenceQuotient f x d t} ≤ r} := by
      ext r
      exact hchar x hx d r
    rw [this, EReal_sInf_coe_image_aux]
  have hepi : epigraph f'_infinity = horizonCone (epigraph f) := by
    ext ⟨d, r⟩
    show f'_infinity d ≤ r ↔ _
    rw [hf'eq x₀ hx₀ d, hchar x₀ hx₀ d r]
  have hbot' : ∀ d, ⊥ < f'_infinity d := by
    intro d
    rw [hf'eq x₀ hx₀ d]
    have h1 : differenceQuotient f x₀ d 1 ≤
        sSup {q : EReal | ∃ (t : ℝ), 0 < t ∧ q = differenceQuotient f x₀ d t} :=
      le_sSup ⟨1, one_pos, rfl⟩
    refine lt_of_lt_of_le ?_ h1
    unfold differenceQuotient
    rw [hfx x₀ hx₀]
    have h2 := hbot (x₀ + (1:ℝ) • d)
    revert h2
    induction f (x₀ + (1:ℝ) • d) with
    | bot => intro h2; exact absurd h2 (lt_irrefl _)
    | top =>
      intro _
      rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast one_pos)
        (EReal.coe_ne_top 1)]
      exact bot_lt_top
    | coe y =>
      intro _
      rw [← EReal.coe_sub, ← EReal.coe_div]
      exact EReal.bot_lt_coe _
  -- monotonicity of the difference quotients
  have hmono : ∀ x ∈ effDom f, ∀ d : E, ∀ s t : ℝ, 0 < s → s ≤ t →
      differenceQuotient f x d s ≤ differenceQuotient f x d t := by
    intro x hx d s t hs hst
    have ht : 0 < t := lt_of_lt_of_le hs hst
    rw [← EReal.le_of_forall_lt_iff_le]
    intro r hr
    unfold differenceQuotient at hr ⊢
    rw [hfx x hx] at hr ⊢
    rw [EReal_dq_le_iff_aux hs]
    have h1 : f (x + t • d) ≤ (((f x).toReal + t * r : ℝ) : EReal) :=
      (EReal_dq_le_iff_aux ht).mp hr.le
    have hmem := hconv' (hxepi x hx) (show (x + t • d, (f x).toReal + t * r) ∈ epigraph f from h1)
      (show (0:ℝ) ≤ 1 - s / t by rw [sub_nonneg, div_le_one ht]; exact hst)
      (show (0:ℝ) ≤ s / t by positivity) (by ring)
    have heq : (1 - s / t) • (x, (f x).toReal) + (s / t) • (x + t • d, (f x).toReal + t * r)
        = (x + s • d, (f x).toReal + s * r) := by
      ext
      · simp only [Prod.fst_add, Prod.smul_fst]
        rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', ← add_assoc, ← add_smul,
          sub_add_cancel, one_smul]
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        field_simp
        ring
    rw [heq] at hmem
    exact hmem
  refine ⟨?_, ⟨⟨hbot', ?_, ?_⟩, ?_⟩, hbot', ?_⟩
  · intro x₁ hx₁
    rw [hepi, hK x₁ hx₁]
  · refine ⟨0, ?_⟩
    have h0 : ((0 : E), (0 : ℝ)) ∈ epigraph f'_infinity := by
      rw [hepi, hK _ (hxepi x₀ hx₀)]
      intro t ht
      simpa using hxepi x₀ hx₀
    exact lt_of_le_of_lt h0 (EReal.coe_lt_top 0)
  · show Convex ℝ (epigraph f'_infinity)
    rw [hepi, hK _ (hxepi x₀ hx₀)]
    exact convex_asymptoticConeAt_aux hconv' _
  · apply lsc_of_isClosed_epigraph_aux
    rw [hepi, hK _ (hxepi x₀ hx₀)]
    exact isClosed_asymptoticConeAt_aux hclosed _
  · intro x hx d
    refine ⟨hf'eq x hx d, ?_⟩
    rw [hf'eq x hx d, tendsto_order]
    constructor
    · intro b hb
      obtain ⟨_, ⟨t₀, ht₀, rfl⟩, hlt⟩ := lt_sSup_iff.mp hb
      filter_upwards [Filter.eventually_ge_atTop t₀] with t ht
      exact lt_of_lt_of_le hlt (hmono x hx d t₀ t ht₀ ht)
    · intro b hb
      filter_upwards [Filter.eventually_gt_atTop 0] with t ht
      refine lt_of_le_of_lt ?_ hb
      exact le_sSup ⟨t, ht, rfl⟩

end FCA_chap_B_3_2_1
