import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_8_iii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_8_iii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_8_iii`, so the main result is `FCA_chap_B_3_2_8_iii.FCA_chap_B_3_2_8_iii`.
-/

namespace FCA_chap_B_3_2_8_iii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

set_option linter.unusedVariables false in
theorem FCA_chap_B_3_2_8_iii
  (f : F → EReal)
  (A₀ : E →ₗ[ℝ] F)
  (b : F)
  (hf_closed_conv : InClosedConvRn f)
  (h_dom_nonempty : Set.Nonempty
    (effDom f ∩ Set.image (fun x ↦ A₀ x + b) Set.univ))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let fA := fun v ↦ f (A₀ v + b)
  let fA'_infinity := asymptoticFun fA
  ∀ d,
    asymptoticFun f (A₀ d) = fA'_infinity d := by
  intro fA fA'_infinity d
  have hconv : Convex ℝ (epigraph f) := hf_closed_conv.1.2.2
  have hclosed : IsClosed (epigraph f) := by
    have h1 : IsClosed {p : F × EReal | f p.1 ≤ p.2} :=
      hf_closed_conv.2.isClosed_epigraph
    have h2 : Continuous (fun p : F × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h1.preimage h2
  -- recession property of the horizon cone of a closed convex set
  have hrec : ∀ p ∈ epigraph f, ∀ q ∈ horizonCone (epigraph f), ∀ t : ℝ, 0 ≤ t →
      p + t • q ∈ epigraph f := by
    rintro p hp q ⟨xseq, l, hx, hl, hlim⟩ t ht
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) :=
      tendsto_nhdsWithin_iff.mp hl |>.1
    have hlpos : ∀ᶠ i in Filter.atTop, 0 < l i :=
      tendsto_nhdsWithin_iff.mp hl |>.2
    have hsmall : ∀ᶠ i in Filter.atTop, t * l i ≤ 1 := by
      have : Filter.Tendsto (fun i => t * l i) Filter.atTop (𝓝 (t * 0)) :=
        hl0.const_mul t
      rw [mul_zero] at this
      exact this.eventually (eventually_le_nhds zero_lt_one)
    have hmem : ∀ᶠ i in Filter.atTop,
        (1 - t * l i) • p + (t * l i) • xseq i ∈ epigraph f := by
      filter_upwards [hlpos, hsmall] with i hi1 hi2
      exact hconv hp (hx i) (by linarith) (by positivity) (by ring)
    have hlim2 : Filter.Tendsto (fun i => (1 - t * l i) • p + (t * l i) • xseq i)
        Filter.atTop (𝓝 (p + t • q)) := by
      have e : ∀ i, (1 - t * l i) • p + (t * l i) • xseq i
          = p - (t * l i) • p + t • (l i • xseq i) := by
        intro i
        simp only [sub_smul, one_smul, mul_smul]
      simp_rw [e]
      have h3 : Filter.Tendsto (fun i => (t * l i) • p) Filter.atTop (𝓝 ((t * 0) • p)) :=
        (hl0.const_mul t).smul_const p
      rw [mul_zero, zero_smul] at h3
      have h4 := (tendsto_const_nhds (x := p)).sub h3
      rw [sub_zero] at h4
      exact h4.add (hlim.const_smul t)
    exact hclosed.mem_of_tendsto hlim2 hmem
  obtain ⟨y, hy_dom, x₀, -, rfl⟩ := h_dom_nonempty
  obtain ⟨r₀, hr₀, -⟩ := EReal.lt_iff_exists_real_btwn.mp hy_dom
  have hA : Continuous A₀ := A₀.continuous_of_finiteDimensional
  show funFromSet _ _ = funFromSet _ _
  unfold funFromSet
  congr 2
  ext r
  simp only [verticalSlice, Set.mem_setOf_eq]
  constructor
  · intro h
    refine ⟨fun i : ℕ => (x₀ + ((i:ℝ) + 1) • d, r₀ + ((i:ℝ) + 1) * r),
      fun i : ℕ => 1 / ((i:ℝ) + 1), ?_, ?_, ?_⟩
    · intro i
      have hp : (A₀ x₀ + b, r₀) ∈ epigraph f := by
        show f (A₀ x₀ + b) ≤ (r₀ : EReal)
        exact hr₀.le
      have := hrec _ hp _ h ((i:ℝ) + 1) (by positivity)
      show f (A₀ (x₀ + ((i:ℝ) + 1) • d) + b) ≤ ((r₀ + ((i:ℝ) + 1) * r : ℝ) : EReal)
      have e : A₀ (x₀ + ((i:ℝ) + 1) • d) + b = A₀ x₀ + b + ((i:ℝ) + 1) • A₀ d := by
        rw [map_add, map_smul]; abel
      rw [e]
      exact this
    · refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall fun i => by
        show (0:ℝ) < 1 / ((i:ℝ) + 1)
        positivity
    · have e : ∀ i : ℕ, (1 / ((i:ℝ) + 1)) • (x₀ + ((i:ℝ) + 1) • d, r₀ + ((i:ℝ) + 1) * r)
          = ((1 / ((i:ℝ) + 1)) • (x₀, r₀)) + (d, r) := by
        intro i
        have hi : ((i:ℝ) + 1) ≠ 0 := by positivity
        ext
        · simp only [Prod.smul_fst, Prod.fst_add, smul_add, smul_smul]
          rw [one_div_mul_cancel hi, one_smul]
        · simp only [Prod.smul_snd, Prod.snd_add, smul_eq_mul]
          field_simp
      simp_rw [e]
      have h0 : Filter.Tendsto (fun i : ℕ => (1 / ((i:ℝ) + 1)) • (x₀, r₀)) Filter.atTop
          (𝓝 ((0:ℝ) • (x₀, r₀))) :=
        tendsto_one_div_add_atTop_nhds_zero_nat.smul_const _
      rw [zero_smul] at h0
      simpa using h0.add_const (d, r)
  · rintro ⟨xseq, l, hx, hl, hlim⟩
    refine ⟨fun i => (A₀ (xseq i).1 + b, (xseq i).2), l, fun i => hx i, hl, ?_⟩
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) :=
      tendsto_nhdsWithin_iff.mp hl |>.1
    have e : ∀ i, l i • (A₀ (xseq i).1 + b, (xseq i).2)
        = (A₀ ((l i • xseq i).1), (l i • xseq i).2) + l i • ((b, 0) : F × ℝ) := by
      intro i
      ext
      · simp [smul_add, map_smul]
      · simp
    simp_rw [e]
    have h1 : Filter.Tendsto (fun i => (A₀ ((l i • xseq i).1), (l i • xseq i).2))
        Filter.atTop (𝓝 (A₀ d, r)) := by
      have hc : Continuous (fun p : E × ℝ => (A₀ p.1, p.2)) :=
        (hA.comp continuous_fst).prodMk continuous_snd
      exact (hc.tendsto (d, r)).comp hlim
    have h2 : Filter.Tendsto (fun i => l i • ((b, 0) : F × ℝ)) Filter.atTop
        (𝓝 ((0:ℝ) • ((b, 0) : F × ℝ))) :=
      hl0.smul_const _
    rw [zero_smul] at h2
    simpa using h1.add h2

end FCA_chap_B_3_2_8_iii
