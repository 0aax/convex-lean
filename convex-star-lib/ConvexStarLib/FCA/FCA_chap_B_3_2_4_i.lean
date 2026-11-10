import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_4_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_4_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_4_i`, so the main result is `FCA_chap_B_3_2_4_i.FCA_chap_B_3_2_4_i`.
-/

namespace FCA_chap_B_3_2_4_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_3_2_4_i
  (f : E → EReal)
  (hf_closed_conv : InClosedConvRn f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let f'_infinity := asymptoticFun f
  ∀ (r : ℝ),
  let Sr := sublevelSet r f
  (Set.Nonempty Sr) → (∀ x₁ ∈ Sr,
  asymptoticConeAt Sr x₁ = {d | f'_infinity d ≤ 0}) := by
  intro f'_infinity r Sr _ x₁ hx₁
  obtain ⟨⟨_, _, hconv⟩, hlsc⟩ := hf_closed_conv
  have hx₁' : f x₁ ≤ (r : EReal) := hx₁
  -- the epigraph (in `E × ℝ`) is closed
  have hclosed : IsClosed (epigraph f) := by
    have h1 : IsClosed {p : E × EReal | f p.1 ≤ p.2} := hlsc.isClosed_epigraph
    have h2 : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h1.preimage h2
  -- key estimate
  have key : ∀ d : E, ∀ s : ℝ, (d, s) ∈ horizonCone (epigraph f) →
      ∀ t : ℝ, 0 < t → f (x₁ + t • d) ≤ ((r + t * s : ℝ) : EReal) := by
    intro d s hds t ht
    obtain ⟨xseq, l, hmem, hl, hlim⟩ := hds
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hl
    have hlpos : ∀ᶠ i in Filter.atTop, 0 < l i := hl.eventually self_mem_nhdsWithin
    have hlsmall : ∀ᶠ i in Filter.atTop, l i < 1 / t :=
      hl0.eventually (gt_mem_nhds (by positivity))
    have hbase : ((x₁, r) : E × ℝ) ∈ epigraph f := hx₁'
    have hev : ∀ᶠ i in Filter.atTop,
        (1 - t * l i) • ((x₁, r) : E × ℝ) + (t * l i) • xseq i ∈ epigraph f := by
      filter_upwards [hlpos, hlsmall] with i hi1 hi2
      apply hconv hbase (hmem i)
      · have : t * l i < 1 := by
          rw [lt_div_iff₀ ht] at hi2
          linarith
        linarith
      · positivity
      · ring
    have htend : Filter.Tendsto
        (fun i => (1 - t * l i) • ((x₁, r) : E × ℝ) + (t * l i) • xseq i)
        Filter.atTop (𝓝 (((x₁, r) : E × ℝ) + t • (d, s))) := by
      have h1 : Filter.Tendsto (fun i => (1 - t * l i) • ((x₁, r) : E × ℝ))
          Filter.atTop (𝓝 ((x₁, r) : E × ℝ)) := by
        have : Filter.Tendsto (fun i => (1 - t * l i)) Filter.atTop (𝓝 1) := by
          have := (tendsto_const_nhds (x := (1:ℝ))).sub (hl0.const_mul t)
          simpa using this
        simpa using this.smul_const ((x₁, r) : E × ℝ)
      have h2 : Filter.Tendsto (fun i => (t * l i) • xseq i)
          Filter.atTop (𝓝 (t • ((d, s) : E × ℝ))) := by
        have := hlim.const_smul t
        refine this.congr (fun i => ?_)
        simp [mul_smul]
      exact h1.add h2
    have hlimmem := hclosed.mem_of_tendsto htend hev
    simpa [epigraph, smul_eq_mul] using hlimmem
  ext d
  simp only [asymptoticConeAt, Set.mem_setOf_eq]
  constructor
  · intro hd
    have hH : (d, (0:ℝ)) ∈ horizonCone (epigraph f) := by
      refine ⟨fun i : ℕ => ((x₁ + ((i:ℝ)+1) • d, r) : E × ℝ), fun i : ℕ => 1 / ((i:ℝ)+1), ?_, ?_, ?_⟩
      · intro i
        exact hd _ (by positivity)
      · apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
        · exact tendsto_one_div_add_atTop_nhds_zero_nat
        · exact Filter.Eventually.of_forall (fun i => by simp; positivity)
      · have hinv : Filter.Tendsto (fun i : ℕ => 1 / ((i:ℝ)+1)) Filter.atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have heq : ∀ i : ℕ, (1 / ((i:ℝ)+1)) • ((x₁ + ((i:ℝ)+1) • d, r) : E × ℝ)
            = (1 / ((i:ℝ)+1)) • ((x₁, r) : E × ℝ) + (d, 0) := by
          intro i
          have hi : ((i:ℝ)+1) ≠ 0 := by positivity
          ext
          · simp [smul_add, smul_smul, hi]
          · simp
        simp_rw [heq]
        have := (hinv.smul_const ((x₁, r) : E × ℝ)).add_const ((d, 0) : E × ℝ)
        simpa using this
    show sInf _ ≤ 0
    have : ((0:ℝ) : EReal) ∈ (fun r : ℝ => (r : EReal)) '' verticalSlice (horizonCone (epigraph f)) d :=
      ⟨0, hH, rfl⟩
    simpa using sInf_le this
  · intro hd t ht
    show f (x₁ + t • d) ≤ (r : EReal)
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : r < z := EReal.coe_lt_coe_iff.mp hz
    set ε := (z - r) / t with hε
    have hεpos : (0 : EReal) < (ε : EReal) := by
      have : 0 < ε := div_pos (by linarith) ht
      exact_mod_cast this
    have hlt : sInf ((fun r : ℝ => (r : EReal)) '' verticalSlice (horizonCone (epigraph f)) d) < (ε : EReal) :=
      lt_of_le_of_lt hd hεpos
    rw [sInf_lt_iff] at hlt
    obtain ⟨_, ⟨s, hs, rfl⟩, hsε⟩ := hlt
    have hsε' : s < ε := EReal.coe_lt_coe_iff.mp hsε
    have := key d s hs t ht
    refine this.trans ?_
    have : r + t * s ≤ z := by
      have h1 : t * s ≤ t * ε := by nlinarith
      have h2 : t * ε = z - r := by rw [hε]; field_simp
      linarith
    exact_mod_cast this

end FCA_chap_B_3_2_4_i
