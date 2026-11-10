import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_8_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_8_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_8_ii`, so the main result is `FCA_chap_B_3_2_8_ii.FCA_chap_B_3_2_8_ii`.
-/

namespace FCA_chap_B_3_2_8_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_B_3_2_8_ii
  {ι : Type*}
  (fj : ι → (E → EReal))
  (J : Set ι)
  (hJ : J.Nonempty)
  (x₀ : E)
  (hf_closed_conv : ∀ j ∈ J, InClosedConvRn (fj j))
  (hf_finite : sSup {fj j x₀ | j ∈ J} < ⊤)
  (fj_ne_bot : ∀ x₁ x₂, ⊥ < fj x₁ x₂) :
  let f := fun x => sSup {fj j x | j ∈ J}
  let f'_sup_infinity := fun d => sSup {asymptoticFun (fj j) d | j ∈ J}
  ∀ d,
  asymptoticFun f d = f'_sup_infinity d := by
  intro f f'_sup_infinity d
  -- monotonicity of the horizon cone
  have hmono : ∀ {C D : Set (E × ℝ)}, C ⊆ D → horizonCone C ⊆ horizonCone D := by
    intro C D hCD v ⟨xseq, l, hx, hl, hlim⟩
    exact ⟨xseq, l, fun i => hCD (hx i), hl, hlim⟩
  -- horizon directions of a closed convex set are recession directions
  have hrec : ∀ {C : Set (E × ℝ)}, IsClosed C → Convex ℝ C → ∀ {v p : E × ℝ},
      v ∈ horizonCone C → p ∈ C → ∀ {t : ℝ}, 0 ≤ t → p + t • v ∈ C := by
    intro C hC hconv v p ⟨xseq, l, hx, hl, hlim⟩ hp t ht
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    have hlpos : ∀ᶠ i in Filter.atTop, 0 < l i := (tendsto_nhdsWithin_iff.mp hl).2
    have htl : Filter.Tendsto (fun i => t * l i) Filter.atTop (𝓝 0) := by
      simpa using hl0.const_mul t
    have htl1 : ∀ᶠ i in Filter.atTop, t * l i < 1 := htl.eventually (gt_mem_nhds one_pos)
    have hlim' : Filter.Tendsto (fun i => (1 - t * l i) • p + t • (l i • xseq i)) Filter.atTop
        (𝓝 (p + t • v)) := by
      have h1 : Filter.Tendsto (fun i => (1 - t * l i) • p) Filter.atTop (𝓝 p) := by
        have : Filter.Tendsto (fun i => 1 - t * l i) Filter.atTop (𝓝 1) := by
          simpa using (tendsto_const_nhds (x := (1:ℝ))).sub htl
        simpa using this.smul_const p
      exact h1.add (hlim.const_smul t)
    apply hC.mem_of_tendsto hlim'
    filter_upwards [hlpos, htl1] with i hi1 hi2
    rw [smul_smul]
    exact hconv hp (hx i) (by linarith) (mul_nonneg ht hi1.le) (by ring)
  -- a ray contained in a set gives a horizon direction
  have hray : ∀ {C : Set (E × ℝ)} {p v : E × ℝ}, (∀ n : ℕ, p + ((n:ℝ) + 1) • v ∈ C) →
      v ∈ horizonCone C := by
    intro C p v h
    refine ⟨fun n => p + ((n:ℝ) + 1) • v, fun n => 1 / ((n:ℝ) + 1), h, ?_, ?_⟩
    · apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => Set.mem_Ioi.mpr (by positivity))
    · have heq : (fun n : ℕ => (1 / ((n:ℝ) + 1)) • (p + ((n:ℝ) + 1) • v))
          = fun n : ℕ => (1 / ((n:ℝ) + 1)) • p + v := by
        funext n
        rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ (by positivity), one_smul]
      rw [heq]
      have : Filter.Tendsto (fun n : ℕ => (1 / ((n:ℝ) + 1)) • p) Filter.atTop (𝓝 0) := by
        have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).smul_const p
        rwa [zero_smul] at h
      simpa using this.add_const v
  -- the epigraphs are closed and convex
  have hclosed : ∀ j ∈ J, IsClosed (epigraph (fj j)) := by
    intro j hj
    have h1 := (hf_closed_conv j hj).2.isClosed_epigraph
    have hcont : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h1.preimage hcont
  have hconvex : ∀ j ∈ J, Convex ℝ (epigraph (fj j)) := fun j hj => (hf_closed_conv j hj).1.2.2
  -- a common point of all the epigraphs
  obtain ⟨ρ₀, hρ₀, -⟩ := EReal.lt_iff_exists_real_btwn.mp hf_finite
  have hp₀ : ∀ j ∈ J, ((x₀, ρ₀) : E × ℝ) ∈ epigraph (fj j) := by
    intro j hj
    show fj j x₀ ≤ (ρ₀ : EReal)
    have hle : fj j x₀ ≤ sSup {fj j x₀ | j ∈ J} := le_sSup ⟨j, hj, rfl⟩
    exact hle.trans hρ₀.le
  -- the epigraph of the supremum is the intersection of the epigraphs
  have hsub : ∀ j ∈ J, epigraph f ⊆ epigraph (fj j) := by
    intro j hj p hp
    show fj j p.1 ≤ (p.2 : EReal)
    have hle : fj j p.1 ≤ sSup {fj j p.1 | j ∈ J} := le_sSup ⟨j, hj, rfl⟩
    exact hle.trans hp
  have hinter : ∀ p : E × ℝ, (∀ j ∈ J, p ∈ epigraph (fj j)) → p ∈ epigraph f := by
    intro p hp
    change sSup {y | ∃ j ∈ J, fj j p.1 = y} ≤ (p.2 : EReal)
    apply sSup_le
    rintro _ ⟨j, hj, rfl⟩
    exact hp j hj
  show sInf _ = sSup _
  apply le_antisymm
  · apply EReal.le_of_forall_lt_iff_le.mp
    intro z hz
    apply sInf_le
    refine ⟨z, ?_, rfl⟩
    show ((d, z) : E × ℝ) ∈ horizonCone (epigraph f)
    apply hray (p := (x₀, ρ₀))
    intro n
    apply hinter
    intro j hj
    have hle : asymptoticFun (fj j) d ≤ sSup {asymptoticFun (fj j) d | j ∈ J} :=
      le_sSup ⟨j, hj, rfl⟩
    have hlt : asymptoticFun (fj j) d < z := lt_of_le_of_lt hle hz
    obtain ⟨_, ⟨r, hr, rfl⟩, hrz⟩ := sInf_lt_iff.mp hlt
    have hr' : ((d, r) : E × ℝ) ∈ horizonCone (epigraph (fj j)) := hr
    have h2 := hrec (hclosed j hj) (hconvex j hj) hr' (hp₀ j hj) (t := (n:ℝ) + 1) (by positivity)
    have h3 : fj j (x₀ + ((n:ℝ)+1) • d) ≤ ((ρ₀ + ((n:ℝ)+1) * r : ℝ) : EReal) := h2
    show fj j (x₀ + ((n:ℝ)+1) • d) ≤ ((ρ₀ + ((n:ℝ)+1) * z : ℝ) : EReal)
    refine h3.trans ?_
    have hrz' : r < z := EReal.coe_lt_coe_iff.mp hrz
    have hn : (0:ℝ) ≤ (n:ℝ) + 1 := by positivity
    exact_mod_cast (by nlinarith : ρ₀ + ((n:ℝ)+1) * r ≤ ρ₀ + ((n:ℝ)+1) * z)
  · apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    apply sSup_le
    rintro _ ⟨j, hj, rfl⟩
    apply sInf_le
    exact ⟨r, hmono (hsub j hj) hr, rfl⟩

end FCA_chap_B_3_2_8_ii
