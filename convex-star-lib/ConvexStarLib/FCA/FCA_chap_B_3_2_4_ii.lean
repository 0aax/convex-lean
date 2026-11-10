import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_4_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_4_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_4_ii`, so the main result is `FCA_chap_B_3_2_4_ii.FCA_chap_B_3_2_4_ii`.
-/

namespace FCA_chap_B_3_2_4_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_3_2_4_ii
  (f : E → EReal)
  (x₀ : E)
  (hf_closed_conv : InClosedConvRn f)
  (hx₀ : x₀ ∈ effDom f)
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let f'_infinity := asymptoticFun f
  List.TFAE [
    ∃ (r : ℝ), (Set.Nonempty (sublevelSet r f)) ∧ (IsCompact (sublevelSet r f)),
    ∀ (r : ℝ), (IsCompact (sublevelSet r f)),
    ∀ (d : E), d ≠ 0 → f'_infinity d > 0
  ] := by
  intro f'_infinity
  obtain ⟨⟨_, _, hconv⟩, hlsc⟩ := hf_closed_conv
  have hepi_closed : IsClosed (epigraph f) := by
    have h := hlsc.isClosed_epigraph
    exact h.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
  have hsub_closed : ∀ r : ℝ, IsClosed (sublevelSet r f) :=
    fun r => hlsc.isClosed_preimage (r : EReal)
  tfae_have 2 → 1 := by
    intro h
    have hfin : f x₀ ≠ ⊤ := ne_of_lt hx₀
    have hfin' : f x₀ ≠ ⊥ := ne_of_gt (f_ne_bot x₀)
    refine ⟨(f x₀).toReal, ⟨x₀, ?_⟩, h _⟩
    show f x₀ ≤ ((f x₀).toReal : EReal)
    rw [EReal.coe_toReal hfin hfin']
  tfae_have 3 → 2 := by
    intro h r
    by_contra hnc
    have hnb : ¬ Bornology.IsBounded (sublevelSet r f) := fun hb =>
      hnc (Metric.isCompact_of_isClosed_isBounded (hsub_closed r) hb)
    have hex : ∀ n : ℕ, ∃ x ∈ sublevelSet r f, (n : ℝ) < ‖x‖ := by
      intro n
      by_contra hcon
      push_neg at hcon
      apply hnb
      rw [Metric.isBounded_iff_subset_closedBall 0]
      exact ⟨n, fun x hx => by simpa using hcon x hx⟩
    choose x hxS hxn using hex
    have hxpos : ∀ n, 0 < ‖x n‖ := fun n => lt_of_le_of_lt (Nat.cast_nonneg n) (hxn n)
    set u : ℕ → E := fun n => ‖x n‖⁻¹ • x n with hu
    have hu_mem : ∀ n, u n ∈ Metric.sphere (0 : E) 1 := by
      intro n
      simp [u, norm_smul, (hxpos n).ne']
    obtain ⟨d, hd, ns, hns, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu_mem
    have hd0 : d ≠ 0 := by
      intro h0
      simp [h0] at hd
    have hinv : Filter.Tendsto (fun i => ‖x (ns i)‖⁻¹) Filter.atTop (𝓝 0) := by
      have h1 : Filter.Tendsto (fun i => ‖x (ns i)‖) Filter.atTop Filter.atTop := by
        refine Filter.tendsto_atTop_mono (fun i => (hxn (ns i)).le) ?_
        exact tendsto_natCast_atTop_atTop.comp hns.tendsto_atTop
      exact h1.inv_tendsto_atTop
    have key : ((d, (0:ℝ)) : E × ℝ) ∈ horizonCone (epigraph f) := by
      refine ⟨fun i => (x (ns i), r), fun i => ‖x (ns i)‖⁻¹, ?_, ?_, ?_⟩
      · intro i; exact hxS (ns i)
      · rw [tendsto_nhdsWithin_iff]
        exact ⟨hinv, Filter.Eventually.of_forall fun i => inv_pos.mpr (hxpos (ns i))⟩
      · have h2 : Filter.Tendsto (fun i => ‖x (ns i)‖⁻¹ * r) Filter.atTop (𝓝 0) := by
          simpa using hinv.mul_const r
        exact (hlim.prodMk_nhds h2)
    have hle : f'_infinity d ≤ 0 := by
      show sInf _ ≤ _
      apply sInf_le
      exact ⟨0, key, rfl⟩
    exact absurd (h d hd0) (not_lt.mpr hle)
  tfae_have 1 → 3 := by
    rintro ⟨r, ⟨y, hy⟩, hcomp⟩ d hd
    by_contra hle
    push_neg at hle
    have hray : ∀ t : ℝ, 0 ≤ t → y + t • d ∈ sublevelSet r f := by
      intro t ht
      have hε : ∀ ε : ℝ, 0 < ε → f (y + t • d) ≤ ((r + t * ε : ℝ) : EReal) := by
        intro ε hε
        have : f'_infinity d < (ε : EReal) := lt_of_le_of_lt hle (by exact_mod_cast hε)
        obtain ⟨_, ⟨s, hsH, rfl⟩, hsε⟩ := sInf_lt_iff.mp this
        have hsε' : s < ε := EReal.coe_lt_coe_iff.mp hsε
        obtain ⟨p, l, hp, hl, hlp⟩ := hsH
        have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := (tendsto_nhdsWithin_iff.mp hl).1
        have hlpos : ∀ᶠ i in Filter.atTop, l i ∈ Set.Ioi (0:ℝ) := (tendsto_nhdsWithin_iff.mp hl).2
        set z : E × ℝ := (y, r) with hz_def
        have hz : z ∈ epigraph f := hy
        have hq : Filter.Tendsto (fun i => (1 - t * l i) • z + (t * l i) • p i) Filter.atTop
            (𝓝 (z + t • (d, s))) := by
          have heq : (fun i => (1 - t * l i) • z + (t * l i) • p i)
              = fun i => z - (t * l i) • z + t • (l i • p i) := by
            funext i
            rw [sub_smul, one_smul, mul_smul, mul_smul]
          rw [heq]
          have h1 : Filter.Tendsto (fun i => (t * l i) • z) Filter.atTop (𝓝 ((t * 0) • z)) :=
            (tendsto_const_nhds.mul hl0).smul_const z
          have h2 : Filter.Tendsto (fun i => t • (l i • p i)) Filter.atTop (𝓝 (t • (d, s))) :=
            hlp.const_smul t
          have h3 := (tendsto_const_nhds (x := z)).sub h1 |>.add h2
          simpa using h3
        have hev : ∀ᶠ i in Filter.atTop, (1 - t * l i) • z + (t * l i) • p i ∈ epigraph f := by
          have h1 : ∀ᶠ i in Filter.atTop, t * l i < 1 := by
            have : Filter.Tendsto (fun i => t * l i) Filter.atTop (𝓝 0) := by
              simpa using hl0.const_mul t
            exact this.eventually (gt_mem_nhds one_pos)
          filter_upwards [h1, hlpos] with i h1 h2
          exact hconv hz (hp i) (by linarith) (mul_nonneg ht (le_of_lt h2)) (by ring)
        have hmem := hepi_closed.mem_of_tendsto hq hev
        have hmem' : f (y + t • d) ≤ ((r + t * s : ℝ) : EReal) := hmem
        calc f (y + t • d) ≤ ((r + t * s : ℝ) : EReal) := hmem'
          _ ≤ ((r + t * ε : ℝ) : EReal) := by
            exact_mod_cast (by nlinarith : r + t * s ≤ r + t * ε)
      show f (y + t • d) ≤ (r : EReal)
      rw [← EReal.le_of_forall_lt_iff_le]
      intro z hz
      have hz' : r < z := by exact_mod_cast hz
      have hpos : 0 < (z - r) / (t + 1) := div_pos (by linarith) (by linarith)
      refine (hε _ hpos).trans ?_
      have : t * ((z - r) / (t + 1)) ≤ z - r := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by linarith)]
        nlinarith
      exact_mod_cast (by linarith : r + t * ((z - r) / (t + 1)) ≤ z)
    obtain ⟨C, hC⟩ := hcomp.isBounded.exists_norm_le
    have hyC : ‖y‖ ≤ C := hC y hy
    have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd
    set t : ℝ := (C + ‖y‖ + 1) / ‖d‖ with ht_def
    have ht : 0 ≤ t := div_nonneg (by linarith [norm_nonneg y]) hdpos.le
    have h1 := hC _ (hray t ht)
    have h2 : ‖t • d‖ = C + ‖y‖ + 1 := by
      rw [norm_smul, Real.norm_of_nonneg ht, ht_def, div_mul_cancel₀ _ hdpos.ne']
    have h3 : ‖t • d‖ ≤ ‖y + t • d‖ + ‖y‖ := by
      have := norm_sub_le (y + t • d) y
      simpa using this
    linarith
  tfae_finish

end FCA_chap_B_3_2_4_ii
