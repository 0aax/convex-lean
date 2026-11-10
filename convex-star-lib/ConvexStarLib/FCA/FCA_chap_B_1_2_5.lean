import ConvexStarLib.Defs

/-!
# `FCA_chap_B_1_2_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_1_2_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_1_2_5`, so the main result is `FCA_chap_B_1_2_5.FCA_chap_B_1_2_5`.
-/

namespace FCA_chap_B_1_2_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma FCA_chap_B_1_2_5_aux_epi (f : E → EReal) (hf : ConvexEReal f) {y w : E} {s M : ℝ} (hy : f y ≤ s)
    (hw : f w ≤ M) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    f (a • y + b • w) ≤ ((a * s + b * M : ℝ) : EReal) := by
  have h := hf (show (y, s) ∈ epigraph f from hy) (show (w, M) ∈ epigraph f from hw) ha hb hab
  simpa [epigraph] using h

lemma FCA_chap_B_1_2_5_aux_bdd (f : E → EReal) (hf : ConvexEReal f) (f_ne_bot : ∀ x, ⊥ < f x) (x₀ : E)
    (hx : x₀ ∈ intrinsicInterior ℝ (effDom f)) :
    ∃ δ > 0, ∃ M : ℝ, ∀ z ∈ affineSpan ℝ (effDom f), dist z x₀ < δ → f z ≤ M := by
  obtain ⟨p, hp, rfl⟩ := hx
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hp)
  let g : (affineSpan ℝ (effDom f)).direction → ℝ := fun v => (f ((v : E) + (p : E))).toReal
  let C : Set (affineSpan ℝ (effDom f)).direction := {v | f ((v : E) + p) < ⊤}
  have hfin : ∀ z, f z < ⊤ → f z = ((f z).toReal : EReal) := fun z hz =>
    (EReal.coe_toReal hz.ne (f_ne_bot z).ne').symm
  have hC : C ∈ 𝓝 (0 : (affineSpan ℝ (effDom f)).direction) := by
    rw [Metric.mem_nhds_iff]
    refine ⟨ε, hε, fun v hv => ?_⟩
    have hmem : (v : E) + (p : E) ∈ affineSpan ℝ (effDom f) :=
      AffineSubspace.vadd_mem_of_mem_direction v.2 p.2
    have : (⟨(v : E) + p, hmem⟩ : affineSpan ℝ (effDom f)) ∈ Metric.ball p ε := by
      rw [Metric.mem_ball, Subtype.dist_eq]
      simpa [dist_eq_norm] using hv
    exact hball this
  have hgC : ConvexOn ℝ C g := by
    have key : ∀ v ∈ C, ∀ w ∈ C, ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
        f ((↑(a • v + b • w) : E) + p) ≤ ((a * g v + b * g w : ℝ) : EReal) := by
      intro v hv w hw a b ha hb hab
      have e : ((↑(a • v + b • w) : E) + p) = a • ((v : E) + p) + b • ((w : E) + p) := by
        simp only [Submodule.coe_add, Submodule.coe_smul, smul_add]
        rw [add_add_add_comm, ← add_smul, hab, one_smul]
      rw [e]
      exact FCA_chap_B_1_2_5_aux_epi f hf (hfin _ hv).le (hfin _ hw).le ha hb hab
    refine ⟨?_, ?_⟩
    · intro v hv w hw a b ha hb hab
      exact lt_of_le_of_lt (key v hv w hw a b ha hb hab) (EReal.coe_lt_top _)
    · intro v hv w hw a b ha hb hab
      have h1 := key v hv w hw a b ha hb hab
      have h2 : f ((↑(a • v + b • w) : E) + p) < ⊤ := lt_of_le_of_lt h1 (EReal.coe_lt_top _)
      rw [hfin _ h2] at h1
      simpa [g, smul_eq_mul] using EReal.coe_le_coe_iff.1 h1
  have hcont : ContinuousAt g 0 :=
    hgC.continuousOn_interior.continuousAt (interior_mem_nhds.2 hC)
  have hev : ∀ᶠ v in 𝓝 (0 : (affineSpan ℝ (effDom f)).direction), v ∈ C ∧ g v < g 0 + 1 :=
    Filter.Eventually.and hC (hcont.eventually (gt_mem_nhds (lt_add_one (g 0))))
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.1 hev
  refine ⟨δ, hδ, g 0 + 1, fun z hz hzd => ?_⟩
  let v : (affineSpan ℝ (effDom f)).direction :=
    ⟨z - p, by simpa using AffineSubspace.vsub_mem_direction hz p.2⟩
  have hv : dist v 0 < δ := by
    rw [_root_.dist_zero_right]
    simpa [dist_eq_norm, v] using hzd
  obtain ⟨hvC, hvg⟩ := hδ' hv
  have hzv : (v : E) + p = z := by simp [v]
  simp only [C, g, Set.mem_setOf_eq, hzv] at hvC hvg
  rw [hfin z hvC]
  exact EReal.coe_le_coe_iff.2 hvg.le

theorem FCA_chap_B_1_2_5
  (f : E → EReal)
  (x₀ : E)
  (hf_convex : InConvRn f)
  (hx : x₀ ∈ intrinsicInterior ℝ (effDom f))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ x, Filter.Tendsto (fun (t : ℝ) => f (x + t • (x₀ - x))) (𝓝[>] 0) (𝓝 (lscHull f x)) := by
  intro x
  have hconv : ConvexEReal f := hf_convex.2.2
  obtain ⟨δ, hδ, M, hM⟩ := FCA_chap_B_1_2_5_aux_bdd f hconv f_ne_bot x₀ hx
  have hx₀A : x₀ ∈ affineSpan ℝ (effDom f) := by
    obtain ⟨p, -, rfl⟩ := hx
    exact p.2
  have hcont : Filter.Tendsto (fun t : ℝ => x + t • (x₀ - x)) (𝓝[>] 0) (𝓝 x) := by
    have : Filter.Tendsto (fun t : ℝ => x + t • (x₀ - x)) (𝓝 0) (𝓝 (x + (0:ℝ) • (x₀ - x))) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    simp only [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  unfold lscHull
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · exact hcont.eventually (Filter.eventually_lt_of_lt_liminf ha)
  · obtain ⟨r, hLr, hra⟩ := EReal.lt_iff_exists_real_btwn.1 ha
    obtain ⟨s, hLs, hsr⟩ := EReal.lt_iff_exists_real_btwn.1 hLr
    have hsr' : s < r := EReal.coe_lt_coe_iff.1 hsr
    have hfreq : ∃ᶠ y in 𝓝 x, f y < s := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hLs
    have hxA : x ∈ affineSpan ℝ (effDom f) := by
      have hcl : x ∈ closure (effDom f) := by
        rw [mem_closure_iff_frequently]
        exact hfreq.mono fun y hy => lt_trans hy (EReal.coe_lt_top s)
      exact closure_minimal (subset_affineSpan ℝ _)
        (affineSpan ℝ (effDom f)).closed_of_finiteDimensional hcl
    have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) * s + t * M) (𝓝 0) (𝓝 s) := by
      have : Filter.Tendsto (fun t : ℝ => (1 - t) * s + t * M) (𝓝 0)
          (𝓝 ((1 - 0) * s + 0 * M)) :=
        (by fun_prop : Continuous (fun t : ℝ => (1 - t) * s + t * M)).tendsto 0
      simpa using this
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ t < 1 ∧ (1 - t) * s + t * M < r := by
      have h1 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
      have h2 : ∀ᶠ t in 𝓝[>] (0:ℝ), t < 1 := nhdsWithin_le_nhds (gt_mem_nhds zero_lt_one)
      have h3 : ∀ᶠ t in 𝓝[>] (0:ℝ), (1 - t) * s + t * M < r :=
        nhdsWithin_le_nhds (hlim.eventually (gt_mem_nhds hsr'))
      exact h1.and (h2.and h3)
    filter_upwards [hev] with t ⟨ht0, ht1, htr⟩
    obtain ⟨y, hys, hyd⟩ :=
      (hfreq.and_eventually (Metric.ball_mem_nhds x (mul_pos ht0 hδ))).exists
    have hyA : y ∈ affineSpan ℝ (effDom f) :=
      subset_affineSpan ℝ _ (lt_trans hys (EReal.coe_lt_top s))
    set w : E := x₀ + ((1 - t) / t) • (x - y) with hw
    have hwA : w ∈ affineSpan ℝ (effDom f) := by
      have hdir : x - y ∈ (affineSpan ℝ (effDom f)).direction := by
        simpa using AffineSubspace.vsub_mem_direction hxA hyA
      have := AffineSubspace.vadd_mem_of_mem_direction
        (Submodule.smul_mem _ ((1 - t) / t) hdir) hx₀A
      simpa [hw, add_comm] using this
    have hwd : dist w x₀ < δ := by
      rw [hw, dist_eq_norm, add_sub_cancel_left, norm_smul]
      rw [dist_eq_norm] at hyd
      have h1t : 0 < (1 - t) / t := div_pos (by linarith) ht0
      rw [Real.norm_of_nonneg h1t.le, norm_sub_rev]
      calc (1 - t) / t * ‖y - x‖ < (1 - t) / t * (t * δ) := by gcongr
        _ = (1 - t) * δ := by field_simp
        _ ≤ δ := by nlinarith
    have hfw : f w ≤ M := hM w hwA hwd
    have hz : (1 - t) • y + t • w = x + t • (x₀ - x) := by
      have htt : t * ((1 - t) / t) = 1 - t := by field_simp
      rw [hw, smul_add, smul_smul, htt]
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have key := FCA_chap_B_1_2_5_aux_epi f hconv hys.le hfw (by linarith : (0:ℝ) ≤ 1 - t) ht0.le (by ring)
    rw [hz] at key
    calc f (x + t • (x₀ - x)) ≤ (((1 - t) * s + t * M : ℝ) : EReal) := key
      _ < r := EReal.coe_lt_coe_iff.2 htr
      _ < a := hra

end FCA_chap_B_1_2_5
