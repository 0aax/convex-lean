import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_2_2`, so the main result is `FCA_chap_B_2_2_2.FCA_chap_B_2_2_2`.
-/

namespace FCA_chap_B_2_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_2_2
  (f : E → EReal)
  (x' : E)
  (hf_convex : InClosedConvRn f)
  (hx : x' ∈ intrinsicInterior ℝ (effDom f))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  let pers : WithLp 2 (ℝ × E) → EReal := fun z => perspective f z.ofLp.1 z.ofLp.2
  let x : WithLp 2 (ℝ × E) := WithLp.toLp 2 (1, x')
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 < 0 → lscHull pers z = ⊤) ∧
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 > 0 →
    lscHull pers z = (z.ofLp.1 : EReal) * f ((z.ofLp.1)⁻¹ • z.ofLp.2)) ∧
  (∀ (z : WithLp 2 (ℝ × E)), z.ofLp.1 ≥ 0 →
    Filter.Tendsto (fun (α : ℝ) => pers (z + α • (x - z)))
      (𝓝[>] 0) (𝓝 (lscHull pers z))) := by
  intro pers x
  have conv_ineq : ∀ {a b : E} {ra rb : ℝ}, f a ≤ ra → f b ≤ rb → ∀ {s : ℝ}, 0 ≤ s → s ≤ 1 →
      f ((1 - s) • a + s • b) ≤ (((1 - s) * ra + s * rb : ℝ) : EReal) := by
    intro a b ra rb ha hb s hs0 hs1
    have h := hf_convex.1.2.2 (show (a, ra) ∈ epigraph f from ha)
      (show (b, rb) ∈ epigraph f from hb) (by linarith : (0:ℝ) ≤ 1 - s) hs0 (by ring)
    simpa [epigraph] using h
  have bot_lt_mul : ∀ {a : ℝ}, 0 < a → ∀ {b : EReal}, ⊥ < b → ⊥ < (a : EReal) * b := by
    intro a ha b hb
    induction b using EReal.rec with
    | bot => exact absurd hb (lt_irrefl _)
    | top => rw [EReal.coe_mul_top_of_pos ha]; exact bot_lt_top
    | coe r => rw [← EReal.coe_mul]; exact EReal.bot_lt_coe _
  have hlsc : LowerSemicontinuous f := hf_convex.2
  have hx'dom' : x' ∈ effDom f := intrinsicInterior_subset hx
  have hx'dom : f x' < ⊤ := hx'dom'
  obtain ⟨fx, hfx⟩ : ∃ r : ℝ, f x' = r :=
    ⟨(f x').toReal, (EReal.coe_toReal hx'dom.ne (f_ne_bot x').ne').symm⟩
  have pers_pos : ∀ w : WithLp 2 (ℝ × E), 0 < w.ofLp.1 →
      pers w = (w.ofLp.1 : EReal) * f ((w.ofLp.1)⁻¹ • w.ofLp.2) := by
    intro w hw
    simp only [pers, perspective, if_pos hw]
  have pers_nonpos : ∀ w : WithLp 2 (ℝ × E), w.ofLp.1 ≤ 0 → pers w = ⊤ := by
    intro w hw
    simp only [pers, perspective, if_neg (not_lt.mpr hw)]
  have hc1 : Continuous (fun w : WithLp 2 (ℝ × E) => w.ofLp.1) := WithLp.continuous_fst 2 ℝ E
  have hc2 : Continuous (fun w : WithLp 2 (ℝ × E) => w.ofLp.2) := WithLp.continuous_snd 2 ℝ E
  have hle_val : ∀ w, lscHull pers w ≤ pers w := by
    intro w
    apply Filter.liminf_le_of_frequently_le'
    have h : ∀ᶠ y in pure w, pers y ≤ pers w := Filter.eventually_pure.mpr le_rfl
    exact h.frequently.filter_mono (pure_le_nhds w)
  have hlsc_pos : ∀ z : WithLp 2 (ℝ × E), 0 < z.ofLp.1 → pers z ≤ lscHull pers z := by
    intro z hz
    apply lowerSemicontinuousAt_iff_le_liminf.mp
    intro y hy
    have hcont : ContinuousAt (fun w : WithLp 2 (ℝ × E) => (w.ofLp.1)⁻¹ • w.ofLp.2) z :=
      ((hc1.continuousAt).inv₀ hz.ne').smul hc2.continuousAt
    have hlscz : LowerSemicontinuousAt
        (fun w : WithLp 2 (ℝ × E) => f ((w.ofLp.1)⁻¹ • w.ofLp.2)) z :=
      (hlsc _).comp hcont
    have hpos_ev : ∀ᶠ w in 𝓝 z, 0 < w.ofLp.1 := (hc1.tendsto z).eventually_const_lt hz
    rw [pers_pos z hz] at hy
    induction y using EReal.rec with
    | bot =>
      filter_upwards [hpos_ev] with w hw
      rw [pers_pos w hw]
      exact bot_lt_mul hw (f_ne_bot _)
    | top => exact absurd hy (not_lt.mpr le_top)
    | coe r =>
      have hc' : (0 : EReal) < (z.ofLp.1 : EReal) := EReal.coe_pos.mpr hz
      have h1 : ((r / z.ofLp.1 : ℝ) : EReal) < f ((z.ofLp.1)⁻¹ • z.ofLp.2) := by
        rw [EReal.coe_div, EReal.div_lt_iff hc' (EReal.coe_ne_top _), mul_comm]
        exact hy
      obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp h1
      have hm1' : r < z.ofLp.1 * m := by
        have := EReal.coe_lt_coe_iff.mp hm1
        rw [div_lt_iff₀ hz] at this
        linarith [mul_comm z.ofLp.1 m]
      have hev1 : ∀ᶠ w in 𝓝 z, (m : EReal) < f ((w.ofLp.1)⁻¹ • w.ofLp.2) := hlscz m hm2
      have hev2 : ∀ᶠ w in 𝓝 z, r < w.ofLp.1 * m :=
        ((hc1.tendsto z).mul_const m).eventually_const_lt hm1'
      filter_upwards [hev1, hev2, hpos_ev] with w hw1 hw2 hw3
      rw [pers_pos w hw3]
      calc (r : EReal) < ((w.ofLp.1 * m : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr hw2
        _ = (w.ofLp.1 : EReal) * (m : EReal) := EReal.coe_mul _ _
        _ ≤ (w.ofLp.1 : EReal) * f ((w.ofLp.1)⁻¹ • w.ofLp.2) :=
          mul_le_mul_of_nonneg_left hw1.le (EReal.coe_nonneg.mpr hw3.le)
  have part2 : ∀ z : WithLp 2 (ℝ × E), 0 < z.ofLp.1 → lscHull pers z = pers z :=
    fun z hz => le_antisymm (hle_val z) (hlsc_pos z hz)
  refine ⟨?_, ?_, ?_⟩
  · -- part 1
    intro z hz
    apply le_antisymm le_top
    have : ∀ᶠ w in 𝓝 z, w.ofLp.1 < 0 := (hc1.tendsto z).eventually_lt_const hz
    have hev : ∀ᶠ w in 𝓝 z, ⊤ ≤ pers w := by
      filter_upwards [this] with w hw
      rw [pers_nonpos w hw.le]
    exact Filter.le_liminf_of_le (by isBoundedDefault) hev
  · intro z hz
    rw [part2 z hz, pers_pos z hz]
  · intro z hz
    have hpath : Filter.Tendsto (fun α : ℝ => z + α • (x - z)) (𝓝[>] 0) (𝓝 z) := by
      have hcont : Continuous (fun α : ℝ => z + α • (x - z)) :=
        continuous_const.add (continuous_id.smul continuous_const)
      have h1 := hcont.tendsto 0
      rw [zero_smul, add_zero] at h1
      exact tendsto_nhdsWithin_of_tendsto_nhds h1
    have hu : ∀ α : ℝ, (z + α • (x - z)).ofLp.1 = z.ofLp.1 + α * (1 - z.ofLp.1) :=
      fun α => rfl
    have hy : ∀ α : ℝ, (z + α • (x - z)).ofLp.2 = z.ofLp.2 + α • (x' - z.ofLp.2) :=
      fun α => rfl
    have ha : lscHull pers z ≤ Filter.liminf (fun α : ℝ => pers (z + α • (x - z))) (𝓝[>] 0) :=
      Filter.liminf_le_liminf_of_le hpath
    have hb : Filter.limsup (fun α : ℝ => pers (z + α • (x - z))) (𝓝[>] 0) ≤ lscHull pers z := by
      rcases hz.lt_or_eq with hz | hz
      · -- positive first coordinate
        rw [part2 z hz]
        set c := z.ofLp.1 with hc
        rcases eq_or_ne (f (c⁻¹ • z.ofLp.2)) ⊤ with hv | hv
        · rw [pers_pos z hz, hv, EReal.coe_mul_top_of_pos hz]
          exact le_top
        obtain ⟨v, hfv⟩ : ∃ r : ℝ, f (c⁻¹ • z.ofLp.2) = r :=
          ⟨_, (EReal.coe_toReal hv (f_ne_bot _).ne').symm⟩
        have hev : ∀ᶠ α in 𝓝[>] (0:ℝ), pers (z + α • (x - z)) ≤
            (((1 - α) * (c * v) + α * fx : ℝ) : EReal) := by
          filter_upwards [Ioo_mem_nhdsGT one_pos] with α hα
          obtain ⟨hα0, hα1⟩ := hα
          obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = c + α * (1 - c) := ⟨_, rfl⟩
          have hu0 : 0 < u := by
            have : 0 < (1 - α) * c + α := by nlinarith
            linarith
          have hpos : 0 < (z + α • (x - z)).ofLp.1 := by rw [hu α, ← hu_def]; exact hu0
          rw [pers_pos _ hpos, hu α, hy α, ← hu_def]
          have hpt : u⁻¹ • (z.ofLp.2 + α • (x' - z.ofLp.2)) =
              (1 - α / u) • (c⁻¹ • z.ofLp.2) + (α / u) • x' := by
            have hu0' : u ≠ 0 := hu0.ne'
            have hc0 : c ≠ 0 := hz.ne'
            subst hu_def
            match_scalars
            · field_simp
              ring
            · field_simp
          rw [hpt]
          have hs0 : 0 ≤ α / u := div_nonneg hα0.le hu0.le
          have hs1 : α / u ≤ 1 := by
            rw [div_le_one hu0]; nlinarith
          have hconv := conv_ineq (le_of_eq hfv) (le_of_eq hfx) hs0 hs1
          calc (u : EReal) * f ((1 - α / u) • (c⁻¹ • z.ofLp.2) + (α / u) • x')
              ≤ (u : EReal) * (((1 - α / u) * v + α / u * fx : ℝ) : EReal) :=
                mul_le_mul_of_nonneg_left hconv (EReal.coe_nonneg.mpr hu0.le)
            _ = (((1 - α) * (c * v) + α * fx : ℝ) : EReal) := by
                rw [← EReal.coe_mul]
                congr 1
                have hu0' : u ≠ 0 := hu0.ne'
                subst hu_def
                field_simp
                ring
        have htend : Filter.Tendsto (fun α : ℝ => (((1 - α) * (c * v) + α * fx : ℝ) : EReal))
            (𝓝[>] 0) (𝓝 ((c * v : ℝ) : EReal)) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds
          have : Continuous (fun α : ℝ => (1 - α) * (c * v) + α * fx) := by fun_prop
          have h2 := (continuous_coe_real_ereal.comp this).tendsto 0
          simpa using h2
        calc Filter.limsup (fun α : ℝ => pers (z + α • (x - z))) (𝓝[>] 0)
            ≤ Filter.limsup (fun α : ℝ => (((1 - α) * (c * v) + α * fx : ℝ) : EReal)) (𝓝[>] 0) :=
              Filter.limsup_le_limsup hev
          _ = ((c * v : ℝ) : EReal) := htend.limsup_eq
          _ = pers z := by rw [pers_pos z hz, hfv, EReal.coe_mul]
      · -- zero first coordinate
        have hz0 : z.ofLp.1 = 0 := hz.symm
        set d := z.ofLp.2 with hd
        have key : ∀ μ : ℝ, lscHull pers z < μ → ∀ t : ℝ, 0 ≤ t →
            f (x' + t • d) ≤ ((fx + t * μ : ℝ) : EReal) := by
          intro μ hμ t ht
          by_contra hcon
          push_neg at hcon
          obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
          have hm1' : fx + t * μ < m := EReal.coe_lt_coe_iff.mp hm1
          have hq : ContinuousAt
              (fun w : WithLp 2 (ℝ × E) => (1 - t * w.ofLp.1) • x' + t • w.ofLp.2) z := by
            have : Continuous
                (fun w : WithLp 2 (ℝ × E) => (1 - t * w.ofLp.1) • x' + t • w.ofLp.2) :=
              ((continuous_const.sub (continuous_const.mul hc1)).smul continuous_const).add
                (continuous_const.smul hc2)
            exact this.continuousAt
          have hqz : (1 - t * z.ofLp.1) • x' + t • z.ofLp.2 = x' + t • d := by
            rw [hz0, mul_zero, sub_zero, one_smul]
          have hev1 : ∀ᶠ w in 𝓝 z, (m : EReal) < f ((1 - t * w.ofLp.1) • x' + t • w.ofLp.2) := by
            have hl : LowerSemicontinuousAt
                (f ∘ (fun w : WithLp 2 (ℝ × E) => (1 - t * w.ofLp.1) • x' + t • w.ofLp.2)) z := by
              apply LowerSemicontinuousAt.comp _ hq
              rw [hqz]
              exact hlsc _
            refine hl m ?_
            show (m : EReal) < f ((1 - t * z.ofLp.1) • x' + t • z.ofLp.2)
            rw [hqz]
            exact hm2
          have hev2 : ∀ᶠ w in 𝓝 z, (1 - t * w.ofLp.1) * fx + t * μ < m := by
            have hcont2 : Continuous (fun w : WithLp 2 (ℝ × E) => (1 - t * w.ofLp.1) * fx + t * μ) :=
              by fun_prop
            have h2 := hcont2.tendsto z
            simp only [hz0, mul_zero, sub_zero, one_mul] at h2
            exact h2.eventually_lt_const hm1'
          have hev3 : ∀ᶠ w in 𝓝 z, t * w.ofLp.1 < 1 := by
            have hcont3 : Continuous (fun w : WithLp 2 (ℝ × E) => t * w.ofLp.1) := by fun_prop
            have h3 := hcont3.tendsto z
            simp only [hz0, mul_zero] at h3
            exact h3.eventually_lt_const one_pos
          have hfr : ∃ᶠ w in 𝓝 z, pers w < μ := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hμ
          obtain ⟨w, hw0, hw1, hw2, hw3⟩ := (hfr.and_eventually (hev1.and (hev2.and hev3))).exists
          have hwpos : 0 < w.ofLp.1 := by
            by_contra h
            push_neg at h
            rw [pers_nonpos w h] at hw0
            exact not_top_lt hw0
          rw [pers_pos w hwpos] at hw0
          have hfp : f ((w.ofLp.1)⁻¹ • w.ofLp.2) ≤ ((μ / w.ofLp.1 : ℝ) : EReal) := by
            rw [EReal.coe_div]
            apply le_of_lt
            rw [EReal.lt_div_iff (EReal.coe_pos.mpr hwpos) (EReal.coe_ne_top _), mul_comm]
            exact hw0
          have hconv := conv_ineq (le_of_eq hfx) hfp
            (s := t * w.ofLp.1) (mul_nonneg ht hwpos.le) hw3.le
          have heq : (1 - t * w.ofLp.1) • x' + (t * w.ofLp.1) • ((w.ofLp.1)⁻¹ • w.ofLp.2) =
              (1 - t * w.ofLp.1) • x' + t • w.ofLp.2 := by
            rw [smul_smul, mul_assoc, mul_inv_cancel₀ hwpos.ne', mul_one]
          rw [heq] at hconv
          have heq2 : (1 - t * w.ofLp.1) * fx + t * w.ofLp.1 * (μ / w.ofLp.1) =
              (1 - t * w.ofLp.1) * fx + t * μ := by
            field_simp
          rw [heq2] at hconv
          have h4 := lt_of_lt_of_le hw1 hconv
          have h5 := EReal.coe_lt_coe_iff.mp h4
          linarith
        rw [← EReal.le_of_forall_lt_iff_le]
        intro μ hμ
        have hev : ∀ᶠ α in 𝓝[>] (0:ℝ), pers (z + α • (x - z)) ≤
            ((α * fx + (1 - α) * μ : ℝ) : EReal) := by
          filter_upwards [Ioo_mem_nhdsGT one_pos] with α hα
          obtain ⟨hα0, hα1⟩ := hα
          have hpos : 0 < (z + α • (x - z)).ofLp.1 := by rw [hu α, hz0]; simpa using hα0
          rw [pers_pos _ hpos, hu α, hy α, hz0]
          have hpt : (0 + α * (1 - 0))⁻¹ • (d + α • (x' - d)) = x' + (α⁻¹ - 1) • d := by
            simp only [zero_add, sub_zero, mul_one]
            rw [smul_add, smul_smul, inv_mul_cancel₀ hα0.ne', one_smul, sub_smul, one_smul]
            abel
          rw [hpt]
          have hk := key μ hμ (α⁻¹ - 1) (by rw [sub_nonneg]; exact one_le_inv₀ hα0 |>.mpr hα1.le)
          calc ((0 + α * (1 - 0) : ℝ) : EReal) * f (x' + (α⁻¹ - 1) • d)
              ≤ ((0 + α * (1 - 0) : ℝ) : EReal) * ((fx + (α⁻¹ - 1) * μ : ℝ) : EReal) :=
                mul_le_mul_of_nonneg_left hk (EReal.coe_nonneg.mpr (by simpa using hα0.le))
            _ = ((α * fx + (1 - α) * μ : ℝ) : EReal) := by
                rw [← EReal.coe_mul]
                congr 1
                field_simp
                ring
        have htend : Filter.Tendsto (fun α : ℝ => ((α * fx + (1 - α) * μ : ℝ) : EReal))
            (𝓝[>] 0) (𝓝 (μ : EReal)) := by
          apply tendsto_nhdsWithin_of_tendsto_nhds
          have : Continuous (fun α : ℝ => α * fx + (1 - α) * μ) := by fun_prop
          have h2 := (continuous_coe_real_ereal.comp this).tendsto 0
          simpa using h2
        calc Filter.limsup (fun α : ℝ => pers (z + α • (x - z))) (𝓝[>] 0)
            ≤ Filter.limsup (fun α : ℝ => ((α * fx + (1 - α) * μ : ℝ) : EReal)) (𝓝[>] 0) :=
              Filter.limsup_le_limsup hev
          _ = (μ : EReal) := htend.limsup_eq
    exact tendsto_of_le_liminf_of_limsup_le ha hb

end FCA_chap_B_2_2_2
