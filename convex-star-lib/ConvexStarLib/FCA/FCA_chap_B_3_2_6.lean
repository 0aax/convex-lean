import ConvexStarLib.Defs

/-!
# `FCA_chap_B_3_2_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_3_2_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_3_2_6`, so the main result is `FCA_chap_B_3_2_6.FCA_chap_B_3_2_6`.
-/

namespace FCA_chap_B_3_2_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_3_2_6
  [Nontrivial E]
  (f : E → ℝ)
  (hf_closed_conv : InClosedConvRn (liftRealtoEReal f)) :
  let f'_infinity := asymptoticFun (liftRealtoEReal f)
  ((∃ L ≥ 0, ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖) ↔
    ∀ x, f'_infinity x < ⊤) ∧
  ((∃ L ≥ 0, ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖) →
    ((sInf {L : ℝ | 0 ≤ L ∧ ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖} : ℝ) : EReal) =
      sSup (f'_infinity '' Metric.sphere (0 : E) 1)) := by
  intro f'_infinity
  -- convexity of the epigraph
  have hconv : Convex ℝ (epigraph (liftRealtoEReal f)) := hf_closed_conv.1.2.2
  -- closedness of the epigraph
  have hclosed : IsClosed (epigraph (liftRealtoEReal f)) := by
    have h1 : IsClosed {p : E × EReal | liftRealtoEReal f p.1 ≤ p.2} :=
      hf_closed_conv.2.isClosed_epigraph
    have h2 : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact h1.preimage h2
  have hmem_epi : ∀ x : E, ∀ s : ℝ, (x, s) ∈ epigraph (liftRealtoEReal f) ↔ f x ≤ s := by
    intro x s
    simp [epigraph, liftRealtoEReal]
  -- elements of the horizon cone of the epigraph
  have hA1 : ∀ d : E, ∀ r : ℝ, (d, r) ∈ horizonCone (epigraph (liftRealtoEReal f)) →
      ∀ x : E, ∀ t : ℝ, 0 < t → f (x + t • d) ≤ f x + t * r := by
    rintro d r ⟨X, l, hX, hl, hlim⟩ x t ht
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hl
    have hlpos : ∀ᶠ i in Filter.atTop, l i ∈ Set.Ioi (0 : ℝ) :=
      (tendsto_nhdsWithin_iff.mp hl).2
    have htl : Filter.Tendsto (fun i => t * l i) Filter.atTop (𝓝 0) := by
      simpa using hl0.const_mul t
    have hsmall : ∀ᶠ i in Filter.atTop, t * l i < 1 := htl.eventually_lt_const one_pos
    set P : E × ℝ := (x, f x) with hP
    have hPmem : P ∈ epigraph (liftRealtoEReal f) := (hmem_epi x (f x)).mpr le_rfl
    have hconv_lim : Filter.Tendsto (fun i => (1 - t * l i) • P + (t * l i) • X i)
        Filter.atTop (𝓝 (P + t • (d, r))) := by
      have h1 : Filter.Tendsto (fun i => (1 - t * l i) • P) Filter.atTop (𝓝 P) := by
        have : Filter.Tendsto (fun i => 1 - t * l i) Filter.atTop (𝓝 (1 - 0)) :=
          tendsto_const_nhds.sub htl
        simpa using this.smul_const P
      have h2 : Filter.Tendsto (fun i => (t * l i) • X i) Filter.atTop (𝓝 (t • (d, r))) := by
        refine (hlim.const_smul t).congr (fun i => ?_)
        exact smul_smul _ _ _
      exact h1.add h2
    have hmem : P + t • (d, r) ∈ epigraph (liftRealtoEReal f) := by
      refine hclosed.mem_of_tendsto hconv_lim ?_
      filter_upwards [hlpos, hsmall] with i hi1 hi2
      exact hconv hPmem (hX i) (by linarith) (mul_pos ht hi1).le (by ring)
    have : P + t • (d, r) = (x + t • d, f x + t * r) := by
      simp [hP]
    rw [this, hmem_epi] at hmem
    exact hmem
  have hA2 : ∀ d : E, ∀ r : ℝ, (∀ n : ℕ, f (((n:ℝ) + 1) • d) ≤ f 0 + ((n:ℝ) + 1) * r) →
      (d, r) ∈ horizonCone (epigraph (liftRealtoEReal f)) := by
    intro d r h
    refine ⟨fun n => (((n:ℝ) + 1) • d, f 0 + ((n:ℝ) + 1) * r), fun n => 1 / ((n:ℝ) + 1),
      ?_, ?_, ?_⟩
    · intro n
      exact (hmem_epi _ _).mpr (h n)
    · refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
      exact Filter.Eventually.of_forall (fun n => by simp only [Set.mem_Ioi]; positivity)
    · have h1 : Filter.Tendsto (fun n : ℕ => (d, f 0 * (1 / ((n:ℝ) + 1)) + r)) Filter.atTop
          (𝓝 (d, r)) := by
        refine Filter.Tendsto.prodMk_nhds tendsto_const_nhds ?_
        have := (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (f 0)).add_const r
        simpa using this
      refine h1.congr (fun n => ?_)
      have hn : ((n:ℝ) + 1) ≠ 0 := by positivity
      simp only [Prod.smul_mk, smul_eq_mul, smul_smul]
      refine Prod.ext ?_ ?_
      · simp [hn]
      · field_simp
  have hasym : ∀ d : E, f'_infinity d = sInf ((fun r : ℝ => (r : EReal)) ''
      {r : ℝ | (d, r) ∈ horizonCone (epigraph (liftRealtoEReal f))}) := fun d => rfl
  -- difference quotients are bounded by the asymptotic function
  have hQ : ∀ x d : E, ∀ t : ℝ, 0 < t →
      (((f (x + t • d) - f x) / t : ℝ) : EReal) ≤ f'_infinity d := by
    intro x d t ht
    rw [hasym]
    apply le_sInf
    rintro _ ⟨r, hr, rfl⟩
    have := hA1 d r hr x t ht
    exact EReal.coe_le_coe_iff.mpr (by rw [div_le_iff₀ ht]; linarith)
  -- a Lipschitz constant bounds the asymptotic function
  have hL : ∀ L : ℝ, (∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖) →
      ∀ d, f'_infinity d ≤ ((L * ‖d‖ : ℝ) : EReal) := by
    intro L hLip d
    rw [hasym]
    apply sInf_le
    refine ⟨L * ‖d‖, ?_, rfl⟩
    apply hA2
    intro n
    have hn : (0:ℝ) < (n:ℝ) + 1 := by positivity
    have h1 : f (((n:ℝ) + 1) • d) - f 0 ≤ L * (((n:ℝ) + 1) * ‖d‖) := by
      have := hLip (((n:ℝ) + 1) • d) 0
      rw [sub_zero, norm_smul, Real.norm_of_nonneg hn.le] at this
      exact le_trans (le_abs_self _) (by rwa [Real.norm_eq_abs] at this)
    linarith
  -- finiteness of the asymptotic function gives a Lipschitz constant
  have hfin_lip : (∀ x, f'_infinity x < ⊤) →
      ∃ L ≥ 0, ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖ := by
    intro hfin
    have hR : ∀ d : E, ∃ r : ℝ, ∀ x : E, ∀ t : ℝ, 0 < t → f (x + t • d) ≤ f x + t * r := by
      intro d
      have := hfin d
      rw [hasym, sInf_lt_iff] at this
      obtain ⟨_, ⟨r, hr, rfl⟩, -⟩ := this
      exact ⟨r, hA1 d r hr⟩
    choose R hR using hR
    set b := stdOrthonormalBasis ℝ E with hb
    set C : ℝ := ∑ i, (|R (b i)| + |R (-b i)|) with hC
    have hC0 : 0 ≤ C := Finset.sum_nonneg (fun i _ => by positivity)
    have hCi : ∀ i, |R (b i)| + |R (-b i)| ≤ C := fun i =>
      Finset.single_le_sum (f := fun i => |R (b i)| + |R (-b i)|)
        (fun i _ => by positivity) (Finset.mem_univ i)
    have hstep : ∀ i, ∀ x : E, ∀ c : ℝ, f (x + c • b i) ≤ f x + |c| * C := by
      intro i x c
      rcases lt_trichotomy c 0 with hc | hc | hc
      · have h1 := hR (-b i) x (-c) (by linarith)
        rw [neg_smul_neg] at h1
        have h3 : R (-b i) ≤ C :=
          le_trans (le_abs_self _) (by linarith [hCi i, abs_nonneg (R (b i))])
        have h2 : -c * R (-b i) ≤ |c| * C := by
          rw [abs_of_neg hc]
          exact mul_le_mul_of_nonneg_left h3 (by linarith)
        linarith
      · simp [hc]
      · have h1 := hR (b i) x c hc
        have h3 : R (b i) ≤ C :=
          le_trans (le_abs_self _) (by linarith [hCi i, abs_nonneg (R (-b i))])
        have h2 : c * R (b i) ≤ |c| * C := by
          rw [abs_of_pos hc]
          exact mul_le_mul_of_nonneg_left h3 hc.le
        linarith
    have hsum : ∀ (s : Finset (Fin (Module.finrank ℝ E))) (c : Fin (Module.finrank ℝ E) → ℝ)
        (x : E), f (x + ∑ i ∈ s, c i • b i) ≤ f x + C * ∑ i ∈ s, |c i| := by
      intro s c
      induction s using Finset.induction_on with
      | empty => intro x; simp
      | insert j s hj ih =>
        intro x
        rw [Finset.sum_insert hj, Finset.sum_insert hj]
        have h1 := hstep j (x + ∑ i ∈ s, c i • b i) (c j)
        have h2 := ih x
        have h3 : x + (c j • b j + ∑ i ∈ s, c i • b i) = x + ∑ i ∈ s, c i • b i + c j • b j := by
          abel
        rw [h3]
        linarith
    have hone : ∀ x v : E, f (x + v) - f x ≤ C * (Module.finrank ℝ E) * ‖v‖ := by
      intro x v
      have h1 := hsum Finset.univ (fun i => inner ℝ (b i) v) x
      rw [b.sum_repr'] at h1
      have h2 : ∑ i, |inner ℝ (b i) v| ≤ (Module.finrank ℝ E) * ‖v‖ := by
        calc ∑ i, |inner ℝ (b i) v| ≤ ∑ _i : Fin (Module.finrank ℝ E), ‖v‖ := by
              apply Finset.sum_le_sum
              intro i _
              calc |inner ℝ (b i) v| ≤ ‖b i‖ * ‖v‖ := abs_real_inner_le_norm _ _
                _ = ‖v‖ := by rw [b.norm_eq_one, one_mul]
          _ = (Module.finrank ℝ E) * ‖v‖ := by simp
      have := mul_le_mul_of_nonneg_left h2 hC0
      linarith
    refine ⟨C * (Module.finrank ℝ E), mul_nonneg hC0 (Nat.cast_nonneg _), ?_⟩
    intro x x'
    have e1 : x' + (x - x') = x := by abel
    have e2 : x + (x' - x) = x' := by abel
    have h1 := hone x' (x - x')
    have h2 := hone x (x' - x)
    rw [e1] at h1
    rw [e2, norm_sub_rev] at h2
    rw [Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hS_bdd : BddBelow {L : ℝ | 0 ≤ L ∧ ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖} :=
    ⟨0, fun L hL => hL.1⟩
  refine ⟨⟨fun ⟨L, _, hLip⟩ d => ?_, hfin_lip⟩, ?_⟩
  · exact lt_of_le_of_lt (hL L hLip d) (EReal.coe_lt_top _)
  · rintro ⟨L0, hL00, hLip0⟩
    set S := {L : ℝ | 0 ≤ L ∧ ∀ x x', ‖f x - f x'‖ ≤ L * ‖x - x'‖} with hS
    have hSne : S.Nonempty := ⟨L0, hL00, hLip0⟩
    apply le_antisymm
    · -- the best Lipschitz constant is at most the supremum
      by_contra hcon
      push_neg at hcon
      obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hm2' : m < sInf S := EReal.coe_lt_coe_iff.mp hm2
      have hdir : ∀ d ∈ Metric.sphere (0:E) 1, f'_infinity d < (m : EReal) :=
        fun d hd => lt_of_le_of_lt (le_sSup (Set.mem_image_of_mem f'_infinity hd)) hm1
      have hstep : ∀ x x' : E, x ≠ x' → f x' - f x < m * ‖x' - x‖ := by
        intro x x' hxx'
        have hne : x' - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hxx')
        have ht : 0 < ‖x' - x‖ := norm_pos_iff.mpr hne
        set d := (‖x' - x‖⁻¹ : ℝ) • (x' - x) with hd
        have hd1 : d ∈ Metric.sphere (0:E) 1 := by
          rw [mem_sphere_zero_iff_norm, hd, norm_smul, norm_inv, norm_norm,
            inv_mul_cancel₀ (ne_of_gt ht)]
        have hxd : x + ‖x' - x‖ • d = x' := by
          rw [hd, smul_inv_smul₀ (ne_of_gt ht)]
          abel
        have h1 := hQ x d ‖x' - x‖ ht
        rw [hxd] at h1
        have h2 := lt_of_le_of_lt h1 (hdir d hd1)
        have h3 : (f x' - f x) / ‖x' - x‖ < m := EReal.coe_lt_coe_iff.mp h2
        rwa [div_lt_iff₀ ht] at h3
      have hmS : m ∈ S := by
        refine ⟨?_, ?_⟩
        · obtain ⟨v, hv⟩ := exists_ne (0 : E)
          have h1 := hstep 0 v hv.symm
          have h2 := hstep v 0 hv
          have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
          rw [sub_zero] at h1
          rw [zero_sub, norm_neg] at h2
          by_contra hm
          push_neg at hm
          nlinarith
        · intro x x'
          by_cases hxx' : x = x'
          · subst hxx'; simp
          · have h1 := hstep x x' hxx'
            have h2 := hstep x' x (Ne.symm hxx')
            rw [norm_sub_rev] at h1
            rw [Real.norm_eq_abs, abs_le]
            constructor <;> linarith
      have := csInf_le hS_bdd hmS
      linarith
    · -- the supremum is at most the best Lipschitz constant
      apply sSup_le
      rintro _ ⟨d, hd, rfl⟩
      by_contra hcon
      push_neg at hcon
      obtain ⟨m, hm1, hm2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
      have hm1' : sInf S < m := EReal.coe_lt_coe_iff.mp hm1
      obtain ⟨L, hLS, hLm⟩ := exists_lt_of_csInf_lt hSne hm1'
      have h1 := hL L hLS.2 d
      rw [mem_sphere_zero_iff_norm.mp hd, mul_one] at h1
      have h2 : (L : EReal) < m := EReal.coe_lt_coe_iff.mpr hLm
      exact absurd (lt_trans (lt_of_le_of_lt h1 h2) hm2) (lt_irrefl _)

end FCA_chap_B_3_2_6
