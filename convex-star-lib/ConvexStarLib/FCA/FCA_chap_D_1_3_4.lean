import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_3_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_3_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_3_4`, so the main result is `FCA_chap_D_1_3_4.FCA_chap_D_1_3_4`.
-/

namespace FCA_chap_D_1_3_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_3_4
  (f : E → ℝ)
  (x : E)
  (hf_convex : ConvexOn ℝ Set.univ f)
  (hf_subdiff : 0 ∉ directionalSubdifferential (liftRealtoEReal f) x) :
  let S := sublevelSetFun (liftRealtoEReal f) x
  (posTangentConeAt S x = {d | directionalDeriv (liftRealtoEReal f) x d ≤ 0}) ∧
  (interior (posTangentConeAt S x) = {d | directionalDeriv (liftRealtoEReal f) x d < 0}) ∧
  Set.Nonempty (interior (posTangentConeAt S x)) := by
  intro S
  set q : E → ℝ → ℝ := fun d t => (f (x + t • d) - f x) / t with hq_def
  have hg : ∀ d : E, ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
    intro d
    refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
    have := hf_convex.2 (Set.mem_univ (x + a • d)) (Set.mem_univ (x + b • d)) hμ hν hμν
    convert this using 2
    simp only [smul_eq_mul]
    calc x + (μ * a + ν * b) • d = (μ + ν) • x + (μ * a + ν * b) • d := by rw [hμν, one_smul]
      _ = μ • (x + a • d) + ν • (x + b • d) := by module
  have hmono : ∀ d : E, MonotoneOn (q d) (Set.Ioi 0) := by
    intro d s hs t ht hst
    have := (hg d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ s) (Set.mem_univ t)
      (ne_of_gt hs) (ne_of_gt ht) hst
    simpa [q] using this
  have hbdd : ∀ d : E, BddBelow (q d '' Set.Ioi 0) := by
    intro d
    refine ⟨(f (x + (-1:ℝ) • d) - f (x + (0:ℝ) • d)) / (-1 - 0), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    have := (hg d).secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ (-1)) (Set.mem_univ t)
      (by norm_num) (ne_of_gt ht) (by linarith [ht.out] : (-1:ℝ) ≤ t)
    simpa [q] using this
  set ψ : E → ℝ := fun d => sInf (q d '' Set.Ioi 0) with hψ_def
  have hlim : ∀ d, Filter.Tendsto (q d) (𝓝[>] 0) (𝓝 (ψ d)) :=
    fun d => (hmono d).tendsto_nhdsGT (hbdd d)
  have hle : ∀ d, ∀ t > 0, ψ d ≤ q d t :=
    fun d t ht => csInf_le (hbdd d) (Set.mem_image_of_mem _ ht)
  have hdir : ∀ d, directionalDeriv (liftRealtoEReal f) x d = (ψ d : EReal) := by
    intro d
    unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have h1 : Filter.Tendsto (fun t => ((q d t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (ψ d : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (hlim d)
    refine h1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [differenceQuotient, liftRealtoEReal, q]
    rw [EReal.coe_div, EReal.coe_sub]
  have hconv : ConvexOn ℝ Set.univ ψ := by
    refine ⟨convex_univ, fun u _ v _ a b ha hb hab => ?_⟩
    have h1 := hlim (a • u + b • v)
    have h2 := ((hlim u).const_mul a).add ((hlim v).const_mul b)
    refine le_of_tendsto_of_tendsto h1 h2 ?_
    filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    simp only [q]
    have key := hf_convex.2 (Set.mem_univ (x + t • u)) (Set.mem_univ (x + t • v)) ha hb hab
    have heq : a • (x + t • u) + b • (x + t • v) = x + t • (a • u + b • v) := by
      calc a • (x + t • u) + b • (x + t • v) = (a + b) • x + t • (a • u + b • v) := by module
        _ = x + t • (a • u + b • v) := by rw [hab, one_smul]
    rw [heq] at key
    simp only [smul_eq_mul] at key
    rw [mul_div_assoc', mul_div_assoc', ← add_div, div_le_div_iff_of_pos_right ht]
    have : f x = a * f x + b * f x := by rw [← add_mul, hab, one_mul]
    linarith
  have hcont : Continuous ψ := hconv.locallyLipschitz.continuous
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, ψ d₀ < 0 := by
    by_contra h
    push_neg at h
    apply hf_subdiff
    intro d
    simp only [inner_zero_left, hdir]
    exact_mod_cast h d
  have hS : ∀ y, y ∈ S ↔ f y ≤ f x := by
    intro y
    simp only [S, sublevelSetFun, liftRealtoEReal, Set.mem_setOf_eq, EReal.coe_le_coe_iff]
  have hneg : ∀ w, ψ w < 0 → w ∈ posTangentConeAt S x := by
    intro w hw
    apply mem_posTangentConeAt_of_frequently_mem
    apply Filter.Eventually.frequently
    filter_upwards [(hlim w).eventually (gt_mem_nhds hw), self_mem_nhdsWithin] with t ht
      (ht0 : 0 < t)
    rw [hS]
    simp only [q] at ht
    have := (div_lt_iff₀ ht0).mp ht
    rw [zero_mul] at this
    linarith
  have hclosed : IsClosed (posTangentConeAt S x) := by
    show IsClosed (tangentConeAt ℝ≥0 S x)
    rw [tangentConeAt_eq_biInter_closure]
    exact isClosed_biInter fun _ _ => isClosed_closure
  have hcone : posTangentConeAt S x = {d | ψ d ≤ 0} := by
    ext d
    constructor
    · intro hd
      obtain ⟨α, l, hl, c, v, hv0, hvS, hcv⟩ := exists_fun_of_mem_tangentConeAt hd
      have h1 : Filter.Tendsto (fun n => ψ (c n • v n)) l (𝓝 (ψ d)) :=
        (hcont.tendsto d).comp hcv
      refine le_of_tendsto h1 ?_
      filter_upwards [hvS] with n hn
      rw [hS] at hn
      rw [NNReal.smul_def]
      rcases eq_or_lt_of_le (NNReal.coe_nonneg (c n)) with h | h
      · rw [← h, zero_smul]
        have := hle 0 1 one_pos
        simpa [q] using this
      · have := hle ((c n : ℝ) • v n) (c n : ℝ)⁻¹ (inv_pos.mpr h)
        simp only [q] at this
        rw [smul_smul, inv_mul_cancel₀ (ne_of_gt h), one_smul, div_inv_eq_mul] at this
        have h2 : (f (x + v n) - f x) * (c n : ℝ) ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (by linarith) h.le
        linarith
    · intro hd
      show d ∈ posTangentConeAt S x
      apply hclosed.mem_of_tendsto (f := fun ε : ℝ => (1 - ε) • d + ε • d₀) (b := 𝓝[>] 0)
      · have : Continuous (fun ε : ℝ => (1 - ε) • d + ε • d₀) := by fun_prop
        have h2 := this.tendsto 0
        simp only [sub_zero, one_smul, zero_smul, add_zero] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      · filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε
        apply hneg
        have := hconv.2 (Set.mem_univ d) (Set.mem_univ d₀) (by linarith [hε.2] : 0 ≤ 1 - ε)
          hε.1.le (by ring)
        simp only [smul_eq_mul] at this
        have h3 : (1 - ε) * ψ d ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by linarith [hε.2]) hd
        have h4 : ε * ψ d₀ < 0 := mul_neg_of_pos_of_neg hε.1 hd₀
        linarith
  have hint : interior (posTangentConeAt S x) = {d | ψ d < 0} := by
    rw [hcone]
    apply Set.Subset.antisymm
    · intro d hd
      rw [mem_interior_iff_mem_nhds] at hd
      have ht : Filter.Tendsto (fun b : ℝ => (1 - b)⁻¹ • (d - b • d₀)) (𝓝[>] 0) (𝓝 d) := by
        have : ContinuousAt (fun b : ℝ => (1 - b)⁻¹ • (d - b • d₀)) 0 := by
          fun_prop (disch := norm_num)
        have h2 := this.tendsto
        simp only [sub_zero, inv_one, one_smul, zero_smul] at h2
        exact h2.mono_left nhdsWithin_le_nhds
      obtain ⟨b, hb, hbI⟩ := ((ht.eventually hd).and (Ioo_mem_nhdsGT one_pos)).exists
      have hb1 : 0 < 1 - b := by linarith [hbI.2]
      have hconvex := hconv.2 (Set.mem_univ ((1 - b)⁻¹ • (d - b • d₀))) (Set.mem_univ d₀)
        hb1.le hbI.1.le (by ring)
      have heq : (1 - b) • ((1 - b)⁻¹ • (d - b • d₀)) + b • d₀ = d := by
        rw [smul_inv_smul₀ (ne_of_gt hb1)]; abel
      rw [heq] at hconvex
      simp only [smul_eq_mul] at hconvex
      have h3 : (1 - b) * ψ ((1 - b)⁻¹ • (d - b • d₀)) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hb1.le hb
      have h4 : b * ψ d₀ < 0 := mul_neg_of_pos_of_neg hbI.1 hd₀
      show ψ d < 0
      linarith
    · apply interior_maximal
      · intro d (hd : ψ d < 0); exact le_of_lt hd
      · exact isOpen_lt hcont continuous_const
  refine ⟨?_, ?_, ?_⟩
  · rw [hcone]; ext d; simp only [Set.mem_setOf_eq, hdir, EReal.coe_nonpos]
  · rw [hint]; ext d; simp only [Set.mem_setOf_eq, hdir, EReal.coe_neg']
  · rw [hint]; exact ⟨d₀, hd₀⟩

end FCA_chap_D_1_3_4
