import ConvexStarLib.Defs

/-!
# `FCA_chap_D_1_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_1_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_1_3_1`, so the main result is `FCA_chap_D_1_3_1.FCA_chap_D_1_3_1`.
-/

namespace FCA_chap_D_1_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_D_1_3_1
  (f : E → ℝ)
  (x s : E)
  (hf : ConvexOn ℝ Set.univ f) :
  let f' := directionalDeriv (liftRealtoEReal f) x
  let f'_epi := epigraph (fun d => f' d : E → EReal)
  let epi_f := epigraph (liftRealtoEReal f)
  let s' : E × ℝ := (s, -1)
  let x' : E × ℝ := (x, f x)
  (s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔ IsNormalToProd epi_f x' s') ∧
  (posTangentConeAt epi_f x' = f'_epi) := by
  intro f' f'_epi epi_f s' x'
  -- the (real) difference quotient
  let q : E → ℝ → ℝ := fun d t => (f (x + t • d) - f x) / t
  have hq : ∀ d t, q d t = (f (x + t • d) - f x) / t := fun _ _ => rfl
  -- monotonicity of the difference quotient
  have hmono : ∀ d : E, ∀ a b : ℝ, 0 < a → a ≤ b → q d a ≤ q d b := by
    intro d a b ha hab
    have hb : 0 < b := lt_of_lt_of_le ha hab
    have h1 : (0:ℝ) ≤ 1 - a / b := sub_nonneg.2 ((div_le_one hb).2 hab)
    have h2 : (0:ℝ) ≤ a / b := div_nonneg ha.le hb.le
    have key := hf.2 (Set.mem_univ x) (Set.mem_univ (x + b • d)) h1 h2 (by ring)
    have hpt : (1 - a / b) • x + (a / b) • (x + b • d) = x + a • d := by
      rw [smul_add, smul_smul, div_mul_cancel₀ a hb.ne', sub_smul, one_smul]; abel
    rw [hpt, smul_eq_mul, smul_eq_mul] at key
    rw [hq, hq, div_le_div_iff₀ ha hb]
    have key2 : b * f (x + a • d) ≤ b * ((1 - a / b) * f x + a / b * f (x + b • d)) :=
      mul_le_mul_of_nonneg_left key hb.le
    have e : b * ((1 - a / b) * f x + a / b * f (x + b • d))
        = (b - a) * f x + a * f (x + b • d) := by
      field_simp
    rw [e] at key2
    nlinarith
  -- lower bound for the difference quotient
  have hlow : ∀ d : E, ∀ t : ℝ, 0 < t → f x - f (x - d) ≤ q d t := by
    intro d t ht
    have h1 : (0:ℝ) ≤ t / (1 + t) := by positivity
    have h2 : (0:ℝ) ≤ 1 / (1 + t) := by positivity
    have hsum : t / (1 + t) + 1 / (1 + t) = 1 := by field_simp; ring
    have key := hf.2 (Set.mem_univ (x - d)) (Set.mem_univ (x + t • d)) h1 h2 hsum
    have hpt : (t / (1 + t)) • (x - d) + (1 / (1 + t)) • (x + t • d) = x := by
      rw [smul_sub, smul_add, smul_smul]
      have e1 : 1 / (1 + t) * t = t / (1 + t) := by ring
      rw [e1]
      have e2 : (t / (1 + t)) • x - (t / (1 + t)) • d + ((1 / (1 + t)) • x + (t / (1 + t)) • d)
          = (t / (1 + t) + 1 / (1 + t)) • x := by
        rw [add_smul]; abel
      rw [e2, hsum, one_smul]
    rw [hpt, smul_eq_mul, smul_eq_mul] at key
    rw [hq, le_div_iff₀ ht]
    have key2 : (1 + t) * f x
        ≤ (1 + t) * (t / (1 + t) * f (x - d) + 1 / (1 + t) * f (x + t • d)) :=
      mul_le_mul_of_nonneg_left key (by positivity)
    have e : (1 + t) * (t / (1 + t) * f (x - d) + 1 / (1 + t) * f (x + t • d))
        = t * f (x - d) + f (x + t • d) := by
      field_simp
    rw [e] at key2
    nlinarith
  have hbdd : ∀ d : E, BddBelow (q d '' Set.Ioi 0) := by
    intro d
    refine ⟨f x - f (x - d), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hlow d t ht
  have hmonoOn : ∀ d : E, MonotoneOn (q d) (Set.Ioi 0) := by
    intro d a ha b _ hab
    exact hmono d a b ha hab
  -- the (real-valued) directional derivative
  let L : E → ℝ := fun d => sInf (q d '' Set.Ioi 0)
  have hlim : ∀ d : E, Filter.Tendsto (q d) (𝓝[>] 0) (𝓝 (L d)) := fun d =>
    (hmonoOn d).tendsto_nhdsGT (hbdd d)
  have hLle : ∀ d : E, ∀ t : ℝ, 0 < t → L d ≤ q d t := fun d t ht =>
    csInf_le (hbdd d) (Set.mem_image_of_mem _ ht)
  have hf'eq : ∀ d : E, f' d = (L d : EReal) := by
    intro d
    show limUnder (𝓝[>] 0) (fun t => differenceQuotient (liftRealtoEReal f) x d t) = (L d : EReal)
    apply Filter.Tendsto.limUnder_eq
    have h1 : Filter.Tendsto (fun t => ((q d t : ℝ) : EReal)) (𝓝[>] 0) (𝓝 (L d : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (hlim d)
    exact h1
  -- membership in the epigraphs
  have hepi : ∀ y : E × ℝ, y ∈ epi_f ↔ f y.1 ≤ y.2 := fun y => EReal.coe_le_coe_iff
  have hepi' : ∀ y : E × ℝ, y ∈ f'_epi ↔ L y.1 ≤ y.2 := by
    intro y
    show f' y.1 ≤ (y.2 : EReal) ↔ _
    rw [hf'eq]
    exact EReal.coe_le_coe_iff
  -- L at 1
  have hL1 : ∀ d : E, L d ≤ f (x + d) - f x := by
    intro d
    have := hLle d 1 one_pos
    rw [hq, one_smul, div_one] at this
    exact this
  -- subadditivity of L
  have hsub : ∀ a b : E, L (a + b) ≤ L a + L b := by
    intro a b
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), L (a + b) ≤ q a t + q b t := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      have ht' : (0:ℝ) < t := ht
      have h1 := hLle (a + b) (t / 2) (by positivity)
      have key := hf.2 (Set.mem_univ (x + t • a)) (Set.mem_univ (x + t • b))
        (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num : (0:ℝ) ≤ 1 / 2) (by norm_num)
      have hpt : (1 / 2 : ℝ) • (x + t • a) + (1 / 2 : ℝ) • (x + t • b) = x + (t / 2) • (a + b) := by
        rw [smul_add, smul_add, smul_add, smul_smul, smul_smul]
        have e1 : (1 / 2 : ℝ) * t = t / 2 := by ring
        rw [e1]
        have e2 : (1 / 2 : ℝ) • x + (t / 2) • a + ((1 / 2 : ℝ) • x + (t / 2) • b)
            = ((1 / 2 : ℝ) + 1 / 2) • x + ((t / 2) • a + (t / 2) • b) := by
          rw [add_smul]; abel
        rw [e2]
        norm_num
      rw [hpt, smul_eq_mul, smul_eq_mul] at key
      rw [hq] at h1
      rw [hq, hq]
      have e3 : (f (x + (t / 2) • (a + b)) - f x) / (t / 2)
          = 2 * (f (x + (t / 2) • (a + b)) - f x) / t := by
        field_simp
      rw [e3] at h1
      have e4 : (f (x + t • a) - f x) / t + (f (x + t • b) - f x) / t
          = ((f (x + t • a) - f x) + (f (x + t • b) - f x)) / t := by
        rw [add_div]
      rw [e4]
      refine h1.trans ?_
      apply div_le_div_of_nonneg_right _ ht'.le
      linarith
    exact ge_of_tendsto ((hlim a).add (hlim b)) hev
  -- L at a nonnegative multiple
  have hLsmul : ∀ (c : ℝ) (u : E), 0 ≤ c → L (c • u) ≤ c * (f (x + u) - f x) := by
    intro c u hc
    rcases hc.lt_or_eq with hc | hc
    · have h1 := hLle (c • u) (1 / c) (by positivity)
      rw [hq, smul_smul, one_div_mul_cancel hc.ne', one_smul, one_div, div_inv_eq_mul,
        mul_comm] at h1
      exact h1
    · subst hc
      have := hL1 0
      simpa using this
  have hcont : Continuous f := hf.locallyLipschitz.continuous
  refine ⟨?_, ?_⟩
  · -- part 1
    constructor
    · intro hs y hy
      have h1 := hs (y.1 - x)
      have h2 : inner ℝ s (y.1 - x) ≤ L (y.1 - x) := by
        have : f' (y.1 - x) = (L (y.1 - x) : EReal) := hf'eq _
        exact EReal.coe_le_coe_iff.1 (this ▸ h1)
      have h3 := hL1 (y.1 - x)
      rw [add_sub_cancel] at h3
      have h4 := (hepi y).1 hy
      show inner ℝ s (y.1 - x) + (-1) * (y.2 - f x) ≤ 0
      linarith
    · intro hN d
      show ((inner ℝ s d : ℝ) : EReal) ≤ f' d
      rw [hf'eq]
      apply EReal.coe_le_coe_iff.2
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), inner ℝ s d ≤ q d t := by
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (0:ℝ) < t := ht
        have h1 := hN (x + t • d, f (x + t • d)) ((hepi _).2 le_rfl)
        change inner ℝ s (x + t • d - x) + (-1) * (f (x + t • d) - f x) ≤ 0 at h1
        rw [add_sub_cancel_left, inner_smul_right] at h1
        rw [hq, le_div_iff₀ ht']
        linarith
      exact ge_of_tendsto (hlim d) hev
  · -- part 2
    ext ⟨d, r⟩
    rw [hepi']
    constructor
    · intro h
      obtain ⟨α, l, hl, c, δ, -, hδs, hcδ⟩ := exists_fun_of_mem_tangentConeAt h
      have hc1 : Filter.Tendsto (fun n => (c n : ℝ) • (δ n).1) l (𝓝 d) := by
        have := (continuous_fst.tendsto _).comp hcδ
        refine this.congr' (Filter.Eventually.of_forall fun n => ?_)
        simp [NNReal.smul_def]
      have hc2 : Filter.Tendsto (fun n => (c n : ℝ) * (δ n).2) l (𝓝 r) := by
        have := (continuous_snd.tendsto _).comp hcδ
        refine this.congr' (Filter.Eventually.of_forall fun n => ?_)
        simp [NNReal.smul_def]
      have hev : ∀ᶠ n in l,
          L d ≤ (c n : ℝ) * (δ n).2 + (f (x + (d - (c n : ℝ) • (δ n).1)) - f x) := by
        filter_upwards [hδs] with n hn
        have hn' : f (x + (δ n).1) ≤ f x + (δ n).2 := by
          have := (hepi _).1 hn
          simpa [x'] using this
        have h1 := hsub ((c n : ℝ) • (δ n).1) (d - (c n : ℝ) • (δ n).1)
        rw [add_sub_cancel] at h1
        have h2 := hLsmul (c n : ℝ) (δ n).1 (c n).coe_nonneg
        have h3 := hL1 (d - (c n : ℝ) • (δ n).1)
        have h4 : (c n : ℝ) * (f (x + (δ n).1) - f x) ≤ (c n : ℝ) * (δ n).2 :=
          mul_le_mul_of_nonneg_left (by linarith) (c n).coe_nonneg
        linarith
      have hlim2 : Filter.Tendsto
          (fun n => (c n : ℝ) * (δ n).2 + (f (x + (d - (c n : ℝ) • (δ n).1)) - f x)) l
          (𝓝 (r + (f (x + (d - d)) - f x))) := by
        refine hc2.add (Filter.Tendsto.sub ?_ tendsto_const_nhds)
        exact (hcont.tendsto _).comp (tendsto_const_nhds.add (tendsto_const_nhds.sub hc1))
      rw [sub_self, add_zero, sub_self, add_zero] at hlim2
      exact ge_of_tendsto hlim2 hev
    · intro h
      change L d ≤ r at h
      show (d, r) ∈ tangentConeAt ℝ≥0 epi_f x'
      have hmax : Filter.Tendsto (fun t => max r (q d t)) (𝓝[>] 0) (𝓝 r) := by
        have := (tendsto_const_nhds (x := r)).max (hlim d)
        rwa [max_eq_left h] at this
      have hid : Filter.Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
      apply mem_tangentConeAt_of_seq (𝓝[>] (0:ℝ)) (fun t => (t⁻¹).toNNReal)
        (fun t => (t • d, t * max r (q d t)))
      · have h1 : Filter.Tendsto (fun t : ℝ => t • d) (𝓝[>] 0) (𝓝 0) := by
          simpa using hid.smul_const d
        have h2 : Filter.Tendsto (fun t : ℝ => t * max r (q d t)) (𝓝[>] 0) (𝓝 0) := by
          simpa using hid.mul hmax
        simpa using h1.prodMk_nhds h2
      · filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (0:ℝ) < t := ht
        apply (hepi _).2
        show f (x + t • d) ≤ f x + t * max r (q d t)
        have : t * q d t = f (x + t • d) - f x := by
          rw [hq]; field_simp
        have h2 : t * q d t ≤ t * max r (q d t) :=
          mul_le_mul_of_nonneg_left (le_max_right _ _) ht'.le
        linarith
      · have hT : Filter.Tendsto (fun t => (d, max r (q d t))) (𝓝[>] 0) (𝓝 (d, r)) :=
          tendsto_const_nhds.prodMk_nhds hmax
        refine hT.congr' ?_
        filter_upwards [self_mem_nhdsWithin] with t ht
        have ht' : (0:ℝ) < t := ht
        rw [NNReal.smul_def, Real.coe_toNNReal _ (inv_nonneg.2 ht'.le)]
        simp only [Prod.smul_mk, smul_smul, smul_eq_mul, inv_mul_cancel₀ ht'.ne', one_smul,
          ← mul_assoc, one_mul]

end FCA_chap_D_1_3_1
