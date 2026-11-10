import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_3_1`, so the main result is `FCA_chap_D_6_3_1.FCA_chap_D_6_3_1`.
-/

namespace FCA_chap_D_6_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma aux_convexOn_line {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    ConvexOn ℝ Set.univ (fun t : ℝ => f (x + t • d)) := by
  have := hf.comp_affineMap (AffineMap.lineMap x (x + d))
  convert this using 1
  funext t
  simp [AffineMap.lineMap_apply, add_comm]

omit [FiniteDimensional ℝ E] in
lemma aux_dirDeriv {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    ∃ L : ℝ, directionalDeriv (liftRealtoEReal f) x d = (L : EReal) ∧
      (∀ τ : ℝ, 0 < τ → L ≤ (f (x + τ • d) - f x) / τ) ∧
      (∀ c : ℝ, (∀ τ : ℝ, 0 < τ → c ≤ (f (x + τ • d) - f x) / τ) → c ≤ L) := by
  set gφ : ℝ → ℝ := fun t : ℝ => f (x + t • d) with hgdef
  have hgφ := aux_convexOn_line hf x d
  have h0 : (0:ℝ) ∈ interior Set.univ := by simp
  have hD := hgφ.hasDerivWithinAt_rightDeriv_of_mem_interior h0
  set L := derivWithin gφ (Set.Ioi 0) 0
  have hslope : ∀ t, slope gφ 0 t = (f (x + t • d) - f x) / t := by
    intro t; simp [slope_def_field, gφ]
  have htend : Filter.Tendsto (fun t => (f (x + t • d) - f x) / t) (𝓝[>] 0) (𝓝 L) := by
    have := (hasDerivWithinAt_iff_tendsto_slope' Set.self_notMem_Ioi).mp hD
    convert this using 1
    funext t
    exact (hslope t).symm
  refine ⟨L, ?_, ?_, ?_⟩
  · unfold directionalDeriv
    apply Filter.Tendsto.limUnder_eq
    have h2 : Filter.Tendsto (fun t => ((((f (x + t • d) - f x) / t : ℝ)) : EReal)) (𝓝[>] 0)
        (𝓝 (L : EReal)) :=
      (continuous_coe_real_ereal.tendsto L).comp htend
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    show _ = ((↑(f (x + t • d)) - ↑(f x)) / ↑t : EReal)
    rw [EReal.coe_div, EReal.coe_sub]
  · intro τ hτ
    have := hgφ.le_slope_of_hasDerivWithinAt_Ioi (Set.mem_univ 0) (Set.mem_univ τ) hτ hD
    rwa [hslope] at this
  · intro c hc
    exact ge_of_tendsto htend (by filter_upwards [self_mem_nhdsWithin] with t ht using hc t ht)

lemma aux_grad_ineq {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) {y : E}
    (hy : DifferentiableAt ℝ f y) (v : E) :
    f y + inner ℝ (gradient f y) v ≤ f (y + v) := by
  have hφ := aux_convexOn_line hf y v
  have hderiv : HasDerivAt (fun t : ℝ => f (y + t • v)) (inner ℝ (gradient f y) v) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => y + t • v) v 0 := by
      simpa using ((hasDerivAt_id (0:ℝ)).smul_const v).const_add y
    have h2 : HasFDerivAt f (fderiv ℝ f y) (y + (0:ℝ) • v) := by simpa using hy.hasFDerivAt
    have := h2.comp_hasDerivAt (0:ℝ) h1
    convert this using 1
    simp [gradient, InnerProductSpace.toDual_symm_apply]
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hderiv
  rw [slope_def_field] at this
  simp at this
  linarith

lemma aux_dense {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) :
    Dense {y : E | DifferentiableAt ℝ f y} := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  rw [dense_iff_inter_open]
  rintro U hU ⟨z, hz⟩
  obtain ⟨K, t, ht, hlip⟩ := hf.locallyLipschitz z
  set W := interior t ∩ U with hWdef
  have hW : IsOpen W := isOpen_interior.inter hU
  have hzW : z ∈ W := ⟨mem_interior_iff_mem_nhds.mpr ht, hz⟩
  have hlipW : LipschitzOnWith K f W := hlip.mono (Set.inter_subset_left.trans interior_subset)
  have hae := hlipW.ae_differentiableWithinAt_of_mem (μ := (Measure.addHaar : Measure E))
  by_contra hcon
  have : (Measure.addHaar : Measure E) W = 0 := by
    rw [measure_eq_zero_iff_ae_notMem]
    filter_upwards [hae] with y hy hyW
    exact hcon ⟨y, hyW.2, (hy hyW).differentiableAt (hW.mem_nhds hyW)⟩
  exact (hW.measure_pos _ ⟨z, hzW⟩).ne' this

lemma aux_isCompact_convexHull {K : Set E} (hK : IsCompact K) :
    IsCompact (convexHull ℝ K) := by
  rcases K.eq_empty_or_nonempty with rfl | ⟨k₀, hk₀⟩
  · simp
  set N := Module.finrank ℝ E + 1
  let Φ : (Fin N → ℝ) × (Fin N → E) → E := fun p => ∑ i, p.1 i • p.2 i
  have hΦ : Continuous Φ := by
    simp only [Φ]
    fun_prop
  have hD : IsCompact (stdSimplex ℝ (Fin N) ×ˢ Set.univ.pi (fun _ : Fin N => K)) :=
    (isCompact_stdSimplex _).prod (isCompact_univ_pi fun _ => hK)
  suffices h : convexHull ℝ K = Φ '' (stdSimplex ℝ (Fin N) ×ˢ Set.univ.pi (fun _ : Fin N => K)) by
    rw [h]; exact hD.image hΦ
  apply Set.Subset.antisymm
  · intro x hx
    obtain ⟨ι, _, z, w, hzK, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
    have hcard : Fintype.card ι ≤ N :=
      hai.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
    obtain ⟨e⟩ : Nonempty (ι ↪ Fin N) :=
      Function.Embedding.nonempty_of_card_le (by simpa using hcard)
    classical
    refine ⟨(Function.extend e w 0, Function.extend e z (fun _ => k₀)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro j
      dsimp only
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply]; exact (hw0 i).le
      · rw [Function.extend_apply' _ _ _ hj]; simp
    · dsimp only
      rw [← hw1]
      symm
      apply Fintype.sum_of_injective e e.injective
      · intro j hj
        rw [Function.extend_apply' _ _ _ (by simpa using hj)]; simp
      · intro i; rw [e.injective.extend_apply]
    · intro j _
      dsimp only
      by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        rw [e.injective.extend_apply]; exact hzK ⟨i, rfl⟩
      · rw [Function.extend_apply' _ _ _ hj]; exact hk₀
    · simp only [Φ]
      rw [← hx]
      symm
      apply Fintype.sum_of_injective e e.injective
      · intro j hj
        rw [Function.extend_apply' _ _ _ (by simpa using hj)]; simp
      · intro i
        rw [e.injective.extend_apply, e.injective.extend_apply]
  · rintro _ ⟨⟨w, p⟩, ⟨hw, hp⟩, rfl⟩
    exact (convex_convexHull ℝ K).sum_mem (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull ℝ K (hp i (Set.mem_univ _)))

theorem FCA_chap_D_6_3_1
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  let delta_set := {y | DifferentiableAt ℝ f y}
  let lim_set := fun x =>
    {s | ∃ (yk : ℕ → E),
      (∀ k, yk k ∈ delta_set) ∧
      (Filter.Tendsto yk Filter.atTop (𝓝 x)) ∧
      (Filter.Tendsto (fun k => gradient f (yk k))
        Filter.atTop (𝓝 s))}
  ∀ (x : E),
  directionalSubdifferential (liftRealtoEReal f) x =
    convexHull ℝ (lim_set x) := by
  intro delta_set lim_set x
  have hcont : Continuous f := hf_convex.locallyLipschitz.continuous
  have hdense := aux_dense hf_convex
  choose L hLeq hLle hLge using aux_dirDeriv hf_convex x
  have hsub : directionalSubdifferential (liftRealtoEReal f) x = {s | ∀ d, inner ℝ s d ≤ L d} := by
    ext s
    simp only [directionalSubdifferential, Set.mem_setOf_eq, hLeq, EReal.coe_le_coe_iff]
  rw [hsub]
  -- local Lipschitz bound near x
  obtain ⟨C, t, ht, hlip⟩ := hf_convex.locallyLipschitz x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp ht
  have hgradbound : ∀ y ∈ Metric.ball x r, DifferentiableAt ℝ f y → ‖gradient f y‖ ≤ C := by
    intro y hy _
    have : ‖fderiv ℝ f y‖ ≤ C :=
      norm_fderiv_le_of_lipschitzOn ℝ (Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds hy) hball) hlip
    simpa [gradient] using this
  -- characterization of lim_set by epsilons
  have hchar : ∀ s, s ∈ lim_set x ↔ ∀ ε > 0, ∃ y, DifferentiableAt ℝ f y ∧ dist y x < ε ∧
      dist (gradient f y) s < ε := by
    intro s
    constructor
    · rintro ⟨yk, hyk, hlim, hglim⟩ ε hε
      obtain ⟨k, hk1, hk2⟩ := ((hlim.eventually (Metric.ball_mem_nhds x hε)).and
        (hglim.eventually (Metric.ball_mem_nhds s hε))).exists
      exact ⟨yk k, hyk k, hk1, hk2⟩
    · intro h
      choose! g hg using h
      refine ⟨fun k => g (1 / ((k:ℝ) + 1)), fun k => (hg _ Nat.one_div_pos_of_nat).1, ?_, ?_⟩
      · rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun _ => dist_nonneg) (fun k => (hg _ Nat.one_div_pos_of_nat).2.1.le) ?_
        exact tendsto_one_div_add_atTop_nhds_zero_nat
      · rw [tendsto_iff_dist_tendsto_zero]
        refine squeeze_zero (fun _ => dist_nonneg) (fun k => (hg _ Nat.one_div_pos_of_nat).2.2.le) ?_
        exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- S(x) ⊆ subdifferential: subgradient inequality in the limit
  have hS_sub : ∀ s ∈ lim_set x, ∀ z, f x + inner ℝ s (z - x) ≤ f z := by
    rintro s ⟨yk, hyk, hlim, hglim⟩ z
    have h1 : ∀ k, f (yk k) + inner ℝ (gradient f (yk k)) (z - yk k) ≤ f z := by
      intro k
      have := aux_grad_ineq hf_convex (hyk k) (z - yk k)
      simpa using this
    have h2 : Filter.Tendsto (fun k => f (yk k) + inner ℝ (gradient f (yk k)) (z - yk k))
        Filter.atTop (𝓝 (f x + inner ℝ s (z - x))) := by
      apply Filter.Tendsto.add ((hcont.tendsto x).comp hlim)
      apply Filter.Tendsto.inner hglim
      exact tendsto_const_nhds.sub hlim
    exact le_of_tendsto' h2 h1
  have hsubgrad : ∀ s, (∀ z, f x + inner ℝ s (z - x) ≤ f z) → ∀ d, inner ℝ s d ≤ L d := by
    intro s hs d
    apply hLge d
    intro τ hτ
    have := hs (x + τ • d)
    rw [le_div_iff₀ hτ]
    simp [real_inner_smul_right] at this
    linarith
  -- main step (B)
  have hB : ∀ d, ∃ s ∈ lim_set x, L d ≤ inner ℝ s d := by
    intro d
    have key : ∀ τ : ℝ, 0 < τ → ∃ y, DifferentiableAt ℝ f y ∧ dist y x < τ * (1 + ‖d‖) ∧
        L d - τ ≤ inner ℝ (gradient f y) d := by
      intro τ hτ
      set a := x + τ • d with ha_def
      set h := τ / 2 with hh_def
      have hh : 0 < h := by positivity
      have e1 : a - h • d = x + h • d := by
        rw [ha_def, hh_def]; module
      have hmid : h * L d ≤ f a - f (a - h • d) := by
        have hq := hLle d h hh
        have hconv : f (x + h • d) ≤ (1/2 : ℝ) • f x + (1/2 : ℝ) • f a := by
          have := hf_convex.2 (Set.mem_univ x) (Set.mem_univ a) (by norm_num : (0:ℝ) ≤ 1/2)
            (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
          convert this using 2
          rw [ha_def, hh_def]; module
        rw [le_div_iff₀ hh] at hq
        rw [e1]
        simp only [smul_eq_mul] at hconv
        linarith
      have hcontg : Continuous (fun y => f y - f (y - h • d)) := by
        fun_prop
      obtain ⟨ρ, hρ, hρball⟩ := Metric.continuous_iff.mp hcontg a (h * τ) (by positivity)
      obtain ⟨y, hya, hyΔ⟩ := Metric.dense_iff.mp hdense a (min ρ τ) (lt_min hρ hτ)
      rw [Metric.mem_ball] at hya
      refine ⟨y, hyΔ, ?_, ?_⟩
      · calc dist y x ≤ dist y a + dist a x := dist_triangle _ _ _
          _ < τ + τ * ‖d‖ := by
            apply add_lt_add_of_lt_of_le
            · exact lt_of_lt_of_le hya (min_le_right _ _)
            · rw [ha_def, dist_eq_norm]; simp [norm_smul, abs_of_pos hτ]
          _ = τ * (1 + ‖d‖) := by ring
      · have hg := aux_grad_ineq hf_convex hyΔ (-(h • d))
        have hclose := hρball y (lt_of_lt_of_le hya (min_le_left _ _))
        rw [Real.dist_eq, abs_lt] at hclose
        rw [inner_neg_right, real_inner_smul_right, ← sub_eq_add_neg, ← sub_eq_add_neg y] at hg
        have h4 : h * (L d - τ) ≤ h * inner ℝ (gradient f y) d := by
          nlinarith [hclose.1, hmid, hg]
        exact le_of_mul_le_mul_left h4 hh
    choose! yk hyk using key
    set y : ℕ → E := fun k => yk (1 / ((k:ℝ) + 1)) with hy_def
    have hpos : ∀ k : ℕ, (0:ℝ) < 1 / ((k:ℝ) + 1) := fun k => Nat.one_div_pos_of_nat
    have hyΔ : ∀ k, DifferentiableAt ℝ f (y k) := fun k => (hyk _ (hpos k)).1
    have hylim : Filter.Tendsto y Filter.atTop (𝓝 x) := by
      rw [tendsto_iff_dist_tendsto_zero]
      refine squeeze_zero (fun _ => dist_nonneg) (fun k => (hyk _ (hpos k)).2.1.le) ?_
      have := (tendsto_one_div_add_atTop_nhds_zero_nat).mul_const (1 + ‖d‖)
      simpa using this
    have hfreq : ∃ᶠ k in Filter.atTop, gradient f (y k) ∈ Metric.closedBall (0:E) C := by
      apply Filter.Eventually.frequently
      filter_upwards [hylim.eventually (Metric.ball_mem_nhds x hr)] with k hk
      rw [mem_closedBall_zero_iff]
      exact hgradbound _ hk (hyΔ k)
    obtain ⟨s, -, ψ, hψ, hψlim⟩ :=
      tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hfreq
    refine ⟨s, ⟨y ∘ ψ, fun k => hyΔ (ψ k), hylim.comp hψ.tendsto_atTop, hψlim⟩, ?_⟩
    have hlim2 : Filter.Tendsto (fun k => inner ℝ (gradient f (y (ψ k))) d + 1 / ((ψ k : ℝ) + 1))
        Filter.atTop (𝓝 (inner ℝ s d + 0)) := by
      apply Filter.Tendsto.add
      · exact Filter.Tendsto.inner hψlim tendsto_const_nhds
      · exact tendsto_one_div_add_atTop_nhds_zero_nat.comp hψ.tendsto_atTop
    rw [add_zero] at hlim2
    apply ge_of_tendsto' hlim2
    intro k
    have := (hyk _ (hpos (ψ k))).2.2
    linarith
  -- S(x) compact
  have hS_closed : IsClosed (lim_set x) := by
    apply isClosed_of_closure_subset
    intro s hs
    rw [hchar]
    intro ε hε
    obtain ⟨s', hs'S, hss'⟩ := Metric.mem_closure_iff.mp hs (ε / 2) (by positivity)
    obtain ⟨y, hy, hyx, hys'⟩ := (hchar s').mp hs'S (ε / 2) (by positivity)
    refine ⟨y, hy, by linarith, ?_⟩
    calc dist (gradient f y) s ≤ dist (gradient f y) s' + dist s' s := dist_triangle _ _ _
      _ < ε / 2 + ε / 2 := by rw [dist_comm s' s]; exact add_lt_add hys' hss'
      _ = ε := by ring
  have hS_bdd : Bornology.IsBounded (lim_set x) := by
    apply (Metric.isBounded_closedBall (x := (0:E)) (r := (C:ℝ))).subset
    rintro s ⟨yk, hyk, hlim, hglim⟩
    rw [mem_closedBall_zero_iff]
    apply le_of_tendsto ((continuous_norm.tendsto s).comp hglim)
    filter_upwards [hlim.eventually (Metric.ball_mem_nhds x hr)] with k hk
    exact hgradbound _ hk (hyk k)
  have hS_cpt : IsCompact (lim_set x) := Metric.isCompact_of_isClosed_isBounded hS_closed hS_bdd
  have hconv_cpt := aux_isCompact_convexHull hS_cpt
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hns
    obtain ⟨φ', u, hφ1, hφ2⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hconv_cpt.isClosed hns
    set d := (InnerProductSpace.toDual ℝ E).symm φ'
    have hφd : ∀ v, φ' v = inner ℝ d v := by
      intro v; simp [d, InnerProductSpace.toDual_symm_apply]
    obtain ⟨s', hs'S, hs'L⟩ := hB d
    have h1 := hφ1 s' (subset_convexHull ℝ _ hs'S)
    have h2 : inner ℝ s d ≤ L d := hs d
    rw [hφd, real_inner_comm] at h1 hφ2
    linarith
  · apply convexHull_min
    · intro s hs
      exact hsubgrad s (hS_sub s hs)
    · intro s1 hs1 s2 hs2 a b ha hb hab d
      simp only [Set.mem_setOf_eq] at hs1 hs2 ⊢
      rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
      have h1 := mul_le_mul_of_nonneg_left (hs1 d) ha
      have h2 := mul_le_mul_of_nonneg_left (hs2 d) hb
      have h3 : a * L d + b * L d = L d := by rw [← add_mul, hab, one_mul]
      linarith

end FCA_chap_D_6_3_1
