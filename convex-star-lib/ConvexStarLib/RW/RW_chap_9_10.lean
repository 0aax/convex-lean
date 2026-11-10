import ConvexStarLib.Defs

/-!
# `RW_chap_9_10`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_9_10` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_9_10`, so the main result is `RW_chap_9_10.RW_chap_9_10`.
-/

namespace RW_chap_9_10

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma RW_chap_9_10_sup_diff_le {κ : Type*} [Nonempty κ] (a b : κ → ℝ) (c : ℝ)
    (ha : BddAbove (Set.range a)) (hb : BddAbove (Set.range b))
    (h : ∀ i, |a i - b i| ≤ c) :
    |sSup (Set.range a) - sSup (Set.range b)| ≤ c := by
  rw [abs_le]
  constructor
  · have : sSup (Set.range b) ≤ sSup (Set.range a) + c := by
      apply csSup_le (Set.range_nonempty b)
      rintro _ ⟨i, rfl⟩
      have h1 := (abs_le.mp (h i)).1
      have h2 : a i ≤ sSup (Set.range a) := le_csSup ha ⟨i, rfl⟩
      linarith
    linarith
  · have : sSup (Set.range a) ≤ sSup (Set.range b) + c := by
      apply csSup_le (Set.range_nonempty a)
      rintro _ ⟨i, rfl⟩
      have h1 := (abs_le.mp (h i)).2
      have h2 : b i ≤ sSup (Set.range b) := le_csSup hb ⟨i, rfl⟩
      linarith
    linarith

lemma RW_chap_9_10_inf_diff_le {κ : Type*} [Nonempty κ] (a b : κ → ℝ) (c : ℝ)
    (ha : BddBelow (Set.range a)) (hb : BddBelow (Set.range b))
    (h : ∀ i, |a i - b i| ≤ c) :
    |sInf (Set.range a) - sInf (Set.range b)| ≤ c := by
  rw [abs_le]
  constructor
  · have : sInf (Set.range b) - c ≤ sInf (Set.range a) := by
      apply le_csInf (Set.range_nonempty a)
      rintro _ ⟨i, rfl⟩
      have h1 := (abs_le.mp (h i)).1
      have h2 : sInf (Set.range b) ≤ b i := csInf_le hb ⟨i, rfl⟩
      linarith
    linarith
  · have : sInf (Set.range a) - c ≤ sInf (Set.range b) := by
      apply le_csInf (Set.range_nonempty b)
      rintro _ ⟨i, rfl⟩
      have h1 := (abs_le.mp (h i)).2
      have h2 : sInf (Set.range a) ≤ a i := csInf_le ha ⟨i, rfl⟩
      linarith
    linarith

lemma RW_chap_9_10_lipModulus_le_of_eventually {u : E → ℝ} {x : E} {L : ℝ}
    (h : ∀ᶠ p in (𝓝 x ×ˢ 𝓝 x), |u p.2 - u p.1| ≤ L * ‖p.2 - p.1‖) :
    lipModulus u x ≤ (L : EReal) := by
  unfold lipModulus lipModulusRel
  rw [nhdsWithin_univ]
  refine Filter.limsup_le_of_le (h := ?_)
  rw [Filter.eventually_inf_principal]
  filter_upwards [h] with p hp hne
  have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
  rw [EReal.coe_le_coe_iff, Real.norm_eq_abs, div_le_iff₀ hpos]
  exact hp

lemma RW_chap_9_10_eventually_of_lipModulus_lt {u : E → ℝ} {x : E} {L : ℝ}
    (h : lipModulus u x < (L : EReal)) :
    ∀ᶠ p in (𝓝 x ×ˢ 𝓝 x), |u p.2 - u p.1| ≤ L * ‖p.2 - p.1‖ := by
  unfold lipModulus lipModulusRel at h
  rw [nhdsWithin_univ] at h
  have h' := Filter.eventually_lt_of_limsup_lt h
  rw [Filter.eventually_inf_principal] at h'
  filter_upwards [h'] with p hp
  by_cases hne : p.1 = p.2
  · rw [hne]; simp
  · have hpos : 0 < ‖p.2 - p.1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm hne))
    have h2 := hp hne
    rw [EReal.coe_lt_coe_iff, Real.norm_eq_abs, div_lt_iff₀ hpos] at h2
    exact h2.le

lemma RW_chap_9_10_lipModulus_nonneg [Nontrivial E] (u : E → ℝ) (x : E) :
    0 ≤ lipModulus u x := by
  unfold lipModulus lipModulusRel
  rw [nhdsWithin_univ]
  haveI : Filter.NeBot ((𝓝 x ×ˢ 𝓝 x) ⊓ Filter.principal {p : E × E | p.1 ≠ p.2}) := by
    rw [Filter.inf_principal_neBot_iff]
    intro U hU
    obtain ⟨A, hA, B, hB, hAB⟩ := Filter.mem_prod_iff.mp hU
    obtain ⟨y, hyB, hyx⟩ : ∃ y ∈ B, y ≠ x := by
      have hB' : B ∈ 𝓝[≠] x := mem_nhdsWithin_of_mem_nhds hB
      obtain ⟨y, hy⟩ := Filter.nonempty_of_mem (Filter.inter_mem hB' self_mem_nhdsWithin)
      exact ⟨y, hy.1, hy.2⟩
    exact ⟨(x, y), hAB ⟨mem_of_mem_nhds hA, hyB⟩, fun h => hyx h.symm⟩
  exact Filter.le_limsup_of_frequently_le (Filter.Eventually.frequently
    (Filter.Eventually.of_forall fun p =>
      EReal.coe_nonneg.mpr (div_nonneg (norm_nonneg _) (norm_nonneg _))))

lemma RW_chap_9_10_isStrictlyContinuousAt_of_le [Nontrivial E] {u : E → ℝ} {x : E} {S : EReal}
    (h : lipModulus u x ≤ S) (hS : S ≠ ⊤) : IsStrictlyContinuousAt u x := by
  have h0 := RW_chap_9_10_lipModulus_nonneg u x
  refine ⟨(lipModulus u x).toReal, ?_⟩
  rw [EReal.coe_toReal]
  · exact ne_top_of_le_ne_top hS h
  · exact (lt_of_lt_of_le EReal.bot_lt_zero h0).ne'

lemma RW_chap_9_10_lipschitz_of_local {s : Set E} (hs : Convex ℝ s) {h : E → ℝ} {L : ℝ}
    (hloc : ∀ y ∈ s, ∀ᶠ p in (𝓝 y ×ˢ 𝓝 y), |h p.2 - h p.1| ≤ L * ‖p.2 - p.1‖) :
    ∀ p ∈ s, ∀ q ∈ s, h q - h p ≤ L * ‖q - p‖ := by
  intro p hp q hq
  set w : ℝ → ℝ := fun t => h (p + t • (q - p)) with hw
  have hseg : ∀ t ∈ Set.Icc (0:ℝ) 1, p + t • (q - p) ∈ s := fun t ht =>
    hs.add_smul_sub_mem hp hq ht
  have hwloc : ∀ t ∈ Set.Icc (0:ℝ) 1, ∀ᶠ z in 𝓝 t, |w z - w t| ≤ L * ‖q - p‖ * |z - t| := by
    intro t ht
    have h1 := hloc _ (hseg t ht)
    have hcont : Filter.Tendsto (fun z : ℝ => (p + t • (q - p), p + z • (q - p))) (𝓝 t)
        (𝓝 (p + t • (q - p)) ×ˢ 𝓝 (p + t • (q - p))) := by
      rw [← nhds_prod_eq]
      apply Continuous.tendsto' _ _ _ (by simp)
      fun_prop
    filter_upwards [hcont.eventually h1] with z hz
    have e : p + z • (q - p) - (p + t • (q - p)) = (z - t) • (q - p) := by
      rw [sub_smul]; abel
    rw [e, norm_smul, Real.norm_eq_abs] at hz
    calc |w z - w t| = |h (p + z • (q - p)) - h (p + t • (q - p))| := rfl
      _ ≤ L * (|z - t| * ‖q - p‖) := hz
      _ = L * ‖q - p‖ * |z - t| := by ring
  have hwcont : ContinuousOn w (Set.Icc 0 1) := by
    intro t ht
    apply ContinuousAt.continuousWithinAt
    rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Filter.Tendsto (fun z => L * ‖q - p‖ * |z - t|) (𝓝 t) (𝓝 0) := by
      have h2 : Filter.Tendsto (fun z : ℝ => |z - t|) (𝓝 t) (𝓝 0) := by
        have := (Continuous.tendsto (by fun_prop : Continuous fun z : ℝ => |z - t|) t)
        simpa using this
      simpa using h2.const_mul (L * ‖q - p‖)
    apply squeeze_zero' (Filter.Eventually.of_forall (fun z => norm_nonneg _)) _ hlim
    filter_upwards [hwloc t ht] with z hz
    rw [Real.norm_eq_abs]; exact hz
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := w) (a := 0) (b := 1) hwcont
    (B := fun t => w 0 + L * ‖q - p‖ * t) (B' := fun _ => L * ‖q - p‖) (by simp)
    (by fun_prop) ?_ ?_ (Set.right_mem_Icc.mpr zero_le_one)
  · simp only [w, one_smul, zero_smul, add_zero, add_sub_cancel, mul_one] at key
    linarith
  · intro t _
    have := ((hasDerivAt_id t).const_mul (L * ‖q - p‖)).const_add (w 0)
    simpa using this.hasDerivWithinAt
  · intro t ht r hr
    apply Filter.Eventually.frequently
    have h1 : ∀ᶠ z in 𝓝[>] t, |w z - w t| ≤ L * ‖q - p‖ * |z - t| :=
      nhdsWithin_le_nhds (hwloc t (Set.Ico_subset_Icc_self ht))
    filter_upwards [h1, self_mem_nhdsWithin] with z hz hzt
    rw [slope_def_field]
    have hzt' : 0 < z - t := sub_pos.mpr hzt
    rw [div_lt_iff₀ hzt']
    rw [abs_of_pos hzt'] at hz
    calc w z - w t ≤ |w z - w t| := le_abs_self _
      _ ≤ L * ‖q - p‖ * (z - t) := hz
      _ < r * (z - t) := mul_lt_mul_of_pos_right hr hzt'

lemma RW_chap_9_10_part2_uniform {κ : Type*} (O : Set E) (g : κ → E → ℝ) (k : E → ℝ)
    (hO_open : IsOpen O)
    (hk_usc : ∀ x ∈ O, UpperSemicontinuousWithinAt k O x)
    (hg_lip_bound : ∀ x ∈ O, ∀ (i : κ), lipModulus (g i) x ≤ (k x : EReal))
    (x : E) (hx : x ∈ O) (L : ℝ) (hL : k x < L) :
    ∃ δ > 0, ∀ i, ∀ p ∈ Metric.ball x δ, ∀ q ∈ Metric.ball x δ,
      |g i q - g i p| ≤ L * ‖q - p‖ := by
  have h1 : ∀ᶠ y in 𝓝[O] x, k y < L := hk_usc x hx L hL
  rw [hO_open.nhdsWithin_eq hx] at h1
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ O := hO_open.mem_nhds hx
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp (h1.and h2)
  refine ⟨δ, hδ, fun i => ?_⟩
  have hloc : ∀ y ∈ Metric.ball x δ, ∀ᶠ p in (𝓝 y ×ˢ 𝓝 y),
      |g i p.2 - g i p.1| ≤ L * ‖p.2 - p.1‖ := by
    intro y hy
    obtain ⟨hky, hyO⟩ := hball y hy
    apply RW_chap_9_10_eventually_of_lipModulus_lt
    calc lipModulus (g i) y ≤ (k y : EReal) := hg_lip_bound y hyO i
      _ < (L : EReal) := EReal.coe_lt_coe_iff.mpr hky
  intro p hp q hq
  rw [abs_le]
  have hpq := RW_chap_9_10_lipschitz_of_local (convex_ball x δ) hloc p hp q hq
  have hqp := RW_chap_9_10_lipschitz_of_local (convex_ball x δ) hloc q hq p hp
  rw [norm_sub_rev] at hqp
  constructor <;> linarith

lemma RW_chap_9_10_part1_uniform {ι : Type*} [Fintype ι] (f : ι → E → ℝ) (x : E) (L : ℝ)
    (hL : sSup ((fun i => lipModulus (f i) x) '' Set.univ) < (L : EReal)) :
    ∀ᶠ p in (𝓝 x ×ˢ 𝓝 x), ∀ i, |f i p.2 - f i p.1| ≤ L * ‖p.2 - p.1‖ := by
  rw [Filter.eventually_all]
  intro i
  apply RW_chap_9_10_eventually_of_lipModulus_lt
  exact lt_of_le_of_lt (le_sSup (Set.mem_image_of_mem (fun i => lipModulus (f i) x) (Set.mem_univ i))) hL

theorem RW_chap_9_10
  [Nontrivial E]
  {ι κ : Type*}
  [Fintype ι]
  [Nonempty ι]
  [Nonempty κ]
  (O : Set E)
  (f : ι → E → ℝ)
  (g : κ → E → ℝ)
  (k : E → ℝ)
  (hO_open : IsOpen O)
  (hk_usc : ∀ x ∈ O, UpperSemicontinuousWithinAt k O x)
  (hg_lip_bound : ∀ x ∈ O, ∀ (i : κ), lipModulus (g i) x ≤ (k x : EReal)) :
  ((∀ x ∈ O,
      lipModulus (fun y => sSup ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ)) ∧
    (∀ x ∈ O,
      lipModulus (fun y => sInf ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ)) ∧
    (∀ x ∈ O, (∀ (i : ι), IsStrictlyContinuousAt (f i) x) →
      IsStrictlyContinuousAt (fun y => sSup ((fun (i : ι) => f i y) '' Set.univ)) x) ∧
    (∀ x ∈ O, (∀ (i : ι), IsStrictlyContinuousAt (f i) x) →
      IsStrictlyContinuousAt (fun y => sInf ((fun (i : ι) => f i y) '' Set.univ)) x)) ∧
  ((∀ x ∈ O, BddAbove ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sSup ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal)) ∧
    (∀ x ∈ O, BddBelow ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sInf ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal)) ∧
    (∀ x ∈ O, BddAbove ((fun (i : κ) => g i x) '' Set.univ) →
      IsStrictlyContinuousAt (fun y => sSup ((fun (i : κ) => g i y) '' Set.univ)) x) ∧
    (∀ x ∈ O, BddBelow ((fun (i : κ) => g i x) '' Set.univ) →
      IsStrictlyContinuousAt (fun y => sInf ((fun (i : κ) => g i y) '' Set.univ)) x)) := by
  -- Part 1 bounds
  have hA : ∀ x ∈ O,
      lipModulus (fun y => sSup ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ) := by
    intro x _
    rw [← EReal.le_of_forall_lt_iff_le]
    intro L hL
    apply RW_chap_9_10_lipModulus_le_of_eventually
    filter_upwards [RW_chap_9_10_part1_uniform f x L hL] with p hp
    simp only [Set.image_univ]
    exact RW_chap_9_10_sup_diff_le _ _ _ (Set.finite_range _).bddAbove
      (Set.finite_range _).bddAbove (fun i => hp i)
  have hB : ∀ x ∈ O,
      lipModulus (fun y => sInf ((fun (i : ι) => f i y) '' Set.univ)) x
        ≤ sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ) := by
    intro x _
    rw [← EReal.le_of_forall_lt_iff_le]
    intro L hL
    apply RW_chap_9_10_lipModulus_le_of_eventually
    filter_upwards [RW_chap_9_10_part1_uniform f x L hL] with p hp
    simp only [Set.image_univ]
    exact RW_chap_9_10_inf_diff_le _ _ _ (Set.finite_range _).bddBelow
      (Set.finite_range _).bddBelow (fun i => hp i)
  have hfin : ∀ x, (∀ (i : ι), IsStrictlyContinuousAt (f i) x) →
      sSup ((fun (i : ι) => lipModulus (f i) x) '' Set.univ) ≠ ⊤ := by
    intro x hfi
    have hne : ((fun i => lipModulus (f i) x) '' Set.univ).Nonempty :=
      Set.image_nonempty.mpr Set.univ_nonempty
    have hfin' : ((fun i => lipModulus (f i) x) '' Set.univ).Finite := Set.toFinite _
    obtain ⟨i, _, hi⟩ := hne.csSup_mem hfin'
    simp only at hi
    rw [← hi]
    obtain ⟨r, hr⟩ := hfi i
    rw [hr]; exact EReal.coe_ne_top r
  -- Part 2 bounds
  have hE : ∀ x ∈ O, BddAbove ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sSup ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal) := by
    intro x hx hbdd
    rw [← EReal.le_of_forall_lt_iff_le]
    intro L hL
    have hL' : k x < L := EReal.coe_lt_coe_iff.mp hL
    obtain ⟨δ, hδ, hlip⟩ := RW_chap_9_10_part2_uniform O g k hO_open hk_usc hg_lip_bound x hx L hL'
    simp only [Set.image_univ] at hbdd
    have hbdd' : ∀ y ∈ Metric.ball x δ, BddAbove (Set.range fun i => g i y) := by
      intro y hy
      obtain ⟨M, hM⟩ := hbdd
      refine ⟨M + L * ‖y - x‖, ?_⟩
      rintro _ ⟨i, rfl⟩
      have h1 := hlip i x (Metric.mem_ball_self hδ) y hy
      have h2 : g i x ≤ M := hM (Set.mem_range_self i)
      have h3 := (abs_le.mp h1).2
      linarith
    apply RW_chap_9_10_lipModulus_le_of_eventually
    have hball : Metric.ball x δ ×ˢ Metric.ball x δ ∈ 𝓝 x ×ˢ 𝓝 x :=
      Filter.prod_mem_prod (Metric.ball_mem_nhds x hδ) (Metric.ball_mem_nhds x hδ)
    filter_upwards [hball] with p hp
    simp only [Set.image_univ]
    exact RW_chap_9_10_sup_diff_le _ _ _ (hbdd' p.2 hp.2) (hbdd' p.1 hp.1)
      (fun i => hlip i p.1 hp.1 p.2 hp.2)
  have hF : ∀ x ∈ O, BddBelow ((fun (i : κ) => g i x) '' Set.univ) →
      lipModulus (fun y => sInf ((fun (i : κ) => g i y) '' Set.univ)) x ≤ (k x : EReal) := by
    intro x hx hbdd
    rw [← EReal.le_of_forall_lt_iff_le]
    intro L hL
    have hL' : k x < L := EReal.coe_lt_coe_iff.mp hL
    obtain ⟨δ, hδ, hlip⟩ := RW_chap_9_10_part2_uniform O g k hO_open hk_usc hg_lip_bound x hx L hL'
    simp only [Set.image_univ] at hbdd
    have hbdd' : ∀ y ∈ Metric.ball x δ, BddBelow (Set.range fun i => g i y) := by
      intro y hy
      obtain ⟨M, hM⟩ := hbdd
      refine ⟨M - L * ‖y - x‖, ?_⟩
      rintro _ ⟨i, rfl⟩
      have h1 := hlip i x (Metric.mem_ball_self hδ) y hy
      have h2 : M ≤ g i x := hM (Set.mem_range_self i)
      have h3 := (abs_le.mp h1).1
      linarith
    apply RW_chap_9_10_lipModulus_le_of_eventually
    have hball : Metric.ball x δ ×ˢ Metric.ball x δ ∈ 𝓝 x ×ˢ 𝓝 x :=
      Filter.prod_mem_prod (Metric.ball_mem_nhds x hδ) (Metric.ball_mem_nhds x hδ)
    filter_upwards [hball] with p hp
    simp only [Set.image_univ]
    exact RW_chap_9_10_inf_diff_le _ _ _ (hbdd' p.2 hp.2) (hbdd' p.1 hp.1)
      (fun i => hlip i p.1 hp.1 p.2 hp.2)
  refine ⟨⟨hA, hB, ?_, ?_⟩, ⟨hE, hF, ?_, ?_⟩⟩
  · intro x hx hfi
    exact RW_chap_9_10_isStrictlyContinuousAt_of_le (hA x hx) (hfin x hfi)
  · intro x hx hfi
    exact RW_chap_9_10_isStrictlyContinuousAt_of_le (hB x hx) (hfin x hfi)
  · intro x hx hbdd
    exact RW_chap_9_10_isStrictlyContinuousAt_of_le (hE x hx hbdd) (EReal.coe_ne_top _)
  · intro x hx hbdd
    exact RW_chap_9_10_isStrictlyContinuousAt_of_le (hF x hx hbdd) (EReal.coe_ne_top _)

end RW_chap_9_10
