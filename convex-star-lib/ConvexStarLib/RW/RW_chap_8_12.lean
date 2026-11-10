import ConvexStarLib.Defs

/-!
# `RW_chap_8_12`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_12`, so the main result is `RW_chap_8_12.RW_chap_8_12`.
-/

namespace RW_chap_8_12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma RW812_conv_ineq {f : E → EReal} (hf : ConvexEReal f) {x y : E} {a b : ℝ}
    (hx : f x ≤ a) (hy : f y ≤ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (x + t • (y - x)) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hf' : Convex ℝ (epigraph f) := hf
  have hmem := hf' (show (x, a) ∈ epigraph f from hx) (show (y, b) ∈ epigraph f from hy)
    (sub_nonneg.2 ht1) ht0 (by ring)
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hmem
  have heq : x + t • (y - x) = (1 - t) • x + t • y := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [heq]; exact hmem

lemma RW812_key_limit {x d : E} {r : E → ℝ} (hr : r =o[𝓝 x] (fun z => ‖z - x‖))
    {V : Set E} (hV : V ∈ 𝓝 x) {c e : ℝ}
    (h : ∀ t : ℝ, 0 < t → t < 1 → x + t • d ∈ V → t * c + r (x + t • d) ≤ t * e) :
    c ≤ e := by
  by_contra hce
  push_neg at hce
  set δ := c - e with hδ
  have hδpos : 0 < δ := by linarith
  set ε := δ / (2 * (‖d‖ + 1)) with hε
  have hεpos : 0 < ε := by positivity
  have hbound := hr.def hεpos
  have htend : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝[>] (0:ℝ)) (𝓝 x) := by
    have : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 (0:ℝ)) (𝓝 (x + (0:ℝ) • d)) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev := (htend.eventually (Filter.inter_mem hV hbound)).and (Ioo_mem_nhdsGT one_pos)
  obtain ⟨t, ⟨htV, htb⟩, ht0, ht1⟩ := hev.exists
  have h1 := h t ht0 ht1 htV
  simp only [Set.mem_setOf_eq, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    abs_norm, abs_of_pos ht0] at htb
  have h2 : -(ε * (t * ‖d‖)) ≤ r (x + t • d) := by
    have := neg_abs_le (r (x + t • d)); linarith
  have h3 : t * δ ≤ t * (ε * ‖d‖) := by rw [hδ]; nlinarith
  have h4 : δ ≤ ε * ‖d‖ := le_of_mul_le_mul_left h3 ht0
  have h5 : ε * ‖d‖ < δ := by
    rw [hε, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith [norm_nonneg d]
  linarith

lemma RW812_regular_global {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ z, ⊥ < f z)
    {x v : E} (hv : IsRegularSubgradientAt f x v) (y : E) :
    f x + ((inner ℝ v (y - x) : ℝ) : EReal) ≤ f y := by
  obtain ⟨hxb, hxt, r, hr, V, hV, hVr⟩ := hv
  rcases eq_or_ne (f y) ⊤ with hy | hy
  · rw [hy]; exact le_top
  set a := (f x).toReal with ha
  set b := (f y).toReal with hb
  have hfx : f x = (a : EReal) := (EReal.coe_toReal hxt.ne hxb.ne').symm
  have hfy : f y = (b : EReal) := (EReal.coe_toReal hy (hbot y).ne').symm
  have key : inner ℝ v (y - x) ≤ b - a := by
    apply RW812_key_limit hr hV
    intro t ht0 ht1 htV
    have h1 := hVr _ htV
    have h2 := RW812_conv_ineq hf hfx.le hfy.le ht0.le ht1.le
    have h3 := h1.trans h2
    rw [hfx, ← EReal.coe_add, EReal.coe_le_coe_iff] at h3
    simp only [add_sub_cancel_left, inner_smul_right] at h3
    linarith
  rw [hfx, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

lemma RW812_regular_normal_convex {C : Set E} (hC : Convex ℝ C) {x v : E}
    (hv : IsRegularNormalAt C x v) : ∀ y ∈ C, inner ℝ v (y - x) ≤ 0 := by
  obtain ⟨hx, r, hr, V, hV, hVr⟩ := hv
  intro y hy
  apply RW812_key_limit hr.neg_left hV
  intro t ht0 ht1 htV
  have h1 := hVr _ htV (hC.add_smul_sub_mem hx hy ⟨ht0.le, ht1.le⟩)
  simp only [add_sub_cancel_left, inner_smul_right] at h1
  simp only [mul_zero]
  linarith

lemma RW812_effDom_convex {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ z, ⊥ < f z) :
    Convex ℝ (effDom f) := by
  intro x hx y hy a b ha hb hab
  have hx2 : f x < ⊤ := hx
  have hy2 : f y < ⊤ := hy
  have hx' : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hx2.ne (hbot x).ne').symm
  have hy' : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hy2.ne (hbot y).ne').symm
  have hf' : Convex ℝ (epigraph f) := hf
  have hmem := hf' (show (x, (f x).toReal) ∈ epigraph f from hx'.le)
    (show (y, (f y).toReal) ∈ epigraph f from hy'.le) ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hmem
  exact lt_of_le_of_lt hmem (EReal.coe_lt_top _)

lemma RW812_convex_to_regular {f : E → EReal} {x s : E} (hxb : ⊥ < f x) (hxt : f x < ⊤)
    (hs : s ∈ convexSubdifferential f x) : IsRegularSubgradientAt f x s := by
  refine ⟨hxb, hxt, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem, ?_⟩
  intro z _
  simpa using hs z

lemma RW812_regular_to_sub {f : E → EReal} {x v : E} (hv : IsRegularSubgradientAt f x v) :
    IsSubgradientAt f x v :=
  ⟨hv.1, hv.2.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => hv⟩

lemma RW812_sub_to_convex {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ z, ⊥ < f z)
    {x v : E} (hv : IsSubgradientAt f x v) : v ∈ convexSubdifferential f x := by
  obtain ⟨hxb, hxt, xs, vs, hxs, hfxs, hvs, hreg⟩ := hv
  intro y
  have h1 : ∀ n, f (xs n) + ((inner ℝ (vs n) (y - xs n) : ℝ) : EReal) ≤ f y :=
    fun n => RW812_regular_global hf hbot (hreg n) y
  have hinner : Filter.Tendsto (fun n => inner ℝ (vs n) (y - xs n)) Filter.atTop
      (𝓝 (inner ℝ v (y - x))) :=
    hvs.inner (tendsto_const_nhds.sub hxs)
  have hinner' := (continuous_coe_real_ereal.tendsto _).comp hinner
  have h2 : Filter.Tendsto (fun n => f (xs n) + ((inner ℝ (vs n) (y - xs n) : ℝ) : EReal))
      Filter.atTop (𝓝 (f x + ((inner ℝ v (y - x) : ℝ) : EReal))) :=
    (EReal.continuousAt_add (p := (f x, ((inner ℝ v (y - x) : ℝ) : EReal)))
      (Or.inl hxt.ne) (Or.inl hxb.ne')).tendsto.comp (hfxs.prodMk_nhds hinner')
  exact le_of_tendsto' h2 h1

lemma RW812_horizon_sub_normal {f : E → EReal} (hf : ConvexEReal f) (hbot : ∀ z, ⊥ < f z)
    {x : E} (hxt : f x < ⊤) :
    horizonSubdifferential f x ⊆ convexNormalCone x (effDom f) := by
  intro v hv
  obtain ⟨hxb, -, xs, vs, l, hxs, hfxs, hl, hlv, hreg⟩ := hv
  intro y hy
  have hyt : f y < ⊤ := hy
  set b := (f y).toReal with hb
  have hfy : f y = (b : EReal) := (EReal.coe_toReal hyt.ne (hbot y).ne').symm
  have hfxn : ∀ n, f (xs n) = (((f (xs n)).toReal : ℝ) : EReal) := fun n =>
    (EReal.coe_toReal (hreg n).2.1.ne (hreg n).1.ne').symm
  have hlpos : ∀ᶠ n in Filter.atTop, 0 < l n := hl.eventually self_mem_nhdsWithin
  have h1 : ∀ᶠ n in Filter.atTop,
      l n * (f (xs n)).toReal + inner ℝ (l n • vs n) (y - xs n) ≤ l n * b := by
    filter_upwards [hlpos] with n hn
    have := RW812_regular_global hf hbot (hreg n) y
    rw [hfxn n, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    rw [real_inner_smul_left]
    nlinarith
  have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
  have ha : Filter.Tendsto (fun n => (f (xs n)).toReal) Filter.atTop (𝓝 (f x).toReal) :=
    (EReal.tendsto_toReal hxt.ne hxb.ne').comp hfxs
  have hL : Filter.Tendsto
      (fun n => l n * (f (xs n)).toReal + inner ℝ (l n • vs n) (y - xs n)) Filter.atTop
      (𝓝 (0 * (f x).toReal + inner ℝ v (y - x))) :=
    (hl0.mul ha).add (hlv.inner (tendsto_const_nhds.sub hxs))
  have hR : Filter.Tendsto (fun n => l n * b) Filter.atTop (𝓝 (0 * b)) := hl0.mul_const b
  have := le_of_tendsto_of_tendsto hL hR h1
  simp only [zero_mul, zero_add] at this
  exact this

lemma RW812_normal_cone {C : Set E} (hC : Convex ℝ C) {x : E} (hx : x ∈ C) :
    normalCone C x = convexNormalCone x C := by
  ext v
  constructor
  · rintro ⟨xs, vs, hxs, hvs, hreg⟩
    intro y hy
    have h1 : ∀ n, inner ℝ (vs n) (y - xs n) ≤ 0 := fun n =>
      RW812_regular_normal_convex hC (hreg n) y hy
    exact le_of_tendsto' (hvs.inner (tendsto_const_nhds.sub hxs)) h1
  · intro hv
    refine ⟨fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_⟩
    refine ⟨hx, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem, ?_⟩
    intro z _ hz
    exact hv z hz

lemma RW812_lsc_part {f : E → EReal} (hbot : ∀ z, ⊥ < f z)
    {x_bar : E} (hxt : f x_bar < ⊤) (hl : LocalLscAt f x_bar) :
    convexNormalCone x_bar (effDom f) ⊆ horizonSubdifferential f x_bar := by
  obtain ⟨-, -, ε, hε⟩ := hl
  set a := (f x_bar).toReal with ha_def
  have hfa : f x_bar = (a : EReal) := (EReal.coe_toReal hxt.ne (hbot x_bar).ne').symm
  have hεpos : 0 < ε := (hε (a + ε) (by rw [hfa, EReal.coe_add])).1
  have hclosed : ∀ α : ℝ, α ≤ a + ε →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ α} := by
    intro α hα
    exact (hε α (by rw [hfa, ← EReal.coe_add]; exact EReal.coe_le_coe_iff.2 hα)).2
  intro v hv
  set S := {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ a} with hS_def
  have hSclosed : IsClosed S := hclosed a (by linarith)
  have hScompact : IsCompact S :=
    (isCompact_closedBall x_bar ε).of_isClosed_subset hSclosed (fun x hx => hx.1)
  have hxS : x_bar ∈ S := ⟨Metric.mem_closedBall_self hεpos.le, hfa.le⟩
  set g : E → ℝ := fun x => (f x).toReal with hg_def
  have hfS : ∀ x ∈ S, f x = ((g x : ℝ) : EReal) := fun x hx =>
    (EReal.coe_toReal (ne_top_of_le_ne_top (EReal.coe_ne_top a) hx.2) (hbot x).ne').symm
  have hgS : ∀ x ∈ S, g x ≤ a := by
    intro x hx
    have := hx.2
    rw [hfS x hx] at this
    exact EReal.coe_le_coe_iff.1 this
  have hlsc : LowerSemicontinuousOn g S := by
    intro x hx y hy
    have hyα : y ≤ a + ε := by linarith [hgS x hx]
    have hT := hclosed y hyα
    have hxT : x ∉ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ y} := by
      rintro ⟨-, h⟩
      rw [hfS x hx, EReal.coe_le_coe_iff] at h
      linarith
    have hmem : {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ y}ᶜ ∈ 𝓝[S] x :=
      mem_nhdsWithin_of_mem_nhds (hT.isOpen_compl.mem_nhds hxT)
    filter_upwards [hmem, self_mem_nhdsWithin] with z hz hzS
    have : ¬ f z ≤ y := fun h => hz ⟨hzS.1, h⟩
    rw [hfS z hzS, EReal.coe_le_coe_iff] at this
    linarith
  obtain ⟨xm, hxmS, hxm⟩ := hlsc.exists_isMinOn ⟨x_bar, hxS⟩ hScompact
  set c := x_bar + v with hc
  have hmin : ∀ n : ℕ, ∃ xn ∈ S, ∀ z ∈ S,
      g xn + ((n:ℝ) + 1) / 2 * ‖xn - c‖ ^ 2 ≤ g z + ((n:ℝ) + 1) / 2 * ‖z - c‖ ^ 2 := by
    intro n
    have hq : Continuous (fun x : E => ((n:ℝ) + 1) / 2 * ‖x - c‖ ^ 2) := by fun_prop
    obtain ⟨xn, hxnS, hxn⟩ := (hlsc.add (hq.lowerSemicontinuous.lowerSemicontinuousOn S)).exists_isMinOn
      ⟨x_bar, hxS⟩ hScompact
    exact ⟨xn, hxnS, fun z hz => isMinOn_iff.1 hxn z hz⟩
  choose xs hxsS hxsmin using hmin
  have hdom : ∀ x ∈ S, x ∈ effDom f := fun x hx => lt_of_le_of_lt hx.2 (EReal.coe_lt_top a)
  have hga : g x_bar = a := rfl
  have hxc : ‖x_bar - c‖ = ‖v‖ := by
    rw [hc, sub_add_cancel_left, norm_neg]
  have hexp : ∀ z : E, ‖z - c‖ ^ 2 = ‖z - x_bar‖ ^ 2 - 2 * inner ℝ (z - x_bar) v + ‖v‖ ^ 2 := by
    intro z
    rw [← norm_sub_sq_real, hc, sub_add_eq_sub_sub]
  have hest : ∀ n : ℕ, g (xs n) + ((n:ℝ)+1)/2 * ‖xs n - x_bar‖ ^ 2 ≤ a := by
    intro n
    have h1 := hxsmin n x_bar hxS
    have h4 : inner ℝ (xs n - x_bar) v ≤ 0 := by
      rw [real_inner_comm]; exact hv _ (hdom _ (hxsS n))
    rw [hxc, hexp, hga] at h1
    have hk : (0:ℝ) ≤ ((n:ℝ)+1)/2 := by positivity
    have h5 := mul_nonneg hk (neg_nonneg.2 h4)
    nlinarith
  have hm : ∀ n, g xm ≤ g (xs n) := fun n => isMinOn_iff.1 hxm _ (hxsS n)
  have hma : g xm ≤ a := isMinOn_iff.1 hxm _ hxS
  have hxs_tend : Filter.Tendsto xs Filter.atTop (𝓝 x_bar) := by
    rw [Metric.tendsto_atTop]
    intro η hη
    obtain ⟨N, hN⟩ := exists_nat_gt (2 * (a - g xm) / η ^ 2)
    refine ⟨N, fun n hn => ?_⟩
    rw [dist_eq_norm]
    have h1 := hest n
    have h2 := hm n
    have h3 : ((n:ℝ)+1) * ‖xs n - x_bar‖ ^ 2 ≤ 2 * (a - g xm) := by linarith
    have h4 : (N:ℝ) ≤ n := by exact_mod_cast hn
    have hη2 : 0 < η ^ 2 := by positivity
    have h5 : 2 * (a - g xm) < ((n:ℝ) + 1) * η ^ 2 := by
      rw [div_lt_iff₀ hη2] at hN; nlinarith
    have h6 : ‖xs n - x_bar‖ ^ 2 < η ^ 2 := by
      by_contra hcon; push_neg at hcon
      have : ((n:ℝ) + 1) * η ^ 2 ≤ ((n:ℝ)+1) * ‖xs n - x_bar‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hcon (by positivity)
      linarith
    nlinarith [norm_nonneg (xs n - x_bar)]
  have hxs_within : Filter.Tendsto xs Filter.atTop (𝓝[S] x_bar) :=
    tendsto_nhdsWithin_iff.2 ⟨hxs_tend, Filter.Eventually.of_forall hxsS⟩
  have hg_tend : Filter.Tendsto (fun n => g (xs n)) Filter.atTop (𝓝 a) := by
    rw [tendsto_order]
    constructor
    · intro β hβ
      exact hxs_within.eventually (hlsc x_bar hxS β hβ)
    · intro β hβ
      exact Filter.Eventually.of_forall (fun n => lt_of_le_of_lt (hgS _ (hxsS n)) hβ)
  have hf_tend : Filter.Tendsto (fun n => f (xs n)) Filter.atTop (𝓝 (f x_bar)) := by
    have : (fun n => f (xs n)) = (fun n => ((g (xs n) : ℝ) : EReal)) :=
      funext fun n => hfS _ (hxsS n)
    rw [this, hfa]
    exact (continuous_coe_real_ereal.tendsto a).comp hg_tend
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1
    (hxs_tend.eventually (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hεpos)))
  have hreg : ∀ n, N ≤ n → IsRegularSubgradientAt f (xs n) (((n:ℝ)+1) • (c - xs n)) := by
    intro n hn
    have hxnS := hxsS n
    refine ⟨hbot _, lt_of_le_of_lt hxnS.2 (EReal.coe_lt_top a),
      fun z => -(((n:ℝ)+1)/2 * ‖z - xs n‖ ^ 2), ?_, Metric.ball x_bar ε,
      Metric.isOpen_ball.mem_nhds (hN n hn), ?_⟩
    · have := ((Asymptotics.isLittleO_pow_sub_pow_sub (xs n)
        (show 1 < 2 by norm_num)).const_mul_left (((n:ℝ)+1)/2)).neg_left
      simpa only [pow_one] using this
    · intro z hz
      have hzB : z ∈ Metric.closedBall x_bar ε := Metric.ball_subset_closedBall hz
      rcases eq_or_ne (f z) ⊤ with hzt | hzt
      · rw [hzt]; exact le_top
      have hfz : f z = ((g z : ℝ) : EReal) := (EReal.coe_toReal hzt (hbot z).ne').symm
      have hcomp : g (xs n) + ((n:ℝ)+1)/2 * ‖xs n - c‖ ^ 2
          ≤ g z + ((n:ℝ)+1)/2 * ‖z - c‖ ^ 2 := by
        by_cases hzS : z ∈ S
        · exact hxsmin n z hzS
        · have hza : a < g z := by
            by_contra hcon; push_neg at hcon
            exact hzS ⟨hzB, by rw [hfz]; exact EReal.coe_le_coe_iff.2 hcon⟩
          have h1 := hxsmin n x_bar hxS
          have h4 : inner ℝ (z - x_bar) v ≤ 0 := by
            rw [real_inner_comm]; exact hv _ (lt_of_le_of_ne le_top hzt : f z < ⊤)
          rw [hxc, hga] at h1
          rw [hexp z]
          have hk : (0:ℝ) ≤ ((n:ℝ)+1)/2 := by positivity
          have h5 : 0 ≤ ((n:ℝ)+1)/2 * (‖z - x_bar‖ ^ 2 - 2 * inner ℝ (z - x_bar) v) :=
            mul_nonneg hk (by nlinarith [sq_nonneg ‖z - x_bar‖])
          nlinarith
      have hid : ‖z - c‖ ^ 2 = ‖z - xs n‖ ^ 2 + 2 * inner ℝ (z - xs n) (xs n - c)
          + ‖xs n - c‖ ^ 2 := by
        rw [← norm_add_sq_real, sub_add_sub_cancel]
      have hinner : inner ℝ (((n:ℝ)+1) • (c - xs n)) (z - xs n)
          = -(((n:ℝ)+1) * inner ℝ (z - xs n) (xs n - c)) := by
        have : c - xs n = -(xs n - c) := (neg_sub _ _).symm
        rw [this, real_inner_smul_left, inner_neg_left, real_inner_comm]
        ring
      rw [hfz, hfS _ hxnS, ← EReal.coe_add, EReal.coe_le_coe_iff, hinner]
      rw [hid] at hcomp
      nlinarith
  refine ⟨hbot x_bar, hxt, fun n => xs (n + N),
    fun n => (((n + N : ℕ) : ℝ) + 1) • (c - xs (n + N)),
    fun n => 1 / (((n + N : ℕ) : ℝ) + 1), ?_, ?_, ?_, ?_, ?_⟩
  · exact hxs_tend.comp (Filter.tendsto_add_atTop_nat N)
  · exact hf_tend.comp (Filter.tendsto_add_atTop_nat N)
  · have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h1 := h0.comp (Filter.tendsto_add_atTop_nat N)
    refine tendsto_nhdsWithin_iff.2 ⟨h1, Filter.Eventually.of_forall fun n => ?_⟩
    simp only [Set.mem_Ioi]; positivity
  · have : (fun n : ℕ => (1 / (((n + N : ℕ) : ℝ) + 1)) •
        ((((n + N : ℕ) : ℝ) + 1) • (c - xs (n + N)))) = fun n => c - xs (n + N) := by
      funext n
      rw [smul_smul, one_div, inv_mul_cancel₀ (by positivity), one_smul]
    rw [this]
    have h2 : c - x_bar = v := by rw [hc, add_sub_cancel_left]
    rw [← h2]
    exact tendsto_const_nhds.sub (hxs_tend.comp (Filter.tendsto_add_atTop_nat N))
  · intro n
    exact hreg (n + N) (Nat.le_add_left N n)

theorem RW_chap_8_12
  (f : E → EReal)
  (x_bar : E)
  (hx_bar : x_bar ∈ effDom f)
  (hf_convex : ConvexEReal f)
  (hf_proper : IsProper f) :
  subdifferential f x_bar = regularSubdifferential f x_bar ∧
  subdifferential f x_bar = convexSubdifferential f x_bar ∧
  horizonSubdifferential f x_bar ⊆ convexNormalCone x_bar (effDom f) ∧
  normalCone (effDom f) x_bar = convexNormalCone x_bar (effDom f) ∧
  (LocalLscAt f x_bar →
    horizonSubdifferential f x_bar = convexNormalCone x_bar (effDom f)) ∧
  (Set.Nonempty (subdifferential f x_bar) →
    (horizonSubdifferential f x_bar = convexNormalCone x_bar (effDom f)) ∧
    (horizonSubdifferential f x_bar = horizonCone (regularSubdifferential f x_bar))) := by
  have hbot := hf_proper.1
  have hxt : f x_bar < ⊤ := hx_bar
  have hxb : ⊥ < f x_bar := hbot x_bar
  have hdomconv := RW812_effDom_convex hf_convex hbot
  have h_sub_conv : subdifferential f x_bar ⊆ convexSubdifferential f x_bar :=
    fun v hv => RW812_sub_to_convex hf_convex hbot hv
  have h_conv_reg : convexSubdifferential f x_bar ⊆ regularSubdifferential f x_bar :=
    fun v hv => RW812_convex_to_regular hxb hxt hv
  have h_reg_sub : regularSubdifferential f x_bar ⊆ subdifferential f x_bar :=
    fun v hv => RW812_regular_to_sub hv
  have h1 : subdifferential f x_bar = regularSubdifferential f x_bar :=
    Set.Subset.antisymm (h_sub_conv.trans h_conv_reg) h_reg_sub
  have h2 : subdifferential f x_bar = convexSubdifferential f x_bar :=
    Set.Subset.antisymm h_sub_conv (h_conv_reg.trans h_reg_sub)
  have h3 := RW812_horizon_sub_normal hf_convex hbot hxt
  have h4 := RW812_normal_cone hdomconv hx_bar
  have h6 : Set.Nonempty (subdifferential f x_bar) →
      convexNormalCone x_bar (effDom f) ⊆
        horizonSubdifferential f x_bar ∩ horizonCone (regularSubdifferential f x_bar) := by
    rintro ⟨w, hw⟩ v hv
    have hwc : w ∈ convexSubdifferential f x_bar := h_sub_conv hw
    have hmem : ∀ n : ℕ, w + ((n:ℝ)+1) • v ∈ regularSubdifferential f x_bar := by
      intro n
      apply h_conv_reg
      intro y
      rcases eq_or_ne (f y) ⊤ with hy | hy
      · rw [hy]; exact le_top
      have hyd : y ∈ effDom f := (lt_of_le_of_ne le_top hy : f y < ⊤)
      have hw1 : f y ≥ f x_bar + ((inner ℝ w (y - x_bar) : ℝ) : EReal) := hwc y
      have hv1 : inner ℝ v (y - x_bar) ≤ 0 := hv y hyd
      have hle : inner ℝ (w + ((n:ℝ)+1) • v) (y - x_bar) ≤ inner ℝ w (y - x_bar) := by
        rw [inner_add_left, real_inner_smul_left]
        have hk : (0:ℝ) ≤ (n:ℝ)+1 := by positivity
        nlinarith
      exact le_trans (add_le_add (le_refl _) (EReal.coe_le_coe_iff.2 hle)) hw1
    have hl : Filter.Tendsto (fun n : ℕ => 1 / ((n:ℝ) + 1)) Filter.atTop (𝓝[>] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
        Filter.Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity⟩
    have hlim : Filter.Tendsto (fun n : ℕ => (1 / ((n:ℝ) + 1)) • (w + ((n:ℝ)+1) • v))
        Filter.atTop (𝓝 v) := by
      have : (fun n : ℕ => (1 / ((n:ℝ) + 1)) • (w + ((n:ℝ)+1) • v))
          = fun n : ℕ => (1 / ((n:ℝ) + 1)) • w + v := by
        funext n
        rw [smul_add, smul_smul, one_div, inv_mul_cancel₀ (by positivity), one_smul]
      rw [this]
      have h0 : Filter.Tendsto (fun n : ℕ => (1 / ((n:ℝ) + 1)) • w) Filter.atTop
          (𝓝 ((0:ℝ) • w)) :=
        (tendsto_one_div_add_atTop_nhds_zero_nat).smul_const w
      rw [zero_smul] at h0
      simpa using h0.add_const v
    exact ⟨⟨hxb, hxt, fun _ => x_bar, fun n => w + ((n:ℝ)+1) • v, fun n => 1 / ((n:ℝ) + 1),
      tendsto_const_nhds, tendsto_const_nhds, hl, hlim, fun n => hmem n⟩,
      fun n => w + ((n:ℝ)+1) • v, fun n => 1 / ((n:ℝ) + 1), hmem, hl, hlim⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · intro hl
    exact Set.Subset.antisymm h3 (RW812_lsc_part hbot hxt hl)
  · intro hne
    have h6' := h6 hne
    have hA : horizonSubdifferential f x_bar = convexNormalCone x_bar (effDom f) :=
      Set.Subset.antisymm h3 (fun v hv => (h6' hv).1)
    refine ⟨hA, Set.Subset.antisymm (fun v hv => (h6' (h3 hv)).2) ?_⟩
    rintro u ⟨us, l, hus, hl, hlu⟩
    exact ⟨hxb, hxt, fun _ => x_bar, us, l, tendsto_const_nhds, tendsto_const_nhds, hl, hlu, hus⟩

end RW_chap_8_12
