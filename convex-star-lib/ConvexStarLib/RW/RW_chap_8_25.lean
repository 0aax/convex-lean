import ConvexStarLib.Defs

/-!
# `RW_chap_8_25`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_25` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_25`, so the main result is `RW_chap_8_25.RW_chap_8_25`.
-/

namespace RW_chap_8_25

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem RW_chap_8_25
  (h : E → EReal)
  (D : Set E)
  (w : E)
  (hh_proper : IsProper h)
  (hh_lsc : LowerSemicontinuous h)
  (hh_sublinear : IsSublinearRW h)
  (hD_rep : ∀ (w : E), h w = supportFunction D w)
  (hD_closed : IsClosed D)
  (hD_convex : Convex ℝ D)
  (hw : w ∈ effDom h) :
  subdifferential h w =
    {v : E | v ∈ D ∧ supportFunction D w = (((inner ℝ v w) : ℝ) : EReal)} ∧
  subdifferential h w =
    {v : E | v ∈ D ∧ w ∈ normalCone D v} := by
  -- key analytic lemma: a first-order inequality bounded by a little-o remainder forces `a ≤ 0`
  have key : ∀ (x d : E) (r : E → ℝ), r =o[𝓝 x] (fun z => ‖z - x‖) → ∀ V ∈ 𝓝 x, ∀ a : ℝ,
      (∀ t : ℝ, 0 < t → t ≤ 1 → x + t • d ∈ V → t * a ≤ r (x + t • d)) → a ≤ 0 := by
    intro x d r hr V hV a hineq
    by_contra ha
    push_neg at ha
    have hd1 : 0 < ‖d‖ + 1 := by positivity
    set ε := a / (‖d‖ + 1) with hε_def
    have hε : 0 < ε := div_pos ha hd1
    have hεd : ε * ‖d‖ < a := by
      have : ε * (‖d‖ + 1) = a := div_mul_cancel₀ a hd1.ne'
      nlinarith
    have hcont : Filter.Tendsto (fun t : ℝ => x + t • d) (𝓝 0) (𝓝 x) := by
      have : Continuous (fun t : ℝ => x + t • d) := by fun_prop
      simpa using this.tendsto 0
    have h1 : ∀ᶠ t in 𝓝 (0:ℝ), x + t • d ∈ V := hcont hV
    have h2 : ∀ᶠ t in 𝓝 (0:ℝ), t ≤ 1 := eventually_le_nhds one_pos
    have h3 : ∀ᶠ t in 𝓝 (0:ℝ), ‖r (x + t • d)‖ ≤ ε * ‖x + t • d - x‖ := by
      filter_upwards [(hr.comp_tendsto hcont).def hε] with t ht
      simpa using ht
    have h4 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t := self_mem_nhdsWithin
    obtain ⟨t, ⟨⟨htV, ht1⟩, htr⟩, ht0⟩ :=
      ((((h1.and h2).and h3).filter_mono nhdsWithin_le_nhds).and h4).exists
    have hineq' := hineq t ht0 ht1 htV
    have hnorm : ‖x + t • d - x‖ = t * ‖d‖ := by
      rw [add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht0.le]
    rw [hnorm] at htr
    have hr_le : r (x + t • d) ≤ ‖r (x + t • d)‖ := Real.le_norm_self _
    nlinarith
  -- a regular subgradient of a convex function is a global (convex-analysis) subgradient
  have regSub : ∀ (f : E → EReal), (∀ x, ⊥ < f x) → ConvexEReal f → ∀ x v : E,
      IsRegularSubgradientAt f x v → ∀ y : E, f x + ((inner ℝ v (y - x) : ℝ) : EReal) ≤ f y := by
    intro f hf_bot hconv x v hv y
    obtain ⟨hxbot, hxtop, r, hr, V, hV, hineq⟩ := hv
    rcases eq_or_ne (f y) ⊤ with hy | hy
    · rw [hy]; exact le_top
    have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hy (hf_bot y).ne').symm
    set c := (f x).toReal
    set b := (f y).toReal
    rw [hfx, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff]
    have hkey := key x (y - x) (fun z => - r z) hr.neg_left V hV (inner ℝ v (y - x) - (b - c)) ?_
    · linarith
    intro t ht0 ht1 htV
    have h1 := hineq _ htV
    have hxe : (x, c) ∈ epigraph f := by
      show f x ≤ (c : EReal)
      rw [← hfx]
    have hye : (y, b) ∈ epigraph f := by
      show f y ≤ (b : EReal)
      rw [← hfy]
    have hmem : (x + t • (y - x), (1 - t) * c + t * b) ∈ epigraph f := by
      have := hconv hxe hye (sub_nonneg.mpr ht1) ht0.le (by ring)
      convert this using 1
      ext
      · simp only [Prod.fst_add, Prod.smul_fst]
        module
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
    have h2 : f (x + t • (y - x)) ≤ (((1 - t) * c + t * b : ℝ) : EReal) := hmem
    rw [hfx, ← EReal.coe_add] at h1
    have h3 := EReal.coe_le_coe_iff.mp (h1.trans h2)
    rw [add_sub_cancel_left, real_inner_smul_right] at h3
    show t * (inner ℝ v (y - x) - (b - c)) ≤ - r (x + t • (y - x))
    linarith
  -- a regular normal to a convex set is a global normal
  have regNormal : ∀ (C : Set E), Convex ℝ C → ∀ x v : E, IsRegularNormalAt C x v →
      ∀ y ∈ C, inner ℝ v (y - x) ≤ 0 := by
    intro C hC x v hv y hy
    obtain ⟨hx, r, hr, V, hV, hineq⟩ := hv
    apply key x (y - x) r hr V hV
    intro t ht0 ht1 htV
    have hmem : x + t • (y - x) ∈ C := by
      have := hC hx hy (sub_nonneg.mpr ht1) ht0.le (by ring)
      convert this using 1
      module
    have := hineq _ htV hmem
    rwa [add_sub_cancel_left, real_inner_smul_right] at this
  have hbot : ∀ x, ⊥ < h x := hh_proper.1
  have hhom := hh_sublinear.1.2
  have hconv : ConvexEReal h := hh_sublinear.2
  -- h 0 = 0
  have h0 : h 0 = 0 := by
    have h0top : h 0 < ⊤ := hh_sublinear.1.1
    have h0eq : h 0 = ((h 0).toReal : EReal) := (EReal.coe_toReal h0top.ne (hbot 0).ne').symm
    set c := (h 0).toReal
    have := hhom 0 2 two_pos
    rw [smul_zero, h0eq, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at this
    have hc : c = 0 := by linarith
    rw [h0eq, hc, EReal.coe_zero]
  -- regular subgradients of h lie in D and are exposed by the point
  have claim : ∀ x v : E, IsRegularSubgradientAt h x v →
      v ∈ D ∧ h x = ((inner ℝ v x : ℝ) : EReal) := by
    intro x v hv
    have hxbot := hv.1
    have hxtop := hv.2.1
    have hglob := regSub h hbot hconv x v hv
    have hfx : h x = ((h x).toReal : EReal) := (EReal.coe_toReal hxtop.ne hxbot.ne').symm
    set c := (h x).toReal with hc
    have e1 := hglob 0
    rw [h0, hfx, ← EReal.coe_add, ← EReal.coe_zero, EReal.coe_le_coe_iff, zero_sub,
      inner_neg_right] at e1
    have e2 := hglob ((2:ℝ) • x)
    rw [hhom x 2 two_pos, hfx, ← EReal.coe_add, ← EReal.coe_mul, EReal.coe_le_coe_iff] at e2
    have hsub : (2:ℝ) • x - x = x := by module
    rw [hsub] at e2
    have hcv : c = inner ℝ v x := by linarith
    have hge : ∀ y, ((inner ℝ v y : ℝ) : EReal) ≤ h y := by
      intro y
      have := hglob y
      rw [hfx, ← EReal.coe_add, inner_sub_right, hcv] at this
      simpa using this
    refine ⟨?_, by rw [hfx, hcv]⟩
    by_contra hvD
    obtain ⟨f, u, hfD, hfv⟩ := geometric_hahn_banach_closed_point hD_convex hD_closed hvD
    set z := (InnerProductSpace.toDual ℝ E).symm f
    have hz : ∀ a, inner ℝ a z = f a := by
      intro a
      rw [real_inner_comm]
      exact InnerProductSpace.toDual_symm_apply
    have hσ : supportFunction D z ≤ (u : EReal) := by
      unfold supportFunction
      apply sSup_le
      rintro _ ⟨a, ha, rfl⟩
      show ((inner ℝ a z : ℝ) : EReal) ≤ (u : EReal)
      rw [EReal.coe_le_coe_iff, hz]
      exact (hfD a ha).le
    have h5 := hge z
    rw [hD_rep z, hz] at h5
    have h6 := EReal.coe_le_coe_iff.mp (h5.trans hσ)
    linarith
  have part1 : subdifferential h w =
      {v : E | v ∈ D ∧ supportFunction D w = (((inner ℝ v w) : ℝ) : EReal)} := by
    ext v
    simp only [subdifferential, Set.mem_setOf_eq]
    constructor
    · rintro ⟨_, _, x, vseq, hx, hfx, hv, hreg⟩
      have hmem : ∀ n, vseq n ∈ D := fun n => (claim _ _ (hreg n)).1
      have heq : ∀ n, h (x n) = ((inner ℝ (vseq n) (x n) : ℝ) : EReal) :=
        fun n => (claim _ _ (hreg n)).2
      refine ⟨hD_closed.mem_of_tendsto hv (Filter.Eventually.of_forall hmem), ?_⟩
      rw [← hD_rep w]
      have hlim : Filter.Tendsto (fun n => h (x n)) Filter.atTop
          (𝓝 ((inner ℝ v w : ℝ) : EReal)) := by
        simp_rw [heq]
        exact (continuous_coe_real_ereal.tendsto _).comp (hv.inner hx)
      exact tendsto_nhds_unique hfx hlim
    · rintro ⟨hvD, hσ⟩
      have hhw : h w = ((inner ℝ v w : ℝ) : EReal) := by rw [hD_rep]; exact hσ
      refine ⟨hbot w, hw, fun _ => w, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
        tendsto_const_nhds, fun _ => ?_⟩
      refine ⟨hbot w, hw, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ,
        Filter.univ_mem, fun x _ => ?_⟩
      rw [hhw, ← EReal.coe_add, hD_rep x]
      unfold supportFunction
      have : inner ℝ v w + (inner ℝ v (x - w) + 0) = inner ℝ v x := by
        rw [inner_sub_right]; ring
      rw [this]
      exact le_sSup ⟨v, hvD, rfl⟩
  have part2 : {v : E | v ∈ D ∧ supportFunction D w = (((inner ℝ v w) : ℝ) : EReal)} =
      {v : E | v ∈ D ∧ w ∈ normalCone D v} := by
    ext v
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hvD, hσ⟩
      refine ⟨hvD, ?_⟩
      have hle : ∀ d ∈ D, inner ℝ d w ≤ inner ℝ v w := by
        intro d hd
        have : ((inner ℝ d w : ℝ) : EReal) ≤ supportFunction D w := le_sSup ⟨d, hd, rfl⟩
        rw [hσ, EReal.coe_le_coe_iff] at this
        exact this
      refine ⟨fun _ => v, fun _ => w, tendsto_const_nhds, tendsto_const_nhds, fun _ => ?_⟩
      refine ⟨hvD, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem,
        fun x _ hx => ?_⟩
      show inner ℝ w (x - v) ≤ 0
      rw [inner_sub_right]
      have e1 := real_inner_comm w x
      have e2 := real_inner_comm w v
      linarith [hle x hx]
    · rintro ⟨hvD, x, wseq, hx, hwseq, hreg⟩
      refine ⟨hvD, le_antisymm ?_ (le_sSup ⟨v, hvD, rfl⟩)⟩
      unfold supportFunction
      apply sSup_le
      rintro _ ⟨d, hd, rfl⟩
      show ((inner ℝ d w : ℝ) : EReal) ≤ ((inner ℝ v w : ℝ) : EReal)
      rw [EReal.coe_le_coe_iff]
      have hn : ∀ n, inner ℝ (wseq n) (d - x n) ≤ 0 :=
        fun n => regNormal D hD_convex (x n) (wseq n) (hreg n) d hd
      have hlim : Filter.Tendsto (fun n => inner ℝ (wseq n) (d - x n)) Filter.atTop
          (𝓝 (inner ℝ w (d - v))) :=
        hwseq.inner (tendsto_const_nhds.sub hx)
      have h7 := le_of_tendsto' hlim hn
      rw [inner_sub_right] at h7
      have e1 := real_inner_comm w d
      have e2 := real_inner_comm w v
      linarith
  exact ⟨part1, part1.trans part2⟩

end RW_chap_8_25
