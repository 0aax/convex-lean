import ConvexStarLib.Defs

/-!
# `RW_chap_8_18`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_18` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_18`, so the main result is `RW_chap_8_18.RW_chap_8_18`.
-/

namespace RW_chap_8_18

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma dq_lt_iff (f : E → EReal) (x v : E) (a : ℝ) (ha : f x = (a : EReal)) {τ : ℝ} (hτ : 0 < τ)
    (c : ℝ) :
    differenceQuotient f x v τ < (c : EReal) ↔ f (x + τ • v) < ((a + c * τ : ℝ) : EReal) := by
  unfold differenceQuotient
  rw [ha, EReal.div_lt_iff (by exact_mod_cast hτ) (EReal.coe_ne_top τ),
    EReal.sub_lt_iff (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a)),
    ← EReal.coe_mul, ← EReal.coe_add, add_comm (c * τ) a]


/-- Characterization of `subderivative ≤ β`. -/
lemma sd_le_iff (f : E → EReal) (x w : E) (β : ℝ) :
    subderivative f x w ≤ (β : EReal) ↔
      ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ η : ℝ, 0 < η →
        ∃ τ ∈ Set.Ioo (0:ℝ) η, ∃ v ∈ Metric.closedBall w δ,
          differenceQuotient f x v τ < ((β + ε : ℝ) : EReal) := by
  have hB : (𝓝[>] (0:ℝ) ×ˢ 𝓝 w).HasBasis (fun i : ℝ × ℝ => 0 < i.1 ∧ 0 < i.2)
      (fun i => Set.Ioo (0:ℝ) i.1 ×ˢ Metric.closedBall w i.2) :=
    (nhdsGT_basis (0:ℝ)).prod Metric.nhds_basis_closedBall
  unfold subderivative
  constructor
  · intro h ε hε δ hδ η hη
    have hlt : Filter.liminf (fun p : ℝ × E => differenceQuotient f x p.2 p.1)
        (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) < ((β + ε : ℝ) : EReal) :=
      lt_of_le_of_lt h (by exact_mod_cast (by linarith : β < β + ε))
    have hfr := Filter.frequently_lt_of_liminf_lt (by isBoundedDefault) hlt
    rw [hB.frequently_iff] at hfr
    obtain ⟨p, hp, hpu⟩ := hfr (η, δ) ⟨hη, hδ⟩
    exact ⟨p.1, hp.1, p.2, hp.2, hpu⟩
  · intro h
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : β < z := by exact_mod_cast hz
    apply Filter.liminf_le_of_frequently_le'
    rw [hB.frequently_iff]
    rintro ⟨η, δ⟩ ⟨hη, hδ⟩
    obtain ⟨τ, hτ, v, hv, hlt⟩ := h (z - β) (by linarith) δ hδ η hη
    refine ⟨(τ, v), ⟨hτ, hv⟩, ?_⟩
    have : β + (z - β) = z := by ring
    rw [this] at hlt
    exact hlt.le


/-- Characterization of `regularSubderivative ≤ β`. -/
lemma rsd_le_iff (f : E → EReal) (x_bar w : E) (β : ℝ) :
    regularSubderivative f x_bar w ≤ (β : EReal) ↔
      ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ → ∀ᶠ p in fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ),
        ∃ v ∈ Metric.closedBall w δ, delta f p.1 p.2 v < ((β + ε : ℝ) : EReal) := by
  set L := fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ) with hL
  set S : ℝ → E × ℝ → EReal :=
    fun δ p => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ) with hS
  set H : ℝ → EReal := fun δ => Filter.limsup (S δ) L with hH
  have hrsd : regularSubderivative f x_bar w = Filter.limsup H (𝓝[>] (0:ℝ)) := rfl
  have hmono : ∀ δ' δ : ℝ, δ' ≤ δ → H δ ≤ H δ' := by
    intro δ' δ hle
    exact Filter.limsup_le_limsup (Filter.Eventually.of_forall (fun p => sInf_le_sInf
      (Set.image_mono (Metric.closedBall_subset_closedBall hle))))
  rw [hrsd]
  constructor
  · intro h ε hε δ hδ
    have h1 : H δ ≤ Filter.limsup H (𝓝[>] (0:ℝ)) := by
      apply Filter.le_limsup_of_frequently_le'
      apply Filter.Eventually.frequently
      filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ'
      exact hmono δ' δ hδ'.2.le
    have hlt : H δ < ((β + ε : ℝ) : EReal) :=
      lt_of_le_of_lt (h1.trans h) (by exact_mod_cast (by linarith : β < β + ε))
    have hev := Filter.eventually_lt_of_limsup_lt hlt
    filter_upwards [hev] with p hp
    obtain ⟨y, ⟨v, hv, rfl⟩, hy⟩ := sInf_lt_iff.mp hp
    exact ⟨v, hv, hy⟩
  · intro h
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [self_mem_nhdsWithin] with δ (hδ : 0 < δ)
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : β < z := by exact_mod_cast hz
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    filter_upwards [h (z - β) (by linarith) δ hδ] with p ⟨v, hv, hlt⟩
    have : β + (z - β) = z := by ring
    rw [this] at hlt
    exact (sInf_le (Set.mem_image_of_mem _ hv)).trans hlt.le


/-- Basis-style description of eventually along `fApproach`. -/
lemma fApproach_eventually_iff (f : E → EReal) (x_bar : E) (m : ℝ) (hm : f x_bar = (m : EReal))
    (P : E → Prop) :
    (∀ᶠ y in fApproach f x_bar, P y) ↔
      ∃ r : ℝ, 0 < r ∧ ∀ y, dist y x_bar < r → f y ≠ ⊤ → f y ≠ ⊥ → |(f y).toReal - m| < r → P y := by
  constructor
  · intro hP
    rw [fApproach, hm, Filter.eventually_inf] at hP
    obtain ⟨s, hs, t, ht, hst⟩ := hP
    obtain ⟨r1, hr1, hball⟩ := Metric.mem_nhds_iff.mp hs
    obtain ⟨V, hV, hVt⟩ := Filter.mem_comap.mp ht
    have hV' : (fun c : ℝ => (c : EReal)) ⁻¹' V ∈ 𝓝 m :=
      continuous_coe_real_ereal.continuousAt.preimage_mem_nhds hV
    obtain ⟨r2, hr2, hball2⟩ := Metric.mem_nhds_iff.mp hV'
    refine ⟨min r1 r2, lt_min hr1 hr2, fun y hy hyt hyb hyr => hst y ⟨?_, ?_⟩⟩
    · apply hball
      rw [Metric.mem_ball]
      exact lt_of_lt_of_le hy (min_le_left _ _)
    · apply hVt
      show f y ∈ V
      have h1 : (f y).toReal ∈ Metric.ball m r2 := by
        rw [Metric.mem_ball, Real.dist_eq]
        exact lt_of_lt_of_le hyr (min_le_right _ _)
      have h2 := hball2 h1
      simp only [Set.mem_preimage] at h2
      rwa [EReal.coe_toReal hyt hyb] at h2
  · rintro ⟨r, hr, hP⟩
    rw [fApproach, hm]
    have hI : Set.Ioo (((m - r : ℝ)) : EReal) (((m + r : ℝ)) : EReal) ∈ 𝓝 (m : EReal) := by
      apply Ioo_mem_nhds
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
      · exact EReal.coe_lt_coe_iff.mpr (by linarith)
    refine Filter.mem_inf_of_inter (Metric.ball_mem_nhds x_bar hr)
      (Filter.preimage_mem_comap hI) ?_
    rintro y ⟨hy1, hy2, hy3⟩
    rw [Metric.mem_ball] at hy1
    have hyt : f y ≠ ⊤ := ne_top_of_lt hy3
    have hyb : f y ≠ ⊥ := ne_bot_of_gt hy2
    have e : f y = (((f y).toReal : ℝ) : EReal) := (EReal.coe_toReal hyt hyb).symm
    rw [e, EReal.coe_lt_coe_iff] at hy2 hy3
    exact hP y hy1 hyt hyb (abs_sub_lt_iff.mpr ⟨by linarith, by linarith⟩)


lemma locLsc_eventually_gt (f : E → EReal) (x_bar : E) (h : LocalLscAt f x_bar) (c : ℝ)
    (hc : (c : EReal) < f x_bar) :
    ∀ᶠ y in 𝓝 x_bar, (c : EReal) < f y := by
  obtain ⟨hb, ht, ε, hε⟩ := h
  set m := (f x_bar).toReal with hm_def
  have hm : f x_bar = (m : EReal) := (EReal.coe_toReal ht.ne hb.ne').symm
  have hεpos : ε > 0 := by
    have := hε (m - |ε|) (by
      rw [hm, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [neg_abs_le ε])
    exact this.1
  have hc' : (c : EReal) ≤ f x_bar + ε := by
    rw [hm, EReal.coe_lt_coe_iff] at hc
    rw [hm, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  obtain ⟨_, hclosed⟩ := hε c hc'
  have hnot : x_bar ∉ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ c} := by
    rintro ⟨_, hle⟩
    exact absurd hc (not_lt.mpr hle)
  have h1 : {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ c}ᶜ ∈ 𝓝 x_bar :=
    hclosed.isOpen_compl.mem_nhds hnot
  have h2 : Metric.ball x_bar ε ∈ 𝓝 x_bar := Metric.ball_mem_nhds x_bar hεpos
  filter_upwards [h1, h2] with y hy1 hy2
  by_contra hcon
  push_neg at hcon
  exact hy1 ⟨Metric.ball_subset_closedBall hy2, hcon⟩


lemma locLsc_closed (f : E → EReal) (x_bar : E) (m : ℝ) (hm : f x_bar = (m : EReal)) (ε0 : ℝ)
    (hε : ∀ α : ℝ, (α : EReal) ≤ f x_bar + ε0 →
      (ε0 > 0 ∧ IsClosed {x | x ∈ Metric.closedBall x_bar ε0 ∧ f x ≤ α})) :
    IsClosed {p : E × ℝ | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2 ∧
      f p.1 ≤ (p.2 : EReal)} := by
  have hε0 : ε0 > 0 := (hε (m - |ε0|) (by
      rw [hm, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [neg_abs_le ε0])).1
  apply isClosed_of_closure_subset
  intro p hp
  have hD : IsClosed {p : E × ℝ | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2} :=
    (Metric.isClosed_closedBall.preimage continuous_fst).inter
      (isClosed_le continuous_snd continuous_const)
  have hsub : {p : E × ℝ | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2 ∧
      f p.1 ≤ (p.2 : EReal)} ⊆ {p : E × ℝ | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2} :=
    fun q hq => ⟨hq.1, hq.2.1⟩
  have hpD := closure_minimal hsub hD hp
  refine ⟨hpD.1, hpD.2, ?_⟩
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  rw [EReal.coe_lt_coe_iff] at hz
  have hα'le : ((min z (m + ε0) : ℝ) : EReal) ≤ f x_bar + ε0 := by
    rw [hm, ← EReal.coe_add, EReal.coe_le_coe_iff]
    exact min_le_right _ _
  have hS := (hε (min z (m + ε0)) hα'le).2
  have hlt : p.2 < min z (m + ε0) := lt_min hz (by linarith [hpD.2])
  have hopen : IsOpen {q : E × ℝ | q.2 < min z (m + ε0)} :=
    isOpen_lt continuous_snd continuous_const
  have h1 := hopen.inter_closure ⟨hlt, hp⟩
  have h2 : {q : E × ℝ | q.2 < min z (m + ε0)} ∩
      {p : E × ℝ | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2 ∧
        f p.1 ≤ (p.2 : EReal)} ⊆
      Prod.fst ⁻¹' {x | x ∈ Metric.closedBall x_bar ε0 ∧ f x ≤ ((min z (m + ε0) : ℝ) : EReal)} := by
    rintro q ⟨hq1, hq2, hq3, hq4⟩
    refine ⟨hq2, le_trans hq4 ?_⟩
    exact EReal.coe_le_coe_iff.mpr (le_of_lt hq1)
  have h3 := closure_minimal h2 (hS.preimage continuous_fst) h1
  exact le_trans h3.2 (EReal.coe_le_coe_iff.mpr (min_le_left _ _))


/-- Abstract fencing argument (Clarke tangent cone vs. contingent cones). -/
lemma fencing_core {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [ProperSpace X]
    (C : Set X) (hC : IsClosed C) (z0 d : X) (hz0 : z0 ∈ C) (τ κ : ℝ) (hτ : 0 < τ) (hκ : 0 < κ)
    (H : ∀ t ∈ Set.Ico (0:ℝ) τ, ∀ c ∈ C, dist (z0 + t • d) c = Metric.infDist (z0 + t • d) C →
        ∀ η : ℝ, 0 < η → ∃ s ∈ Set.Ioo (0:ℝ) η, ∃ c' ∈ C, ‖c' - (c + s • d)‖ ≤ κ * s) :
    Metric.infDist (z0 + τ • d) C ≤ 2 * κ * τ := by
  set g : ℝ → ℝ := fun t => Metric.infDist (z0 + t • d) C with hg
  have hcont : Continuous g :=
    (Metric.continuous_infDist_pt C).comp (continuous_const.add (continuous_id.smul continuous_const))
  have hg0 : g 0 = 0 := by
    simp only [hg, zero_smul, add_zero]
    exact Metric.infDist_zero_of_mem hz0
  have key := image_le_of_liminf_slope_right_lt_deriv_boundary' (f := g) (f' := fun _ => κ)
    (a := 0) (b := τ) (B := fun t => 2 * κ * t) (B' := fun _ => 2 * κ) hcont.continuousOn ?_
    (by simp [hg0]) (by fun_prop) ?_ ?_
  · exact key ⟨hτ.le, le_rfl⟩
  · -- hf'
    intro t ht r hr
    obtain ⟨c, hcC, hc⟩ := hC.exists_infDist_eq_dist ⟨z0, hz0⟩ (z0 + t • d)
    rw [(nhdsGT_basis t).frequently_iff]
    intro i hi
    obtain ⟨s, ⟨hs0, hsη⟩, c', hc'C, hc'⟩ := H t ht c hcC hc.symm (i - t) (by linarith)
    refine ⟨t + s, ⟨by linarith, by linarith⟩, ?_⟩
    rw [slope_def_field]
    have h1 : g (t + s) ≤ g t + κ * s := by
      simp only [hg]
      calc Metric.infDist (z0 + (t + s) • d) C ≤ dist (z0 + (t + s) • d) c' :=
            Metric.infDist_le_dist_of_mem hc'C
        _ ≤ dist (z0 + t • d) c + ‖c' - (c + s • d)‖ := by
          rw [dist_eq_norm, dist_eq_norm]
          have : z0 + (t + s) • d - c' = (z0 + t • d - c) - (c' - (c + s • d)) := by
            rw [add_smul]; abel
          rw [this]
          exact norm_sub_le _ _
        _ ≤ Metric.infDist (z0 + t • d) C + κ * s := by rw [← hc]; linarith
    have hts : t + s - t = s := by ring
    rw [hts, div_lt_iff₀ hs0]
    have : κ * s < r * s := mul_lt_mul_of_pos_right hr hs0
    linarith
  · intro x _
    simpa using ((hasDerivAt_id x).const_mul (2 * κ)).hasDerivWithinAt
  · intro x _ _
    linarith


lemma posHom_of_scaling (g : E → EReal)
    (h : ∀ t : ℝ, 0 < t → ∀ w : E, ∀ β : ℝ, g w ≤ (β : EReal) → g (t • w) ≤ ((t * β : ℝ) : EReal)) :
    IsERealPosHomogeneous g := by
  intro x t ht
  apply le_antisymm
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have h1 : g x ≤ ((z / t : ℝ) : EReal) := by
      induction hgx : g x using EReal.rec with
      | bot => exact bot_le
      | top => rw [hgx, EReal.coe_mul_top_of_pos ht] at hz; exact absurd hz (not_lt.mpr le_top)
      | coe a =>
        rw [hgx, ← EReal.coe_mul] at hz
        have := EReal.coe_lt_coe_iff.mp hz
        exact EReal.coe_le_coe_iff.mpr (by rw [le_div_iff₀ ht]; linarith)
    have := h t ht x (z / t) h1
    rwa [mul_div_cancel₀ _ ht.ne'] at this
  · rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have h1 := h t⁻¹ (inv_pos.mpr ht) (t • x) z hz.le
    rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h1
    induction hgx : g x using EReal.rec with
    | bot => rw [EReal.coe_mul_bot_of_pos ht]; exact bot_le
    | top => rw [hgx] at h1; exact absurd h1 (not_le.mpr (EReal.coe_lt_top _))
    | coe a =>
      rw [hgx] at h1
      rw [← EReal.coe_mul]
      have := EReal.coe_le_coe_iff.mp h1
      refine EReal.coe_le_coe_iff.mpr ?_
      have h2 : a * t ≤ z := by rwa [le_inv_mul_iff₀ ht, mul_comm] at this
      linarith


lemma rsd_scaling (f : E → EReal) (x_bar : E) :
    ∀ t : ℝ, 0 < t → ∀ w : E, ∀ β : ℝ, regularSubderivative f x_bar w ≤ (β : EReal) →
      regularSubderivative f x_bar (t • w) ≤ ((t * β : ℝ) : EReal) := by
  intro t ht w β hyp
  rw [rsd_le_iff] at hyp ⊢
  intro ε hε δ hδ
  have H := hyp (ε / t) (div_pos hε ht) (δ / t) (div_pos hδ ht)
  have h2 : Tendsto (fun τ : ℝ => τ * t) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have : Tendsto (fun τ : ℝ => τ * t) (𝓝 0) (𝓝 (0 * t)) := tendsto_id.mul_const t
      rw [zero_mul] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact mul_pos hτ ht
  have hφ : Tendsto (Prod.map id (fun τ : ℝ => τ * t))
      (fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ)) (fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ)) :=
    tendsto_id.prodMap h2
  have hτ : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := self_mem_nhdsWithin
  filter_upwards [hφ.eventually H, hτ.prod_inr (fApproach f x_bar)] with p hp hp2
  obtain ⟨u, hu, hlt⟩ := hp
  simp only [Prod.map_fst, Prod.map_snd, id_eq] at hlt
  refine ⟨t • u, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hu ⊢
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht]
    calc t * dist u w ≤ t * (δ / t) := mul_le_mul_of_nonneg_left hu ht.le
      _ = δ := mul_div_cancel₀ _ ht.ne'
  · simp only [delta, differenceQuotient] at hlt ⊢
    have hx : p.1 + p.2 • (t • u) = p.1 + (p.2 * t) • u := by
      rw [smul_smul]
    rw [hx]
    have hτt : (0:EReal) < ((p.2 * t : ℝ) : EReal) := by exact_mod_cast mul_pos hp2 ht
    have hτ' : (0:EReal) < ((p.2 : ℝ) : EReal) := by exact_mod_cast hp2
    rw [EReal.div_lt_iff hτt (EReal.coe_ne_top _)] at hlt
    rw [EReal.div_lt_iff hτ' (EReal.coe_ne_top _)]
    rw [← EReal.coe_mul] at hlt ⊢
    convert hlt using 2
    field_simp


lemma sd_scaling (f : E → EReal) (x : E) :
    ∀ t : ℝ, 0 < t → ∀ w : E, ∀ β : ℝ, subderivative f x w ≤ (β : EReal) →
      subderivative f x (t • w) ≤ ((t * β : ℝ) : EReal) := by
  intro t ht w β hyp
  rw [sd_le_iff] at hyp ⊢
  intro ε hε δ hδ η hη
  obtain ⟨σ, ⟨hσ0, hση⟩, u, hu, hlt⟩ :=
    hyp (ε / t) (div_pos hε ht) (δ / t) (div_pos hδ ht) (η * t) (mul_pos hη ht)
  refine ⟨σ / t, ⟨div_pos hσ0 ht, (div_lt_iff₀ ht).mpr hση⟩, t • u, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hu ⊢
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht]
    calc t * dist u w ≤ t * (δ / t) := mul_le_mul_of_nonneg_left hu ht.le
      _ = δ := mul_div_cancel₀ _ ht.ne'
  · unfold differenceQuotient at hlt ⊢
    have hx : x + (σ / t) • (t • u) = x + σ • u := by
      rw [smul_smul, div_mul_cancel₀ _ ht.ne']
    rw [hx]
    have hσt : (0:EReal) < ((σ / t : ℝ) : EReal) := by exact_mod_cast div_pos hσ0 ht
    have hσ' : (0:EReal) < ((σ : ℝ) : EReal) := by exact_mod_cast hσ0
    rw [EReal.div_lt_iff hσ' (EReal.coe_ne_top _)] at hlt
    rw [EReal.div_lt_iff hσt (EReal.coe_ne_top _)]
    rw [← EReal.coe_mul] at hlt ⊢
    convert hlt using 2
    field_simp


lemma rsd_zero_lt_top (f : E → EReal) (x_bar : E) : regularSubderivative f x_bar 0 < ⊤ := by
  have h0 : regularSubderivative f x_bar 0 ≤ ((0:ℝ) : EReal) := by
    rw [rsd_le_iff]
    intro ε hε δ hδ
    have hτ : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := self_mem_nhdsWithin
    filter_upwards [hτ.prod_inr (fApproach f x_bar)] with p hp
    refine ⟨0, Metric.mem_closedBall_self hδ.le, ?_⟩
    simp only [delta, differenceQuotient, smul_zero, add_zero]
    refine lt_of_le_of_lt (EReal.div_nonpos_of_nonpos_of_nonneg EReal.sub_self_le_zero
      (by exact_mod_cast hp.le)) ?_
    exact_mod_cast (by linarith : (0:ℝ) < 0 + ε)
  exact lt_of_le_of_lt h0 (EReal.coe_lt_top _)


lemma sd_zero_lt_top (f : E → EReal) (x : E) : subderivative f x 0 < ⊤ := by
  have h0 : subderivative f x 0 ≤ ((0:ℝ) : EReal) := by
    rw [sd_le_iff]
    intro ε hε δ hδ η hη
    refine ⟨η / 2, ⟨by linarith, by linarith⟩, 0, Metric.mem_closedBall_self hδ.le, ?_⟩
    simp only [differenceQuotient, smul_zero, add_zero]
    refine lt_of_le_of_lt (EReal.div_nonpos_of_nonpos_of_nonneg EReal.sub_self_le_zero
      (by exact_mod_cast (by linarith : (0:ℝ) ≤ η / 2))) ?_
    exact_mod_cast (by linarith : (0:ℝ) < 0 + ε)
  exact lt_of_le_of_lt h0 (EReal.coe_lt_top _)


lemma rsd_lsc (f : E → EReal) (x_bar : E) : LowerSemicontinuous (regularSubderivative f x_bar) := by
  intro w₀ y hy
  obtain ⟨β, hyβ, hβ⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hnot : ¬ (regularSubderivative f x_bar w₀ ≤ (β : EReal)) := not_le.mpr hβ
  rw [rsd_le_iff] at hnot
  simp only [not_forall] at hnot
  obtain ⟨ε, hε, δ, hδ, hfail⟩ := hnot
  have hball : Metric.ball w₀ (δ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ (by linarith)
  filter_upwards [hball] with w hw
  refine lt_of_lt_of_le hyβ ?_
  by_contra hle
  have hle' : regularSubderivative f x_bar w ≤ (β : EReal) := le_of_lt (not_le.mp hle)
  rw [rsd_le_iff] at hle'
  apply hfail
  filter_upwards [hle' ε hε (δ / 2) (by linarith)] with p hp
  obtain ⟨v, hv, hlt⟩ := hp
  refine ⟨v, ?_, hlt⟩
  rw [Metric.mem_closedBall] at hv ⊢
  rw [Metric.mem_ball] at hw
  calc dist v w₀ ≤ dist v w + dist w w₀ := dist_triangle _ _ _
    _ ≤ δ := by linarith


lemma sd_lsc (f : E → EReal) (x : E) : LowerSemicontinuous (subderivative f x) := by
  intro w₀ y hy
  obtain ⟨β, hyβ, hβ⟩ := EReal.lt_iff_exists_real_btwn.mp hy
  have hnot : ¬ (subderivative f x w₀ ≤ (β : EReal)) := not_le.mpr hβ
  rw [sd_le_iff] at hnot
  simp only [not_forall] at hnot
  obtain ⟨ε, hε, δ, hδ, η, hη, hfail⟩ := hnot
  have hball : Metric.ball w₀ (δ / 2) ∈ 𝓝 w₀ := Metric.ball_mem_nhds w₀ (by linarith)
  filter_upwards [hball] with w hw
  refine lt_of_lt_of_le hyβ ?_
  by_contra hle
  have hle' : subderivative f x w ≤ (β : EReal) := le_of_lt (not_le.mp hle)
  rw [sd_le_iff] at hle'
  apply hfail
  obtain ⟨τ, hτ, v, hv, hlt⟩ := hle' ε hε (δ / 2) (by linarith) η hη
  refine ⟨τ, hτ, v, ?_, hlt⟩
  rw [Metric.mem_closedBall] at hv ⊢
  rw [Metric.mem_ball] at hw
  calc dist v w₀ ≤ dist v w + dist w w₀ := dist_triangle _ _ _
    _ ≤ δ := by linarith


lemma sd_le_rsd (f : E → EReal) (x_bar : E) (w : E) :
    subderivative f x_bar w ≤ regularSubderivative f x_bar w := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro β hβ
  have hle : regularSubderivative f x_bar w ≤ (β : EReal) := le_of_lt hβ
  rw [rsd_le_iff] at hle
  rw [sd_le_iff]
  intro ε hε δ hδ η hη
  have hpure : pure x_bar ≤ fApproach f x_bar := by
    unfold fApproach
    refine le_inf (pure_le_nhds x_bar) ?_
    rw [← Filter.map_le_iff_le_comap, Filter.map_pure]
    exact pure_le_nhds _
  have h1 : ∀ᶠ p in (pure x_bar : Filter E) ×ˢ 𝓝[>] (0:ℝ),
      ∃ v ∈ Metric.closedBall w δ, delta f p.1 p.2 v < ((β + ε : ℝ) : EReal) :=
    Filter.Eventually.filter_mono (Filter.prod_mono hpure le_rfl) (hle ε hε δ hδ)
  rw [Filter.pure_prod, Filter.eventually_map] at h1
  have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo (0:ℝ) η := Ioo_mem_nhdsGT hη
  obtain ⟨τ, ⟨v, hv, hlt⟩, hτ⟩ := (h1.and h2).exists
  exact ⟨τ, hτ, v, hv, hlt⟩


lemma rsd_add (f : E → EReal) (x_bar : E) (hx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hlsc : LowerSemicontinuousAt f x_bar) (w1 w2 : E) (β1 β2 : ℝ)
    (h1 : regularSubderivative f x_bar w1 ≤ (β1 : EReal))
    (h2 : regularSubderivative f x_bar w2 ≤ (β2 : EReal)) :
    regularSubderivative f x_bar (w1 + w2) ≤ ((β1 + β2 : ℝ) : EReal) := by
  obtain ⟨m, hm⟩ : ∃ m : ℝ, f x_bar = (m : EReal) :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal hx.2.ne hx.1.ne').symm⟩
  rw [rsd_le_iff]
  intro ε hε δ hδ
  have hε2 : 0 < ε / 2 := by positivity
  have hδ2 : 0 < δ / 2 := by positivity
  -- unpack h2 into radius form
  have H2 := (rsd_le_iff f x_bar w2 β2).1 h2 (ε / 2) hε2 (δ / 2) hδ2
  rw [Filter.eventually_prod_iff] at H2
  obtain ⟨pa, hpa, pb, hpb, hpab⟩ := H2
  obtain ⟨r1, hr1, hr1P⟩ := (fApproach_eventually_iff f x_bar m hm pa).1 hpa
  obtain ⟨u, hu, hu_sub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hpb
  have hr2 : (0:ℝ) < u := hu
  -- lower semicontinuity
  have hlsc' := lowerSemicontinuousAt_iff.1 hlsc ((m - r1 : ℝ) : EReal)
    (by rw [hm]; exact EReal.coe_lt_coe_iff.2 (by linarith))
  obtain ⟨r', hr', hr'P⟩ := Metric.eventually_nhds_iff.1 hlsc'
  -- h1
  have H1 := (rsd_le_iff f x_bar w1 β1).1 h1 (ε / 2) hε2 (δ / 2) hδ2
  -- choose ρ
  obtain ⟨K, hK_def⟩ : ∃ K : ℝ, K = 1 + (‖w1‖ + δ / 2) + |β1 + ε / 2| := ⟨_, rfl⟩
  have hK : 1 ≤ K := by
    have := norm_nonneg w1
    have := abs_nonneg (β1 + ε / 2)
    linarith
  have hKpos : 0 < K := by linarith
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = min (min r1 u) r' := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hR_def]; exact lt_min (lt_min hr1 hr2) hr'
  have hRr1 : R ≤ r1 := by rw [hR_def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hRu : R ≤ u := by rw [hR_def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hRr' : R ≤ r' := by rw [hR_def]; exact min_le_right _ _
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = R / K := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact div_pos hR hKpos
  have hρK : ρ * K = R := by rw [hρ_def]; field_simp
  have hρR : ρ ≤ R := by rw [hρ_def]; exact div_le_self hR.le hK
  -- eventually-near property
  have HA : ∀ᶠ y in fApproach f x_bar,
      dist y x_bar < ρ ∧ f y ≠ ⊤ ∧ f y ≠ ⊥ ∧ |(f y).toReal - m| < ρ :=
    (fApproach_eventually_iff f x_bar m hm _).2 ⟨ρ, hρ, fun y a b c d => ⟨a, b, c, d⟩⟩
  have HB : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo (0:ℝ) ρ := Ioo_mem_nhdsGT hρ
  filter_upwards [HA.prod_mk HB, H1] with ⟨x, τ⟩ hp hv1
  obtain ⟨⟨hxd, hxt, hxb, hxm⟩, hτ0, hτρ⟩ := hp
  obtain ⟨v1, hv1, hdq1⟩ := hv1
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = (a : EReal) := ⟨(f x).toReal, (EReal.coe_toReal hxt hxb).symm⟩
  have hxm' : |a - m| < ρ := by rw [ha] at hxm; simpa using hxm
  have hf1 : f (x + τ • v1) < ((a + (β1 + ε / 2) * τ : ℝ) : EReal) :=
    (dq_lt_iff f x v1 a ha hτ0 (β1 + ε / 2)).1 hdq1
  have hv1n : ‖v1‖ ≤ ‖w1‖ + δ / 2 := norm_le_of_mem_closedBall hv1
  have hdist' : dist (x + τ • v1) x_bar < R := by
    have h_1 : dist (x + τ • v1) x_bar ≤ dist x x_bar + τ * ‖v1‖ := by
      calc dist (x + τ • v1) x_bar = ‖(x - x_bar) + τ • v1‖ := by
            rw [dist_eq_norm]; congr 1; abel
        _ ≤ ‖x - x_bar‖ + ‖τ • v1‖ := norm_add_le _ _
        _ = dist x x_bar + τ * ‖v1‖ := by
            rw [dist_eq_norm, norm_smul, Real.norm_of_nonneg hτ0.le]
    have h_2 : τ * ‖v1‖ ≤ ρ * (‖w1‖ + δ / 2) := mul_le_mul hτρ.le hv1n (norm_nonneg _) hρ.le
    have h_3 : ρ + ρ * (‖w1‖ + δ / 2) ≤ R := by
      have := mul_nonneg hρ.le (abs_nonneg (β1 + ε / 2))
      rw [← hρK, hK_def]; linarith
    linarith
  -- bounds on f x'
  have hlow : ((m - r1 : ℝ) : EReal) < f (x + τ • v1) := hr'P (lt_of_lt_of_le hdist' hRr')
  have hx't : f (x + τ • v1) ≠ ⊤ := ne_top_of_lt hf1
  have hx'b : f (x + τ • v1) ≠ ⊥ := ne_bot_of_gt hlow
  obtain ⟨a', ha'⟩ : ∃ a' : ℝ, f (x + τ • v1) = (a' : EReal) :=
    ⟨(f (x + τ • v1)).toReal, (EReal.coe_toReal hx't hx'b).symm⟩
  have ha'1 : a' < a + (β1 + ε / 2) * τ := by
    rw [ha'] at hf1; exact EReal.coe_lt_coe_iff.1 hf1
  have ha'2 : m - r1 < a' := by
    rw [ha'] at hlow; exact EReal.coe_lt_coe_iff.1 hlow
  have hbound : (β1 + ε / 2) * τ ≤ |β1 + ε / 2| * ρ :=
    mul_le_mul (le_abs_self _) hτρ.le hτ0.le (abs_nonneg _)
  have ha_m : a - m < ρ := lt_of_le_of_lt (le_abs_self _) hxm'
  have h_4 : ρ + |β1 + ε / 2| * ρ ≤ R := by
    have := mul_nonneg hρ.le (add_nonneg (norm_nonneg w1) hδ2.le)
    rw [← hρK, hK_def]; linarith
  have ha'm : |(f (x + τ • v1)).toReal - m| < r1 := by
    rw [ha', EReal.toReal_coe, abs_lt]; constructor <;> linarith
  have hpbτ : pb τ := hu_sub ⟨hτ0, lt_of_lt_of_le hτρ (hρR.trans hRu)⟩
  obtain ⟨v2, hv2, hdq2⟩ := hpab (hr1P _ (lt_of_lt_of_le hdist' hRr1) hx't hx'b ha'm) hpbτ
  have hf2 : f ((x + τ • v1) + τ • v2) < ((a' + (β2 + ε / 2) * τ : ℝ) : EReal) :=
    (dq_lt_iff f _ v2 a' ha' hτ0 (β2 + ε / 2)).1 hdq2
  refine ⟨v1 + v2, ?_, ?_⟩
  · rw [Metric.mem_closedBall] at hv1 hv2 ⊢
    calc dist (v1 + v2) (w1 + w2) ≤ dist v1 w1 + dist v2 w2 := dist_add_add_le _ _ _ _
      _ ≤ δ / 2 + δ / 2 := add_le_add hv1 hv2
      _ = δ := by ring
  · show differenceQuotient f x (v1 + v2) τ < _
    rw [dq_lt_iff f x (v1 + v2) a ha hτ0 (β1 + β2 + ε)]
    have heq : x + τ • (v1 + v2) = (x + τ • v1) + τ • v2 := by rw [smul_add, add_assoc]
    rw [heq]
    refine lt_of_lt_of_le hf2 (EReal.coe_le_coe_iff.2 ?_)
    linarith


lemma rsd_convex (f : E → EReal) (x_bar : E) (hx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hlsc : LowerSemicontinuousAt f x_bar) : ConvexEReal (regularSubderivative f x_bar) := by
  unfold ConvexEReal
  intro p hp q hq a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
  rcases ha.eq_or_lt with rfl | ha'
  · rw [zero_add] at hab
    subst hab
    simpa using hq
  rcases hb.eq_or_lt with rfl | hb'
  · rw [add_zero] at hab
    subst hab
    simpa using hp
  have h1 := rsd_scaling f x_bar a ha' p.1 p.2 hp
  have h2 := rsd_scaling f x_bar b hb' q.1 q.2 hq
  have h3 := rsd_add f x_bar hx hlsc _ _ _ _ h1 h2
  have e1 : (a • p + b • q).1 = a • p.1 + b • q.1 := rfl
  have e2 : (a • p + b • q).2 = a * p.2 + b * q.2 := rfl
  rw [e1, e2]
  exact h3


lemma epi_forward (f : E → EReal) (x_bar : E) (w : E) (β : ℝ)
    (h : regularSubderivative f x_bar w ≤ (β : EReal)) :
    ∀ W ∈ 𝓝 (w, β), ∀ᶠ x in fApproach f x_bar, ∃ q ∈ epigraph (subderivative f x), q ∈ W := by
  intro W hW
  obtain ⟨R, hR, hball⟩ := Metric.mem_nhds_iff.mp hW
  have hκ : (0:ℝ) < R / 2 := by linarith
  have H := (rsd_le_iff f x_bar w β).mp h (R/2) hκ (R/2) hκ
  have H2 := H.curry
  filter_upwards [H2] with x hx
  obtain ⟨η0, hη0pos, hη0⟩ : ∃ η0 : ℝ, 0 < η0 ∧ ∀ τ ∈ Set.Ioo (0:ℝ) η0,
      ∃ v ∈ Metric.closedBall w (R/2), delta f x τ v < ((β + R/2 : ℝ) : EReal) := by
    obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hx
    exact ⟨u, hu, fun τ hτ => hsub hτ⟩
  set τ : ℕ → ℝ := fun n => (η0 / 2) * (1 / ((n : ℝ) + 1)) with hτdef
  have hτpos : ∀ n, 0 < τ n := fun n => by
    simp only [hτdef]; positivity
  have hτlt : ∀ n, τ n < η0 := fun n => by
    simp only [hτdef]
    have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith [n.cast_nonneg (α := ℝ)]
    have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    nlinarith
  have hτlim : Tendsto τ atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (η0 / 2)
    rw [mul_zero] at this
    exact this
  choose v hv1 hv2 using fun n => hη0 (τ n) ⟨hτpos n, hτlt n⟩
  obtain ⟨wstar, hwstar, ψ, hψ, hlim⟩ := (isCompact_closedBall w (R/2)).tendsto_subseq hv1
  have hsd : subderivative f x wstar ≤ ((β + R/2 : ℝ) : EReal) := by
    rw [sd_le_iff]
    intro ε hε δ hδ η hη
    have e1 : ∀ᶠ n in atTop, (v ∘ ψ) n ∈ Metric.closedBall wstar δ :=
      hlim (Metric.closedBall_mem_nhds wstar hδ)
    have e2 : ∀ᶠ n in atTop, τ (ψ n) < η :=
      (hτlim.comp hψ.tendsto_atTop) (Iio_mem_nhds hη)
    obtain ⟨n, hn1, hn2⟩ := (e1.and e2).exists
    refine ⟨τ (ψ n), ⟨hτpos _, hn2⟩, v (ψ n), hn1, ?_⟩
    calc differenceQuotient f x (v (ψ n)) (τ (ψ n)) = delta f x (τ (ψ n)) (v (ψ n)) := rfl
      _ < ((β + R/2 : ℝ) : EReal) := hv2 (ψ n)
      _ < ((β + R/2 + ε : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  refine ⟨(wstar, β + R/2), hsd, hball ?_⟩
  rw [Metric.mem_ball, Prod.dist_eq]
  refine max_lt ?_ ?_
  · have := Metric.mem_closedBall.mp hwstar
    simp only
    linarith
  · simp only [Real.dist_eq, add_sub_cancel_left]
    rw [abs_of_pos hκ]
    linarith


lemma epi_backward (f : E → EReal) (x_bar : E) (hx : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hloc : LocalLscAt f x_bar) (w : E) (β : ℝ)
    (H : ∀ W ∈ 𝓝 (w, β), ∀ᶠ x in fApproach f x_bar, ∃ q ∈ epigraph (subderivative f x), q ∈ W) :
    regularSubderivative f x_bar w ≤ (β : EReal) := by
  set m := (f x_bar).toReal with hm_def
  have hm : f x_bar = (m : EReal) := (EReal.coe_toReal hx.2.ne hx.1.ne').symm
  obtain ⟨-, -, ε0, hε0⟩ := id hloc
  have hε0pos : 0 < ε0 := by
    refine (hε0 (m - |ε0|) ?_).1
    rw [hm, ← EReal.coe_add]
    exact_mod_cast (by linarith [neg_abs_le ε0] : m - |ε0| ≤ m + ε0)
  set C : Set (E × ℝ) := {p | p.1 ∈ Metric.closedBall x_bar ε0 ∧ p.2 ≤ m + ε0 / 2 ∧
      f p.1 ≤ (p.2 : EReal)} with hC_def
  have hC : IsClosed C := locLsc_closed f x_bar m hm ε0 hε0
  rw [rsd_le_iff]
  intro ε hε δ hδ
  set κ := min ε δ / 8 with hκ_def
  have hκ : 0 < κ := by positivity
  have hκε : 8 * κ ≤ ε := by rw [hκ_def]; linarith [min_le_left ε δ]
  have hκδ : 8 * κ ≤ δ := by rw [hκ_def]; linarith [min_le_right ε δ]
  -- the hypothesis H, made explicit
  have H1 := H (Metric.ball (w, β) κ) (Metric.ball_mem_nhds _ hκ)
  rw [fApproach_eventually_iff f x_bar m hm] at H1
  obtain ⟨r1, hr1, H1⟩ := H1
  -- lower semicontinuity at x_bar
  have hlsc := locLsc_eventually_gt f x_bar hloc (m - r1)
    (by rw [hm]; exact_mod_cast (by linarith : m - r1 < m))
  obtain ⟨r3, hr3, hlsc⟩ := Metric.eventually_nhds_iff.mp hlsc
  set R := min (min r1 r3) (ε0 / 4) with hR_def
  have hR : 0 < R := by positivity
  have hR1 : R ≤ r1 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hR3 : R ≤ r3 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hR0 : R ≤ ε0 / 4 := min_le_right _ _
  set D := ‖((w, β) : E × ℝ)‖ with hD_def
  have hD : 0 ≤ D := norm_nonneg _
  set ρ := R / (2 * (1 + 2 * D)) with hρ_def
  have hρ : 0 < ρ := by positivity
  have hρR : ρ * (1 + 2 * D) = R / 2 := by
    rw [hρ_def]; field_simp
  have hρR' : ρ ≤ R / 2 := by
    have : ρ ≤ ρ * (1 + 2 * D) := le_mul_of_one_le_right hρ.le (by linarith)
    linarith
  have hev : ∀ᶠ p in fApproach f x_bar ×ˢ 𝓝[>] (0:ℝ),
      (dist p.1 x_bar < ρ ∧ f p.1 ≠ ⊤ ∧ f p.1 ≠ ⊥ ∧ |(f p.1).toReal - m| < ρ) ∧
        p.2 ∈ Set.Ioo 0 ρ := by
    have h1 : ∀ᶠ y in fApproach f x_bar,
        dist y x_bar < ρ ∧ f y ≠ ⊤ ∧ f y ≠ ⊥ ∧ |(f y).toReal - m| < ρ := by
      rw [fApproach_eventually_iff f x_bar m hm]
      exact ⟨ρ, hρ, fun y h1 h2 h3 h4 => ⟨h1, h2, h3, h4⟩⟩
    have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 ρ := Ioo_mem_nhdsGT hρ
    exact h1.prod_mk h2
  filter_upwards [hev] with p hp
  obtain ⟨x, τ⟩ := p
  obtain ⟨⟨hxd, hxt, hxb, hxm⟩, hτ0, hτρ⟩ := hp
  simp only at hxd hxt hxb hxm hτ0 hτρ ⊢
  set a := (f x).toReal with ha_def
  have ha : f x = (a : EReal) := (EReal.coe_toReal hxt hxb).symm
  have hz0 : ((x, a) : E × ℝ) ∈ C := by
    refine ⟨?_, ?_, ha.le⟩
    · rw [Metric.mem_closedBall]; linarith
    · have := (abs_lt.mp hxm).2; linarith
  -- tangent condition
  have Hf : ∀ t ∈ Set.Ico (0:ℝ) τ, ∀ c ∈ C,
      dist ((x, a) + t • ((w, β) : E × ℝ)) c = Metric.infDist ((x, a) + t • ((w, β) : E × ℝ)) C →
      ∀ η : ℝ, 0 < η → ∃ s ∈ Set.Ioo (0:ℝ) η, ∃ c' ∈ C,
        ‖c' - (c + s • ((w, β) : E × ℝ))‖ ≤ (2 * κ) * s := by
    intro t ht c hc hcd η hη
    obtain ⟨y, a'⟩ := c
    obtain ⟨hy, ha', hfy⟩ := hc
    simp only at hy ha' hfy
    have hcz : dist ((x, a) + t • ((w, β) : E × ℝ)) (y, a') ≤ t * D := by
      rw [hcd]
      refine (Metric.infDist_le_dist_of_mem hz0).trans (le_of_eq ?_)
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have hz0b : dist ((x, a) : E × ℝ) (x_bar, m) < ρ := by
      rw [Prod.dist_eq]
      exact max_lt hxd (by rw [Real.dist_eq]; exact hxm)
    have hz0t : dist ((x, a) + t • ((w, β) : E × ℝ)) (x, a) = t * D := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
    have htρ : t < ρ := lt_trans ht.2 hτρ
    have hcb : dist ((y, a') : E × ℝ) (x_bar, m) < R / 2 := by
      calc dist ((y, a') : E × ℝ) (x_bar, m)
          ≤ dist ((y, a') : E × ℝ) ((x, a) + t • ((w, β) : E × ℝ)) +
            dist ((x, a) + t • ((w, β) : E × ℝ)) (x, a) + dist ((x, a) : E × ℝ) (x_bar, m) :=
            dist_triangle4 _ _ _ _
        _ < t * D + t * D + ρ := by
            rw [_root_.dist_comm] at hcz; rw [hz0t]; linarith
        _ ≤ ρ * D + ρ * D + ρ := by
            have := mul_le_mul_of_nonneg_right htρ.le hD; linarith
        _ = R / 2 := by linarith [hρR]
    rw [Prod.dist_eq] at hcb
    have hyd : dist y x_bar < R / 2 := lt_of_le_of_lt (le_max_left _ _) hcb
    have ha'm : dist a' m < R / 2 := lt_of_le_of_lt (le_max_right _ _) hcb
    rw [Real.dist_eq] at ha'm
    have ha'm' := abs_lt.mp ha'm
    -- f y finite and close to m
    have hfy_gt : ((m - r1 : ℝ) : EReal) < f y := hlsc (by linarith)
    have hfy_lt : f y < ((m + r1 : ℝ) : EReal) :=
      lt_of_le_of_lt hfy (by exact_mod_cast (by linarith : a' < m + r1))
    have hyt : f y ≠ ⊤ := ne_top_of_lt hfy_lt
    have hyb : f y ≠ ⊥ := ne_bot_of_gt hfy_gt
    set b0 := (f y).toReal with hb0_def
    have hb0 : f y = (b0 : EReal) := (EReal.coe_toReal hyt hyb).symm
    have hb0a : b0 ≤ a' := by rw [hb0] at hfy; exact_mod_cast hfy
    have hb0m : |b0 - m| < r1 := by
      rw [hb0] at hfy_gt
      have h1 : m - r1 < b0 := by exact_mod_cast hfy_gt
      rw [abs_lt]; constructor <;> linarith
    obtain ⟨⟨w', β'⟩, hq, hqball⟩ := H1 y (by linarith) hyt hyb hb0m
    have hq' : subderivative f y w' ≤ (β' : EReal) := hq
    rw [Metric.mem_ball, Prod.dist_eq] at hqball
    have hw' : dist w' w < κ := lt_of_le_of_lt (le_max_left _ _) hqball
    have hβ' : dist β' β < κ := lt_of_le_of_lt (le_max_right _ _) hqball
    rw [Real.dist_eq] at hβ'
    have hβ'' := abs_lt.mp hβ'
    -- bound M
    set M := ‖w‖ + |β| + 2 * κ + 1 with hM_def
    have hM : 0 < M := by positivity
    set η1 := min η (ε0 / (4 * M)) with hη1_def
    have hη1 : 0 < η1 := by positivity
    obtain ⟨s, ⟨hs0, hsη⟩, v, hv, hdq⟩ := (sd_le_iff f y w' β').mp hq' κ hκ κ hκ η1 hη1
    have hsη' : s < η := lt_of_lt_of_le hsη (min_le_left _ _)
    have hsM : s * M < ε0 / 4 := by
      have := lt_of_lt_of_le hsη (min_le_right _ _)
      rw [lt_div_iff₀ (by positivity)] at this; linarith
    rw [dq_lt_iff f y v b0 hb0 hs0] at hdq
    have hvw : ‖v - w‖ ≤ 2 * κ := by
      have := Metric.mem_closedBall.mp hv
      calc ‖v - w‖ = dist v w := (dist_eq_norm _ _).symm
        _ ≤ dist v w' + dist w' w := dist_triangle _ _ _
        _ ≤ 2 * κ := by linarith
    have hvnorm : ‖v‖ ≤ ‖w‖ + 2 * κ := by
      calc ‖v‖ = ‖(v - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖v - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ _ := by linarith
    refine ⟨s, ⟨hs0, hsη'⟩, (y + s • v, a' + s * (β' + κ)), ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [Metric.mem_closedBall]
      have h1 : dist (y + s • v) y = s * ‖v‖ := by
        rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hs0]
      have h2 : s * ‖v‖ ≤ s * M := by
        apply mul_le_mul_of_nonneg_left _ hs0.le; linarith [abs_nonneg β]
      calc dist (y + s • v) x_bar ≤ dist (y + s • v) y + dist y x_bar := dist_triangle _ _ _
        _ ≤ ε0 := by linarith
    · have h1 : s * (β' + κ) ≤ s * M := by
        apply mul_le_mul_of_nonneg_left _ hs0.le
        linarith [le_abs_self β, norm_nonneg w]
      show a' + s * (β' + κ) ≤ m + ε0 / 2
      linarith
    · have hreal : b0 + (β' + κ) * s ≤ a' + s * (β' + κ) := by
        rw [mul_comm]; linarith
      exact le_trans hdq.le (EReal.coe_le_coe_iff.mpr hreal)
    · have heq : ((y + s • v, a' + s * (β' + κ)) : E × ℝ) - ((y, a') + s • ((w, β) : E × ℝ)) =
          (s • (v - w), s * (β' + κ - β)) := by
        ext
        · simp [smul_sub]
        · simp; ring
      rw [heq, Prod.norm_mk, norm_smul, Real.norm_eq_abs, abs_of_pos hs0, Real.norm_eq_abs,
        abs_mul, abs_of_pos hs0]
      apply max_le
      · have := mul_le_mul_of_nonneg_left hvw hs0.le; linarith
      · have : |β' + κ - β| ≤ 2 * κ := by
          rw [abs_le]; constructor <;> linarith
        have := mul_le_mul_of_nonneg_left this hs0.le; linarith
  have hfin := fencing_core C hC (x, a) (w, β) hz0 τ (2 * κ) hτ0 (by positivity) Hf
  have hlt : Metric.infDist ((x, a) + τ • ((w, β) : E × ℝ)) C < 5 * κ * τ := by
    have := mul_pos hκ hτ0; linarith
  obtain ⟨⟨u, b⟩, hc, hdist⟩ := (Metric.infDist_lt_iff ⟨_, hz0⟩).mp hlt
  obtain ⟨hu, hb, hfu⟩ := hc
  simp only at hu hb hfu
  rw [Prod.dist_eq] at hdist
  have hd1 : dist (x + τ • w) u < 5 * κ * τ := lt_of_le_of_lt (le_max_left _ _) hdist
  have hd2 : dist (a + τ * β) b < 5 * κ * τ := lt_of_le_of_lt (le_max_right _ _) hdist
  refine ⟨τ⁻¹ • (u - x), ?_, ?_⟩
  · rw [Metric.mem_closedBall, dist_eq_norm]
    have : τ⁻¹ • (u - x) - w = τ⁻¹ • (u - (x + τ • w)) := by
      rw [smul_sub, smul_sub, smul_add, smul_smul, inv_mul_cancel₀ hτ0.ne', one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hτ0, ← dist_eq_norm, _root_.dist_comm,
      inv_mul_le_iff₀ hτ0]
    have := mul_le_mul_of_nonneg_right (show 5 * κ ≤ δ by linarith) hτ0.le
    linarith
  · show differenceQuotient f x (τ⁻¹ • (u - x)) τ < ((β + ε : ℝ) : EReal)
    rw [dq_lt_iff f x _ a ha hτ0]
    have hxu : x + τ • τ⁻¹ • (u - x) = u := by
      rw [smul_smul, mul_inv_cancel₀ hτ0.ne', one_smul]; abel
    rw [hxu]
    refine lt_of_le_of_lt hfu ?_
    have : b < a + (β + ε) * τ := by
      rw [Real.dist_eq] at hd2
      have := (abs_lt.mp hd2)
      have := mul_le_mul_of_nonneg_right (show 5 * κ ≤ ε by linarith) hτ0.le
      linarith
    exact_mod_cast this



theorem RW_chap_8_18
  (f : E → EReal)
  (x_bar : E)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  LowerSemicontinuous (regularSubderivative f x_bar) ∧
  LowerSemicontinuous (subderivative f x_bar) ∧
  (0 ∈ effDom (regularSubderivative f x_bar) ∧ IsERealPosHomogeneous (regularSubderivative f x_bar)) ∧
  (0 ∈ effDom (subderivative f x_bar) ∧ IsERealPosHomogeneous (subderivative f x_bar)) ∧
  (∀ (w : E), subderivative f x_bar w ≤ regularSubderivative f x_bar w) ∧
  (LowerSemicontinuousAt f x_bar →
    (∀ (w : E), ⊥ < regularSubderivative f x_bar w) →
    IsSublinearRW (regularSubderivative f x_bar)) ∧
  (LocalLscAt f x_bar →
    IsEpiLimsup
      (fun x => subderivative f x)
      (fApproach f x_bar)
      (regularSubderivative f x_bar)) := by
  refine ⟨rsd_lsc f x_bar, sd_lsc f x_bar,
    ⟨rsd_zero_lt_top f x_bar, posHom_of_scaling _ (rsd_scaling f x_bar)⟩,
    ⟨sd_zero_lt_top f x_bar, posHom_of_scaling _ (sd_scaling f x_bar)⟩,
    sd_le_rsd f x_bar, ?_, ?_⟩
  · intro hlsc _
    exact ⟨⟨rsd_zero_lt_top f x_bar, posHom_of_scaling _ (rsd_scaling f x_bar)⟩,
      rsd_convex f x_bar hx_bar hlsc⟩
  · intro hloc
    ext ⟨w, β⟩
    simp only [epigraph, Set.mem_setOf_eq]
    exact ⟨epi_forward f x_bar w β, epi_backward f x_bar hx_bar hloc w β⟩

end RW_chap_8_18
