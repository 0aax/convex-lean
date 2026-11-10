import ConvexStarLib.Defs

/-!
# `RW_chap_8_30`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_30` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_30`, so the main result is `RW_chap_8_30.RW_chap_8_30`.
-/

namespace RW_chap_8_30

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/- ===== from taskA ===== -/

/-! Agent A: basic properties of the subderivative -/

/-- Auxiliary: if `Φ` maps `F` to `G`, `Ψ` maps `G` to `F` and `Φ ∘ Ψ = id`, then `map Φ F = G`. -/
lemma A_map_eq_of_tendsto {α β : Type*} {F : Filter α} {G : Filter β} {Φ : α → β} {Ψ : β → α}
    (h1 : Filter.Tendsto Φ F G) (h2 : Filter.Tendsto Ψ G F) (h3 : ∀ b, Φ (Ψ b) = b) :
    Filter.map Φ F = G := by
  apply le_antisymm h1
  have hid : Φ ∘ Ψ = id := funext h3
  calc G = Filter.map (Φ ∘ Ψ) G := by rw [hid, Filter.map_id]
    _ = Filter.map Φ (Filter.map Ψ G) := (Filter.map_map).symm
    _ ≤ Filter.map Φ F := Filter.map_mono h2

/-- Auxiliary: scaling identity for difference quotients. -/
lemma A_dq_scale (f : E → EReal) (x u : E) (σ t : ℝ) (ht : t ≠ 0) :
    differenceQuotient f x (t • u) (σ / t) = (t : EReal) * differenceQuotient f x u σ := by
  unfold differenceQuotient
  have h1 : (σ / t) • (t • u) = σ • u := by
    rw [smul_smul, div_mul_cancel₀ σ ht]
  have h2 : ((σ / t : ℝ) : EReal)⁻¹ = (t : EReal) * ((σ : EReal))⁻¹ := by
    rw [← EReal.coe_inv, ← EReal.coe_inv, ← EReal.coe_mul, inv_div, div_eq_mul_inv]
  rw [h1, div_eq_mul_inv (f (x + σ • u) - f x) ((σ / t : ℝ) : EReal), h2, div_eq_mul_inv]
  exact mul_left_comm _ _ _

/-- Auxiliary: multiplication by a positive real is an order isomorphism of `EReal`. -/
noncomputable def A_mulOrderIso (t : ℝ) (ht : 0 < t) : EReal ≃o EReal where
  toFun x := (t : EReal) * x
  invFun x := ((t⁻¹ : ℝ) : EReal) * x
  left_inv x := by
    simp only
    rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one, one_mul]
  right_inv x := by
    simp only
    rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul]
  map_rel_iff' {a b} := by
    simp only [Equiv.coe_fn_mk]
    constructor
    · intro h
      have h0 : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.mpr ht).le
      have := mul_le_mul_of_nonneg_left h h0
      rwa [← mul_assoc, ← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one,
        one_mul, one_mul] at this
    · intro h
      exact mul_le_mul_of_nonneg_left h (by exact_mod_cast ht.le)

lemma A_mulOrderIso_apply (t : ℝ) (ht : 0 < t) (x : EReal) :
    A_mulOrderIso t ht x = (t : EReal) * x := rfl

/-- Auxiliary: `σ ↦ σ * c` maps `𝓝[>] 0` into itself for `c > 0`. -/
lemma A_tendsto_mul_const_nhdsGT (c : ℝ) (hc : 0 < c) :
    Filter.Tendsto (fun σ : ℝ => σ * c) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · have h : Filter.Tendsto (fun σ : ℝ => σ * c) (𝓝 (0:ℝ)) (𝓝 (0 * c)) :=
      (continuous_id.mul continuous_const).tendsto 0
    rw [zero_mul] at h
    exact h.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with σ hσ
    exact mul_pos hσ hc

lemma subderivative_zero_le (f : E → EReal) (x_bar : E) (hf : ⊥ < f x_bar ∧ f x_bar < ⊤) :
    subderivative f x_bar 0 ≤ 0 := by
  unfold subderivative
  apply Filter.liminf_le_of_frequently_le'
  have hT : Filter.Tendsto (fun τ : ℝ => (τ, (0:E))) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ) ×ˢ 𝓝 (0:E)) :=
    Filter.tendsto_id.prodMk tendsto_const_nhds
  apply hT.frequently
  apply Filter.Eventually.frequently
  filter_upwards with τ
  simp only [differenceQuotient, smul_zero, add_zero]
  rw [EReal.sub_self hf.2.ne hf.1.ne', EReal.zero_div]

lemma subderivative_lsc (f : E → EReal) (x_bar : E) :
    LowerSemicontinuous (subderivative f x_bar) := by
  intro w y hy
  obtain ⟨y', hyy', hy'⟩ := exists_between hy
  have hev : ∀ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w, y' < differenceQuotient f x_bar p.2 p.1 :=
    Filter.eventually_lt_of_lt_liminf hy'
  rw [Filter.eventually_prod_iff] at hev
  obtain ⟨pa, hpa, pb, hpb, h⟩ := hev
  rw [eventually_nhds_iff] at hpb
  obtain ⟨U, hU, hUo, hwU⟩ := hpb
  filter_upwards [hUo.mem_nhds hwU] with w' hw'
  apply lt_of_lt_of_le hyy'
  refine Filter.le_liminf_of_le (h := ?_)
  rw [Filter.eventually_prod_iff]
  exact ⟨pa, hpa, fun u => u ∈ U, hUo.mem_nhds hw', fun {a} ha {b} hb => (h ha (hU b hb)).le⟩

lemma subderivative_posHom (f : E → EReal) (x_bar : E) :
    IsERealPosHomogeneous (subderivative f x_bar) := by
  intro w t ht
  have ht0 : t ≠ 0 := ht.ne'
  set G : ℝ × E → EReal := fun p => differenceQuotient f x_bar p.2 p.1 with hG
  set Φ : ℝ × E → ℝ × E := fun p => (p.1 / t, t • p.2) with hΦ
  set Ψ : ℝ × E → ℝ × E := fun p => (p.1 * t, t⁻¹ • p.2) with hΨ
  have hΦt : Filter.Tendsto Φ (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) (𝓝[>] (0:ℝ) ×ˢ 𝓝 (t • w)) := by
    have h1 : Filter.Tendsto (fun σ : ℝ => σ / t) (𝓝[>] (0:ℝ)) (𝓝[>] (0:ℝ)) := by
      simp_rw [div_eq_mul_inv]
      exact A_tendsto_mul_const_nhdsGT t⁻¹ (inv_pos.mpr ht)
    have h2 : Filter.Tendsto (fun u : E => t • u) (𝓝 w) (𝓝 (t • w)) :=
      (continuous_const_smul t).tendsto w
    exact h1.prodMap h2
  have hΨt : Filter.Tendsto Ψ (𝓝[>] (0:ℝ) ×ˢ 𝓝 (t • w)) (𝓝[>] (0:ℝ) ×ˢ 𝓝 w) := by
    have h1 := A_tendsto_mul_const_nhdsGT t ht
    have h2 : Filter.Tendsto (fun u : E => t⁻¹ • u) (𝓝 (t • w)) (𝓝 (t⁻¹ • t • w)) :=
      (continuous_const_smul t⁻¹).tendsto (t • w)
    rw [inv_smul_smul₀ ht0] at h2
    exact h1.prodMap h2
  have hΦΨ : ∀ p, Φ (Ψ p) = p := by
    rintro ⟨σ, u⟩
    simp only [hΦ, hΨ, Prod.mk.injEq]
    exact ⟨mul_div_cancel_right₀ σ ht0, smul_inv_smul₀ ht0 u⟩
  have hmap := A_map_eq_of_tendsto hΦt hΨt hΦΨ
  have hcomp : G ∘ Φ = fun p => (t : EReal) * G p := by
    funext p
    simp only [Function.comp, hG, hΦ]
    exact A_dq_scale f x_bar p.2 p.1 t ht0
  show Filter.liminf G (𝓝[>] (0:ℝ) ×ˢ 𝓝 (t • w)) = (t : EReal) * Filter.liminf G (𝓝[>] (0:ℝ) ×ˢ 𝓝 w)
  rw [← hmap, ← Filter.liminf_comp, hcomp]
  exact (OrderIso.liminf_apply (A_mulOrderIso t ht)).symm

/- ===== from taskC ===== -/

/-! Agent C: subgradients and horizon subgradients are bounded by the regular subderivative -/

omit [FiniteDimensional ℝ E] in
/-- (F1) the inner limsup is antitone in the radius. -/
lemma C_aux_anti (f : E → EReal) (x_bar w : E) {δ δ' : ℝ} (h : δ ≤ δ') :
    Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ'))
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) ≤
    Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
  exact Filter.limsup_le_limsup (Filter.Eventually.of_forall (fun p =>
    sInf_le_sInf (Set.image_mono (Metric.closedBall_subset_closedBall h))))

omit [FiniteDimensional ℝ E] in
/-- (F2) for `δ > 0` the inner limsup is below the regular subderivative. -/
lemma C_aux_le (f : E → EReal) (x_bar w : E) {δ : ℝ} (hδ : 0 < δ) :
    Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) ≤ regularSubderivative f x_bar w := by
  unfold regularSubderivative
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  have hI : Set.Ioo (0:ℝ) δ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hδ
  filter_upwards [hI] with δ' hδ'
  exact C_aux_anti f x_bar w hδ'.2.le

omit [FiniteDimensional ℝ E] in
/-- (F4) the pointwise step at a fixed regular subgradient. -/
lemma C_aux_reg (f : E → EReal) (y0 v w : E) (hreg : IsRegularSubgradientAt f y0 v)
    (δ β θ : ℝ) (hδ : 0 < δ) (hθ : 0 < θ)
    (hgood : ∀ τ ∈ Set.Ioo (0:ℝ) θ,
      sInf ((delta f y0 τ) '' Metric.closedBall w δ) < (β : EReal)) :
    ∃ w' ∈ Metric.closedBall w δ, inner ℝ v w' < β + δ * (‖w‖ + δ) := by
  obtain ⟨hbot, htop, r, hr, V, hV, hineq⟩ := hreg
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f y0 = (c : EReal) :=
    ⟨(f y0).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  have hev : ∀ᶠ y in 𝓝 y0, ‖r y‖ ≤ δ * ‖‖y - y0‖‖ := hr.def hδ
  have hev2 : ∀ᶠ y in 𝓝 y0, y ∈ V ∧ ‖r y‖ ≤ δ * ‖‖y - y0‖‖ :=
    (Filter.eventually_of_mem hV (fun y hy => hy)).and hev
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.1 hev2
  set K : ℝ := ‖w‖ + δ + 1 with hK
  have hKpos : 0 < K := by positivity
  set τ : ℝ := min (θ / 2) (ρ / K) with hτ
  have hτpos : 0 < τ := lt_min (by linarith) (div_pos hρ hKpos)
  have hτθ : τ < θ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hτρ : τ * K ≤ ρ := by
    have h1 : τ ≤ ρ / K := min_le_right _ _
    calc τ * K ≤ ρ / K * K := by gcongr
      _ = ρ := div_mul_cancel₀ ρ hKpos.ne'
  have hlt := hgood τ ⟨hτpos, hτθ⟩
  obtain ⟨_, ⟨w', hw', rfl⟩, hw'lt⟩ := sInf_lt_iff.1 hlt
  refine ⟨w', hw', ?_⟩
  have hw'norm : ‖w'‖ ≤ ‖w‖ + δ := by
    have h1 : ‖w' - w‖ ≤ δ := mem_closedBall_iff_norm.1 hw'
    calc ‖w'‖ = ‖w + (w' - w)‖ := by rw [add_sub_cancel]
      _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + δ := by linarith
  have hyy0 : (y0 + τ • w') - y0 = τ • w' := add_sub_cancel_left _ _
  have hnorm : ‖(y0 + τ • w') - y0‖ ≤ τ * (‖w‖ + δ) := by
    rw [hyy0, norm_smul, Real.norm_of_nonneg hτpos.le]
    gcongr
  have hdist : dist (y0 + τ • w') y0 < ρ := by
    rw [dist_eq_norm]
    calc ‖(y0 + τ • w') - y0‖ ≤ τ * (‖w‖ + δ) := hnorm
      _ < τ * K := mul_lt_mul_of_pos_left (by rw [hK]; linarith) hτpos
      _ ≤ ρ := hτρ
  obtain ⟨hyV, hry⟩ := hball hdist
  have hsub := hineq _ hyV
  simp only [delta, differenceQuotient] at hw'lt
  rw [hc] at hsub hw'lt
  rw [hyy0, inner_smul_right] at hsub
  have hry' : -(r (y0 + τ • w')) ≤ δ * (τ * (‖w‖ + δ)) := by
    rw [Real.norm_eq_abs, norm_norm] at hry
    have h1 := neg_abs_le (r (y0 + τ • w'))
    have h2 : δ * ‖(y0 + τ • w') - y0‖ ≤ δ * (τ * (‖w‖ + δ)) := by gcongr
    linarith
  generalize f (y0 + τ • w') = z at hsub hw'lt
  induction z using EReal.rec with
  | bot =>
    exfalso
    rw [← EReal.coe_add] at hsub
    exact EReal.coe_ne_bot _ (le_bot_iff.1 hsub)
  | top =>
    exfalso
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (EReal.coe_pos.2 hτpos)
      (EReal.coe_ne_top _)] at hw'lt
    exact not_top_lt hw'lt
  | coe d =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_lt_coe_iff, div_lt_iff₀ hτpos] at hw'lt
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hsub
    have key : τ * inner ℝ v w' < τ * (β + δ * (‖w‖ + δ)) := by nlinarith
    exact lt_of_mul_lt_mul_left key hτpos.le

lemma core_C (f : E → EReal) (x_bar w : E) (x vseq : ℕ → E)
    (hx : Filter.Tendsto x Filter.atTop (𝓝 x_bar))
    (hfx : Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)))
    (hreg : ∀ n, IsRegularSubgradientAt f (x n) (vseq n))
    (β : ℝ) (hβ : regularSubderivative f x_bar w < β) (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, ∃ w' ∈ Metric.closedBall w δ,
      inner ℝ (vseq n) w' < β + δ * (‖w‖ + δ) := by
  have hIle := C_aux_le f x_bar w hδ
  have hev : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      sInf ((delta f p.1 p.2) '' Metric.closedBall w δ) < (β : EReal) :=
    Filter.eventually_lt_of_limsup_lt (lt_of_le_of_lt hIle hβ)
  obtain ⟨A, hA, T, hT, hAT⟩ := Filter.mem_prod_iff.1 hev
  obtain ⟨θ, hθ, hθT⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hT
  have htend : Filter.Tendsto x Filter.atTop (fApproach f x_bar) :=
    Filter.tendsto_inf.2 ⟨hx, Filter.tendsto_comap_iff.2 hfx⟩
  have hxA : ∀ᶠ n in Filter.atTop, x n ∈ A := htend hA
  filter_upwards [hxA] with n hn
  apply C_aux_reg f (x n) (vseq n) w (hreg n) δ β θ hδ hθ
  intro τ hτ
  exact hAT (Set.mk_mem_prod hn (hθT hτ))

lemma subgradient_le_regularSubderivative (f : E → EReal) (x_bar v : E)
    (hv : v ∈ subdifferential f x_bar) (w : E) :
    ((inner ℝ v w : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
  obtain ⟨_, _, x, vseq, hx, hfx, hvseq, hreg⟩ := hv
  have key : ∀ β : ℝ, regularSubderivative f x_bar w < β → inner ℝ v w ≤ β := by
    intro β hβ
    have h1 : ∀ δ : ℝ, 0 < δ → inner ℝ v w ≤ β + δ * (‖w‖ + δ) + ‖v‖ * δ := by
      intro δ hδ
      have hev := core_C f x_bar w x vseq hx hfx hreg β hβ δ hδ
      have hev2 : ∀ᶠ n in Filter.atTop,
          inner ℝ (vseq n) w - ‖vseq n‖ * δ ≤ β + δ * (‖w‖ + δ) := by
        filter_upwards [hev] with n hn
        obtain ⟨w', hw', hlt⟩ := hn
        have hww' : ‖w - w'‖ ≤ δ := by
          rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hw'
        have h2 : inner ℝ (vseq n) (w - w') ≤ ‖vseq n‖ * δ :=
          calc inner ℝ (vseq n) (w - w') ≤ ‖vseq n‖ * ‖w - w'‖ := real_inner_le_norm _ _
            _ ≤ ‖vseq n‖ * δ := by gcongr
        have h3 : inner ℝ (vseq n) w = inner ℝ (vseq n) w' + inner ℝ (vseq n) (w - w') := by
          rw [inner_sub_right]; ring
        linarith
      have ht : Filter.Tendsto (fun n => inner ℝ (vseq n) w - ‖vseq n‖ * δ) Filter.atTop
          (𝓝 (inner ℝ v w - ‖v‖ * δ)) :=
        (hvseq.inner tendsto_const_nhds).sub (hvseq.norm.mul_const δ)
      have := le_of_tendsto ht hev2
      linarith
    have ht : Filter.Tendsto (fun δ : ℝ => (β : ℝ) + δ * (‖w‖ + δ) + ‖v‖ * δ) (𝓝[>] 0)
        (𝓝 β) := by
      have h0 : Filter.Tendsto (fun δ : ℝ => (β : ℝ) + δ * (‖w‖ + δ) + ‖v‖ * δ) (𝓝 0)
          (𝓝 ((β : ℝ) + 0 * (‖w‖ + 0) + ‖v‖ * 0)) := by
        apply Continuous.tendsto; fun_prop
      simp only [zero_mul, add_zero, mul_zero] at h0
      exact tendsto_nhdsWithin_of_tendsto_nhds h0
    exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => h1 δ hδ)
  exact EReal.le_of_forall_lt_iff_le.1 (fun z hz => EReal.coe_le_coe_iff.2 (key z hz))

lemma horizon_le_zero (f : E → EReal) (x_bar v : E)
    (hv : v ∈ horizonSubdifferential f x_bar) (w : E)
    (hw : regularSubderivative f x_bar w < ⊤) :
    inner ℝ v w ≤ 0 := by
  obtain ⟨_, _, x, vseq, l, hx, hfx, hl, hlv, hreg⟩ := hv
  obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hw
  have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := tendsto_nhds_of_tendsto_nhdsWithin hl
  have hlpos : ∀ᶠ n in Filter.atTop, l n ∈ Set.Ioi (0 : ℝ) := (tendsto_nhdsWithin_iff.1 hl).2
  have h1 : ∀ δ : ℝ, 0 < δ → inner ℝ v w ≤ ‖v‖ * δ := by
    intro δ hδ
    have hev := core_C f x_bar w x vseq hx hfx hreg β hβ δ hδ
    have hev2 : ∀ᶠ n in Filter.atTop, inner ℝ (l n • vseq n) w - ‖l n • vseq n‖ * δ ≤
        l n * (β + δ * (‖w‖ + δ)) := by
      filter_upwards [hev, hlpos] with n hn hln
      obtain ⟨w', hw', hlt⟩ := hn
      have hln' : 0 < l n := hln
      have hww' : ‖w - w'‖ ≤ δ := by
        rw [norm_sub_rev]; exact mem_closedBall_iff_norm.1 hw'
      have h2 : inner ℝ (l n • vseq n) (w - w') ≤ ‖l n • vseq n‖ * δ :=
        calc inner ℝ (l n • vseq n) (w - w') ≤ ‖l n • vseq n‖ * ‖w - w'‖ :=
              real_inner_le_norm _ _
          _ ≤ ‖l n • vseq n‖ * δ := by gcongr
      have h3 : inner ℝ (l n • vseq n) w =
          l n * inner ℝ (vseq n) w' + inner ℝ (l n • vseq n) (w - w') := by
        rw [inner_sub_right, real_inner_smul_left, real_inner_smul_left]; ring
      have h4 : l n * inner ℝ (vseq n) w' ≤ l n * (β + δ * (‖w‖ + δ)) :=
        mul_le_mul_of_nonneg_left hlt.le hln'.le
      linarith
    have ht1 : Filter.Tendsto (fun n => inner ℝ (l n • vseq n) w - ‖l n • vseq n‖ * δ)
        Filter.atTop (𝓝 (inner ℝ v w - ‖v‖ * δ)) :=
      (hlv.inner tendsto_const_nhds).sub (hlv.norm.mul_const δ)
    have ht2 : Filter.Tendsto (fun n => l n * (β + δ * (‖w‖ + δ))) Filter.atTop
        (𝓝 (0 * (β + δ * (‖w‖ + δ)))) := hl0.mul_const _
    rw [zero_mul] at ht2
    have := le_of_tendsto_of_tendsto ht1 ht2 hev2
    linarith
  have ht : Filter.Tendsto (fun δ : ℝ => ‖v‖ * δ) (𝓝[>] 0) (𝓝 0) := by
    have h0 : Filter.Tendsto (fun δ : ℝ => ‖v‖ * δ) (𝓝 0) (𝓝 (‖v‖ * 0)) :=
      (continuous_const.mul continuous_id).tendsto 0
    rw [mul_zero] at h0
    exact tendsto_nhdsWithin_of_tendsto_nhds h0
  exact ge_of_tendsto ht (eventually_nhdsWithin_of_forall fun δ hδ => h1 δ hδ)

/- ===== from taskD ===== -/

/-! Agent D: regular subgradients from the subderivative -/

lemma D_quot_le (a : EReal) (b c τ : ℝ) (hτ : 0 < τ) (h : a ≤ (b : EReal)) :
    (a - (c : EReal)) / (τ : EReal) ≤ (((b - c) / τ : ℝ) : EReal) := by
  rw [EReal.coe_div, EReal.coe_sub]
  exact EReal.div_le_div_right_of_nonneg (by exact_mod_cast hτ.le) (EReal.sub_le_sub h le_rfl)

lemma D_key (f : E → EReal) (x_bar v : E) (c : ℝ) (hc : f x_bar = (c : EReal))
    (hv : ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w) :
    ∀ ε > 0, ∃ θ > 0, ∀ y : E, ‖y‖ ≤ θ →
      (((c + inner ℝ v y - ε * ‖y‖ : ℝ)) : EReal) ≤ f (x_bar + y) := by
  intro ε hε
  by_contra hcon
  push_neg at hcon
  choose y hy_norm hy_lt using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hy0 : ∀ n, y n ≠ 0 := by
    intro n h0
    have := hy_lt n
    rw [h0] at this
    simp [hc] at this
  have hτpos : ∀ n, 0 < ‖y n‖ := fun n => norm_pos_iff.mpr (hy0 n)
  have hw_norm : ∀ n, ‖‖y n‖⁻¹ • y n‖ = 1 := by
    intro n
    rw [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hτpos n).ne'
  obtain ⟨w0, -, ns, hns, hwns⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq
    (x := fun n => ‖y n‖⁻¹ • y n) (fun n => mem_sphere_zero_iff_norm.mpr (hw_norm n))
  have hτ_tend : Filter.Tendsto (fun n => ‖y n‖) Filter.atTop (𝓝 0) :=
    squeeze_zero (fun n => (hτpos n).le) hy_norm tendsto_one_div_add_atTop_nhds_zero_nat
  have hτns : Filter.Tendsto ((fun n => ‖y n‖) ∘ ns) Filter.atTop (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hτ_tend.comp hns.tendsto_atTop, Filter.Eventually.of_forall fun n => hτpos (ns n)⟩
  have hprod := hτns.prodMk hwns
  have hq : ∀ n, differenceQuotient f x_bar (‖y n‖⁻¹ • y n) ‖y n‖
      ≤ ((inner ℝ v (‖y n‖⁻¹ • y n) - ε : ℝ) : EReal) := by
    intro n
    have h1 : ‖y n‖ • ‖y n‖⁻¹ • y n = y n := smul_inv_smul₀ (hτpos n).ne' (y n)
    have h2 : inner ℝ v (‖y n‖⁻¹ • y n) - ε
        = ((c + inner ℝ v (y n) - ε * ‖y n‖) - c) / ‖y n‖ := by
      rw [real_inner_smul_right]
      have := (hτpos n).ne'
      field_simp
      ring
    unfold differenceQuotient
    rw [h1, hc, h2]
    exact D_quot_le _ _ _ _ (hτpos n) (hy_lt n).le
  have hinner : Filter.Tendsto (fun n => inner ℝ v (((fun n => ‖y n‖⁻¹ • y n) ∘ ns) n))
      Filter.atTop (𝓝 (inner ℝ v w0)) :=
    tendsto_const_nhds.inner hwns
  have hev : ∀ᶠ n in Filter.atTop,
      inner ℝ v (((fun n => ‖y n‖⁻¹ • y n) ∘ ns) n) < inner ℝ v w0 + ε / 2 :=
    hinner.eventually (gt_mem_nhds (by linarith))
  have hfreq : ∃ᶠ p in 𝓝[>] (0:ℝ) ×ˢ 𝓝 w0,
      differenceQuotient f x_bar p.2 p.1 ≤ ((inner ℝ v w0 - ε / 2 : ℝ) : EReal) := by
    refine hprod.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [hev] with n hn
    refine (hq (ns n)).trans ?_
    simp only [Function.comp_apply] at hn
    exact EReal.coe_le_coe_iff.mpr (by linarith)
  have hle : subderivative f x_bar w0 ≤ ((inner ℝ v w0 - ε / 2 : ℝ) : EReal) :=
    Filter.liminf_le_of_frequently_le' hfreq
  have h3 := EReal.coe_le_coe_iff.mp ((hv w0).trans hle)
  linarith

lemma regularSubgradient_of_le_subderivative (f : E → EReal) (x_bar v : E)
    (hf : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hv : ∀ w, ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x_bar w) :
    IsRegularSubgradientAt f x_bar v := by
  obtain ⟨hbot, htop⟩ := hf
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f x_bar = (c : EReal) :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  have key := D_key f x_bar v c hc hv
  refine ⟨hbot, htop,
    fun x => if f x = ⊤ then 0 else min 0 ((f x).toReal - c - inner ℝ v (x - x_bar)), ?_, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨θ, hθ, hθ'⟩ := key ε hε
    filter_upwards [Metric.closedBall_mem_nhds x_bar hθ] with x hx
    have hxn : ‖x - x_bar‖ ≤ θ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hx
    have hfx := hθ' (x - x_bar) hxn
    rw [add_sub_cancel] at hfx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hnn := norm_nonneg (x - x_bar)
    have hεn : 0 ≤ ε * ‖x - x_bar‖ := mul_nonneg hε.le hnn
    have hr_le : (if f x = ⊤ then 0 else min 0 ((f x).toReal - c - inner ℝ v (x - x_bar))) ≤ 0 := by
      split_ifs
      · exact le_rfl
      · exact min_le_left _ _
    have hr_ge : -(ε * ‖x - x_bar‖)
        ≤ (if f x = ⊤ then 0 else min 0 ((f x).toReal - c - inner ℝ v (x - x_bar))) := by
      split_ifs with h
      · linarith
      · refine le_min (by linarith) ?_
        have hne_bot : f x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hfx
        have hfx_eq : f x = ((f x).toReal : EReal) := (EReal.coe_toReal h hne_bot).symm
        rw [hfx_eq] at hfx
        have := EReal.coe_le_coe_iff.mp hfx
        linarith
    exact abs_le.mpr ⟨hr_ge, by linarith⟩
  · obtain ⟨θ, hθ, hθ'⟩ := key 1 one_pos
    refine ⟨Metric.closedBall x_bar θ, Metric.closedBall_mem_nhds x_bar hθ, ?_⟩
    intro x hx
    by_cases h : f x = ⊤
    · rw [h]; exact le_top
    · have hxn : ‖x - x_bar‖ ≤ θ := by rwa [Metric.mem_closedBall, dist_eq_norm] at hx
      have hfx := hθ' (x - x_bar) hxn
      rw [add_sub_cancel] at hfx
      have hne_bot : f x ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hfx
      have hfx_eq : f x = ((f x).toReal : EReal) := (EReal.coe_toReal h hne_bot).symm
      simp only [if_neg h]
      conv_rhs => rw [hfx_eq]
      rw [hc, ← EReal.coe_add, EReal.coe_le_coe_iff]
      have := min_le_right 0 ((f x).toReal - c - inner ℝ v (x - x_bar))
      linarith

/- ===== from taskE ===== -/

/-! Agent E: key inequality for elements of the polar of the domain of the subderivative -/

lemma polar_key_ineq (f : E → EReal) (x_bar v : E)
    (hv : v ∈ polarCone (effDom (subderivative f x_bar))) (ε : ℝ) (hε : 0 < ε) :
    ∃ θ > 0, ∀ y : E, ‖y‖ ≤ θ →
      inner ℝ v y ≤ ε * ‖y‖ ∨ (((inner ℝ v y / ε : ℝ)) : EReal) ≤ f (x_bar + y) - f x_bar := by
  by_contra hcon
  push_neg at hcon
  choose y hy_norm hy_inner hy_f using fun n : ℕ => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  have hτpos : ∀ n, 0 < ‖y n‖ := by
    intro n
    have h1 := hy_inner n
    rw [norm_pos_iff]
    rintro h0
    rw [h0] at h1
    simp at h1
  obtain ⟨w, hw_def⟩ : ∃ w : ℕ → E, w = fun n => ‖y n‖⁻¹ • y n := ⟨_, rfl⟩
  have hw_sphere : ∀ n, w n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, hw_def]
    simp only [norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hτpos n).ne'
  have hy_eq : ∀ n, ‖y n‖ • w n = y n := by
    intro n
    rw [hw_def]
    simp only [smul_smul, mul_inv_cancel₀ (hτpos n).ne', one_smul]
  have hw_inner : ∀ n, ε ≤ inner ℝ v (w n) := by
    intro n
    rw [hw_def]
    simp only [inner_smul_right]
    rw [le_inv_mul_iff₀ (hτpos n)]
    have := hy_inner n
    linarith [mul_comm ε ‖y n‖]
  obtain ⟨w0, hw0, ns, hns, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hw_sphere
  have hw0_inner : ε ≤ inner ℝ v w0 := by
    have hc : Filter.Tendsto (fun n => inner ℝ v ((w ∘ ns) n)) Filter.atTop
        (𝓝 (inner ℝ v w0)) :=
      ((continuous_const.inner continuous_id).tendsto w0).comp hlim
    exact ge_of_tendsto hc (Filter.Eventually.of_forall fun n => hw_inner (ns n))
  have hτlim : Filter.Tendsto (fun n => ‖y n‖) Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    exact squeeze_zero (fun n => norm_nonneg _) hy_norm h1
  have hτlim' : Filter.Tendsto (fun n => ‖y (ns n)‖) Filter.atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hτlim.comp hns.tendsto_atTop, Filter.Eventually.of_forall fun n => hτpos (ns n)⟩
  have hprod : Filter.Tendsto (fun n => (‖y (ns n)‖, w (ns n))) Filter.atTop
      (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w0) := hτlim'.prodMk hlim
  have hbound : ∀ n, differenceQuotient f x_bar (w n) ‖y n‖ ≤ ((‖v‖ / ε : ℝ) : EReal) := by
    intro n
    unfold differenceQuotient
    rw [hy_eq n]
    calc (f (x_bar + y n) - f x_bar) / ((‖y n‖ : ℝ) : EReal)
        ≤ ((inner ℝ v (y n) / ε : ℝ) : EReal) / ((‖y n‖ : ℝ) : EReal) :=
          EReal.div_le_div_right_of_nonneg (EReal.coe_nonneg.mpr (norm_nonneg _)) (hy_f n).le
      _ = ((inner ℝ v (y n) / ε / ‖y n‖ : ℝ) : EReal) := (EReal.coe_div _ _).symm
      _ ≤ ((‖v‖ / ε : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff]
          have h1 : inner ℝ v (y n) ≤ ‖v‖ * ‖y n‖ := real_inner_le_norm v (y n)
          rw [div_div, div_le_div_iff₀ (mul_pos hε (hτpos n)) hε]
          nlinarith
  have hfreq : ∃ᶠ p in 𝓝[>] (0 : ℝ) ×ˢ 𝓝 w0,
      differenceQuotient f x_bar p.2 p.1 ≤ ((‖v‖ / ε : ℝ) : EReal) :=
    hprod.frequently (Filter.Frequently.of_forall fun n => hbound (ns n))
  have hsub : subderivative f x_bar w0 ≤ ((‖v‖ / ε : ℝ) : EReal) :=
    Filter.liminf_le_of_frequently_le' hfreq
  have hdom : w0 ∈ effDom (subderivative f x_bar) :=
    lt_of_le_of_lt hsub (EReal.coe_lt_top _)
  have hle := hv w0 hdom
  linarith

/- ===== from taskF ===== -/


lemma F5_log_ineq (t : ℝ) (ht : -1/2 ≤ t) : t - 2 * t^2 ≤ Real.log (1 + t) := by
  have h1 : 0 < 1 + t := by linarith
  have h3 := Real.one_sub_inv_le_log_of_pos h1
  have h2 : t - 2 * t^2 ≤ 1 - (1 + t)⁻¹ := by
    rw [show 1 - (1 + t)⁻¹ = t / (1 + t) by field_simp; ring]
    rw [le_div_iff₀ h1]
    nlinarith [mul_nonneg (sq_nonneg t) (by linarith : (0:ℝ) ≤ 1 + 2 * t)]
  linarith

lemma F5_regular (f : E → EReal) (xs z : E) (A b c₀ κ s : ℝ)
    (hA : 0 < A) (hb : 0 < b) (hκ : 0 < κ) (hs : 0 < s)
    (hfin : ⊥ < f xs ∧ f xs < ⊤)
    (hbot : ∀ x ∈ Metric.ball xs s, ⊥ < f x)
    (hmin : ∀ x ∈ Metric.ball xs s, f x < ⊤ → f x ≤ f xs + (κ : EReal) →
        ‖xs - z‖^2 + A * Real.exp (((f xs).toReal - c₀)/b)
          ≤ ‖x - z‖^2 + A * Real.exp (((f x).toReal - c₀)/b)) :
    IsRegularSubgradientAt f xs ((2 * b / (A * Real.exp (((f xs).toReal - c₀)/b))) • (z - xs)) := by
  set C := A * Real.exp (((f xs).toReal - c₀)/b) with hC
  have hCpos : 0 < C := mul_pos hA (Real.exp_pos _)
  set u := (2 * b / C) • (z - xs) with hu
  set L : E → ℝ := fun x => ‖xs - z‖^2 - ‖x - z‖^2 with hL
  set r : E → ℝ := fun x => -(b / C) * ‖x - xs‖^2 - 2 * b * (L x / C)^2 with hr
  have hLid : ∀ x, L x = 2 * inner ℝ (z - xs) (x - xs) - ‖x - xs‖^2 := by
    intro x
    simp only [hL]
    have e1 : x - z = (x - xs) - (z - xs) := by abel
    have e2 : xs - z = -(z - xs) := by abel
    rw [e1, e2, norm_sub_sq_real, norm_neg, real_inner_comm]
    ring
  have hid : ∀ x, inner ℝ u (x - xs) + r x = b * (L x / C) - 2 * b * (L x / C)^2 := by
    intro x
    simp only [hu, hr, real_inner_smul_left]
    rw [hLid x]
    field_simp
    ring
  have hLbound : ∀ x, |L x| ≤ (2 * ‖z - xs‖ + ‖x - xs‖) * ‖x - xs‖ := by
    intro x
    rw [hLid x]
    have h1 : |inner ℝ (z - xs) (x - xs)| ≤ ‖z - xs‖ * ‖x - xs‖ := abs_real_inner_le_norm _ _
    rw [abs_le] at h1 ⊢
    have h2 := norm_nonneg (x - xs)
    have h3 := norm_nonneg (z - xs)
    constructor <;> nlinarith [h1.1, h1.2, sq_nonneg ‖x - xs‖]
  have hr_nonpos : ∀ x, r x ≤ 0 := by
    intro x
    simp only [hr]
    have : 0 ≤ b / C * ‖x - xs‖^2 := by positivity
    have : 0 ≤ 2 * b * (L x / C)^2 := by positivity
    linarith
  refine ⟨hfin.1, hfin.2, r, ?_, ?_⟩
  · -- little o
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    set K := b / C + 2 * b * ((2 * ‖z - xs‖ + 1) / C)^2 with hK
    have hKpos : 0 < K := by positivity
    have hball : Metric.ball xs (min 1 (c / K)) ∈ 𝓝 xs :=
      Metric.ball_mem_nhds _ (lt_min one_pos (div_pos hc hKpos))
    filter_upwards [hball] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hx1 : ‖x - xs‖ < 1 := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : ‖x - xs‖ < c / K := lt_of_lt_of_le hx (min_le_right _ _)
    have hn := norm_nonneg (x - xs)
    have hLx : |L x| ≤ (2 * ‖z - xs‖ + 1) * ‖x - xs‖ := by
      calc |L x| ≤ (2 * ‖z - xs‖ + ‖x - xs‖) * ‖x - xs‖ := hLbound x
        _ ≤ (2 * ‖z - xs‖ + 1) * ‖x - xs‖ := by gcongr
    have hLC : (L x / C)^2 ≤ ((2 * ‖z - xs‖ + 1) / C)^2 * ‖x - xs‖^2 := by
      rw [div_pow, div_pow, ← sq_abs (L x)]
      have : |L x|^2 ≤ ((2 * ‖z - xs‖ + 1) * ‖x - xs‖)^2 := by
        gcongr
      calc |L x|^2 / C^2 ≤ ((2 * ‖z - xs‖ + 1) * ‖x - xs‖)^2 / C^2 := by gcongr
        _ = (2 * ‖z - xs‖ + 1)^2 / C^2 * ‖x - xs‖^2 := by ring
    have hr_bound : |r x| ≤ K * ‖x - xs‖^2 := by
      rw [abs_of_nonpos (hr_nonpos x)]
      simp only [hr, hK]
      have : 0 ≤ b := hb.le
      nlinarith [hLC]
    rw [Real.norm_eq_abs, norm_norm]
    calc |r x| ≤ K * ‖x - xs‖^2 := hr_bound
      _ = (K * ‖x - xs‖) * ‖x - xs‖ := by ring
      _ ≤ c * ‖x - xs‖ := by
        gcongr
        have := (lt_div_iff₀ hKpos).1 hx2
        linarith
  · -- inequality on a neighbourhood
    set s' := min s (min 1 (min (κ / (‖u‖ + 1)) (C / (2 * (2 * ‖z - xs‖ + 1))))) with hs'
    have hs'pos : 0 < s' := by
      apply lt_min hs
      apply lt_min one_pos
      apply lt_min
      · positivity
      · positivity
    refine ⟨Metric.ball xs s', Metric.ball_mem_nhds _ hs'pos, ?_⟩
    intro x hx
    have hxs : x ∈ Metric.ball xs s :=
      Metric.ball_subset_ball (min_le_left _ _) hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hn := norm_nonneg (x - xs)
    have hx1 : ‖x - xs‖ ≤ 1 := by
      have := lt_of_lt_of_le hx (min_le_right _ _); exact le_trans this.le (min_le_left _ _)
    have hx3 : ‖x - xs‖ ≤ κ / (‖u‖ + 1) := by
      have := lt_of_lt_of_le hx (min_le_right _ _)
      exact le_trans (le_trans this.le (min_le_right _ _)) (min_le_left _ _)
    have hx4 : ‖x - xs‖ ≤ C / (2 * (2 * ‖z - xs‖ + 1)) := by
      have := lt_of_lt_of_le hx (min_le_right _ _)
      exact le_trans (le_trans this.le (min_le_right _ _)) (min_le_right _ _)
    -- value of f xs
    obtain ⟨a, ha⟩ : ∃ a : ℝ, f xs = (a : EReal) :=
      ⟨(f xs).toReal, (EReal.coe_toReal hfin.2.ne hfin.1.ne').symm⟩
    have hlin : inner ℝ u (x - xs) ≤ κ := by
      have h1 : inner ℝ u (x - xs) ≤ ‖u‖ * ‖x - xs‖ := real_inner_le_norm _ _
      have h2 : ‖u‖ * ‖x - xs‖ ≤ κ := by
        have := mul_le_mul_of_nonneg_left hx3 (norm_nonneg u)
        calc ‖u‖ * ‖x - xs‖ ≤ ‖u‖ * (κ / (‖u‖ + 1)) := this
          _ ≤ κ := by
            rw [mul_div_assoc']
            rw [div_le_iff₀ (by positivity)]
            nlinarith [norm_nonneg u]
      linarith
    by_cases htop : f x = ⊤
    · rw [htop]; exact le_top
    by_cases hbig : f xs + (κ : EReal) < f x
    · refine le_trans ?_ hbig.le
      rw [ha, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
      linarith [hr_nonpos x]
    push_neg at hbig
    have hfx_lt : f x < ⊤ := lt_top_iff_ne_top.2 htop
    have hm := hmin x hxs hfx_lt hbig
    obtain ⟨d, hd⟩ : ∃ d : ℝ, f x = (d : EReal) :=
      ⟨(f x).toReal, (EReal.coe_toReal htop (hbot x hxs).ne').symm⟩
    rw [hd] at hm
    rw [ha, hd]
    simp only [EReal.toReal_coe] at hm
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, hid x]
    -- t := L x / C
    set t := L x / C with ht
    have hLx : |L x| ≤ C / 2 := by
      calc |L x| ≤ (2 * ‖z - xs‖ + ‖x - xs‖) * ‖x - xs‖ := hLbound x
        _ ≤ (2 * ‖z - xs‖ + 1) * ‖x - xs‖ := by gcongr
        _ ≤ (2 * ‖z - xs‖ + 1) * (C / (2 * (2 * ‖z - xs‖ + 1))) := by gcongr
        _ = C / 2 := by field_simp
    have htabs : -1/2 ≤ t := by
      rw [ht, le_div_iff₀ hCpos]
      have := (abs_le.1 hLx).1
      linarith
    have hpos : 0 < 1 + t := by linarith
    -- from hm: A * exp((d - c₀)/b) ≥ C + L x = C * (1 + t)
    have hkey : C * (1 + t) ≤ A * Real.exp ((d - c₀) / b) := by
      have : C * (1 + t) = C + L x := by rw [ht]; field_simp
      rw [this]
      simp only [hL] at hm ⊢
      linarith
    -- C = A * exp((a - c₀)/b)
    have hCa : C = A * Real.exp ((a - c₀) / b) := by
      rw [hC, ha, EReal.toReal_coe]
    rw [hCa] at hkey
    have hkey2 : Real.exp ((a - c₀) / b) * (1 + t) ≤ Real.exp ((d - c₀) / b) := by
      have := hkey
      rw [mul_assoc] at this
      exact le_of_mul_le_mul_left this hA
    have hkey3 : Real.log (1 + t) ≤ (d - c₀) / b - (a - c₀) / b := by
      have h1 : Real.log (Real.exp ((a - c₀) / b) * (1 + t)) ≤ Real.log (Real.exp ((d - c₀) / b)) :=
        Real.log_le_log (by positivity) hkey2
      rw [Real.log_mul (Real.exp_pos _).ne' hpos.ne', Real.log_exp, Real.log_exp] at h1
      linarith
    have hlog := F5_log_ineq t htabs
    have : (d - c₀) / b - (a - c₀) / b = (d - a) / b := by ring
    rw [this] at hkey3
    have h4 : t - 2 * t^2 ≤ (d - a) / b := le_trans hlog hkey3
    rw [le_div_iff₀ hb] at h4
    nlinarith [h4]

/-! ### Helpers for agent F -/

/-- Step 0: a lower bound for `f` near `x_bar` coming from local lower semicontinuity. -/
lemma F_lsc_lower (f : E → EReal) (x_bar : E) (c ε₀ α : ℝ) (hc : f x_bar = (c : EReal))
    (hε₀pos : 0 < ε₀) (hα : α < c)
    (hcl : IsClosed {x | x ∈ Metric.closedBall x_bar ε₀ ∧ f x ≤ (α : EReal)}) :
    ∃ r > 0, ∀ x, ‖x - x_bar‖ ≤ r → (α : EReal) < f x := by
  have hxK : x_bar ∉ {x | x ∈ Metric.closedBall x_bar ε₀ ∧ f x ≤ (α : EReal)} := by
    rintro ⟨_, h⟩
    rw [hc, EReal.coe_le_coe_iff] at h
    linarith
  obtain ⟨r', hr', hball⟩ := Metric.isOpen_iff.mp hcl.isOpen_compl x_bar hxK
  refine ⟨min (r' / 2) ε₀, lt_min (by positivity) hε₀pos, fun x hx => ?_⟩
  have h1 : x ∈ Metric.ball x_bar r' := by
    rw [Metric.mem_ball, dist_eq_norm]
    linarith [min_le_left (r' / 2) ε₀]
  have h2 : x ∈ Metric.closedBall x_bar ε₀ := by
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [min_le_right (r' / 2) ε₀]
  have h3 := hball h1
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at h3
  exact h3 h2

/-- `x ↦ (f x).toReal` is lower semicontinuous on `S` when the relevant sublevel sets are
closed and `f` is finite on `S`. -/
lemma F_toReal_lsc (f : E → EReal) (S T : Set E) (β : ℝ) (hST : S ⊆ T)
    (hS : ∀ x ∈ S, ⊥ < f x ∧ f x ≤ (β : EReal))
    (hcl : ∀ α : ℝ, α ≤ β → IsClosed {x | x ∈ T ∧ f x ≤ (α : EReal)}) :
    LowerSemicontinuousOn (fun x => (f x).toReal) S := by
  intro x hx y hy
  obtain ⟨hxb, hxβ⟩ := hS x hx
  have hxt : f x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top β) hxβ
  have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal hxt hxb.ne').symm
  have hyβ : y ≤ β := by
    have h1 : (f x).toReal ≤ β := by
      have h2 := hxβ
      rw [hfx] at h2
      exact EReal.coe_le_coe_iff.mp h2
    have h3 : y < (f x).toReal := hy
    linarith
  have hK := hcl y hyβ
  have hxK : x ∉ {x | x ∈ T ∧ f x ≤ (y : EReal)} := by
    rintro ⟨_, h⟩
    rw [hfx] at h
    have h4 := EReal.coe_le_coe_iff.mp h
    have h3 : y < (f x).toReal := hy
    linarith
  have hmem : {x | x ∈ T ∧ f x ≤ (y : EReal)}ᶜ ∈ 𝓝 x := hK.isOpen_compl.mem_nhds hxK
  filter_upwards [mem_nhdsWithin_of_mem_nhds hmem, self_mem_nhdsWithin] with x' hx'1 hx'2
  obtain ⟨hb', hβ'⟩ := hS x' hx'2
  have ht' : f x' ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top β) hβ'
  have hfx' : f x' = ((f x').toReal : EReal) := (EReal.coe_toReal ht' hb'.ne').symm
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at hx'1
  have h5 := hx'1 (hST hx'2)
  rw [hfx'] at h5
  exact EReal.coe_lt_coe_iff.mp h5

/-- Lower semicontinuity of the smoothed objective `Φ`. -/
lemma F_Phi_lsc (f : E → EReal) (S T : Set E) (β c A b : ℝ) (z : E) (hA : 0 < A) (hb : 0 < b)
    (hST : S ⊆ T) (hS : ∀ x ∈ S, ⊥ < f x ∧ f x ≤ (β : EReal))
    (hcl : ∀ α : ℝ, α ≤ β → IsClosed {x | x ∈ T ∧ f x ≤ (α : EReal)}) :
    LowerSemicontinuousOn (fun x => ‖x - z‖^2 + A * Real.exp (((f x).toReal - c) / b)) S := by
  have h1 := F_toReal_lsc f S T β hST hS hcl
  have hmono : Monotone (fun s : ℝ => A * Real.exp ((s - c) / b)) := by
    intro s t hst
    have h2 : (s - c) / b ≤ (t - c) / b := div_le_div_of_nonneg_right (by linarith) hb.le
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h2) hA.le
  have hcont : Continuous (fun s : ℝ => A * Real.exp ((s - c) / b)) := by fun_prop
  have h2 : LowerSemicontinuousOn (fun x => A * Real.exp (((f x).toReal - c) / b)) S :=
    hcont.comp_lowerSemicontinuousOn h1 hmono
  have h3 : LowerSemicontinuousOn (fun x : E => ‖x - z‖^2) S :=
    (by fun_prop : Continuous (fun x : E => ‖x - z‖^2)).lowerSemicontinuous.lowerSemicontinuousOn S
  exact h3.add h2

/-- Choice of the step size `τ`. -/
lemma F_exists_tau (P e m η : ℝ) (hP : 0 ≤ P) (he : 0 < e) (hm : 0 < m) (hη : 0 < η) :
    ∃ τ > 0, τ * (2 * P + e) ≤ m ∧ τ * e ≤ η := by
  have hd : 0 < 2 * P + e := by linarith
  refine ⟨min (m / (2 * P + e)) (η / e), lt_min (div_pos hm hd) (div_pos hη he), ?_, ?_⟩
  · have h : min (m / (2 * P + e)) (η / e) ≤ m / (2 * P + e) := min_le_left _ _
    rwa [le_div_iff₀ hd] at h
  · have h : min (m / (2 * P + e)) (η / e) ≤ η / e := min_le_right _ _
    rwa [le_div_iff₀ he] at h

/-- First (crude) localisation of the minimiser. -/
lemma F_ybound (τ e A q : ℝ) (v y : E) (hτ : 0 < τ) (he : 0 < e) (hA : A = (τ * e)^2)
    (hq : 0 < q) (hΦ : ‖y - τ • v‖^2 + A * q ≤ ‖τ • v‖^2 + A) :
    ‖y‖ < τ * (2 * ‖v‖ + e) := by
  have hnv : ‖τ • v‖ = τ * ‖v‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have h1 : ‖y‖ - τ * ‖v‖ ≤ ‖y - τ • v‖ := by rw [← hnv]; exact norm_sub_norm_le y (τ • v)
  rw [hnv] at hΦ
  have hA0 : 0 < A := by rw [hA]; positivity
  have hAq : 0 < A * q := mul_pos hA0 hq
  by_contra hcon
  push_neg at hcon
  have h2 : τ * ‖v‖ + τ * e ≤ ‖y - τ • v‖ := by nlinarith
  have h3 : 0 ≤ τ * ‖v‖ + τ * e := by positivity
  have h4 : (τ * ‖v‖ + τ * e)^2 ≤ ‖y - τ • v‖^2 := pow_le_pow_left₀ h3 h2 2
  have h5 : 0 ≤ τ * ‖v‖ * (τ * e) := by positivity
  nlinarith

/-- The main estimates on the minimiser (Step 3). -/
lemma F_estimates (τ e A b Δ : ℝ) (v y : E) (hτ : 0 < τ) (he : 0 < e) (hA : A = (τ * e)^2)
    (hb : b = τ * e / 2)
    (hΦ : ‖y - τ • v‖^2 + A * Real.exp (Δ / b) ≤ ‖τ • v‖^2 + A)
    (hcase : inner ℝ v y ≤ e * ‖y‖ ∨ inner ℝ v y / e ≤ Δ) :
    ‖y‖ ≤ 3 * (τ * e) ∧ Real.exp (Δ / b) ≤ 2 := by
  have hb0 : 0 < b := by rw [hb]; positivity
  have hA0 : 0 < A := by rw [hA]; positivity
  obtain ⟨X, hX⟩ : ∃ X, X = Real.exp (Δ / b) := ⟨_, rfl⟩
  rw [← hX] at hΦ ⊢
  have hX0 : 0 < X := by rw [hX]; exact Real.exp_pos _
  have hexp : ‖y - τ • v‖^2 = ‖y‖^2 - 2 * τ * inner ℝ v y + ‖τ • v‖^2 := by
    rw [norm_sub_sq_real, real_inner_smul_right, real_inner_comm]; ring
  rw [hexp] at hΦ
  have key : ‖y‖^2 - 2 * τ * inner ℝ v y + A * X ≤ A := by linarith
  have hcs : inner ℝ v y ≤ ‖v‖ * ‖y‖ := real_inner_le_norm v y
  have hny := norm_nonneg y
  have hyv : inner ℝ v y ≤ e * ‖y‖ := by
    rcases hcase with h | h
    · exact h
    · by_contra hlt
      push_neg at hlt
      have h1 : Δ / b + 1 ≤ X := by rw [hX]; exact Real.add_one_le_exp _
      have h2 : A * (Δ / b) = 2 * τ * (e * Δ) := by
        rw [hA, hb]; field_simp
      have h3 : inner ℝ v y ≤ e * Δ := by
        have h3' := (div_le_iff₀ he).mp h
        linarith [mul_comm Δ e]
      have h4 : A * (Δ / b + 1) ≤ A * X := mul_le_mul_of_nonneg_left h1 hA0.le
      have h3'' : 2 * τ * inner ℝ v y ≤ 2 * τ * (e * Δ) :=
        mul_le_mul_of_nonneg_left h3 (by positivity)
      have h5 : ‖y‖^2 ≤ 0 := by nlinarith
      have h6 : ‖y‖ = 0 := by nlinarith
      rw [h6] at hcs hlt
      linarith
  have hτy : 2 * τ * inner ℝ v y ≤ 2 * τ * (e * ‖y‖) := mul_le_mul_of_nonneg_left hyv (by positivity)
  have key2 : ‖y‖^2 - 2 * τ * (e * ‖y‖) + A * X ≤ A := by linarith
  have hAX : 0 < A * X := mul_pos hA0 hX0
  constructor
  · by_contra hlt
    push_neg at hlt
    have hk : 0 < τ * e := by positivity
    nlinarith [mul_pos (by linarith : (0:ℝ) < ‖y‖ - 3 * (τ * e)) (by linarith : (0:ℝ) < ‖y‖ + τ * e)]
  · by_contra hlt
    push_neg at hlt
    nlinarith [sq_nonneg (‖y‖ - τ * e), mul_pos hA0 (by linarith : (0:ℝ) < X - 2)]

/-- The rescaled subgradient is close to `v`. -/
lemma F_lu_norm (x_bar v xs : E) (τ : ℝ) (hτ : 0 < τ) :
    ‖τ⁻¹ • (x_bar + τ • v - xs) - v‖ = ‖xs - x_bar‖ / τ := by
  have h : τ⁻¹ • (x_bar + τ • v - xs) - v = τ⁻¹ • (x_bar - xs) := by
    rw [show x_bar + τ • v - xs = (x_bar - xs) + τ • v by abel, smul_add, smul_smul,
      inv_mul_cancel₀ hτ.ne', one_smul]
    abel
  rw [h, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hτ, norm_sub_rev, inv_mul_eq_div]

/-- Splitting the exponential term. -/
lemma F_exp_split (A c a b g : ℝ) :
    A * Real.exp ((g - c) / b) = A * Real.exp ((a - c) / b) * Real.exp ((g - a) / b) := by
  rw [mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-! Agent F: one approximation step for horizon subgradients -/

lemma horizon_step (f : E → EReal) (x_bar v : E)
    (hf : ⊥ < f x_bar ∧ f x_bar < ⊤) (hlsc : LocalLscAt f x_bar)
    (hI : ∀ ε > 0, ∃ θ > 0, ∀ y : E, ‖y‖ ≤ θ →
      inner ℝ v y ≤ ε * ‖y‖ ∨ (((inner ℝ v y / ε : ℝ)) : EReal) ≤ f (x_bar + y) - f x_bar)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ x' u : E, ∃ l : ℝ, ‖x' - x_bar‖ ≤ ε ∧ f x' ≤ f x_bar + (ε : EReal) ∧
      f x_bar - (ε : EReal) ≤ f x' ∧ 0 < l ∧ l ≤ ε ∧ ‖l • u - v‖ ≤ ε ∧
      IsRegularSubgradientAt f x' u := by
  obtain ⟨hfb, hft⟩ := hf
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f x_bar = (c : EReal) :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal hft.ne hfb.ne').symm⟩
  have hxbar_toReal : (f x_bar).toReal = c := by rw [hc, EReal.toReal_coe]
  obtain ⟨_, _, ε₀, hε₀⟩ := hlsc
  have hε₀pos : 0 < ε₀ := (hε₀ (c + ε₀) (by rw [hc, EReal.coe_add])).1
  have hZ : ∀ α : ℝ, α ≤ c + ε₀ →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε₀ ∧ f x ≤ (α : EReal)} := by
    intro α hα
    refine (hε₀ α ?_).2
    rw [hc, ← EReal.coe_add, EReal.coe_le_coe_iff]; exact hα
  -- Step 0: lower bound near x_bar
  have hγ : 0 < min ε 1 := lt_min hε one_pos
  obtain ⟨r₁, hr₁, hlow⟩ := F_lsc_lower f x_bar c ε₀ (c - min ε 1) hc hε₀pos (by linarith)
    (hZ _ (by linarith))
  -- Step 1: parameters
  obtain ⟨e, he_def⟩ : ∃ e : ℝ, e = ε / 4 := ⟨_, rfl⟩
  have he : 0 < e := by rw [he_def]; positivity
  obtain ⟨θ, hθ, hIθ⟩ := hI e he
  obtain ⟨ρ, hρ_def⟩ : ∃ ρ : ℝ, ρ = min r₁ ε₀ := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρ_def]; exact lt_min hr₁ hε₀pos
  have hρr₁ : ρ ≤ r₁ := by rw [hρ_def]; exact min_le_left _ _
  have hρε₀ : ρ ≤ ε₀ := by rw [hρ_def]; exact min_le_right _ _
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = min θ (min ρ ε) := ⟨_, rfl⟩
  have hm : 0 < m := by rw [hm_def]; exact lt_min hθ (lt_min hρ hε)
  have hmθ : m ≤ θ := by rw [hm_def]; exact min_le_left _ _
  have hmρ : m ≤ ρ := by rw [hm_def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hmε : m ≤ ε := by rw [hm_def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨τ, hτ, hτm, hτη⟩ :=
    F_exists_tau ‖v‖ e m (min ε₀ ε) (norm_nonneg v) he hm (lt_min hε₀pos hε)
  have hτε₀ : τ * e ≤ ε₀ := le_trans hτη (min_le_left _ _)
  have hτε : τ * e ≤ ε := le_trans hτη (min_le_right _ _)
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = (τ * e)^2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = τ * e / 2 := ⟨_, rfl⟩
  have hA0 : 0 < A := by rw [hA]; positivity
  have hb0 : 0 < b := by rw [hb]; positivity
  obtain ⟨z, hz⟩ : ∃ z : E, z = x_bar + τ • v := ⟨_, rfl⟩
  -- Step 2: the compact set and the minimiser
  let K : Set E := {x | x ∈ Metric.closedBall x_bar ε₀ ∧ f x ≤ ((c + ε₀ : ℝ) : EReal)}
  have hKcl : IsClosed K := hZ (c + ε₀) le_rfl
  let S : Set E := Metric.closedBall x_bar ρ ∩ K
  have hScpt : IsCompact S := (isCompact_closedBall x_bar ρ).inter_right hKcl
  have hxbarS : x_bar ∈ S := by
    refine ⟨Metric.mem_closedBall_self hρ.le, Metric.mem_closedBall_self hε₀pos.le, ?_⟩
    rw [hc, EReal.coe_le_coe_iff]; linarith
  have hSprop : ∀ x ∈ S, ⊥ < f x ∧ f x ≤ ((c + ε₀ : ℝ) : EReal) := by
    intro x hx
    refine ⟨?_, hx.2.2⟩
    have h1 : ‖x - x_bar‖ ≤ r₁ := by
      have h2 := hx.1
      rw [Metric.mem_closedBall, dist_eq_norm] at h2
      linarith
    exact lt_trans (EReal.bot_lt_coe _) (hlow x h1)
  have hΦlsc : LowerSemicontinuousOn
      (fun x => ‖x - z‖^2 + A * Real.exp (((f x).toReal - c) / b)) S :=
    F_Phi_lsc f S (Metric.closedBall x_bar ε₀) (c + ε₀) c A b z hA0 hb0 (fun x hx => hx.2.1)
      hSprop hZ
  obtain ⟨xs, hxsS, hxsmin⟩ := hΦlsc.exists_isMinOn ⟨x_bar, hxbarS⟩ hScpt
  rw [isMinOn_iff] at hxsmin
  -- basic facts on the minimiser
  have hxs_bot : ⊥ < f xs := (hSprop xs hxsS).1
  have hxs_top : f xs ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) (hSprop xs hxsS).2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f xs = (a : EReal) :=
    ⟨(f xs).toReal, (EReal.coe_toReal hxs_top hxs_bot.ne').symm⟩
  have hxs_toReal : (f xs).toReal = a := by rw [ha, EReal.toReal_coe]
  have hxsρ : ‖xs - x_bar‖ ≤ ρ := by
    have h2 := hxsS.1
    rwa [Metric.mem_closedBall, dist_eq_norm] at h2
  -- Step 3: estimates
  have hΦ := hxsmin x_bar hxbarS
  simp only [hxs_toReal, hxbar_toReal, sub_self, zero_div, Real.exp_zero, mul_one] at hΦ
  have hz1 : xs - z = (xs - x_bar) - τ • v := by rw [hz]; abel
  have hz2 : ‖x_bar - z‖ = ‖τ • v‖ := by
    rw [hz, show x_bar - (x_bar + τ • v) = -(τ • v) by abel, norm_neg]
  rw [hz1, hz2] at hΦ
  have hy1 : ‖xs - x_bar‖ < τ * (2 * ‖v‖ + e) :=
    F_ybound τ e A _ v (xs - x_bar) hτ he hA (Real.exp_pos _) hΦ
  have hym : ‖xs - x_bar‖ < m := lt_of_lt_of_le hy1 hτm
  have hcase : inner ℝ v (xs - x_bar) ≤ e * ‖xs - x_bar‖ ∨
      inner ℝ v (xs - x_bar) / e ≤ a - c := by
    rcases hIθ (xs - x_bar) (by linarith) with h | h
    · exact Or.inl h
    · right
      rw [show x_bar + (xs - x_bar) = xs by abel, ha, hc, ← EReal.coe_sub,
        EReal.coe_le_coe_iff] at h
      exact h
  obtain ⟨hy3, hexp2⟩ := F_estimates τ e A b (a - c) v (xs - x_bar) hτ he hA hb hΦ hcase
  have hΔb : a - c < b := by
    have h1 : Real.exp ((a - c) / b) < Real.exp 1 := by
      have h2 := Real.exp_one_gt_d9
      have h3 : (2 : ℝ) < Real.exp 1 := by linarith
      linarith
    rw [Real.exp_lt_exp, div_lt_one hb0] at h1
    exact h1
  -- Step 4: outputs
  have hCdef : A * Real.exp (((f xs).toReal - c) / b) = A * Real.exp ((a - c) / b) := by
    rw [hxs_toReal]
  refine ⟨xs, (2 * b / (A * Real.exp (((f xs).toReal - c) / b))) • (z - xs),
    e * Real.exp ((a - c) / b), by linarith, ?_, ?_, by positivity, ?_, ?_, ?_⟩
  · -- f xs ≤ f x_bar + ε
    rw [ha, hc, ← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith
  · -- f x_bar - ε ≤ f xs
    have h1 := hlow xs (by linarith)
    rw [hc, ← EReal.coe_sub]
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) h1.le
    linarith [min_le_left ε 1]
  · -- l ≤ ε
    have h1 := mul_le_mul_of_nonneg_left hexp2 he.le
    linarith
  · -- ‖l • u - v‖ ≤ ε
    rw [smul_smul, hCdef]
    have h1 : e * Real.exp ((a - c) / b) * (2 * b / (A * Real.exp ((a - c) / b))) = τ⁻¹ := by
      rw [hA, hb]
      field_simp
    rw [h1, hz, F_lu_norm x_bar v xs τ hτ, div_le_iff₀ hτ]
    nlinarith [mul_pos hε hτ]
  · -- regular subgradient at xs
    have hs0 : 0 < ρ - ‖xs - x_bar‖ := by linarith
    have hκ : 0 < c + ε₀ - a := by linarith
    refine F5_regular f xs z A b c (c + ε₀ - a) (ρ - ‖xs - x_bar‖) hA0 hb0 hκ hs0
      ⟨hxs_bot, lt_top_iff_ne_top.mpr hxs_top⟩ ?_ ?_
    · intro x hx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h1 : ‖x - x_bar‖ ≤ r₁ := by
        have h2 : ‖x - x_bar‖ ≤ ‖x - xs‖ + ‖xs - x_bar‖ := by
          rw [show x - x_bar = (x - xs) + (xs - x_bar) by abel]; exact norm_add_le _ _
        linarith
      exact lt_trans (EReal.bot_lt_coe _) (hlow x h1)
    · intro x hx _ hfx
      rw [Metric.mem_ball, dist_eq_norm] at hx
      have h2 : ‖x - x_bar‖ ≤ ‖x - xs‖ + ‖xs - x_bar‖ := by
        rw [show x - x_bar = (x - xs) + (xs - x_bar) by abel]; exact norm_add_le _ _
      have hxS : x ∈ S := by
        refine ⟨?_, ?_, ?_⟩
        · rw [Metric.mem_closedBall, dist_eq_norm]; linarith
        · rw [Metric.mem_closedBall, dist_eq_norm]; linarith
        · rw [ha, ← EReal.coe_add] at hfx
          rw [show c + ε₀ = a + (c + ε₀ - a) by ring]
          exact hfx
      exact hxsmin x hxS

/- ===== from taskB ===== -/

/-! Agent B: subadditivity of the regular subderivative, convexity of the subderivative -/


/-- An EReal neighbourhood of a real point contains a symmetric real open interval. -/
lemma B_ereal_nhds (c : ℝ) (t : Set EReal) (ht : t ∈ 𝓝 (c : EReal)) :
    ∃ η > 0, Set.Ioo ((c - η : ℝ) : EReal) ((c + η : ℝ) : EReal) ⊆ t := by
  rcases (mem_nhds_iff_exists_Ioo_subset' ⟨⊥, EReal.bot_lt_coe c⟩ ⟨⊤, EReal.coe_lt_top c⟩).1 ht with
    ⟨l, u, ⟨hl, hu⟩, hsub⟩
  obtain ⟨a, hla, hac⟩ := EReal.lt_iff_exists_real_btwn.1 hl
  obtain ⟨b, hcb, hbu⟩ := EReal.lt_iff_exists_real_btwn.1 hu
  have hac' : a < c := EReal.coe_lt_coe_iff.1 hac
  have hcb' : c < b := EReal.coe_lt_coe_iff.1 hcb
  refine ⟨min (c - a) (b - c), lt_min (by linarith) (by linarith), fun y hy => hsub ⟨?_, ?_⟩⟩
  · calc l < (a : EReal) := hla
      _ ≤ ((c - min (c - a) (b - c) : ℝ) : EReal) :=
          EReal.coe_le_coe_iff.2 (by linarith [min_le_left (c - a) (b - c)])
      _ < y := hy.1
  · calc y < ((c + min (c - a) (b - c) : ℝ) : EReal) := hy.2
      _ ≤ (b : EReal) := EReal.coe_le_coe_iff.2 (by linarith [min_le_right (c - a) (b - c)])
      _ < u := hbu

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Building an eventually-statement for the filter `fApproach ×ˢ 𝓝[>] 0` from explicit radii. -/
lemma B_eventually_of_ball (f : E → EReal) (x_bar : E) (c : ℝ) (hc : f x_bar = c)
    (P : E × ℝ → Prop) (r η θ : ℝ) (hr : 0 < r) (hη : 0 < η) (hθ : 0 < θ)
    (h : ∀ x τ, dist x x_bar < r → ((c - η : ℝ) : EReal) < f x → f x < ((c + η : ℝ) : EReal) →
      0 < τ → τ < θ → P (x, τ)) :
    ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)), P p := by
  have h1 : Metric.ball x_bar r ∩ f ⁻¹' (Set.Ioo ((c - η : ℝ) : EReal) ((c + η : ℝ) : EReal))
      ∈ fApproach f x_bar := by
    apply Filter.inter_mem_inf (Metric.ball_mem_nhds _ hr)
    apply Filter.preimage_mem_comap
    rw [hc]
    apply Ioo_mem_nhds
    · exact EReal.coe_lt_coe_iff.2 (by linarith)
    · exact EReal.coe_lt_coe_iff.2 (by linarith)
  have h2 : Set.Ioo (0:ℝ) θ ∈ 𝓝[>] (0:ℝ) := Ioo_mem_nhdsGT hθ
  filter_upwards [Filter.prod_mem_prod h1 h2] with p hp
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  exact h p.1 p.2 hp1 hp2.1 hp2.2 hp3.1 hp3.2

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Extracting explicit radii from an eventually-statement for `fApproach ×ˢ 𝓝[>] 0`. -/
lemma B_ball_of_eventually (f : E → EReal) (x_bar : E) (c : ℝ) (hc : f x_bar = c)
    (P : E × ℝ → Prop) (h : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)), P p) :
    ∃ r > 0, ∃ η > 0, ∃ θ > 0, ∀ x τ, dist x x_bar < r → ((c - η : ℝ) : EReal) < f x →
      f x < ((c + η : ℝ) : EReal) → 0 < τ → τ < θ → P (x, τ) := by
  rw [Filter.eventually_prod_iff] at h
  obtain ⟨pa, hpa, pb, hpb, hP⟩ := h
  obtain ⟨θ, hθ, hθ'⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hpb
  unfold fApproach at hpa
  obtain ⟨t₁, ht₁, t₂, ht₂, hsub⟩ := Filter.mem_inf_iff_superset.1 hpa
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 ht₁
  obtain ⟨t, ht, htsub⟩ := Filter.mem_comap.1 ht₂
  rw [hc] at ht
  obtain ⟨η, hη, hηsub⟩ := B_ereal_nhds c t ht
  refine ⟨r, hr, η, hη, θ, hθ, fun x τ hx h1 h2 h3 h4 => ?_⟩
  exact hP (hsub ⟨hball hx, htsub (hηsub ⟨h1, h2⟩)⟩) (hθ' ⟨h3, h4⟩)

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Local lower semicontinuity gives a uniform lower bound near `x_bar`. -/
lemma B_lsc_lower (f : E → EReal) (x_bar : E) (c : ℝ) (hc : f x_bar = c)
    (hlsc : LocalLscAt f x_bar) (η : ℝ) (hη : 0 < η) :
    ∃ r > 0, ∀ x, dist x x_bar < r → ((c - η : ℝ) : EReal) < f x := by
  obtain ⟨-, -, ε, hε⟩ := hlsc
  have hε0 : ε > 0 := (hε (c + ε) (by rw [hc, EReal.coe_add])).1
  have hcl := (hε (c - η) (by
    rw [hc, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.2 (by linarith))).2
  have hmem : x_bar ∈ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ ((c - η : ℝ) : EReal)}ᶜ := by
    intro hx
    have h2 := hx.2
    rw [hc] at h2
    have := EReal.coe_le_coe_iff.1 h2
    linarith
  obtain ⟨r₁, hr₁, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x_bar hmem
  refine ⟨min r₁ ε, lt_min hr₁ hε0, fun x hx => ?_⟩
  have h1 : x ∈ Metric.ball x_bar r₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : x ∈ Metric.closedBall x_bar ε := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
  have h3 := hball h1
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at h3
  exact h3 h2

/-- EReal arithmetic for difference quotients with a finite base value. -/
lemma B_quot_lt_iff (a : EReal) (y τ β : ℝ) (hτ : 0 < τ) :
    (a - (y : EReal)) / (τ : EReal) < (β : EReal) ↔ a < ((y + τ * β : ℝ) : EReal) := by
  have hτ' : (0 : EReal) < (τ : EReal) := EReal.coe_pos.2 hτ
  have hτt : (τ : EReal) ≠ ⊤ := EReal.coe_ne_top τ
  induction a using EReal.rec with
  | bot =>
    simp only [EReal.bot_sub, EReal.bot_div_of_pos_ne_top hτ' hτt, EReal.bot_lt_coe]
  | top =>
    simp only [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top hτ' hτt, not_top_lt]
  | coe z =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff,
      div_lt_iff₀ hτ]
    constructor <;> intro h <;> linarith

omit [FiniteDimensional ℝ E] in
/-- (F1)+(F2): the inner limsup at a positive radius bounds the regular subderivative from below. -/
lemma B_inner_le_rsd (f : E → EReal) (x_bar w : E) (δ : ℝ) (hδ : 0 < δ) :
    Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) ≤ regularSubderivative f x_bar w := by
  unfold regularSubderivative
  refine Filter.le_limsup_of_frequently_le ?_
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ'
  refine Filter.limsup_le_limsup (Filter.Eventually.of_forall fun p => ?_)
  exact sInf_le_sInf (Set.image_mono (Metric.closedBall_subset_closedBall hδ'.2.le))

/-- Monotonicity of multiplication by a positive real in EReal (target is real). -/
lemma B_mul_le (s : ℝ) (hs : 0 < s) (a : EReal) (b : ℝ) (h : a ≤ b) :
    (s : EReal) * a ≤ ((s * b : ℝ) : EReal) := by
  induction a using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hs]; exact bot_le
  | top => exact absurd h (not_le.2 (EReal.coe_lt_top b))
  | coe z =>
    rw [← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.2 (mul_le_mul_of_nonneg_left (EReal.coe_le_coe_iff.1 h) hs.le)

/-- An EReal bounded by `A + η` for every `η > 0` is bounded by `A`. -/
lemma B_le_of_forall (X : EReal) (A : ℝ) (h : ∀ η : ℝ, 0 < η → X ≤ ((A + η : ℝ) : EReal)) :
    X ≤ (A : EReal) := by
  apply le_of_forall_gt_imp_ge_of_dense
  intro a ha
  obtain ⟨z, hAz, hza⟩ := EReal.lt_iff_exists_real_btwn.1 ha
  have hAz' : A < z := EReal.coe_lt_coe_iff.1 hAz
  calc X ≤ ((A + (z - A) : ℝ) : EReal) := h (z - A) (by linarith)
    _ = (z : EReal) := by congr 1; ring
    _ ≤ a := hza.le

/-- Main step: combining a `w₂`-good step and a `w₁`-good step. -/
lemma B_main (f : E → EReal) (x_bar : E) (c : ℝ) (hc : f x_bar = c)
    (hlsc : LocalLscAt f x_bar) (w₁ w₂ : E) (β₁ β₂ δ : ℝ) (hδ : 0 < δ)
    (h₁ : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      sInf ((delta f p.1 p.2) '' Metric.closedBall w₁ (δ / 2)) < (β₁ : EReal))
    (h₂ : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      sInf ((delta f p.1 p.2) '' Metric.closedBall w₂ (δ / 2)) < (β₂ : EReal)) :
    ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)),
      sInf ((delta f p.1 p.2) '' Metric.closedBall (w₁ + w₂) δ) < ((β₁ + β₂ : ℝ) : EReal) := by
  obtain ⟨r₁, hr₁, η₁, hη₁, θ₁, hθ₁, H₁⟩ := B_ball_of_eventually f x_bar c hc _ h₁
  obtain ⟨r₂, hr₂, η₂, hη₂, θ₂, hθ₂, H₂⟩ := B_ball_of_eventually f x_bar c hc _ h₂
  obtain ⟨r₀, hr₀, H₀⟩ := B_lsc_lower f x_bar c hc hlsc η₁ hη₁
  -- parameters
  obtain ⟨R, hR0, hRr₁, hRr₀⟩ : ∃ R : ℝ, 0 < R ∧ R ≤ r₁ ∧ R ≤ r₀ :=
    ⟨min r₁ r₀, lt_min hr₁ hr₀, min_le_left _ _, min_le_right _ _⟩
  obtain ⟨M, hM0, hMw⟩ : ∃ M : ℝ, 0 < M ∧ ‖w₂‖ + δ / 2 ≤ M :=
    ⟨‖w₂‖ + δ / 2 + 1, by positivity, by linarith⟩
  obtain ⟨θ, hθ0, hθ1, hθ2, hθ3, hθ4⟩ : ∃ θ : ℝ, 0 < θ ∧ θ ≤ θ₁ ∧ θ ≤ θ₂ ∧
      θ ≤ R / (2 * M) ∧ θ ≤ η₁ / (2 * (|β₂| + 1)) :=
    ⟨min θ₁ (min θ₂ (min (R / (2 * M)) (η₁ / (2 * (|β₂| + 1))))),
      lt_min hθ₁ (lt_min hθ₂ (lt_min (by positivity) (by positivity))),
      min_le_left _ _, le_trans (min_le_right _ _) (min_le_left _ _),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)),
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))⟩
  obtain ⟨r, hr0, hrr₂, hrR⟩ : ∃ r : ℝ, 0 < r ∧ r ≤ r₂ ∧ r ≤ R / 2 :=
    ⟨min r₂ (R / 2), lt_min hr₂ (by positivity), min_le_left _ _, min_le_right _ _⟩
  obtain ⟨η, hη0, hηη₂, hηη₁⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ η₂ ∧ η ≤ η₁ / 2 :=
    ⟨min η₂ (η₁ / 2), lt_min hη₂ (by positivity), min_le_left _ _, min_le_right _ _⟩
  apply B_eventually_of_ball f x_bar c hc _ r η θ hr0 hη0 hθ0
  intro x τ hx hfx1 hfx2 hτ0 hτθ
  -- f x is finite
  have hfx_ne_bot : f x ≠ ⊥ := ne_bot_of_gt hfx1
  have hfx_ne_top : f x ≠ ⊤ := ne_top_of_lt hfx2
  obtain ⟨y, hfxy⟩ : ∃ y : ℝ, f x = (y : EReal) :=
    ⟨(f x).toReal, (EReal.coe_toReal hfx_ne_top hfx_ne_bot).symm⟩
  have hy1 : c - η < y := by rw [hfxy] at hfx1; exact EReal.coe_lt_coe_iff.1 hfx1
  have hy2 : y < c + η := by rw [hfxy] at hfx2; exact EReal.coe_lt_coe_iff.1 hfx2
  -- step 1: (x, τ) is w₂-good
  have G₂ : sInf ((delta f x τ) '' Metric.closedBall w₂ (δ / 2)) < (β₂ : EReal) :=
    H₂ x τ (lt_of_lt_of_le hx hrr₂)
      (by rw [hfxy]; exact EReal.coe_lt_coe_iff.2 (by linarith))
      (by rw [hfxy]; exact EReal.coe_lt_coe_iff.2 (by linarith))
      hτ0 (lt_of_lt_of_le hτθ hθ2)
  obtain ⟨_, ⟨w₂', hw₂', rfl⟩, hlt₂⟩ := sInf_lt_iff.1 G₂
  have hq₂ : f (x + τ • w₂') < ((y + τ * β₂ : ℝ) : EReal) := by
    have : delta f x τ w₂' = (f (x + τ • w₂') - (y : EReal)) / (τ : EReal) := by
      simp only [delta, differenceQuotient, hfxy]
    rw [this, B_quot_lt_iff _ _ _ _ hτ0] at hlt₂
    exact hlt₂
  -- norm bound on w₂'
  have hw₂'n : ‖w₂'‖ ≤ ‖w₂‖ + δ / 2 := by
    have h := Metric.mem_closedBall.1 hw₂'
    rw [dist_eq_norm] at h
    calc ‖w₂'‖ = ‖(w₂' - w₂) + w₂‖ := by rw [sub_add_cancel]
      _ ≤ ‖w₂' - w₂‖ + ‖w₂‖ := norm_add_le _ _
      _ ≤ δ / 2 + ‖w₂‖ := by linarith
      _ = ‖w₂‖ + δ / 2 := by ring
  have hτM : τ * M < R / 2 := by
    have h1 : τ < R / (2 * M) := lt_of_lt_of_le hτθ hθ3
    rw [lt_div_iff₀ (by positivity)] at h1
    linarith
  have hτβ : τ * |β₂| < η₁ / 2 := by
    have h1 : τ < η₁ / (2 * (|β₂| + 1)) := lt_of_lt_of_le hτθ hθ4
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [abs_nonneg β₂]
  have hx'dist : dist (x + τ • w₂') x_bar < R := by
    have e1 : dist (x + τ • w₂') x = τ * ‖w₂'‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hτ0.le]
    have e2 : τ * ‖w₂'‖ ≤ τ * M := mul_le_mul_of_nonneg_left (by linarith) hτ0.le
    have e3 := dist_triangle (x + τ • w₂') x x_bar
    have e4 : dist x x_bar < R / 2 := lt_of_lt_of_le hx hrR
    linarith
  have hfx'1 : ((c - η₁ : ℝ) : EReal) < f (x + τ • w₂') :=
    H₀ _ (lt_of_lt_of_le hx'dist hRr₀)
  have hfx'2 : f (x + τ • w₂') < ((c + η₁ : ℝ) : EReal) := by
    refine lt_of_lt_of_le hq₂ (EReal.coe_le_coe_iff.2 ?_)
    have : τ * β₂ ≤ τ * |β₂| := mul_le_mul_of_nonneg_left (le_abs_self β₂) hτ0.le
    linarith
  -- step 2: (x + τ • w₂', τ) is w₁-good
  have G₁ : sInf ((delta f (x + τ • w₂') τ) '' Metric.closedBall w₁ (δ / 2)) < (β₁ : EReal) :=
    H₁ _ τ (lt_of_lt_of_le hx'dist hRr₁) hfx'1 hfx'2 hτ0 (lt_of_lt_of_le hτθ hθ1)
  obtain ⟨_, ⟨w₁', hw₁', rfl⟩, hlt₁⟩ := sInf_lt_iff.1 G₁
  have hfx'_ne_bot : f (x + τ • w₂') ≠ ⊥ := ne_bot_of_gt hfx'1
  have hfx'_ne_top : f (x + τ • w₂') ≠ ⊤ := ne_top_of_lt hfx'2
  obtain ⟨z, hfx'z⟩ : ∃ z : ℝ, f (x + τ • w₂') = (z : EReal) :=
    ⟨(f (x + τ • w₂')).toReal, (EReal.coe_toReal hfx'_ne_top hfx'_ne_bot).symm⟩
  have hq₁ : f (x + τ • w₂' + τ • w₁') < ((z + τ * β₁ : ℝ) : EReal) := by
    have : delta f (x + τ • w₂') τ w₁'
        = (f (x + τ • w₂' + τ • w₁') - (z : EReal)) / (τ : EReal) := by
      simp only [delta, differenceQuotient, hfx'z]
    rw [this, B_quot_lt_iff _ _ _ _ hτ0] at hlt₁
    exact hlt₁
  have hzy : z < y + τ * β₂ := by
    rw [hfx'z] at hq₂
    exact EReal.coe_lt_coe_iff.1 hq₂
  -- conclusion
  have hmem : w₁' + w₂' ∈ Metric.closedBall (w₁ + w₂) δ := by
    rw [Metric.mem_closedBall]
    calc dist (w₁' + w₂') (w₁ + w₂) ≤ dist w₁' w₁ + dist w₂' w₂ := dist_add_add_le _ _ _ _
      _ ≤ δ / 2 + δ / 2 :=
          add_le_add (Metric.mem_closedBall.1 hw₁') (Metric.mem_closedBall.1 hw₂')
      _ = δ := by ring
  refine lt_of_le_of_lt (sInf_le (Set.mem_image_of_mem _ hmem)) ?_
  show delta f x τ (w₁' + w₂') < ((β₁ + β₂ : ℝ) : EReal)
  have hpt : x + τ • (w₁' + w₂') = x + τ • w₂' + τ • w₁' := by
    rw [smul_add]; abel
  have : delta f x τ (w₁' + w₂') = (f (x + τ • w₂' + τ • w₁') - (y : EReal)) / (τ : EReal) := by
    simp only [delta, differenceQuotient, hfxy, hpt]
  rw [this, B_quot_lt_iff _ _ _ _ hτ0]
  refine lt_of_lt_of_le hq₁ (EReal.coe_le_coe_iff.2 ?_)
  have : y + τ * (β₁ + β₂) = (y + τ * β₂) + τ * β₁ := by ring
  linarith

lemma regularSubderivative_add_le (f : E → EReal) (x_bar : E) (hf : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hlsc : LocalLscAt f x_bar) (w₁ w₂ : E) (β₁ β₂ : ℝ)
    (h₁ : regularSubderivative f x_bar w₁ < β₁) (h₂ : regularSubderivative f x_bar w₂ < β₂) :
    regularSubderivative f x_bar (w₁ + w₂) ≤ ((β₁ + β₂ : ℝ) : EReal) := by
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f x_bar = c :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal hf.2.ne hf.1.ne').symm⟩
  have key : ∀ δ : ℝ, 0 < δ →
      Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall (w₁ + w₂) δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) ≤ ((β₁ + β₂ : ℝ) : EReal) := by
    intro δ hδ
    have e₁ := Filter.eventually_lt_of_limsup_lt
      (lt_of_le_of_lt (B_inner_le_rsd f x_bar w₁ (δ / 2) (by positivity)) h₁)
    have e₂ := Filter.eventually_lt_of_limsup_lt
      (lt_of_le_of_lt (B_inner_le_rsd f x_bar w₂ (δ / 2) (by positivity)) h₂)
    have := B_main f x_bar c hc hlsc w₁ w₂ β₁ β₂ δ hδ e₁ e₂
    exact Filter.limsup_le_of_le (h := this.mono (fun p hp => hp.le))
  unfold regularSubderivative
  exact Filter.limsup_le_of_le (h := Filter.eventually_of_mem self_mem_nhdsWithin key)

lemma convex_subderivative (f : E → EReal) (x_bar : E) (hf : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hlsc : LocalLscAt f x_bar)
    (heq : ∀ w, subderivative f x_bar w = regularSubderivative f x_bar w) :
    ConvexEReal (subderivative f x_bar) := by
  have hpos := subderivative_posHom f x_bar
  intro p hp q hq s t hs ht hst
  simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rcases hs.eq_or_lt with hs0 | hs0
  · have ht1 : t = 1 := by linarith
    subst ht1
    subst hs0
    simpa using hq
  rcases ht.eq_or_lt with ht0 | ht0
  · have hs1 : s = 1 := by linarith
    subst hs1
    subst ht0
    simpa using hp
  apply B_le_of_forall
  intro η hη
  have e1 : regularSubderivative f x_bar (s • p.1) < ((s * p.2 + η / 2 : ℝ) : EReal) := by
    rw [← heq, hpos p.1 s hs0]
    exact lt_of_le_of_lt (B_mul_le s hs0 _ _ hp) (EReal.coe_lt_coe_iff.2 (by linarith))
  have e2 : regularSubderivative f x_bar (t • q.1) < ((t * q.2 + η / 2 : ℝ) : EReal) := by
    rw [← heq, hpos q.1 t ht0]
    exact lt_of_le_of_lt (B_mul_le t ht0 _ _ hq) (EReal.coe_lt_coe_iff.2 (by linarith))
  rw [heq]
  calc regularSubderivative f x_bar (s • p.1 + t • q.1)
      ≤ (((s * p.2 + η / 2) + (t * q.2 + η / 2) : ℝ) : EReal) :=
        regularSubderivative_add_le f x_bar hf hlsc _ _ _ _ e1 e2
    _ = ((s * p.2 + t * q.2 + η : ℝ) : EReal) := by congr 1; ring

/- ===== from taskG ===== -/

/-! Agent G: assembling horizon subgradients from approximation steps -/



lemma horizon_of_polar (f : E → EReal) (x_bar v : E)
    (hf : ⊥ < f x_bar ∧ f x_bar < ⊤) (hlsc : LocalLscAt f x_bar)
    (hv : v ∈ polarCone (effDom (subderivative f x_bar))) :
    v ∈ horizonSubdifferential f x_bar := by
  have hI : ∀ ε > 0, ∃ θ > 0, ∀ y : E, ‖y‖ ≤ θ →
      inner ℝ v y ≤ ε * ‖y‖ ∨ (((inner ℝ v y / ε : ℝ)) : EReal) ≤ f (x_bar + y) - f x_bar :=
    fun ε hε => polar_key_ineq f x_bar v hv ε hε
  have hstep : ∀ n : ℕ, ∃ x' u : E, ∃ l : ℝ, ‖x' - x_bar‖ ≤ 1 / ((n : ℝ) + 1) ∧
      f x' ≤ f x_bar + ((1 / ((n : ℝ) + 1) : ℝ) : EReal) ∧
      f x_bar - ((1 / ((n : ℝ) + 1) : ℝ) : EReal) ≤ f x' ∧ 0 < l ∧ l ≤ 1 / ((n : ℝ) + 1) ∧
      ‖l • u - v‖ ≤ 1 / ((n : ℝ) + 1) ∧ IsRegularSubgradientAt f x' u := fun n =>
    horizon_step f x_bar v hf hlsc hI (1 / ((n : ℝ) + 1)) (by positivity)
  choose x u l hx hfu hfl hl0 hl1 hlu hreg using hstep
  have h0 : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  refine ⟨hf.1, hf.2, x, u, l, ?_, ?_, ?_, ?_, hreg⟩
  · -- x n → x_bar
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hx h0
  · -- f (x n) → f x_bar
    set c : ℝ := (f x_bar).toReal with hc_def
    have hc : f x_bar = (c : EReal) := (EReal.coe_toReal hf.2.ne hf.1.ne').symm
    rw [hc]
    have hlo : ∀ n : ℕ, (((c - 1 / ((n : ℝ) + 1)) : ℝ) : EReal) ≤ f (x n) := by
      intro n
      have := hfl n
      rw [hc] at this
      rw [EReal.coe_sub]
      exact this
    have hup : ∀ n : ℕ, f (x n) ≤ (((c + 1 / ((n : ℝ) + 1)) : ℝ) : EReal) := by
      intro n
      have := hfu n
      rw [hc] at this
      rw [EReal.coe_add]
      exact this
    have h1 : Filter.Tendsto (fun n : ℕ => (((c - 1 / ((n : ℝ) + 1)) : ℝ) : EReal))
        Filter.atTop (𝓝 (c : EReal)) := by
      apply EReal.tendsto_coe.2
      simpa using (tendsto_const_nhds (x := c)).sub h0
    have h2 : Filter.Tendsto (fun n : ℕ => (((c + 1 / ((n : ℝ) + 1)) : ℝ) : EReal))
        Filter.atTop (𝓝 (c : EReal)) := by
      apply EReal.tendsto_coe.2
      simpa using (tendsto_const_nhds (x := c)).add h0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 h2 hlo hup
  · -- l → 0⁺
    refine tendsto_nhdsWithin_iff.2 ⟨?_, Filter.Eventually.of_forall hl0⟩
    exact squeeze_zero (fun n => (hl0 n).le) hl1 h0
  · -- l n • u n → v
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) hlu h0

/- ===== from taskH1 ===== -/

/-! Agent H1: proper lsc sublinear functions are support functions -/

lemma H1_ereal_le_of_forall {x : EReal} {y : ℝ} (H : ∀ b : ℝ, x ≤ b → y ≤ b) :
    (y : EReal) ≤ x := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨b, hxb, hby⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have h1 := H b hxb.le
  have h2 : b < y := EReal.coe_lt_coe_iff.1 hby
  linarith

omit [FiniteDimensional ℝ E] in
lemma H1_mem_of_sep (h : E → EReal) (g : E) (κ : ℝ) (hκ : κ < 0)
    (hsep : ∀ p ∈ epigraph h, inner ℝ g p.1 + κ * p.2 ≤ 0) :
    (-κ)⁻¹ • g ∈ supportSublevelSet h := by
  intro w'
  apply H1_ereal_le_of_forall
  intro b hb
  have hb' := hsep (w', b) hb
  simp only at hb'
  rw [real_inner_smul_left, inv_mul_le_iff₀ (by linarith)]
  linarith

lemma H1_cone_sep (C : Set (E × ℝ)) (hconv : Convex ℝ C) (hclosed : IsClosed C)
    (h00 : (0 : E × ℝ) ∈ C) (hcone : ∀ p ∈ C, ∀ t : ℝ, 0 < t → t • p ∈ C)
    (q : E × ℝ) (hq : q ∉ C) :
    ∃ g : E, ∃ κ : ℝ, (∀ p ∈ C, inner ℝ g p.1 + κ * p.2 ≤ 0) ∧
      0 < inner ℝ g q.1 + κ * q.2 := by
  obtain ⟨ψ, u, hψC, hψq⟩ := geometric_hahn_banach_closed_point hconv hclosed hq
  have hu : 0 < u := by simpa using hψC 0 h00
  have hle : ∀ p ∈ C, ψ p ≤ 0 := by
    intro p hp
    by_contra hcon
    push_neg at hcon
    have ht : 0 < u / ψ p + 1 := add_pos (div_pos hu hcon) one_pos
    have := hψC _ (hcone p hp _ ht)
    rw [map_smul, smul_eq_mul, add_mul, div_mul_cancel₀ _ hcon.ne'] at this
    linarith
  have hdecomp : ∀ p : E × ℝ,
      ψ p = inner ℝ ((InnerProductSpace.toDual ℝ E).symm
        (ψ.comp (ContinuousLinearMap.inl ℝ E ℝ))) p.1 + ψ (0, 1) * p.2 := by
    intro p
    rw [InnerProductSpace.toDual_symm_apply]
    have hp : p = (p.1, 0) + p.2 • ((0 : E), (1 : ℝ)) := by ext <;> simp
    conv_lhs => rw [hp]
    rw [map_add, map_smul, smul_eq_mul]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
    ring
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (ψ.comp (ContinuousLinearMap.inl ℝ E ℝ)),
    ψ (0, 1), ?_, ?_⟩
  · intro p hp
    rw [← hdecomp]
    exact hle p hp
  · rw [← hdecomp]
    linarith

lemma sublinear_support (h : E → EReal) (hlsc : LowerSemicontinuous h)
    (hsub : IsSublinearRW h) (h0 : h 0 ≠ ⊥) :
    (supportSublevelSet h).Nonempty ∧ ∀ w, h w = supportFunction (supportSublevelSet h) w := by
  obtain ⟨⟨hdom, hhom⟩, hconv⟩ := hsub
  have hh0 : h 0 = 0 := by
    have h2 := hhom 0 2 (by norm_num)
    rw [smul_zero] at h2
    obtain ⟨a, ha⟩ : ∃ a : ℝ, h 0 = a := ⟨(h 0).toReal, (EReal.coe_toReal hdom.ne h0).symm⟩
    rw [ha, ← EReal.coe_mul, EReal.coe_eq_coe_iff] at h2
    rw [ha]
    have : a = 0 := by linarith
    simp [this]
  have hclosed : IsClosed (epigraph h) := by
    have := hlsc.isClosed_epigraph
    have hcont : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
      continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
    exact this.preimage hcont
  have hcone : ∀ p ∈ epigraph h, ∀ t : ℝ, 0 < t → t • p ∈ epigraph h := by
    intro p hp t ht
    show h (t • p).1 ≤ ((t • p).2 : EReal)
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [hhom p.1 t ht, EReal.coe_mul]
    exact mul_le_mul_of_nonneg_left hp (EReal.coe_nonneg.2 ht.le)
  have h00 : (0 : E × ℝ) ∈ epigraph h := by
    show h 0 ≤ ((0 : ℝ) : EReal)
    rw [hh0]; simp
  have h01 : ((0 : E), (1 : ℝ)) ∈ epigraph h := by
    show h 0 ≤ ((1 : ℝ) : EReal)
    rw [hh0]; simp
  -- nonempty
  obtain ⟨v₀, hv₀⟩ : (supportSublevelSet h).Nonempty := by
    have hq : ((0 : E), (-1 : ℝ)) ∉ epigraph h := by
      intro hq
      change h 0 ≤ ((-1 : ℝ) : EReal) at hq
      rw [hh0] at hq
      have : (0 : ℝ) ≤ -1 := by exact_mod_cast hq
      linarith
    obtain ⟨g, κ, hsep, hpos⟩ := H1_cone_sep _ hconv hclosed h00 hcone _ hq
    simp only [inner_zero_right] at hpos
    exact ⟨_, H1_mem_of_sep h g κ (by linarith) hsep⟩
  have key : ∀ w : E, ∀ α : ℝ, (α : EReal) < h w →
      ∃ v ∈ supportSublevelSet h, α < inner ℝ v w := by
    intro w α hα
    have hq : (w, α) ∉ epigraph h := by
      intro hq
      change h w ≤ (α : EReal) at hq
      exact absurd hα (not_lt.2 hq)
    obtain ⟨g, κ, hsep, hpos⟩ := H1_cone_sep _ hconv hclosed h00 hcone _ hq
    have hκ : κ ≤ 0 := by
      have := hsep _ h01
      simp only [inner_zero_right] at this
      linarith
    simp only at hpos
    rcases hκ.lt_or_eq with hκ | hκ
    · refine ⟨_, H1_mem_of_sep h g κ hκ hsep, ?_⟩
      rw [real_inner_smul_left, lt_inv_mul_iff₀ (by linarith)]
      linarith
    · subst hκ
      have hcpos : 0 < inner ℝ g w := by linarith
      obtain ⟨t, ht0, htc⟩ : ∃ t : ℝ, 0 ≤ t ∧ α < inner ℝ v₀ w + t * inner ℝ g w := by
        refine ⟨|α - inner ℝ v₀ w| / inner ℝ g w + 1,
          add_nonneg (div_nonneg (abs_nonneg _) hcpos.le) zero_le_one, ?_⟩
        rw [add_mul, div_mul_cancel₀ _ hcpos.ne', one_mul]
        have := le_abs_self (α - inner ℝ v₀ w)
        linarith
      refine ⟨v₀ + t • g, ?_, ?_⟩
      · intro w'
        apply H1_ereal_le_of_forall
        intro b hb
        have h1 := hsep (w', b) hb
        simp only [zero_mul, add_zero] at h1
        have h2 : inner ℝ v₀ w' ≤ b := EReal.coe_le_coe_iff.1 ((hv₀ w').trans hb)
        rw [inner_add_left, real_inner_smul_left]
        nlinarith
      · rw [inner_add_left, real_inner_smul_left]
        exact htc
  refine ⟨⟨v₀, hv₀⟩, fun w => le_antisymm ?_ ?_⟩
  · by_contra hcon
    push_neg at hcon
    obtain ⟨α, hα1, hα2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
    obtain ⟨v, hv, hvα⟩ := key w α hα2
    have h1 : ((inner ℝ v w : ℝ) : EReal) ≤ supportFunction (supportSublevelSet h) w :=
      le_sSup ⟨v, hv, rfl⟩
    have h2 : (α : EReal) < (inner ℝ v w : ℝ) := EReal.coe_lt_coe_iff.2 hvα
    exact absurd (hα1.trans (h2.trans_le h1)) (lt_irrefl _)
  · unfold supportFunction
    apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    exact hv w

/- ===== from taskH2 ===== -/

/-! Agent H2: bipolar of the domain, closedness/convexity of support sublevel sets -/

lemma H2_coe_mul_lt_top {c : ℝ} (hc : 0 < c) {z : EReal} (hz : z < ⊤) :
    (c : EReal) * z < ⊤ := by
  induction z using EReal.rec with
  | bot => rw [EReal.coe_mul_bot_of_pos hc]; exact bot_lt_top
  | coe r => rw [← EReal.coe_mul]; exact EReal.coe_lt_top _
  | top => exact absurd hz (lt_irrefl _)

lemma H2_effDom_smul (h : E → EReal) (hsub : IsSublinearRW h) {c : ℝ} (hc : 0 < c) {x : E}
    (hx : x ∈ effDom h) : c • x ∈ effDom h := by
  have hh := hsub.1.2 x c hc
  simp only [effDom, Set.mem_setOf_eq] at hx ⊢
  rw [hh]
  exact H2_coe_mul_lt_top hc hx

lemma H2_effDom_convex (h : E → EReal) (hsub : IsSublinearRW h) {x y : E}
    (hx : x ∈ effDom h) (hy : y ∈ effDom h) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hab : a + b = 1) : a • x + b • y ∈ effDom h := by
  simp only [effDom, Set.mem_setOf_eq] at hx hy ⊢
  obtain ⟨α, hα, -⟩ := EReal.lt_iff_exists_real_btwn.1 hx
  obtain ⟨β, hβ, -⟩ := EReal.lt_iff_exists_real_btwn.1 hy
  have h1 : ((x, α) : E × ℝ) ∈ epigraph h := by
    simp only [epigraph, Set.mem_setOf_eq]; exact hα.le
  have h2 : ((y, β) : E × ℝ) ∈ epigraph h := by
    simp only [epigraph, Set.mem_setOf_eq]; exact hβ.le
  have h3 := hsub.2 h1 h2 ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.smul_fst, Prod.snd_add,
    Prod.smul_snd, smul_eq_mul] at h3
  exact lt_of_le_of_lt h3 (EReal.coe_lt_top _)

lemma H2_effDom_add (h : E → EReal) (hsub : IsSublinearRW h) {x y : E}
    (hx : x ∈ effDom h) (hy : y ∈ effDom h) : x + y ∈ effDom h := by
  have hm := H2_effDom_convex h hsub hx hy (a := 1/2) (b := 1/2) (by norm_num) (by norm_num)
    (by norm_num)
  have h2 := H2_effDom_smul h hsub (c := 2) (by norm_num) hm
  have heq : (2 : ℝ) • ((1/2 : ℝ) • x + (1/2 : ℝ) • y) = x + y := by
    rw [smul_add, smul_smul, smul_smul]; norm_num
  rwa [heq] at h2

lemma H2_polarCone_closed (K : Set E) : IsClosed (polarCone K) := by
  have : polarCone K = ⋂ x ∈ K, {s : E | inner ℝ s x ≤ 0} := by
    ext s; simp [polarCone]
  rw [this]
  exact isClosed_biInter fun x _ => isClosed_le (continuous_id.inner continuous_const)
    continuous_const

lemma H2_subset_polar_polar (K : Set E) : K ⊆ polarCone (polarCone K) := by
  intro x hx s hs
  rw [real_inner_comm]
  exact hs x hx

lemma polar_polar_effDom (h : E → EReal) (hsub : IsSublinearRW h) :
    polarCone (polarCone (effDom h)) = closure (effDom h) := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨K0, hK0⟩ : ∃ K0 : ConvexCone ℝ E, (K0 : Set E) = effDom h :=
    ⟨⟨effDom h, fun c hc x hx => H2_effDom_smul h hsub hc hx,
      fun x hx y hy => H2_effDom_add h hsub hx hy⟩, rfl⟩
  apply Set.Subset.antisymm
  · intro x hx
    by_contra hxc
    have hdisj : x ∉ K0.closure := by
      rw [← SetLike.mem_coe, ConvexCone.coe_closure, hK0]; exact hxc
    have hne : (K0.closure : Set E).Nonempty := by
      refine ⟨0, ?_⟩
      rw [ConvexCone.coe_closure, hK0]
      exact subset_closure hsub.1.1
    have hcl : IsClosed (K0.closure : Set E) := by
      rw [ConvexCone.coe_closure]; exact isClosed_closure
    obtain ⟨y, hy1, hy2⟩ :=
      ConvexCone.hyperplane_separation_of_nonempty_of_isClosed_of_notMem K0.closure hne hcl hdisj
    have hneg : -y ∈ polarCone (effDom h) := by
      intro x' hx'
      have hx'c : x' ∈ K0.closure := by
        rw [← SetLike.mem_coe, ConvexCone.coe_closure, hK0]; exact subset_closure hx'
      have := hy1 x' hx'c
      rw [inner_neg_left, real_inner_comm]
      linarith
    have h4 := hx (-y) hneg
    rw [inner_neg_right, real_inner_comm] at h4
    linarith
  · exact closure_minimal (H2_subset_polar_polar _) (H2_polarCone_closed _)

lemma supportSublevelSet_closed (h : E → EReal) : IsClosed (supportSublevelSet h) := by
  have : supportSublevelSet h = ⋂ w, {v : E | (((inner ℝ v w) : ℝ) : EReal) ≤ h w} := by
    ext v; simp [supportSublevelSet]
  rw [this]
  exact isClosed_iInter fun w =>
    isClosed_le (continuous_coe_real_ereal.comp (continuous_id.inner continuous_const))
      continuous_const

lemma supportSublevelSet_convex (h : E → EReal) : Convex ℝ (supportSublevelSet h) := by
  intro v₁ hv₁ v₂ hv₂ a b ha hb hab w
  have h1 := hv₁ w
  have h2 := hv₂ w
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  generalize h w = z at h1 h2 ⊢
  induction z using EReal.rec with
  | bot => exact absurd h1 (by simp)
  | coe c =>
    rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
    have e1 := mul_le_mul_of_nonneg_left h1 ha
    have e2 := mul_le_mul_of_nonneg_left h2 hb
    have e3 : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith
  | top => exact le_top

/-! Glue lemmas and the main theorem -/

lemma subdiff_eq (f : E → EReal) (x_bar : E) (hreg : IsRegularAt f x_bar) :
    subdifferential f x_bar = supportSublevelSet (subderivative f x_bar) := by
  obtain ⟨hf, hlsc, heq⟩ := hreg
  ext v
  constructor
  · intro hv w
    rw [heq w]
    exact subgradient_le_regularSubderivative f x_bar v hv w
  · intro hv
    have hr := regularSubgradient_of_le_subderivative f x_bar v hf hv
    refine ⟨hf.1, hf.2, fun _ => x_bar, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => hr⟩

lemma subderivative_sublinear (f : E → EReal) (x_bar : E) (hreg : IsRegularAt f x_bar) :
    IsSublinearRW (subderivative f x_bar) := by
  obtain ⟨hf, hlsc, heq⟩ := hreg
  refine ⟨⟨?_, subderivative_posHom f x_bar⟩, convex_subderivative f x_bar hf hlsc heq⟩
  show subderivative f x_bar 0 < ⊤
  exact lt_of_le_of_lt (subderivative_zero_le f x_bar hf) EReal.zero_lt_top

lemma horizon_eq (f : E → EReal) (x_bar : E) (hreg : IsRegularAt f x_bar) :
    horizonSubdifferential f x_bar = polarCone (effDom (subderivative f x_bar)) := by
  obtain ⟨hf, hlsc, heq⟩ := hreg
  ext v
  constructor
  · intro hv w hw
    have hw' : regularSubderivative f x_bar w < ⊤ := by
      rw [← heq w]; exact hw
    exact horizon_le_zero f x_bar v hv w hw'
  · intro hv
    exact horizon_of_polar f x_bar v hf hlsc hv

theorem RW_chap_8_30
  (f : E → EReal)
  (x_bar : E)
  (hreg : IsRegularAt f x_bar) :
  ((Set.Nonempty (subdifferential f x_bar)) ↔
      subderivative f x_bar 0 ≠ ⊥) ∧
  ((Set.Nonempty (subdifferential f x_bar)) →
    (∀ (w : E),
      subderivative f x_bar w = supportFunction (subdifferential f x_bar) w) ∧
    (subdifferential f x_bar =
      supportSublevelSet (subderivative f x_bar)) ∧
    IsClosed (subdifferential f x_bar) ∧
    Convex ℝ (subdifferential f x_bar) ∧
    IsSublinearRW (subderivative f x_bar) ∧
    LowerSemicontinuous (subderivative f x_bar)) ∧
  (horizonSubdifferential f x_bar =
      polarCone (effDom (subderivative f x_bar))) ∧
  (polarCone (horizonSubdifferential f x_bar) =
      closure (effDom (subderivative f x_bar))) := by
  have hS := subdiff_eq f x_bar hreg
  have hsub := subderivative_sublinear f x_bar hreg
  have hlsc := subderivative_lsc f x_bar
  have hH := horizon_eq f x_bar hreg
  have hA : (Set.Nonempty (subdifferential f x_bar)) ↔ subderivative f x_bar 0 ≠ ⊥ := by
    constructor
    · rintro ⟨v, hv⟩
      rw [hS] at hv
      have h0 := hv 0
      rw [inner_zero_right, EReal.coe_zero] at h0
      intro hbot
      rw [hbot] at h0
      exact absurd h0 (by simp)
    · intro h0
      rw [hS]
      exact (sublinear_support _ hlsc hsub h0).1
  refine ⟨hA, ?_, hH, ?_⟩
  · intro hne
    have h0 := hA.1 hne
    refine ⟨?_, hS, ?_, ?_, hsub, hlsc⟩
    · rw [hS]
      exact (sublinear_support _ hlsc hsub h0).2
    · rw [hS]; exact supportSublevelSet_closed _
    · rw [hS]; exact supportSublevelSet_convex _
  · rw [hH]
    exact polar_polar_effDom _ hsub

end RW_chap_8_30
