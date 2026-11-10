import ConvexStarLib.Defs

/-!
# `RW_chap_8_22`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_8_22` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_8_22`, so the main result is `RW_chap_8_22.RW_chap_8_22`.
-/

namespace RW_chap_8_22

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedSectionVars false

noncomputable def RW822gδ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x_bar w : E) (δ : ℝ) : EReal :=
  Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
    ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ)))

noncomputable def RW822h {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x_bar w_bar : E) : EReal :=
  Filter.limsup (fun p : E × ℝ × E => delta f p.1 p.2.1 p.2.2)
    ((fApproach f x_bar) ×ˢ ((𝓝[>] 0) ×ˢ (𝓝 w_bar)))

def RW822good {E : Type*} [NormedAddCommGroup E] (f : E → EReal) (x_bar : E) (a ε : ℝ) :
    Set E :=
  {x | dist x x_bar < ε ∧ ((a - ε : ℝ) : EReal) < f x ∧ f x < ((a + ε : ℝ) : EReal)}

lemma RW822_good_mono {f : E → EReal} {x_bar : E} {a ε ε' : ℝ} (h : ε ≤ ε') :
    RW822good f x_bar a ε ⊆ RW822good f x_bar a ε' := by
  rintro x ⟨h1, h2, h3⟩
  refine ⟨lt_of_lt_of_le h1 h, lt_of_le_of_lt ?_ h2, lt_of_lt_of_le h3 ?_⟩
  · exact_mod_cast (by linarith : a - ε' ≤ a - ε)
  · exact_mod_cast (by linarith : a + ε ≤ a + ε')

lemma RW822_good_finite {f : E → EReal} {x_bar : E} {a ε : ℝ} {x : E}
    (hx : x ∈ RW822good f x_bar a ε) : f x = ((f x).toReal : EReal) := by
  obtain ⟨-, h2, h3⟩ := hx
  exact (EReal.coe_toReal (ne_top_of_lt h3) (ne_bot_of_gt h2)).symm

lemma RW822_ereal_basis {a : ℝ} : (𝓝 (a : EReal)).HasBasis (fun ε : ℝ => 0 < ε)
    (fun ε => Set.Ioo ((a - ε : ℝ) : EReal) ((a + ε : ℝ) : EReal)) := by
  rw [EReal.nhds_coe]
  refine (Metric.nhds_basis_ball (x := a)).map _ |>.to_hasBasis ?_ ?_
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    intro e he
    induction e using EReal.rec with
    | bot => exact absurd he.1 (not_lt.2 bot_le)
    | top => exact absurd he.2 (not_lt.2 le_top)
    | coe r =>
      refine ⟨r, ?_, rfl⟩
      have h1 : a - ε < r := by exact_mod_cast he.1
      have h2 : r < a + ε := by exact_mod_cast he.2
      rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff]
      constructor <;> linarith
  · intro ε hε
    refine ⟨ε, hε, ?_⟩
    rintro _ ⟨r, hr, rfl⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_lt_iff] at hr
    constructor <;> exact_mod_cast (by linarith)

lemma RW822_basisF {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a) :
    (fApproach f x_bar).HasBasis (fun ε : ℝ => 0 < ε) (RW822good f x_bar a) := by
  have hE : (𝓝 (f x_bar)).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => Set.Ioo ((a - ε : ℝ) : EReal) ((a + ε : ℝ) : EReal)) := by
    rw [ha]; exact RW822_ereal_basis
  have hB := (Metric.nhds_basis_ball (x := x_bar)).inf (hE.comap f)
  refine ⟨fun t => ?_⟩
  rw [fApproach, hB.mem_iff]
  constructor
  · rintro ⟨⟨ε1, ε2⟩, ⟨hε1, hε2⟩, hsub⟩
    refine ⟨min ε1 ε2, lt_min hε1 hε2, fun x hx => hsub ⟨?_, ?_, ?_⟩⟩
    · exact lt_of_lt_of_le hx.1 (min_le_left _ _)
    · exact lt_of_le_of_lt (by exact_mod_cast (by linarith [min_le_right ε1 ε2] :
        a - ε2 ≤ a - min ε1 ε2)) hx.2.1
    · exact lt_of_lt_of_le hx.2.2 (by exact_mod_cast (by linarith [min_le_right ε1 ε2] :
        a + min ε1 ε2 ≤ a + ε2))
  · rintro ⟨ε, hε, hsub⟩
    exact ⟨⟨ε, ε⟩, ⟨hε, hε⟩, fun x hx => hsub ⟨hx.1, hx.2.1, hx.2.2⟩⟩

lemma RW822_basisG {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a) :
    ((fApproach f x_bar) ×ˢ (𝓝[>] (0:ℝ))).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => RW822good f x_bar a ε ×ˢ Set.Ioo 0 ε) := by
  refine (RW822_basisF ha).prod_same_index_mono (nhdsGT_basis 0) ?_ ?_
  · intro i _ j _ hij
    exact RW822_good_mono hij
  · intro i _ j _ hij
    exact Set.Ioo_subset_Ioo_right hij

lemma RW822_basisH {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a) (w : E) :
    ((fApproach f x_bar) ×ˢ ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w)).HasBasis (fun ε : ℝ => 0 < ε)
      (fun ε => RW822good f x_bar a ε ×ˢ (Set.Ioo 0 ε ×ˢ Metric.ball w ε)) := by
  refine (RW822_basisF ha).prod_same_index_mono
    ((nhdsGT_basis 0).prod_same_index_mono Metric.nhds_basis_ball ?_ ?_) ?_ ?_
  · intro i _ j _ hij
    exact Set.Ioo_subset_Ioo_right hij
  · intro i _ j _ hij
    exact Metric.ball_subset_ball hij
  · intro i _ j _ hij
    exact RW822_good_mono hij
  · intro i _ j _ hij
    exact Set.prod_mono (Set.Ioo_subset_Ioo_right hij) (Metric.ball_subset_ball hij)

lemma RW822_delta_lt_iff {f : E → EReal} {x w : E} {τ b c : ℝ} (hτ : 0 < τ)
    (hb : f x = b) :
    delta f x τ w < (c : EReal) ↔ f (x + τ • w) < ((b + τ * c : ℝ) : EReal) := by
  unfold delta differenceQuotient
  rw [hb]
  generalize f (x + τ • w) = A
  induction A using EReal.rec with
  | bot =>
    rw [EReal.bot_sub, EReal.bot_div_of_pos_ne_top (by exact_mod_cast hτ) (EReal.coe_ne_top τ)]
    exact iff_of_true (EReal.bot_lt_coe _) (EReal.bot_lt_coe _)
  | top =>
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast hτ) (EReal.coe_ne_top τ)]
    exact iff_of_false (not_lt.2 le_top) (not_lt.2 le_top)
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_lt_coe_iff, EReal.coe_lt_coe_iff,
      div_lt_iff₀ hτ]
    constructor <;> intro h <;> linarith

lemma RW822_delta_le_iff {f : E → EReal} {x w : E} {τ b c : ℝ} (hτ : 0 < τ)
    (hb : f x = b) :
    delta f x τ w ≤ (c : EReal) ↔ f (x + τ • w) ≤ ((b + τ * c : ℝ) : EReal) := by
  unfold delta differenceQuotient
  rw [hb]
  generalize f (x + τ • w) = A
  induction A using EReal.rec with
  | bot =>
    rw [EReal.bot_sub, EReal.bot_div_of_pos_ne_top (by exact_mod_cast hτ) (EReal.coe_ne_top τ)]
    exact iff_of_true bot_le bot_le
  | top =>
    rw [EReal.top_sub_coe, EReal.top_div_of_pos_ne_top (by exact_mod_cast hτ) (EReal.coe_ne_top τ)]
    exact iff_of_false (not_le.2 (EReal.coe_lt_top _)) (not_le.2 (EReal.coe_lt_top _))
  | coe r =>
    rw [← EReal.coe_sub, ← EReal.coe_div, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff,
      div_le_iff₀ hτ]
    constructor <;> intro h <;> linarith

lemma RW822_le_delta_iff {f : E → EReal} {x w : E} {τ b c : ℝ} (hτ : 0 < τ)
    (hb : f x = b) :
    (c : EReal) ≤ delta f x τ w ↔ ((b + τ * c : ℝ) : EReal) ≤ f (x + τ • w) := by
  rw [← not_lt, RW822_delta_lt_iff hτ hb, not_lt]

lemma RW822_lt_delta_iff {f : E → EReal} {x w : E} {τ b c : ℝ} (hτ : 0 < τ)
    (hb : f x = b) :
    (c : EReal) < delta f x τ w ↔ ((b + τ * c : ℝ) : EReal) < f (x + τ • w) := by
  rw [← not_le, RW822_delta_le_iff hτ hb, not_le]

lemma RW822_lsc_below {f : E → EReal} {x_bar : E} {a εL : ℝ} (ha : f x_bar = a)
    (hεL : 0 < εL)
    (hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)})
    {η : ℝ} (hη : 0 < η) : ∃ r > 0, ∀ z, dist z x_bar < r → ((a - η : ℝ) : EReal) < f z := by
  have hcl := hL (a - η) (by linarith)
  have hmem : x_bar ∈ {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ ((a - η : ℝ) : EReal)}ᶜ := by
    intro hx
    have h2 := hx.2
    rw [ha] at h2
    have : a ≤ a - η := by exact_mod_cast h2
    linarith
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hcl.isOpen_compl x_bar hmem
  refine ⟨min r εL, lt_min hr hεL, fun z hz => ?_⟩
  have hz1 : z ∈ Metric.ball x_bar r := lt_of_lt_of_le hz (min_le_left _ _)
  have hz2 : z ∈ Metric.closedBall x_bar εL := le_of_lt (lt_of_lt_of_le hz (min_le_right _ _))
  have h3 := hball hz1
  simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at h3
  exact h3 hz2

lemma RW822_gδ_anti {f : E → EReal} {x_bar w : E} {δ δ' : ℝ} (h : δ' ≤ δ) :
    RW822gδ f x_bar w δ ≤ RW822gδ f x_bar w δ' := by
  unfold RW822gδ
  apply Filter.limsup_le_limsup (Filter.Eventually.of_forall fun p => ?_)
  exact sInf_le_sInf (Set.image_mono (Metric.closedBall_subset_closedBall h))

lemma RW822_gδ_le_R {f : E → EReal} {x_bar w : E} {δ : ℝ} (hδ : 0 < δ) :
    RW822gδ f x_bar w δ ≤ regularSubderivative f x_bar w := by
  unfold regularSubderivative
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT hδ] with δ' hδ'
  exact RW822_gδ_anti hδ'.2.le

lemma RW822_R_le_h {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a) (w : E) :
    regularSubderivative f x_bar w ≤ RW822h f x_bar w := by
  unfold regularSubderivative
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hδ : 0 < δ := hδ
  show RW822gδ f x_bar w δ ≤ RW822h f x_bar w
  apply le_of_forall_gt_imp_ge_of_dense
  intro c hc
  obtain ⟨ε, hε, hS⟩ :=
    (RW822_basisH ha w).eventually_iff.1 (Filter.eventually_lt_of_limsup_lt hc)
  unfold RW822gδ
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  rw [(RW822_basisG ha).eventually_iff]
  refine ⟨ε, hε, fun p hp => ?_⟩
  have h1 : sInf ((delta f p.1 p.2) '' Metric.closedBall w δ) ≤ delta f p.1 p.2 w :=
    sInf_le (Set.mem_image_of_mem _ (Metric.mem_closedBall_self hδ.le))
  exact h1.trans (hS (x := (p.1, p.2, w)) ⟨hp.1, hp.2, Metric.mem_ball_self hε⟩).le

lemma RW822_isOpen {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a) :
    IsOpen {w | RW822h f x_bar w < ⊤} := by
  rw [Metric.isOpen_iff]
  intro w hw
  obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.1 hw
  obtain ⟨ε, hε, hS⟩ :=
    (RW822_basisH ha w).eventually_iff.1 (Filter.eventually_lt_of_limsup_lt hc)
  refine ⟨ε / 2, by positivity, fun w' hw' => ?_⟩
  show RW822h f x_bar w' < ⊤
  apply lt_of_le_of_lt _ (EReal.coe_lt_top c)
  refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
  rw [(RW822_basisH ha w').eventually_iff]
  refine ⟨ε / 2, by positivity, fun p hp => (hS ⟨?_, ?_, ?_⟩).le⟩
  · exact RW822_good_mono (by linarith) hp.1
  · exact Set.Ioo_subset_Ioo_right (by linarith) hp.2.1
  · have h1 : dist p.2.2 w' < ε / 2 := hp.2.2
    have h2 : dist w' w < ε / 2 := hw'
    show dist p.2.2 w < ε
    linarith [dist_triangle p.2.2 w' w]

lemma RW822_R_lsc {f : E → EReal} {x_bar : E} (w : E) (c : EReal)
    (hc : c < regularSubderivative f x_bar w) :
    ∀ᶠ w' in 𝓝 w, c < regularSubderivative f x_bar w' := by
  have hfr := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hc
  obtain ⟨δ0, hδ0, hδ0pos⟩ := (hfr.and_eventually self_mem_nhdsWithin).exists
  have hδ0pos : 0 < δ0 := hδ0pos
  filter_upwards [Metric.ball_mem_nhds w (half_pos hδ0pos)] with w' hw'
  apply lt_of_lt_of_le hδ0
  show RW822gδ f x_bar w δ0 ≤ Filter.limsup (fun δ => RW822gδ f x_bar w' δ) (𝓝[>] 0)
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT (half_pos hδ0pos)] with δ hδ
  unfold RW822gδ
  apply Filter.limsup_le_limsup (Filter.Eventually.of_forall fun p => ?_)
  apply sInf_le_sInf
  apply Set.image_mono
  intro u hu
  rw [Metric.mem_closedBall] at hu ⊢
  rw [Metric.mem_ball] at hw'
  calc dist u w ≤ dist u w' + dist w' w := dist_triangle _ _ _
    _ ≤ δ + δ0 / 2 := add_le_add hu hw'.le
    _ ≤ δ0 := by linarith [hδ.2]

lemma RW822_h_le_R {f : E → EReal} {x_bar : E} {a εL : ℝ} (ha : f x_bar = a) (hεL : 0 < εL)
    (hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)})
    (w_bar : E) (hw : RW822h f x_bar w_bar < ⊤) :
    RW822h f x_bar w_bar ≤ regularSubderivative f x_bar w_bar := by
  apply EReal.ge_of_forall_gt_iff_ge.1
  intro β' hβ'
  obtain ⟨β, hβ'β, hβh⟩ := EReal.lt_iff_exists_real_btwn.1 hβ'
  have hβ'β' : β' < β := EReal.coe_lt_coe_iff.1 hβ'β
  obtain ⟨M, hMh, hM⟩ := EReal.lt_iff_exists_real_btwn.1 hw
  have hβM : β < M := EReal.coe_lt_coe_iff.1 (hβh.trans hMh)
  obtain ⟨θ, hθpos, hθ1, hθkey⟩ : ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ β - θ * M = (1 - θ) * β' := by
    refine ⟨(β - β') / (M - β'), div_pos (by linarith) (by linarith),
      (div_lt_one (by linarith)).2 (by linarith), ?_⟩
    have : M - β' ≠ 0 := by linarith
    field_simp
    ring
  unfold RW822h at hMh hβh
  obtain ⟨ε0, hε0, hε0prop⟩ :=
    (RW822_basisH ha w_bar).eventually_iff.1 (Filter.eventually_lt_of_limsup_lt hMh)
  obtain ⟨r, hr, hrprop⟩ := RW822_lsc_below ha hεL hL hε0
  have hfreq := Filter.frequently_lt_of_lt_limsup (by isBoundedDefault) hβh
  rw [(RW822_basisH ha w_bar).frequently_iff] at hfreq
  have hδpos : 0 < θ * ε0 / 2 := by positivity
  show (β' : EReal) ≤ Filter.limsup (fun δ => RW822gδ f x_bar w_bar δ) (𝓝[>] 0)
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [Ioo_mem_nhdsGT hδpos] with δ' hδ'
  unfold RW822gδ
  apply Filter.le_limsup_of_frequently_le'
  rw [(RW822_basisG ha).frequently_iff]
  intro ε hε
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = ‖w_bar‖ + ε0 := ⟨_, rfl⟩
  have hKpos : 0 < K := by rw [hK]; positivity
  have hmin0 : 0 < min ε0 r := lt_min hε0 hr
  obtain ⟨ε1, hε1pos, hε1ε, hε1θ, hε1K, hε1β⟩ : ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε ∧
      ε1 ≤ θ * ε0 / 2 ∧ ε1 * (2 * (1 + K)) ≤ min ε0 r ∧ ε1 * (2 * (1 + |β'|)) ≤ ε0 := by
    refine ⟨min (min ε (θ * ε0 / 2)) (min ((min ε0 r) / (2 * (1 + K)))
      (ε0 / (2 * (1 + |β'|)))), ?_, le_trans (min_le_left _ _) (min_le_left _ _),
      le_trans (min_le_left _ _) (min_le_right _ _), ?_, ?_⟩
    · simp only [lt_min_iff]
      refine ⟨⟨hε, hδpos⟩, ?_, ?_⟩ <;> positivity
    · rw [← le_div_iff₀ (by positivity)]
      exact le_trans (min_le_right _ _) (min_le_left _ _)
    · rw [← le_div_iff₀ (by positivity)]
      exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨⟨x, τ, w0⟩, ⟨hxgood, hτ, hw0⟩, hβlt⟩ := hfreq ε1 hε1pos
  have hβlt2 : (β : EReal) < delta f x τ w0 := hβlt
  have hxgood' : dist x x_bar < ε1 ∧ ((a - ε1 : ℝ) : EReal) < f x ∧
      f x < ((a + ε1 : ℝ) : EReal) := hxgood
  have hτpos : 0 < τ := hτ.1
  have hτε1 : τ < ε1 := hτ.2
  have h1θτ : 0 < (1 - θ) * τ := mul_pos (by linarith) hτpos
  have h1θτ' : (1 - θ) * τ < τ := by nlinarith
  refine ⟨(x, (1 - θ) * τ), ⟨RW822_good_mono hε1ε hxgood, h1θτ, by linarith⟩, ?_⟩
  apply le_sInf
  rintro _ ⟨w, hwball, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f x = b := ⟨_, RW822_good_finite hxgood⟩
  have hβlt' := (RW822_lt_delta_iff hτpos hb).1 hβlt2
  show (β' : EReal) ≤ delta f x ((1 - θ) * τ) w
  rw [RW822_le_delta_iff h1θτ hb]
  have hwball' : dist w w_bar ≤ δ' := hwball
  have hδ'ε0 : δ' ≤ ε0 := by nlinarith [hδ'.2]
  have hwnorm : ‖w‖ ≤ K := by
    have h2 : ‖w‖ ≤ ‖w_bar‖ + dist w w_bar := by
      rw [dist_eq_norm]
      calc ‖w‖ = ‖w_bar + (w - w_bar)‖ := by congr 1; abel
        _ ≤ ‖w_bar‖ + ‖w - w_bar‖ := norm_add_le _ _
    linarith
  obtain ⟨z, hz⟩ : ∃ z : E, z = x + ((1 - θ) * τ) • w := ⟨_, rfl⟩
  rw [← hz]
  have hzdist : dist z x_bar < (min ε0 r) / 2 := by
    have h1 : dist z x_bar ≤ dist x x_bar + ((1 - θ) * τ) * ‖w‖ := by
      rw [hz, dist_eq_norm, dist_eq_norm]
      calc ‖x + ((1 - θ) * τ) • w - x_bar‖ = ‖(x - x_bar) + ((1 - θ) * τ) • w‖ := by
            congr 1; abel
        _ ≤ ‖x - x_bar‖ + ‖((1 - θ) * τ) • w‖ := norm_add_le _ _
        _ = ‖x - x_bar‖ + ((1 - θ) * τ) * ‖w‖ := by
            rw [norm_smul, Real.norm_of_nonneg h1θτ.le]
    have h2 : ((1 - θ) * τ) * ‖w‖ ≤ ε1 * K :=
      mul_le_mul (by linarith) hwnorm (norm_nonneg _) hε1pos.le
    linarith [hxgood'.1]
  have hzr : dist z x_bar < r := by
    have := min_le_right ε0 r
    linarith
  have hzε0 : dist z x_bar < ε0 := by
    have := min_le_left ε0 r
    linarith
  have hfz_lb := hrprop z hzr
  by_cases hcase : f z < ((a + ε0 : ℝ) : EReal)
  · have hzgood : z ∈ RW822good f x_bar a ε0 := ⟨hzε0, hfz_lb, hcase⟩
    obtain ⟨bz, hbz⟩ : ∃ bz : ℝ, f z = bz := ⟨_, RW822_good_finite hzgood⟩
    have hσpos : 0 < θ * τ := mul_pos hθpos hτpos
    have hσε0 : θ * τ < ε0 := by nlinarith
    obtain ⟨v, hv⟩ : ∃ v : E, v = θ⁻¹ • (w0 - (1 - θ) • w) := ⟨_, rfl⟩
    have hθv : θ • v = w0 - (1 - θ) • w := by
      rw [hv, smul_smul, mul_inv_cancel₀ hθpos.ne', one_smul]
    have hzv : z + (θ * τ) • v = x + τ • w0 := by
      rw [mul_comm θ τ, ← smul_smul, hθv, hz]
      module
    have hvball : v ∈ Metric.ball w_bar ε0 := by
      rw [Metric.mem_ball, dist_eq_norm]
      have hid : θ • (v - w_bar) = (w0 - w_bar) - (1 - θ) • (w - w_bar) := by
        rw [smul_sub, hθv]; module
      have hn : θ * ‖v - w_bar‖ ≤ ‖w0 - w_bar‖ + (1 - θ) * ‖w - w_bar‖ := by
        have := norm_sub_le (w0 - w_bar) ((1 - θ) • (w - w_bar))
        rw [← hid, norm_smul, norm_smul, Real.norm_of_nonneg hθpos.le,
          Real.norm_of_nonneg (by linarith)] at this
        exact this
      have hw0' : ‖w0 - w_bar‖ < ε1 := by rw [← dist_eq_norm]; exact hw0
      have hw' : ‖w - w_bar‖ ≤ δ' := by rw [← dist_eq_norm]; exact hwball'
      have h3 : (1 - θ) * ‖w - w_bar‖ ≤ δ' := by nlinarith [norm_nonneg (w - w_bar)]
      have h4 : θ * ‖v - w_bar‖ < θ * ε0 := by nlinarith [hδ'.2]
      exact lt_of_mul_lt_mul_left h4 hθpos.le
    have hM2 : delta f z (θ * τ) v < (M : EReal) :=
      @hε0prop (z, θ * τ, v) ⟨hzgood, ⟨hσpos, hσε0⟩, hvball⟩
    have hM3 := (RW822_delta_lt_iff hσpos hbz).1 hM2
    rw [hzv] at hM3
    have hlt : b + τ * β < bz + θ * τ * M := EReal.coe_lt_coe_iff.1 (hβlt'.trans hM3)
    rw [hbz]
    have hkey2 : (1 - θ) * τ * β' = τ * β - θ * τ * M := by
      have : (1 - θ) * τ * β' = τ * ((1 - θ) * β') := by ring
      rw [this, ← hθkey]; ring
    have : b + (1 - θ) * τ * β' ≤ bz := by
      rw [hkey2]
      linarith
    exact EReal.coe_le_coe_iff.2 this
  · push_neg at hcase
    refine le_trans ?_ hcase
    have hbx : b < a + ε1 := by
      have := hxgood'.2.2
      rw [hb] at this
      exact EReal.coe_lt_coe_iff.1 this
    have h0 : (1 - θ) * τ ≤ ε1 := by linarith
    have hab : |β'| * ((1 - θ) * τ) ≤ |β'| * ε1 :=
      mul_le_mul_of_nonneg_left h0 (abs_nonneg _)
    have h1 : β' * ((1 - θ) * τ) ≤ |β'| * ((1 - θ) * τ) :=
      mul_le_mul_of_nonneg_right (le_abs_self β') h1θτ.le
    have : b + (1 - θ) * τ * β' ≤ a + ε0 := by linarith
    exact EReal.coe_le_coe_iff.2 this

lemma RW822_mixed {f : E → EReal} {x_bar : E} {a εL : ℝ} (ha : f x_bar = a) (hεL : 0 < εL)
    (hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)})
    {w1 w2 : E} {t M1 M2 : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : regularSubderivative f x_bar w1 < M1) (h2 : RW822h f x_bar w2 < M2) :
    RW822h f x_bar ((1 - t) • w1 + t • w2) ≤ (((1 - t) * M1 + t * M2 : ℝ) : EReal) := by
  -- Step 1: neighbourhood for w2
  have hev2 : ∀ᶠ p in (fApproach f x_bar) ×ˢ ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w2),
      delta f p.1 p.2.1 p.2.2 < (M2 : EReal) := by
    unfold RW822h at h2
    exact Filter.eventually_lt_of_limsup_lt h2
  obtain ⟨ε2, hε2, hε2'⟩ := (RW822_basisH ha w2).eventually_iff.1 hev2
  -- Step 2: neighbourhood for w1
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = t * ε2 / 2 := ⟨_, rfl⟩
  have hδ : 0 < δ := by rw [hδdef]; positivity
  have hg1 : RW822gδ f x_bar w1 δ < (M1 : EReal) := lt_of_le_of_lt (RW822_gδ_le_R hδ) h1
  have hev1 : ∀ᶠ p in (fApproach f x_bar) ×ˢ (𝓝[>] (0:ℝ)),
      sInf ((delta f p.1 p.2) '' Metric.closedBall w1 δ) < (M1 : EReal) := by
    unfold RW822gδ at hg1
    exact Filter.eventually_lt_of_limsup_lt hg1
  obtain ⟨ε1, hε1, hε1'⟩ := (RW822_basisG ha).eventually_iff.1 hev1
  -- Step 3: lower semicontinuity
  obtain ⟨r, hr, hr'⟩ := RW822_lsc_below ha hεL hL hε2
  -- Step 4: choose ε
  have hK1 : 0 < 1 + ‖w1‖ + δ := by positivity
  have hK2 : 0 < 1 + |M1| := by positivity
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = min (min ε1 δ)
      (min (min ε2 r / (1 + ‖w1‖ + δ)) (ε2 / (1 + |M1|))) := ⟨_, rfl⟩
  have hεpos : 0 < ε := by
    rw [hεdef]
    exact lt_min (lt_min hε1 hδ) (lt_min (div_pos (lt_min hε2 hr) hK1) (div_pos hε2 hK2))
  have hεle1 : ε ≤ ε1 := hεdef ▸ (min_le_left _ _).trans (min_le_left _ _)
  have hεleδ : ε ≤ δ := hεdef ▸ (min_le_left _ _).trans (min_le_right _ _)
  have hεle3 : ε ≤ min ε2 r / (1 + ‖w1‖ + δ) :=
    hεdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hεle4 : ε ≤ ε2 / (1 + |M1|) :=
    hεdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  rw [le_div_iff₀ hK1] at hεle3
  rw [le_div_iff₀ hK2] at hεle4
  unfold RW822h
  refine Filter.limsup_le_of_le (h := ?_)
  rw [(RW822_basisH ha ((1 - t) • w1 + t • w2)).eventually_iff]
  refine ⟨ε, hεpos, ?_⟩
  rintro ⟨x, τ, w⟩ ⟨hx, hτ, hw⟩
  show delta f x τ w ≤ _
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f x = b := ⟨_, RW822_good_finite hx⟩
  obtain ⟨hx1, hx2, hx3⟩ := hx
  have hτpos : 0 < τ := hτ.1
  have hτlt : τ < ε := hτ.2
  have hw' : dist w ((1 - t) • w1 + t • w2) < ε := hw
  -- τ' = (1 - t) * τ
  have h1t : 0 < 1 - t := by linarith
  have hτ'pos : 0 < (1 - t) * τ := mul_pos h1t hτpos
  have htτ : 0 < t * τ := mul_pos ht0 hτpos
  have hτ'le : (1 - t) * τ ≤ τ := by linarith
  have hx1' : x ∈ RW822good f x_bar a ε1 := RW822_good_mono hεle1 ⟨hx1, hx2, hx3⟩
  have hsInf := hε1' (Set.mk_mem_prod hx1' (Set.mem_Ioo.2 ⟨hτ'pos, by linarith⟩))
  obtain ⟨_, ⟨u, hu, rfl⟩, hlt⟩ := sInf_lt_iff.1 hsInf
  have hfz := (RW822_delta_lt_iff hτ'pos hb).1 hlt
  obtain ⟨z, hzdef⟩ : ∃ z : E, z = x + ((1 - t) * τ) • u := ⟨_, rfl⟩
  rw [← hzdef] at hfz
  have hu' : dist u w1 ≤ δ := Metric.mem_closedBall.1 hu
  have hun : ‖u‖ ≤ ‖w1‖ + δ := by
    have := norm_le_insert' u w1
    rw [← dist_eq_norm] at this
    linarith
  have hdistz : dist z x_bar < min ε2 r := by
    have e1 : dist z x_bar ≤ dist x x_bar + ((1 - t) * τ) * ‖u‖ := by
      rw [hzdef]
      calc dist (x + ((1 - t) * τ) • u) x_bar
          ≤ dist (x + ((1 - t) * τ) • u) x + dist x x_bar := dist_triangle _ _ _
        _ = ‖((1 - t) * τ) • u‖ + dist x x_bar := by rw [dist_eq_norm, add_sub_cancel_left]
        _ = dist x x_bar + ((1 - t) * τ) * ‖u‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ'pos]; ring
    have e2 : ((1 - t) * τ) * ‖u‖ ≤ ε * (‖w1‖ + δ) :=
      mul_le_mul (by linarith) hun (norm_nonneg _) hεpos.le
    linarith
  have hz1 : dist z x_bar < ε2 := lt_of_lt_of_le hdistz (min_le_left _ _)
  have hz2 := hr' z (lt_of_lt_of_le hdistz (min_le_right _ _))
  have hbε : b < a + ε := by
    rw [hb] at hx3
    exact EReal.coe_lt_coe_iff.1 hx3
  have hM1abs : (1 - t) * τ * M1 ≤ ε * |M1| := by
    calc (1 - t) * τ * M1 ≤ (1 - t) * τ * |M1| :=
          mul_le_mul_of_nonneg_left (le_abs_self M1) hτ'pos.le
      _ ≤ ε * |M1| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg M1)
  have hz3 : f z < ((a + ε2 : ℝ) : EReal) := by
    refine lt_of_lt_of_le hfz ?_
    exact EReal.coe_le_coe_iff.2 (by linarith)
  have hz : z ∈ RW822good f x_bar a ε2 := ⟨hz1, hz2, hz3⟩
  obtain ⟨bz, hbz⟩ : ∃ bz : ℝ, f z = bz := ⟨_, RW822_good_finite hz⟩
  have hbzlt : bz < b + (1 - t) * τ * M1 := by
    rw [hbz] at hfz
    exact EReal.coe_lt_coe_iff.1 hfz
  -- σ = t * τ, v
  have hσlt : t * τ < ε2 := by
    have : t * τ < τ := mul_lt_of_lt_one_left hτpos ht1
    have : t * ε2 < ε2 := mul_lt_of_lt_one_left hε2 ht1
    linarith
  obtain ⟨v, hvdef⟩ : ∃ v : E, v = t⁻¹ • (w - (1 - t) • u) := ⟨_, rfl⟩
  have hvid : t • (v - w2) = (w - ((1 - t) • w1 + t • w2)) - (1 - t) • (u - w1) := by
    rw [hvdef, smul_sub, smul_smul, mul_inv_cancel₀ ht0.ne', one_smul]
    module
  have hv : dist v w2 < ε2 := by
    rw [dist_eq_norm]
    have e1 : t * ‖v - w2‖ = ‖(w - ((1 - t) • w1 + t • w2)) - (1 - t) • (u - w1)‖ := by
      rw [← hvid, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
    have e2 : ‖(w - ((1 - t) • w1 + t • w2)) - (1 - t) • (u - w1)‖ < t * ε2 := by
      calc ‖(w - ((1 - t) • w1 + t • w2)) - (1 - t) • (u - w1)‖
          ≤ ‖w - ((1 - t) • w1 + t • w2)‖ + ‖(1 - t) • (u - w1)‖ := norm_sub_le _ _
        _ = dist w ((1 - t) • w1 + t • w2) + (1 - t) * dist u w1 := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_pos h1t, dist_eq_norm, dist_eq_norm]
        _ < t * ε2 := by
            have : (1 - t) * dist u w1 ≤ (1 - t) * δ := mul_le_mul_of_nonneg_left hu' h1t.le
            have : 0 ≤ t * δ := by positivity
            linarith
    exact lt_of_mul_lt_mul_left (by rw [e1]; exact e2) ht0.le
  have hzv : z + (t * τ) • v = x + τ • w := by
    rw [hzdef, hvdef, smul_smul,
      show t * τ * t⁻¹ = τ by rw [mul_comm t τ, mul_assoc, mul_inv_cancel₀ ht0.ne', mul_one]]
    module
  have hdel := hε2' (Set.mk_mem_prod hz
    (Set.mk_mem_prod (Set.mem_Ioo.2 ⟨htτ, hσlt⟩) (Metric.mem_ball.2 hv)))
  have hfxw := (RW822_delta_lt_iff (w := v) htτ hbz).1 hdel
  rw [hzv] at hfxw
  apply le_of_lt
  rw [RW822_delta_lt_iff hτpos hb]
  refine lt_of_lt_of_le hfxw ?_
  exact EReal.coe_le_coe_iff.2 (by linarith)

lemma RW822F_uniform {f : E → EReal} {x_bar : E} {a : ℝ} (ha : f x_bar = a)
    {w0 : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : ∀ w ∈ Metric.closedBall w0 ρ, regularSubderivative f x_bar w < ⊤) :
    ∃ M : ℝ, ∃ ε > 0, ∀ x ∈ RW822good f x_bar a ε, ∀ σ ∈ Set.Ioo 0 ε,
      ∀ d ∈ Metric.closedBall w0 ρ, ∃ u ∈ Metric.ball d (ρ / 2),
        delta f x σ u < (M : EReal) := by
  have hδ : 0 < ρ / 2 := by positivity
  have key : ∃ M : ℝ, ∀ᶠ q in (fApproach f x_bar) ×ˢ 𝓝[>] (0:ℝ),
      ∀ d ∈ Metric.closedBall w0 ρ, ∃ u ∈ Metric.ball d (ρ / 2),
        delta f q.1 q.2 u < (M : EReal) := by
    refine (isCompact_closedBall w0 ρ).induction_on
      (p := fun S => ∃ M : ℝ, ∀ᶠ q in (fApproach f x_bar) ×ˢ 𝓝[>] (0:ℝ),
        ∀ d ∈ S, ∃ u ∈ Metric.ball d (ρ / 2), delta f q.1 q.2 u < (M : EReal)) ?_ ?_ ?_ ?_
    · exact ⟨0, Filter.Eventually.of_forall fun q d hd => absurd hd (Set.notMem_empty d)⟩
    · intro s t hst hpt
      obtain ⟨M, hM⟩ := hpt
      exact ⟨M, hM.mono fun q hq d hd => hq d (hst hd)⟩
    · intro s t hps hpt
      obtain ⟨M1, hM1⟩ := hps
      obtain ⟨M2, hM2⟩ := hpt
      refine ⟨max M1 M2, (hM1.and hM2).mono fun q hq d hd => ?_⟩
      rcases hd with hd | hd
      · obtain ⟨u, hu, hlt⟩ := hq.1 d hd
        exact ⟨u, hu, lt_of_lt_of_le hlt (by exact_mod_cast le_max_left M1 M2)⟩
      · obtain ⟨u, hu, hlt⟩ := hq.2 d hd
        exact ⟨u, hu, lt_of_lt_of_le hlt (by exact_mod_cast le_max_right M1 M2)⟩
    · intro d hd
      refine ⟨Metric.ball d (ρ / 2 / 2),
        mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds d (by positivity)), ?_⟩
      obtain ⟨M, hM, -⟩ := EReal.lt_iff_exists_real_btwn.1 (hdom d hd)
      have h1 : RW822gδ f x_bar d (ρ / 2 / 2) < (M : EReal) :=
        lt_of_le_of_lt (RW822_gδ_le_R (by positivity)) hM
      unfold RW822gδ at h1
      have h2 := Filter.eventually_lt_of_limsup_lt h1
      refine ⟨M, h2.mono fun q hq d' hd' => ?_⟩
      obtain ⟨v, ⟨u, hu, rfl⟩, hlt⟩ := sInf_lt_iff.1 hq
      refine ⟨u, ?_, hlt⟩
      rw [Metric.mem_ball]
      rw [Metric.mem_closedBall] at hu
      rw [Metric.mem_ball] at hd'
      have := dist_triangle u d d'
      rw [dist_comm d d'] at this
      linarith
  obtain ⟨M, hM⟩ := key
  obtain ⟨ε, hε, hεsub⟩ := (RW822_basisG ha).eventually_iff.1 hM
  exact ⟨M, ε, hε, fun x hx σ hσ d hd =>
    hεsub (show (x, σ) ∈ RW822good f x_bar a ε ×ˢ Set.Ioo 0 ε from ⟨hx, hσ⟩) d hd⟩

lemma RW822F_core {f : E → EReal} {x_bar : E} {a εL : ℝ}
    (hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)})
    {w0 : E} {ρ δ M ε r : ℝ} (hδ : 0 < δ) (hρδ : 2 * δ ≤ ρ)
    (hU : ∀ x ∈ RW822good f x_bar a ε, ∀ σ ∈ Set.Ioo 0 ε,
      ∀ d ∈ Metric.closedBall w0 ρ, ∃ u ∈ Metric.ball d δ, delta f x σ u < (M : EReal))
    (hlsc : ∀ z, dist z x_bar < r → ((a - ε : ℝ) : EReal) < f z)
    {x w : E} {τ b : ℝ} (hxb : f x = b) (hτ : 0 < τ) (hτε : τ < ε)
    (hw : ‖w - w0‖ < δ)
    (hD : dist x x_bar + 2 * (τ * (‖w0‖ + δ)) < min ε (min r εL))
    (hB : b + τ * |M| < a + min ε εL) :
    f (x + τ • w) ≤ ((b + τ * |M| : ℝ) : EReal) := by
  set y := x + τ • w with hy
  have hN : 0 ≤ ‖w0‖ + δ := add_nonneg (norm_nonneg _) hδ.le
  have hyx : ‖y - x‖ ≤ τ * (‖w0‖ + δ) := by
    have h1 : y - x = τ • w := by rw [hy]; abel
    rw [h1, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    apply mul_le_mul_of_nonneg_left _ hτ.le
    have h2 : ‖w‖ ≤ ‖w0‖ + ‖w - w0‖ := by
      calc ‖w‖ = ‖w0 + (w - w0)‖ := by congr 1; abel
        _ ≤ ‖w0‖ + ‖w - w0‖ := norm_add_le _ _
    linarith
  have hdz : ∀ (z e : E) (s : ℝ), 0 < s → s ≤ τ → ‖e‖ < δ → y - z = s • (w0 + e) →
      dist z x_bar < min ε (min r εL) := by
    intro z e s hs hsτ he hyz
    have h2 : ‖y - z‖ ≤ s * (‖w0‖ + δ) := by
      rw [hyz, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
      apply mul_le_mul_of_nonneg_left _ hs.le
      have := norm_add_le w0 e
      linarith
    have h3 : s * (‖w0‖ + δ) ≤ τ * (‖w0‖ + δ) := mul_le_mul_of_nonneg_right hsτ hN
    have h4 : dist z x_bar ≤ dist x x_bar + ‖y - x‖ + ‖y - z‖ := by
      rw [dist_eq_norm, dist_eq_norm]
      calc ‖z - x_bar‖ = ‖((x - x_bar) + (y - x)) - (y - z)‖ := by congr 1; abel
        _ ≤ ‖(x - x_bar) + (y - x)‖ + ‖y - z‖ := norm_sub_le _ _
        _ ≤ ‖x - x_bar‖ + ‖y - x‖ + ‖y - z‖ := by
          have := norm_add_le (x - x_bar) (y - x)
          linarith
    linarith
  have hpow : ∀ k : ℕ, 0 < τ / 2 ^ k ∧ τ / 2 ^ k ≤ τ := by
    intro k
    exact ⟨div_pos hτ (by positivity), div_le_self hτ.le (one_le_pow₀ (by norm_num))⟩
  have hMb : ∀ s : ℝ, 0 ≤ s → s ≤ τ → (τ - s) * M ≤ τ * |M| := by
    intro s hs0 hsτ
    calc (τ - s) * M ≤ (τ - s) * |M| :=
          mul_le_mul_of_nonneg_left (le_abs_self M) (by linarith)
      _ ≤ τ * |M| := mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg M)
  have hex : ∀ k : ℕ, ∃ z : E, (∃ e : E, ‖e‖ < δ ∧ y - z = (τ / 2 ^ k) • (w0 + e)) ∧
      f z ≤ ((b + (τ - τ / 2 ^ k) * M : ℝ) : EReal) := by
    intro k
    induction k with
    | zero =>
      refine ⟨x, ⟨w - w0, hw, ?_⟩, ?_⟩
      · rw [hy]; simp
      · rw [hxb]; simp
    | succ k ih =>
      obtain ⟨z, ⟨e, he, hyz⟩, hfz⟩ := ih
      obtain ⟨hs, hsτ⟩ := hpow k
      obtain ⟨hσ, hστ⟩ := hpow (k + 1)
      have hs2 : τ / 2 ^ k = 2 * (τ / 2 ^ (k + 1)) := by
        rw [pow_succ]; field_simp
      have hdzk := hdz z e _ hs hsτ he hyz
      have hzε : dist z x_bar < ε := lt_of_lt_of_le hdzk (min_le_left _ _)
      have hzr : dist z x_bar < r :=
        lt_of_lt_of_le hdzk (le_trans (min_le_right _ _) (min_le_left _ _))
      have hzgood : z ∈ RW822good f x_bar a ε := by
        refine ⟨hzε, hlsc z hzr, lt_of_le_of_lt hfz ?_⟩
        have := hMb _ hs.le hsτ
        have := min_le_left ε εL
        exact_mod_cast (by linarith : b + (τ - τ / 2 ^ k) * M < a + ε)
      have hfin := RW822_good_finite hzgood
      have hd : w0 + (2:ℝ) • e ∈ Metric.closedBall w0 ρ := by
        rw [Metric.mem_closedBall, dist_eq_norm]
        have : w0 + (2:ℝ) • e - w0 = (2:ℝ) • e := by abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_two]
        linarith
      obtain ⟨u, hu, hlt⟩ := hU z hzgood (τ / 2 ^ (k + 1)) ⟨hσ, by linarith⟩ _ hd
      have hlt2 := (RW822_delta_lt_iff hσ hfin).1 hlt
      refine ⟨z + (τ / 2 ^ (k + 1)) • u, ⟨w0 + (2:ℝ) • e - u, ?_, ?_⟩, ?_⟩
      · rw [Metric.mem_ball, dist_eq_norm] at hu
        rw [norm_sub_rev]; exact hu
      · rw [sub_add_eq_sub_sub, hyz, hs2]; module
      · have hfz' : (f z).toReal ≤ b + (τ - τ / 2 ^ k) * M := by
          rw [hfin] at hfz; exact_mod_cast hfz
        refine le_of_lt (lt_of_lt_of_le hlt2 ?_)
        rw [hs2] at hfz'
        exact_mod_cast (by linarith :
          (f z).toReal + τ / 2 ^ (k + 1) * M ≤ b + (τ - τ / 2 ^ (k + 1)) * M)
  choose zk hzk using hex
  have hS : IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧
      f x ≤ ((b + τ * |M| : ℝ) : EReal)} :=
    hL _ (by have := min_le_right ε εL; linarith)
  have hmem : ∀ k, zk k ∈ {x | x ∈ Metric.closedBall x_bar εL ∧
      f x ≤ ((b + τ * |M| : ℝ) : EReal)} := by
    intro k
    obtain ⟨⟨e, he, hyz⟩, hfz⟩ := hzk k
    obtain ⟨hs, hsτ⟩ := hpow k
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall]
      have := hdz (zk k) e _ hs hsτ he hyz
      have := min_le_right r εL
      have := min_le_right ε (min r εL)
      linarith
    · refine le_trans hfz ?_
      have := hMb _ hs.le hsτ
      exact_mod_cast (by linarith : b + (τ - τ / 2 ^ k) * M ≤ b + τ * |M|)
  have hlim : Filter.Tendsto zk Filter.atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have h0 : Filter.Tendsto (fun k : ℕ => τ / 2 ^ k * (‖w0‖ + δ)) Filter.atTop (𝓝 0) := by
      have := ((tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => τ) Filter.atTop (𝓝 τ)).div_atTop
        (tendsto_pow_atTop_atTop_of_one_lt (one_lt_two (α := ℝ)))).mul_const (‖w0‖ + δ)
      rw [zero_mul] at this
      exact this
    refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) h0
    obtain ⟨⟨e, he, hyz⟩, -⟩ := hzk k
    obtain ⟨hs, -⟩ := hpow k
    rw [norm_sub_rev, hyz, norm_smul, Real.norm_eq_abs, abs_of_pos hs]
    apply mul_le_mul_of_nonneg_left _ hs.le
    have := norm_add_le w0 e
    linarith
  exact (hS.mem_of_tendsto hlim (Filter.Eventually.of_forall hmem)).2

lemma RW822_ball {f : E → EReal} {x_bar : E} {a εL : ℝ} (ha : f x_bar = a) (hεL : 0 < εL)
    (hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)})
    {w0 : E} {ρ : ℝ} (hρ : 0 < ρ)
    (hdom : ∀ w ∈ Metric.closedBall w0 ρ, regularSubderivative f x_bar w < ⊤) :
    RW822h f x_bar w0 < ⊤ := by
  have hδ : 0 < ρ / 2 := by positivity
  obtain ⟨M, ε, hε, hU⟩ := RW822F_uniform ha hρ hdom
  obtain ⟨r, hr, hlsc⟩ := RW822_lsc_below ha hεL hL hε
  have hN : 0 < ‖w0‖ + ρ / 2 := by have := norm_nonneg w0; linarith
  have hm : 0 < min ε (min r εL) := lt_min hε (lt_min hr hεL)
  have hm2 : 0 < min ε εL := lt_min hε hεL
  have hA1 : 0 < 2 * (1 + 2 * (‖w0‖ + ρ / 2)) := by linarith
  have hA2 : 0 < 2 * (1 + |M|) := by have := abs_nonneg M; linarith
  obtain ⟨ε', hε'def⟩ : ∃ ε', ε' = min (min ε (ρ / 2))
      (min (min ε (min r εL) / (2 * (1 + 2 * (‖w0‖ + ρ / 2))))
        (min ε εL / (2 * (1 + |M|)))) := ⟨_, rfl⟩
  have hε' : 0 < ε' := by
    rw [hε'def]
    exact lt_min (lt_min hε hδ) (lt_min (div_pos hm hA1) (div_pos hm2 hA2))
  have hε'1 : ε' ≤ ε := by
    rw [hε'def]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hε'2 : ε' ≤ ρ / 2 := by
    rw [hε'def]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  have hε'3 : ε' * (2 * (1 + 2 * (‖w0‖ + ρ / 2))) ≤ min ε (min r εL) := by
    have : ε' ≤ min ε (min r εL) / (2 * (1 + 2 * (‖w0‖ + ρ / 2))) := by
      rw [hε'def]; exact le_trans (min_le_right _ _) (min_le_left _ _)
    rwa [le_div_iff₀ hA1] at this
  have hε'4 : ε' * (2 * (1 + |M|)) ≤ min ε εL := by
    have : ε' ≤ min ε εL / (2 * (1 + |M|)) := by
      rw [hε'def]; exact le_trans (min_le_right _ _) (min_le_right _ _)
    rwa [le_div_iff₀ hA2] at this
  have hbound : RW822h f x_bar w0 ≤ ((|M| : ℝ) : EReal) := by
    unfold RW822h
    refine Filter.limsup_le_of_le (by isBoundedDefault) ?_
    rw [(RW822_basisH ha w0).eventually_iff]
    refine ⟨ε', hε', ?_⟩
    rintro ⟨x, τ, w⟩ ⟨hx, hτ, hw⟩
    have hfin := RW822_good_finite hx
    obtain ⟨hx1, -, hx3⟩ := hx
    obtain ⟨hτ0, hτ1⟩ := hτ
    simp only at hx1 hx3 hτ0 hτ1 hw hfin ⊢
    rw [RW822_delta_le_iff hτ0 hfin]
    have hb : (f x).toReal < a + ε' := by
      rw [hfin] at hx3; exact_mod_cast hx3
    have hw' : ‖w - w0‖ < ρ / 2 := by
      rw [Metric.mem_ball, dist_eq_norm] at hw; linarith
    have hτN : τ * (‖w0‖ + ρ / 2) ≤ ε' * (‖w0‖ + ρ / 2) :=
      mul_le_mul_of_nonneg_right hτ1.le hN.le
    have hτM : τ * |M| ≤ ε' * |M| := mul_le_mul_of_nonneg_right hτ1.le (abs_nonneg M)
    exact RW822F_core hL hδ (by linarith) hU hlsc hfin hτ0 (by linarith) hw'
      (by linarith) (by linarith)
  exact lt_of_le_of_lt hbound (EReal.coe_lt_top _)

theorem RW_chap_8_22
  (f : E → EReal)
  (x_bar : E)
  (hf_local_lsc : LocalLscAt f x_bar)
  (hx_bar : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  let h : E → EReal := fun w_bar =>
    Filter.limsup
      (fun p : E × ℝ × E =>
        let x := p.1
        let τ := p.2.1
        let w := p.2.2
        delta f x τ w)
      ((fApproach f x_bar) ×ˢ ((𝓝[>] 0) ×ˢ (𝓝 w_bar)))
  let O : Set E := {w | h w < ⊤}
  (interior (effDom (regularSubderivative f x_bar)) = O) ∧
  (∀ w_bar ∈ O, regularSubderivative f x_bar w_bar = h w_bar) ∧
  (Set.Nonempty O →
    (∀ w_bar ∉ closure O, regularSubderivative f x_bar w_bar = ⊤) ∧
    (∀ w_bar ∈ frontier O, ∀ w_hat ∈ O,
      Filter.Tendsto
        (fun (τ : ℝ) => h ((1 - τ) • w_bar + τ • w_hat))
        (𝓝[>] 0)
        (𝓝 (regularSubderivative f x_bar w_bar)))) := by
  intro h O
  obtain ⟨-, -, εL, hεL⟩ := hf_local_lsc
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x_bar = a :=
    ⟨(f x_bar).toReal, (EReal.coe_toReal hx_bar.2.ne hx_bar.1.ne').symm⟩
  have hεpos : 0 < εL := (hεL (a + εL) (by rw [ha]; exact le_of_eq (EReal.coe_add a εL))).1
  have hL : ∀ α : ℝ, α ≤ a + εL →
      IsClosed {x | x ∈ Metric.closedBall x_bar εL ∧ f x ≤ (α : EReal)} := by
    intro α hα
    refine (hεL α ?_).2
    rw [ha, ← EReal.coe_add]
    exact_mod_cast hα
  have hh : ∀ w, h w = RW822h f x_bar w := fun w => rfl
  have hRh : ∀ w, regularSubderivative f x_bar w ≤ h w := fun w => RW822_R_le_h ha w
  have hOopen : IsOpen O := RW822_isOpen ha
  refine ⟨?_, ?_, ?_⟩
  · apply Set.Subset.antisymm
    · intro w hw
      rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at hw
      obtain ⟨ρ, hρ, hball⟩ := hw
      exact RW822_ball ha hεpos hL (ρ := ρ / 2) (by positivity)
        (fun w' hw' => hball (Metric.closedBall_subset_ball (by linarith) hw'))
    · apply interior_maximal _ hOopen
      intro w hw
      exact lt_of_le_of_lt (hRh w) hw
  · intro w hw
    exact le_antisymm (hRh w) (RW822_h_le_R ha hεpos hL w hw)
  · intro hne
    obtain ⟨wh, hwh⟩ := hne
    have key : ∀ w, regularSubderivative f x_bar w < ⊤ → ∀ t : ℝ, 0 < t → t < 1 →
        (1 - t) • w + t • wh ∈ O := by
      intro w hw t ht0 ht1
      obtain ⟨M1, hM1, -⟩ := EReal.lt_iff_exists_real_btwn.1 hw
      obtain ⟨M2, hM2, -⟩ := EReal.lt_iff_exists_real_btwn.1 (show h wh < ⊤ from hwh)
      exact lt_of_le_of_lt (RW822_mixed ha hεpos hL ht0 ht1 hM1 hM2) (EReal.coe_lt_top _)
    have hcont : ∀ w w' : E, Filter.Tendsto (fun t : ℝ => (1 - t) • w + t • w') (𝓝[>] 0)
        (𝓝 w) := by
      intro w w'
      have : Filter.Tendsto (fun t : ℝ => (1 - t) • w + t • w') (𝓝 0)
          (𝓝 ((1 - 0 : ℝ) • w + (0 : ℝ) • w')) := by
        apply Continuous.tendsto
        fun_prop
      simpa using this.mono_left nhdsWithin_le_nhds
    refine ⟨?_, ?_⟩
    · intro w hw
      by_contra hne
      apply hw
      have hlt : regularSubderivative f x_bar w < ⊤ := lt_top_iff_ne_top.2 hne
      apply mem_closure_of_tendsto (hcont w wh)
      filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht
      exact key w hlt t ht.1 ht.2
    · intro w _ wh' hwh'
      rw [tendsto_order]
      refine ⟨?_, ?_⟩
      · intro c hc
        have h1 := RW822_R_lsc w c hc
        filter_upwards [(hcont w wh').eventually h1] with t ht
        exact lt_of_lt_of_le ht (hRh _)
      · intro c hc
        obtain ⟨M1, hM1, hM1c⟩ := EReal.lt_iff_exists_real_btwn.1 hc
        obtain ⟨c', hc'1, hc'2⟩ := EReal.lt_iff_exists_real_btwn.1 hM1c
        obtain ⟨M2, hM2, -⟩ := EReal.lt_iff_exists_real_btwn.1 (show h wh' < ⊤ from hwh')
        have hlim : Filter.Tendsto (fun t : ℝ => (1 - t) * M1 + t * M2) (𝓝[>] 0)
            (𝓝 ((1 - 0) * M1 + 0 * M2)) := by
          apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
          apply Continuous.tendsto
          fun_prop
        have hc'1' : M1 < c' := by exact_mod_cast hc'1
        have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), (1 - t) * M1 + t * M2 < c' :=
          hlim.eventually (gt_mem_nhds (by simpa using hc'1'))
        filter_upwards [hev, Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with t ht ht'
        calc h ((1 - t) • w + t • wh') ≤ (((1 - t) * M1 + t * M2 : ℝ) : EReal) :=
              RW822_mixed ha hεpos hL ht'.1 ht'.2 hM1 hM2
          _ < c' := by exact_mod_cast ht
          _ < c := hc'2

end RW_chap_8_22
