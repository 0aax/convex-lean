import ConvexStarLib.Defs

/-!
# `RW_chap_11_8`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_11_8` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_11_8`, so the main result is `RW_chap_11_8.RW_chap_11_8`.
-/

namespace RW_chap_11_8

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace RW118

/-! ### Basic facts about the conjugate -/

lemma conj_ge (f : E → EReal) (v x : E) :
    ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v := by
  unfold conjugate
  exact le_sSup ⟨x, Set.mem_univ _, rfl⟩

lemma conj_le (f : E → EReal) (v : E) (c : EReal)
    (h : ∀ x, ((inner ℝ v x : ℝ) : EReal) - f x ≤ c) : conjugate f v ≤ c := by
  unfold conjugate
  apply sSup_le
  rintro _ ⟨x, -, rfl⟩
  exact h x

lemma conj_gt_bot (f : E → EReal) (hf : IsProper f) (v : E) : ⊥ < conjugate f v := by
  obtain ⟨x, hx⟩ := hf.2
  have hx' : f x < ⊤ := hx
  have hne_top : f x ≠ ⊤ := hx'.ne
  have hne_bot : f x ≠ ⊥ := (hf.1 x).ne'
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal hne_top hne_bot).symm⟩
  refine lt_of_lt_of_le ?_ (conj_ge f v x)
  rw [hr, ← EReal.coe_sub]
  exact EReal.bot_lt_coe _

lemma part_a (f : E → EReal) : sInf (Set.range f) = - conjugate f 0 := by
  unfold conjugate
  simp only [inner_zero_left, EReal.coe_zero, zero_sub, Set.image_univ]
  apply le_antisymm
  · rw [EReal.le_neg]
    apply sSup_le
    rintro _ ⟨x, rfl⟩
    rw [EReal.neg_le_neg_iff]
    exact sInf_le ⟨x, rfl⟩
  · apply le_sInf
    rintro _ ⟨x, rfl⟩
    rw [EReal.neg_le]
    exact le_sSup ⟨x, rfl⟩

/-! ### Convexity -/

lemma epi_convex_ineq (f : E → EReal) (hf : ConvexEReal f) {x y : E} {a b : ℝ}
    (hx : f x ≤ a) (hy : f y ≤ b) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f ((1 - t) • x + t • y) ≤ (((1 - t) * a + t * b : ℝ) : EReal) := by
  have hxmem : ((x, a) : E × ℝ) ∈ epigraph f := hx
  have hymem : ((y, b) : E × ℝ) ∈ epigraph f := hy
  have h := hf hxmem hymem (sub_nonneg.2 ht1) ht0 (by ring)
  exact h

lemma conj_convex_ineq (f : E → EReal) (hf : IsProper f) {a b : E} {A B : ℝ}
    (ha : conjugate f a ≤ A) (hb : conjugate f b ≤ B) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    conjugate f ((1 - t) • a + t • b) ≤ (((1 - t) * A + t * B : ℝ) : EReal) := by
  apply conj_le
  intro x
  by_cases htop : f x = ⊤
  · rw [htop, EReal.sub_top]; exact bot_le
  have hbot : f x ≠ ⊥ := (hf.1 x).ne'
  obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
  have h1 := (conj_ge f a x).trans ha
  have h2 := (conj_ge f b x).trans hb
  rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1 h2
  rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  nlinarith [mul_nonneg (sub_nonneg.2 ht1) (sub_nonneg.2 h1), mul_nonneg ht0 (sub_nonneg.2 h2)]

/-! ### Subgradients of the conjugate are global (convex) subgradients -/

lemma regular_conj_global (f : E → EReal) (hf : IsProper f) {x0 w : E}
    (h : IsRegularSubgradientAt (conjugate f) x0 w) (y : E) :
    conjugate f x0 + ((inner ℝ w (y - x0) : ℝ) : EReal) ≤ conjugate f y := by
  obtain ⟨hbot, htop, r, hr, V, hV, hineq⟩ := h
  obtain ⟨c, hc⟩ : ∃ c : ℝ, conjugate f x0 = c :=
    ⟨(conjugate f x0).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  rcases eq_or_ne (conjugate f y) ⊤ with hy | hy
  · rw [hy]; exact le_top
  obtain ⟨d, hd⟩ : ∃ d : ℝ, conjugate f y = d :=
    ⟨(conjugate f y).toReal, (EReal.coe_toReal hy (conj_gt_bot f hf y).ne').symm⟩
  have hn0 : 0 ≤ ‖y - x0‖ := norm_nonneg _
  have hg : Filter.Tendsto (fun t : ℝ => x0 + t • (y - x0)) (𝓝[>] (0:ℝ)) (𝓝 x0) := by
    have h1 : Filter.Tendsto (fun t : ℝ => x0 + t • (y - x0)) (𝓝 (0:ℝ))
        (𝓝 (x0 + (0:ℝ) • (y - x0))) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at h1
    exact h1.mono_left nhdsWithin_le_nhds
  have key : ∀ ε > 0, inner ℝ w (y - x0) - ε * ‖y - x0‖ ≤ d - c := by
    intro ε hε
    have hev1 : ∀ᶠ t in 𝓝[>] (0:ℝ), x0 + t • (y - x0) ∈ V := hg.eventually_mem hV
    have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ),
        ‖r (x0 + t • (y - x0))‖ ≤ ε * ‖‖x0 + t • (y - x0) - x0‖‖ :=
      hg.eventually (Asymptotics.isLittleO_iff.mp hr hε)
    have hev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT (by norm_num)
    obtain ⟨t, htV, htr, ht0, ht1⟩ := (hev1.and (hev2.and hev3)).exists
    have hxt : x0 + t • (y - x0) = (1 - t) • x0 + t • y := by module
    have hconv := conj_convex_ineq f hf hc.le hd.le ht0.le ht1.le
    rw [← hxt] at hconv
    have hin := hineq _ htV
    have hsub : x0 + t • (y - x0) - x0 = t • (y - x0) := add_sub_cancel_left _ _
    rw [hsub, real_inner_smul_right] at hin
    rw [hsub, norm_norm, norm_smul, Real.norm_of_nonneg ht0.le, Real.norm_eq_abs] at htr
    have hcomb := hin.trans hconv
    rw [hc] at hcomb
    have hreal : c + (t * inner ℝ w (y - x0) + r (x0 + t • (y - x0))) ≤ (1 - t) * c + t * d := by
      exact_mod_cast hcomb
    have hr' : -(ε * (t * ‖y - x0‖)) ≤ r (x0 + t • (y - x0)) := by
      have := neg_abs_le (r (x0 + t • (y - x0)))
      linarith
    have h3 : t * (inner ℝ w (y - x0) - ε * ‖y - x0‖) ≤ t * (d - c) := by nlinarith
    exact le_of_mul_le_mul_left h3 ht0
  have hfinal : inner ℝ w (y - x0) ≤ d - c := by
    apply _root_.le_of_forall_pos_le_add
    intro δ hδ
    have h1 := key (δ / (‖y - x0‖ + 1)) (by positivity)
    have h2 : δ / (‖y - x0‖ + 1) * ‖y - x0‖ ≤ δ := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  rw [hc, hd]
  exact_mod_cast (by linarith : c + inner ℝ w (y - x0) ≤ d)

lemma subgrad_conj_global (f : E → EReal) (hf : IsProper f) {x0 w : E}
    (h : IsSubgradientAt (conjugate f) x0 w) (y : E) :
    conjugate f x0 + ((inner ℝ w (y - x0) : ℝ) : EReal) ≤ conjugate f y := by
  obtain ⟨hbot, htop, xs, vs, hxs, hfx, hvs, hreg⟩ := h
  have hglob : ∀ n, conjugate f (xs n) + ((inner ℝ (vs n) (y - xs n) : ℝ) : EReal)
      ≤ conjugate f y :=
    fun n => regular_conj_global f hf (hreg n) y
  obtain ⟨c, hc⟩ : ∃ c : ℝ, conjugate f x0 = c :=
    ⟨(conjugate f x0).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  rcases eq_or_ne (conjugate f y) ⊤ with hy | hy
  · rw [hy]; exact le_top
  obtain ⟨d, hd⟩ : ∃ d : ℝ, conjugate f y = d :=
    ⟨(conjugate f y).toReal, (EReal.coe_toReal hy (conj_gt_bot f hf y).ne').symm⟩
  have hle : ∀ n, conjugate f (xs n) ≤ ((d - inner ℝ (vs n) (y - xs n) : ℝ) : EReal) := by
    intro n
    obtain ⟨hb, ht, -⟩ := hreg n
    obtain ⟨e, he⟩ : ∃ e : ℝ, conjugate f (xs n) = e :=
      ⟨_, (EReal.coe_toReal ht.ne hb.ne').symm⟩
    have h1 := hglob n
    rw [he, hd] at h1
    rw [he]
    have h2 : e + inner ℝ (vs n) (y - xs n) ≤ d := by exact_mod_cast h1
    exact_mod_cast (by linarith : e ≤ d - inner ℝ (vs n) (y - xs n))
  have hlim : Filter.Tendsto (fun n => ((d - inner ℝ (vs n) (y - xs n) : ℝ) : EReal))
      Filter.atTop (𝓝 ((d - inner ℝ w (y - x0) : ℝ) : EReal)) := by
    apply (continuous_coe_real_ereal.tendsto _).comp
    apply tendsto_const_nhds.sub
    exact hvs.inner (tendsto_const_nhds.sub hxs)
  have h1 := le_of_tendsto_of_tendsto' hfx hlim hle
  rw [hc] at h1
  rw [hc, hd]
  have h2 : c ≤ d - inner ℝ w (y - x0) := by exact_mod_cast h1
  exact_mod_cast (by linarith : c + inner ℝ w (y - x0) ≤ d)

/-! ### Separation -/

lemma epi_closed (f : E → EReal) (hf : LowerSemicontinuous f) : IsClosed (epigraph f) := by
  have h1 : IsClosed {p : E × EReal | f p.1 ≤ p.2} := hf.isClosed_epigraph
  have h2 : Continuous (fun p : E × ℝ => (p.1, (p.2 : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact IsClosed.preimage h2 h1

lemma sep_key (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) {m : ℝ} (hm : ∀ x, (m : EReal) ≤ f x)
    (h0 : conjugate f 0 = ((-m : ℝ) : EReal)) {v : E}
    (hv : ∀ y, conjugate f 0 + ((inner ℝ v y : ℝ) : EReal) ≤ conjugate f y) :
    f v ≤ m := by
  by_contra hlt
  push_neg at hlt
  have hnotmem : ((v, m) : E × ℝ) ∉ epigraph f := by
    intro h
    exact absurd h (not_le.mpr hlt)
  obtain ⟨Λ, u, hΛu, huΛ⟩ :=
    geometric_hahn_banach_closed_point hf_convex (epi_closed f hf_lsc) hnotmem
  obtain ⟨y, hy⟩ : ∃ y : E, ∀ x : E, inner ℝ y x = Λ (x, 0) :=
    ⟨(InnerProductSpace.toDual ℝ E).symm (Λ.comp (ContinuousLinearMap.inl ℝ E ℝ)),
      fun x => by rw [InnerProductSpace.toDual_symm_apply]; simp⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℝ, Λ (0, 1) = β := ⟨_, rfl⟩
  have key : ∀ x : E, ∀ t : ℝ, Λ (x, t) = inner ℝ y x + t * β := by
    intro x t
    have hxt : ((x, t) : E × ℝ) = (x, 0) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [hxt, map_add, map_smul, smul_eq_mul, hy, hβ]
  -- β ≤ 0
  obtain ⟨x0, hx0⟩ := hf_proper.2
  have hx0_ne_top : f x0 ≠ ⊤ := ne_of_lt hx0
  have hx0_ne_bot : f x0 ≠ ⊥ := ne_of_gt (hf_proper.1 x0)
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x0 = a :=
    ⟨(f x0).toReal, (EReal.coe_toReal hx0_ne_top hx0_ne_bot).symm⟩
  have hβ_le : β ≤ 0 := by
    by_contra hβpos
    push_neg at hβpos
    obtain ⟨s, hs⟩ : ∃ s : ℝ, s = |u - inner ℝ y x0 - a * β| / β + 1 := ⟨_, rfl⟩
    have hs0 : 0 ≤ s := by rw [hs]; positivity
    have hmem : ((x0, a + s) : E × ℝ) ∈ epigraph f := by
      show f x0 ≤ ((a + s : ℝ) : EReal)
      rw [ha]
      exact_mod_cast (by linarith : a ≤ a + s)
    have h1 := hΛu _ hmem
    rw [key] at h1
    have h2 : s * β = |u - inner ℝ y x0 - a * β| + β := by
      rw [hs]; field_simp
    have h3 := le_abs_self (u - inner ℝ y x0 - a * β)
    nlinarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / (1 - β) := ⟨_, rfl⟩
  have hβ1 : (0 : ℝ) < 1 - β := by linarith
  have hc_pos : 0 < c := by
    rw [hc]; exact _root_.div_pos one_pos hβ1
  have hc1 : c * (1 - β) = 1 := by
    rw [hc]; exact one_div_mul_cancel hβ1.ne'
  -- upper bound
  have hup : conjugate f (c • y) ≤ ((c * (u - m) : ℝ) : EReal) := by
    apply conj_le
    intro x
    by_cases hfx : f x = ⊤
    · rw [hfx, EReal.sub_top]
      exact bot_le
    · have hfx_bot : f x ≠ ⊥ := ne_of_gt (hf_proper.1 x)
      obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
        ⟨(f x).toReal, (EReal.coe_toReal hfx hfx_bot).symm⟩
      have hmem : ((x, r) : E × ℝ) ∈ epigraph f := by
        show f x ≤ (r : EReal)
        rw [hr]
      have h1 := hΛu _ hmem
      rw [key] at h1
      have hmr : m ≤ r := by
        have := hm x
        rw [hr] at this
        exact_mod_cast this
      rw [hr, real_inner_smul_left, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      nlinarith [mul_pos hc_pos (show 0 < u - (inner ℝ y x + r * β) by linarith),
        mul_nonneg hc_pos.le (sub_nonneg.mpr hmr),
        show r * (c * (1 - β)) = r by rw [hc1, mul_one]]
  -- lower bound
  have hlow := (hv (c • y)).trans hup
  rw [h0, ← EReal.coe_add, EReal.coe_le_coe_iff, real_inner_smul_right] at hlow
  have h1 := huΛ
  rw [key] at h1
  have hcomm : inner ℝ v y = inner ℝ y v := real_inner_comm _ _
  rw [hcomm] at hlow
  nlinarith [mul_pos hc_pos (show 0 < inner ℝ y v + m * β - u by linarith),
    show m * (c * (1 - β)) = m by rw [hc1, mul_one]]

lemma part_b (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) :
    {x : E | ∀ (y : E), f x ≤ f y} = subdifferential (conjugate f) (0 : E) := by
  ext v
  simp only [Set.mem_setOf_eq, subdifferential]
  constructor
  · intro hv
    obtain ⟨x0, hx0⟩ := hf_proper.2
    have hv_top : f v ≠ ⊤ := ne_of_lt (lt_of_le_of_lt (hv x0) hx0)
    have hv_bot : f v ≠ ⊥ := ne_of_gt (hf_proper.1 v)
    obtain ⟨m, hm⟩ : ∃ m : ℝ, f v = m := ⟨(f v).toReal, (EReal.coe_toReal hv_top hv_bot).symm⟩
    have hinf : sInf (Set.range f) = f v := by
      apply le_antisymm
      · exact sInf_le ⟨v, rfl⟩
      · apply le_sInf
        rintro _ ⟨y, rfl⟩
        exact hv y
    have h0 : conjugate f 0 = ((-m : ℝ) : EReal) := by
      have := part_a f
      rw [hinf, hm] at this
      rw [EReal.coe_neg, this, neg_neg]
    have hreg : IsRegularSubgradientAt (conjugate f) 0 v := by
      refine ⟨?_, ?_, fun _ => 0, ?_, Set.univ, Filter.univ_mem, ?_⟩
      · rw [h0]; exact EReal.bot_lt_coe _
      · rw [h0]; exact EReal.coe_lt_top _
      · exact Asymptotics.isLittleO_zero _ _
      · intro x _
        rw [h0, sub_zero, add_zero]
        have := conj_ge f x v
        rw [hm, real_inner_comm, ← EReal.coe_sub] at this
        rw [← EReal.coe_add]
        convert this using 2
        ring
    refine ⟨?_, ?_, fun _ => 0, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => hreg⟩
    · rw [h0]; exact EReal.bot_lt_coe _
    · rw [h0]; exact EReal.coe_lt_top _
  · intro hv
    have hbot : ⊥ < conjugate f 0 := hv.1
    have htop : conjugate f 0 < ⊤ := hv.2.1
    obtain ⟨m, hm⟩ : ∃ m : ℝ, conjugate f 0 = ((-m : ℝ) : EReal) :=
      ⟨-(conjugate f 0).toReal, by rw [neg_neg]; exact (EReal.coe_toReal htop.ne hbot.ne').symm⟩
    have hinf : sInf (Set.range f) = (m : EReal) := by
      rw [part_a f, hm, EReal.coe_neg, neg_neg]
    have hle : ∀ x, (m : EReal) ≤ f x := by
      intro x
      rw [← hinf]
      exact sInf_le ⟨x, rfl⟩
    have hglob : ∀ y, conjugate f 0 + ((inner ℝ v y : ℝ) : EReal) ≤ conjugate f y := by
      intro y
      have := subgrad_conj_global f hf_proper hv y
      simpa using this
    have hfv := sep_key f hf_proper hf_lsc hf_convex hle hm hglob
    intro y
    exact hfv.trans (hle y)

/-! ### Compactness and growth -/

lemma lsc_compact_bound (f : E → EReal) (hf : LowerSemicontinuous f) {K : Set E}
    (hK : IsCompact K) {a : EReal} (ha : a ≠ ⊤) (h : ∀ x ∈ K, a < f x) :
    ∃ c : ℝ, a < c ∧ ∀ x ∈ K, (c : EReal) ≤ f x := by
  rcases K.eq_empty_or_nonempty with hKe | hne
  · obtain ⟨c, hc, -⟩ := EReal.lt_iff_exists_real_btwn.1 (lt_top_iff_ne_top.2 ha)
    refine ⟨c, hc, fun x hx => ?_⟩
    rw [hKe] at hx
    exact absurd hx (Set.notMem_empty x)
  · obtain ⟨x1, hx1K, hmin⟩ :=
      LowerSemicontinuousOn.exists_isMinOn hne hK (hf.lowerSemicontinuousOn K)
    obtain ⟨c, hac, hcf⟩ := EReal.lt_iff_exists_real_btwn.1 (h x1 hx1K)
    exact ⟨c, hac, fun x hx => hcf.le.trans (isMinOn_iff.1 hmin x hx)⟩

lemma growth (f : E → EReal) (hf : ConvexEReal f) {x0 : E} {a c R : ℝ}
    (hx0 : f x0 ≤ a) (hR : 0 < R)
    (hS : ∀ y, ‖y - x0‖ = R → (c : EReal) ≤ f y) :
    ∀ x (b : ℝ), R ≤ ‖x - x0‖ → f x ≤ b → a + (c - a) * ‖x - x0‖ / R ≤ b := by
  intro x b hRD hxb
  have hDpos : 0 < ‖x - x0‖ := lt_of_lt_of_le hR hRD
  have hl0 : 0 ≤ R / ‖x - x0‖ := div_nonneg hR.le hDpos.le
  have hl1 : R / ‖x - x0‖ ≤ 1 := (div_le_one₀ hDpos).2 hRD
  have hlD : R / ‖x - x0‖ * ‖x - x0‖ = R := div_mul_cancel₀ R hDpos.ne'
  have hy := epi_convex_ineq f hf hx0 hxb hl0 hl1
  have hyn : ‖((1 - R / ‖x - x0‖) • x0 + (R / ‖x - x0‖) • x) - x0‖ = R := by
    have e : ((1 - R / ‖x - x0‖) • x0 + (R / ‖x - x0‖) • x) - x0
        = (R / ‖x - x0‖) • (x - x0) := by
      rw [sub_smul, one_smul, smul_sub]; abel
    rw [e, norm_smul, Real.norm_eq_abs, abs_of_nonneg hl0, hlD]
  have hreal : c ≤ (1 - R / ‖x - x0‖) * a + R / ‖x - x0‖ * b :=
    EReal.coe_le_coe_iff.1 ((hS _ hyn).trans hy)
  have key : (c - a) * ‖x - x0‖ ≤ (b - a) * R := by
    have h2 : c - a ≤ R / ‖x - x0‖ * (b - a) := by linarith
    calc (c - a) * ‖x - x0‖ ≤ R / ‖x - x0‖ * (b - a) * ‖x - x0‖ :=
          mul_le_mul_of_nonneg_right h2 hDpos.le
      _ = (R / ‖x - x0‖ * ‖x - x0‖) * (b - a) := by ring
      _ = (b - a) * R := by rw [hlD]; ring
  have : (c - a) * ‖x - x0‖ / R ≤ b - a := (div_le_iff₀ hR).2 key
  linarith

/-! ### Part (c) -/

lemma conj_upper (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) (x_bar : E)
    (h : {x : E | ∀ (y : E), f x ≤ f y} = {x_bar}) {δ : ℝ} (hδ : 0 < δ) :
    ∃ η > 0, ∀ v : E, ‖v‖ < η →
      conjugate f v ≤ ((inner ℝ v x_bar - (f x_bar).toReal + δ * ‖v‖ : ℝ) : EReal) := by
  have hmin : ∀ y, f x_bar ≤ f y := by
    have hx : x_bar ∈ {x : E | ∀ (y : E), f x ≤ f y} := h ▸ Set.mem_singleton x_bar
    exact hx
  obtain ⟨x0, hx0⟩ := hf_proper.2
  have hne_top : f x_bar ≠ ⊤ := ne_top_of_le_ne_top (ne_of_lt hx0) (hmin x0)
  have hne_bot : f x_bar ≠ ⊥ := ne_of_gt (hf_proper.1 x_bar)
  obtain ⟨m, hm_def⟩ : ∃ m : ℝ, m = (f x_bar).toReal := ⟨_, rfl⟩
  rw [← hm_def]
  have hm : f x_bar = (m : EReal) := by
    rw [hm_def]; exact (EReal.coe_toReal hne_top hne_bot).symm
  have hsph : ∀ y ∈ Metric.sphere x_bar δ, (m : EReal) < f y := by
    intro y hy
    rw [mem_sphere_iff_norm] at hy
    have hyne : y ≠ x_bar := by
      intro heq
      rw [heq, sub_self, norm_zero] at hy
      exact (ne_of_gt hδ) hy.symm
    have hy_notin : y ∉ {x : E | ∀ (y : E), f x ≤ f y} := by
      rw [h]; exact hyne
    simp only [Set.mem_setOf_eq, not_forall, not_le] at hy_notin
    obtain ⟨z, hz⟩ := hy_notin
    rw [← hm]
    exact lt_of_le_of_lt (hmin z) hz
  obtain ⟨c, hmc, hc⟩ :=
    lsc_compact_bound f hf_lsc (isCompact_sphere x_bar δ) (EReal.coe_ne_top m) hsph
  have hmc' : m < c := EReal.coe_lt_coe_iff.mp hmc
  have hgrowth := growth f hf_convex (x0 := x_bar) (a := m) (c := c) (R := δ) (le_of_eq hm) hδ
    (fun y hy => hc y (by rw [mem_sphere_iff_norm]; exact hy))
  refine ⟨(c - m) / δ, div_pos (sub_pos.mpr hmc') hδ, ?_⟩
  intro v hv
  apply conj_le
  intro x
  rcases eq_or_ne (f x) ⊤ with hfx | hfx
  · rw [hfx, EReal.sub_top]
    exact bot_le
  · have hfx_bot : f x ≠ ⊥ := ne_of_gt (hf_proper.1 x)
    obtain ⟨b, hb⟩ : ∃ b : ℝ, f x = b := ⟨(f x).toReal, (EReal.coe_toReal hfx hfx_bot).symm⟩
    rw [hb, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    have hmb : m ≤ b := by
      have hle := hmin x
      rw [hm, hb] at hle
      exact EReal.coe_le_coe_iff.mp hle
    have hinner : inner ℝ v x ≤ inner ℝ v x_bar + ‖v‖ * ‖x - x_bar‖ := by
      have heq : inner ℝ v x = inner ℝ v x_bar + inner ℝ v (x - x_bar) := by
        rw [inner_sub_right]; ring
      rw [heq]
      have hcs := real_inner_le_norm v (x - x_bar)
      linarith
    have h2 : 0 ≤ δ * ‖v‖ := mul_nonneg (le_of_lt hδ) (norm_nonneg v)
    rcases le_or_gt ‖x - x_bar‖ δ with hDδ | hDδ
    · have h1 : ‖v‖ * ‖x - x_bar‖ ≤ δ * ‖v‖ := by
        rw [mul_comm δ]
        exact mul_le_mul_of_nonneg_left hDδ (norm_nonneg v)
      linarith
    · have hg := hgrowth x b (le_of_lt hDδ) (le_of_eq hb)
      have hη : (c - m) * ‖x - x_bar‖ / δ = (c - m) / δ * ‖x - x_bar‖ := by ring
      rw [hη] at hg
      have h1 : ‖v‖ * ‖x - x_bar‖ ≤ (c - m) / δ * ‖x - x_bar‖ :=
        mul_le_mul_of_nonneg_right (le_of_lt hv) (norm_nonneg _)
      linarith

lemma part_c_mp (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) (x_bar : E)
    (h : {x : E | ∀ (y : E), f x ≤ f y} = {x_bar}) :
    IsDifferentiableAtWithGradientEReal (conjugate f) (0 : E) x_bar := by
  have hmin : ∀ y, f x_bar ≤ f y := by
    have hx : x_bar ∈ {x : E | ∀ (y : E), f x ≤ f y} := h ▸ Set.mem_singleton x_bar
    exact hx
  obtain ⟨x0, hx0⟩ := hf_proper.2
  have hne_top : f x_bar ≠ ⊤ := ne_top_of_le_ne_top (ne_of_lt hx0) (hmin x0)
  have hne_bot : f x_bar ≠ ⊥ := ne_of_gt (hf_proper.1 x_bar)
  have hm : f x_bar = (((f x_bar).toReal : ℝ) : EReal) := (EReal.coe_toReal hne_top hne_bot).symm
  have hlow : ∀ v, ((inner ℝ v x_bar - (f x_bar).toReal : ℝ) : EReal) ≤ conjugate f v := by
    intro v
    have hge := conj_ge f v x_bar
    rw [hm, ← EReal.coe_sub] at hge
    exact hge
  obtain ⟨η₁, hη₁, hup₁⟩ := conj_upper f hf_proper hf_lsc hf_convex x_bar h one_pos
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, ∀ v, g v = (conjugate f v).toReal := ⟨_, fun _ => rfl⟩
  have hfin : ∀ v, ‖v‖ < η₁ → conjugate f v = (g v : EReal) := by
    intro v hv
    have h1 := hup₁ v hv
    have h2 := hlow v
    have hne_top' : conjugate f v ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hne_bot' : conjugate f v ≠ ⊥ := ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) h2
    rw [hg]
    exact (EReal.coe_toReal hne_top' hne_bot').symm
  have hg_low : ∀ v, ‖v‖ < η₁ → inner ℝ v x_bar - (f x_bar).toReal ≤ g v := by
    intro v hv
    have hl := hlow v
    rw [hfin v hv] at hl
    exact EReal.coe_le_coe_iff.mp hl
  have hg_up : ∀ ε > 0, ∃ η > 0, ∀ v, ‖v‖ < η → ‖v‖ < η₁ →
      g v ≤ inner ℝ v x_bar - (f x_bar).toReal + ε * ‖v‖ := by
    intro ε hε
    obtain ⟨η, hη, hup⟩ := conj_upper f hf_proper hf_lsc hf_convex x_bar h hε
    refine ⟨η, hη, fun v hv hv1 => ?_⟩
    have hu := hup v hv
    rw [hfin v hv1] at hu
    exact EReal.coe_le_coe_iff.mp hu
  have hg0 : g 0 = -(f x_bar).toReal := by
    have h1 := hg_low 0 (by simpa using hη₁)
    obtain ⟨η, hη, hup⟩ := hg_up 1 one_pos
    have h2 := hup 0 (by simpa using hη) (by simpa using hη₁)
    simp only [inner_zero_left, norm_zero, mul_zero, add_zero, zero_sub] at h1 h2
    linarith
  have hgrad : HasGradientAt g x_bar 0 := by
    rw [hasGradientAt_iff_hasFDerivAt, hasFDerivAt_iff_isLittleO_nhds_zero,
      Asymptotics.isLittleO_iff]
    intro ε hε
    obtain ⟨η, hη, hup⟩ := hg_up ε hε
    have hball : Metric.ball (0 : E) (min η₁ η) ∈ 𝓝 (0 : E) :=
      Metric.ball_mem_nhds _ (lt_min hη₁ hη)
    filter_upwards [hball] with v hv
    rw [mem_ball_zero_iff] at hv
    have hv1 : ‖v‖ < η₁ := lt_of_lt_of_le hv (min_le_left _ _)
    have hv2 : ‖v‖ < η := lt_of_lt_of_le hv (min_le_right _ _)
    have hl := hg_low v hv1
    have hu := hup v hv2 hv1
    rw [zero_add, InnerProductSpace.toDual_apply_apply, hg0, real_inner_comm, Real.norm_eq_abs,
      abs_le]
    constructor <;> nlinarith [norm_nonneg v]
  refine ⟨g, ⟨Metric.ball 0 η₁, Metric.ball_mem_nhds _ hη₁, fun v hv => ?_⟩,
    hgrad.differentiableAt, hgrad.gradient⟩
  rw [mem_ball_zero_iff] at hv
  exact hfin v hv

lemma part_c_mpr (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) (x_bar : E)
    (h : IsDifferentiableAtWithGradientEReal (conjugate f) (0 : E) x_bar) :
    {x : E | ∀ (y : E), f x ≤ f y} = {x_bar} := by
  obtain ⟨g, ⟨U, hU, hgU⟩, hdiff, hgrad⟩ := h
  rw [part_b f hf_proper hf_lsc hf_convex]
  have h0U : (0 : E) ∈ U := mem_of_mem_nhds hU
  have hg0 : conjugate f 0 = ((g 0 : ℝ) : EReal) := hgU 0 h0U
  have hgradAt : HasGradientAt g x_bar 0 := by
    have := hdiff.hasGradientAt
    rwa [hgrad] at this
  have hfd : HasFDerivAt g (InnerProductSpace.toDual ℝ E x_bar) 0 :=
    hasGradientAt_iff_hasFDerivAt.mp hgradAt
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨?_, ?_⟩
  · -- x_bar ∈ subdifferential
    have hreg : IsRegularSubgradientAt (conjugate f) 0 x_bar := by
      refine ⟨?_, ?_, fun x => g x - g 0 - inner ℝ x_bar (x - 0), ?_, U, hU, ?_⟩
      · rw [hg0]; exact EReal.bot_lt_coe _
      · rw [hg0]; exact EReal.coe_lt_top _
      · have h1 := hfd.isLittleO
        have h2 : (fun x => g x - g 0 - inner ℝ x_bar (x - 0)) =o[𝓝 (0:E)]
            (fun x => x - 0) := h1
        exact Asymptotics.isLittleO_norm_right.mpr h2
      · intro x hx
        rw [hg0, hgU x hx]
        apply le_of_eq
        rw [← EReal.coe_add]
        congr 1
        ring
    exact ⟨hreg.1, hreg.2.1, fun _ => 0, fun _ => x_bar, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => hreg⟩
  · intro v hv
    have hglob := subgrad_conj_global f hf_proper hv
    have hmin : IsLocalMin (fun y => g y - inner ℝ v y) 0 := by
      refine Filter.eventually_of_mem hU ?_
      intro y hy
      have := hglob y
      rw [hg0, hgU y hy, sub_zero, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
      simp only [inner_zero_right, sub_zero]
      linarith
    have hk : HasFDerivAt (fun y => g y - inner ℝ v y)
        (InnerProductSpace.toDual ℝ E x_bar - InnerProductSpace.toDual ℝ E v) 0 :=
      hfd.sub (InnerProductSpace.toDual ℝ E v).hasFDerivAt
    have h3 := hmin.hasFDerivAt_eq_zero hk
    have h4 : InnerProductSpace.toDual ℝ E x_bar = InnerProductSpace.toDual ℝ E v :=
      sub_eq_zero.mp h3
    exact ((InnerProductSpace.toDual ℝ E).injective h4).symm

/-! ### Parts (d) and (e) -/

lemma agentG_helper1 (f : E → EReal) {w x : E} {r M : ℝ}
    (hw : conjugate f w ≤ (M : EReal)) (hx : f x ≤ (r : EReal)) :
    inner ℝ w x - r ≤ M := by
  have h1 := conj_ge f w x
  have h2 : ((inner ℝ w x : ℝ) : EReal) - (r : EReal) ≤ ((inner ℝ w x : ℝ) : EReal) - f x :=
    EReal.sub_le_sub le_rfl hx
  have h3 : ((inner ℝ w x - r : ℝ) : EReal) ≤ (M : EReal) := by
    rw [EReal.coe_sub]
    exact h2.trans (h1.trans hw)
  exact_mod_cast h3

lemma basis_bound (f : E → EReal) {K : ℝ} (hK : 0 < K)
    (hfin : ∀ v : E, ‖v‖ ≤ K → conjugate f v < ⊤) :
    ∃ M : ℝ, ∀ x (r : ℝ), f x ≤ r → K * ‖x‖ ≤ (Module.finrank ℝ E : ℝ) * (r + M) := by
  set b := stdOrthonormalBasis ℝ E with hb
  have hb1 : ∀ i, ‖b i‖ = 1 := fun i => b.orthonormal.1 i
  have hn1 : ∀ i, ‖K • b i‖ ≤ K := by
    intro i
    rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs, abs_of_pos hK]
  have hn2 : ∀ i, ‖-(K • b i)‖ ≤ K := by
    intro i
    rw [norm_neg]
    exact hn1 i
  set M : ℝ := ∑ i, (|(conjugate f (K • b i)).toReal| + |(conjugate f (-(K • b i))).toReal|)
    with hM
  have key : ∀ w : E, conjugate f w < ⊤ → |(conjugate f w).toReal| ≤ M →
      conjugate f w ≤ (M : EReal) := by
    intro w hw hle
    calc conjugate f w ≤ ((conjugate f w).toReal : EReal) := EReal.le_coe_toReal hw.ne
      _ ≤ ((|(conjugate f w).toReal| : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr (le_abs_self _)
      _ ≤ (M : EReal) := EReal.coe_le_coe_iff.mpr hle
  have hsingle : ∀ i, |(conjugate f (K • b i)).toReal| + |(conjugate f (-(K • b i))).toReal| ≤ M :=
    fun i => Finset.single_le_sum
      (f := fun i => |(conjugate f (K • b i)).toReal| + |(conjugate f (-(K • b i))).toReal|)
      (fun j _ => add_nonneg (abs_nonneg _) (abs_nonneg _)) (Finset.mem_univ i)
  have hM1 : ∀ i, conjugate f (K • b i) ≤ (M : EReal) := by
    intro i
    apply key _ (hfin _ (hn1 i))
    exact (le_add_of_nonneg_right (abs_nonneg _)).trans (hsingle i)
  have hM2 : ∀ i, conjugate f (-(K • b i)) ≤ (M : EReal) := by
    intro i
    apply key _ (hfin _ (hn2 i))
    exact (le_add_of_nonneg_left (abs_nonneg _)).trans (hsingle i)
  refine ⟨M, fun x r hx => ?_⟩
  have hcoord : ∀ i, K * |inner ℝ (b i) x| ≤ r + M := by
    intro i
    have e1 := agentG_helper1 f (hM1 i) hx
    have e2 := agentG_helper1 f (hM2 i) hx
    rw [real_inner_smul_left] at e1
    rw [inner_neg_left, real_inner_smul_left] at e2
    rw [← abs_of_pos hK, ← abs_mul, abs_le]
    constructor <;> linarith
  have hnorm : ‖x‖ ≤ ∑ i, |inner ℝ (b i) x| := by
    conv_lhs => rw [← b.sum_repr' x]
    refine (norm_sum_le _ _).trans ?_
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro i _
    rw [norm_smul, hb1 i, mul_one, Real.norm_eq_abs]
  calc K * ‖x‖ ≤ K * ∑ i, |inner ℝ (b i) x| := mul_le_mul_of_nonneg_left hnorm hK.le
    _ = ∑ i, K * |inner ℝ (b i) x| := Finset.mul_sum _ _ _
    _ ≤ ∑ _i : Fin (Module.finrank ℝ E), (r + M) := Finset.sum_le_sum (fun i _ => hcoord i)
    _ = (Module.finrank ℝ E : ℝ) * (r + M) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

lemma part_d_mp (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (hf_convex : ConvexEReal f) (h : IsLevelBounded f) :
    (0 : E) ∈ interior (effDom (conjugate f)) := by
  obtain ⟨x0, hx0⟩ := hf_proper.2
  have hx0top : f x0 ≠ ⊤ := hx0.ne
  have hx0bot : f x0 ≠ ⊥ := (hf_proper.1 x0).ne'
  set a : ℝ := (f x0).toReal with ha_def
  have hfa : f x0 = (a : EReal) := (EReal.coe_toReal hx0top hx0bot).symm
  obtain ⟨C0, hC0⟩ := isBounded_iff_forall_norm_le.mp (h (a + 1))
  have hC0' : ∀ x, f x ≤ ((a + 1 : ℝ) : EReal) → ‖x‖ ≤ C0 := fun x hx => hC0 x hx
  have hx0C : ‖x0‖ ≤ C0 :=
    hC0' x0 (by rw [hfa]; exact EReal.coe_le_coe_iff.mpr (by linarith))
  set R : ℝ := C0 + ‖x0‖ + 1 with hR_def
  have hRpos : 0 < R := by have := norm_nonneg x0; linarith
  have hS : ∀ y, ‖y - x0‖ = R → (((a + 1 : ℝ)) : EReal) ≤ f y := by
    intro y hy
    by_contra hcon
    push_neg at hcon
    have hy' := hC0' y hcon.le
    have : ‖y - x0‖ ≤ ‖y‖ + ‖x0‖ := norm_sub_le y x0
    linarith
  have hgrowth := growth f hf_convex (le_of_eq hfa) hRpos hS
  have hgrowth' : ∀ x (b : ℝ), R ≤ ‖x - x0‖ → f x ≤ b → a + ‖x - x0‖ / R ≤ b := by
    intro x b hx hb
    have := hgrowth x b hx hb
    have e : a + 1 - a = 1 := by ring
    rw [e, one_mul] at this
    exact this
  obtain ⟨L, -, hL⟩ := lsc_compact_bound f hf_lsc (isCompact_closedBall x0 R) (a := ⊥)
    bot_ne_top (fun x _ => hf_proper.1 x)
  have hball : Metric.ball (0 : E) (1 / R) ⊆ effDom (conjugate f) := by
    intro v hv
    rw [mem_ball_zero_iff] at hv
    show conjugate f v < ⊤
    have key : ∀ x, ((inner ℝ v x : ℝ) : EReal) - f x ≤
        ((max (inner ℝ v x0 - a) (‖v‖ * (‖x0‖ + R) - L) : ℝ) : EReal) := by
      intro x
      by_cases htop : f x = ⊤
      · rw [htop]; simp
      · have hbot : f x ≠ ⊥ := (hf_proper.1 x).ne'
        obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
        rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        by_cases hx : R ≤ ‖x - x0‖
        · have hb := hgrowth' x r hx (le_of_eq hr)
          have h1 : inner ℝ v x = inner ℝ v x0 + inner ℝ v (x - x0) := by
            rw [inner_sub_right]; ring
          have h2 : inner ℝ v (x - x0) ≤ ‖v‖ * ‖x - x0‖ := real_inner_le_norm v (x - x0)
          have h3 : ‖v‖ * ‖x - x0‖ ≤ ‖x - x0‖ / R := by
            rw [div_eq_mul_inv, mul_comm (‖x - x0‖)]
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
            rw [one_div] at hv; exact hv.le
          have : inner ℝ v x - r ≤ inner ℝ v x0 - a := by linarith
          exact le_trans this (le_max_left _ _)
        · push_neg at hx
          have hxK : x ∈ Metric.closedBall x0 R := by
            rw [Metric.mem_closedBall, dist_eq_norm]; exact hx.le
          have hLx := hL x hxK
          rw [hr, EReal.coe_le_coe_iff] at hLx
          have h2 : inner ℝ v x ≤ ‖v‖ * ‖x‖ := real_inner_le_norm v x
          have hxn : ‖x‖ ≤ ‖x0‖ + R := by
            have : ‖x‖ - ‖x0‖ ≤ ‖x - x0‖ := norm_sub_norm_le x x0
            linarith
          have h3 : ‖v‖ * ‖x‖ ≤ ‖v‖ * (‖x0‖ + R) :=
            mul_le_mul_of_nonneg_left hxn (norm_nonneg v)
          have : inner ℝ v x - r ≤ ‖v‖ * (‖x0‖ + R) - L := by linarith
          exact le_trans this (le_max_right _ _)
    exact lt_of_le_of_lt (conj_le f v _ key) (EReal.coe_lt_top _)
  rw [mem_interior_iff_mem_nhds]
  exact Filter.mem_of_superset (Metric.ball_mem_nhds 0 (by positivity)) hball

lemma part_d_mpr (f : E → EReal) (h : (0 : E) ∈ interior (effDom (conjugate f))) :
    IsLevelBounded f := by
  rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff] at h
  obtain ⟨ε, hε, hball⟩ := h
  have hK : (0 : ℝ) < ε / 2 := by linarith
  have hfin : ∀ v : E, ‖v‖ ≤ ε / 2 → conjugate f v < ⊤ := by
    intro v hv
    have hv' : v ∈ Metric.ball (0 : E) ε := by
      rw [mem_ball_zero_iff]; linarith
    exact hball hv'
  obtain ⟨M, hM⟩ := basis_bound f hK hfin
  intro α
  rw [isBounded_iff_forall_norm_le]
  refine ⟨(Module.finrank ℝ E : ℝ) * (α + M) / (ε / 2), ?_⟩
  intro x hx
  have hx' : f x ≤ ((α : ℝ) : EReal) := hx
  have h1 := hM x α hx'
  rw [le_div_iff₀ hK]
  linarith

lemma part_e_mp (f : E → EReal) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h : IsOneCoerciveFun f) :
    effDom (conjugate f) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro v
  show conjugate f v < ⊤
  have hv := h (‖v‖ + 1)
  rw [Filter.eventually_comap, Filter.eventually_atTop] at hv
  obtain ⟨N, hN⟩ := hv
  set R : ℝ := max N 1 with hR_def
  have hR1 : 1 ≤ R := le_max_right _ _
  have hRpos : 0 < R := lt_of_lt_of_le one_pos hR1
  obtain ⟨L, -, hL⟩ := lsc_compact_bound f hf_lsc (isCompact_closedBall (0 : E) R) (a := ⊥)
    bot_ne_top (fun x _ => hf_proper.1 x)
  have key : ∀ x, ((inner ℝ v x : ℝ) : EReal) - f x ≤ ((max 0 (‖v‖ * R - L) : ℝ) : EReal) := by
    intro x
    by_cases htop : f x = ⊤
    · rw [htop]; simp
    · have hbot : f x ≠ ⊥ := (hf_proper.1 x).ne'
      obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop hbot).symm⟩
      rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      by_cases hx : R ≤ ‖x‖
      · have hxN : N ≤ ‖x‖ := le_trans (le_max_left _ _) hx
        have hcoer := hN ‖x‖ hxN x rfl
        rw [hr, ← EReal.coe_mul, EReal.coe_le_coe_iff] at hcoer
        have hxpos : 0 < ‖x‖ := lt_of_lt_of_le hRpos hx
        have h1 : (‖v‖ + 1) * ‖x‖ ≤ r := by
          have := mul_le_mul_of_nonneg_right hcoer hxpos.le
          rwa [mul_comm ‖x‖⁻¹ r, mul_assoc, inv_mul_cancel₀ hxpos.ne', mul_one] at this
        have h2 : inner ℝ v x ≤ ‖v‖ * ‖x‖ := real_inner_le_norm v x
        have : inner ℝ v x - r ≤ 0 := by nlinarith
        exact le_trans this (le_max_left _ _)
      · push_neg at hx
        have hxK : x ∈ Metric.closedBall (0 : E) R := by
          rw [mem_closedBall_zero_iff]; exact hx.le
        have hLx := hL x hxK
        rw [hr, EReal.coe_le_coe_iff] at hLx
        have h2 : inner ℝ v x ≤ ‖v‖ * ‖x‖ := real_inner_le_norm v x
        have h3 : ‖v‖ * ‖x‖ ≤ ‖v‖ * R := mul_le_mul_of_nonneg_left hx.le (norm_nonneg v)
        have : inner ℝ v x - r ≤ ‖v‖ * R - L := by linarith
        exact le_trans this (le_max_right _ _)
  exact lt_of_le_of_lt (conj_le f v _ key) (EReal.coe_lt_top _)

lemma part_e_mpr (f : E → EReal) (h : effDom (conjugate f) = Set.univ) :
    IsOneCoerciveFun f := by
  have hfin : ∀ v : E, conjugate f v < ⊤ := by
    intro v
    have hv : v ∈ effDom (conjugate f) := by rw [h]; exact Set.mem_univ v
    exact hv
  have hnbot : ∀ x : E, f x ≠ ⊥ := by
    intro x hx
    have h1 := conj_ge f 0 x
    rw [hx, EReal.coe_sub_bot, top_le_iff] at h1
    exact (ne_of_lt (hfin 0)) h1
  intro C
  have hn0 : (0 : ℝ) ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
  have hKpos : (0 : ℝ) < ((Module.finrank ℝ E : ℝ) + 1) * (|C| + 1) := by positivity
  obtain ⟨M, hM⟩ := basis_bound f hKpos (fun v _ => hfin v)
  rw [Filter.eventually_comap, Filter.eventually_atTop]
  refine ⟨max M 1, ?_⟩
  intro t ht x hxt
  subst hxt
  have hxM : M ≤ ‖x‖ := le_trans (le_max_left _ _) ht
  have hx1 : (1 : ℝ) ≤ ‖x‖ := le_trans (le_max_right _ _) ht
  have hxpos : (0 : ℝ) < ‖x‖ := by linarith
  have hinvpos : (0 : ℝ) < ‖x‖⁻¹ := inv_pos.mpr hxpos
  by_cases htop : f x = ⊤
  · rw [htop, EReal.coe_mul_top_of_pos hinvpos]
    exact le_top
  · obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r := ⟨(f x).toReal, (EReal.coe_toReal htop (hnbot x)).symm⟩
    have hb := hM x r (le_of_eq hr)
    have hrM : 0 ≤ r + M := by
      by_contra hneg
      push_neg at hneg
      have h2 : (Module.finrank ℝ E : ℝ) * (r + M) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hn0 hneg.le
      have h3 : 0 < ((Module.finrank ℝ E : ℝ) + 1) * (|C| + 1) * ‖x‖ := mul_pos hKpos hxpos
      linarith
    have h4 : (Module.finrank ℝ E : ℝ) * (r + M) ≤ ((Module.finrank ℝ E : ℝ) + 1) * (r + M) := by
      nlinarith
    have h5 : (|C| + 1) * ‖x‖ ≤ r + M := by
      have h6 : ((Module.finrank ℝ E : ℝ) + 1) * ((|C| + 1) * ‖x‖)
          ≤ ((Module.finrank ℝ E : ℝ) + 1) * (r + M) := by
        rw [← mul_assoc]; linarith
      have hn1 : (0 : ℝ) < (Module.finrank ℝ E : ℝ) + 1 := by linarith
      exact le_of_mul_le_mul_left h6 hn1
    have hCx : C * ‖x‖ ≤ r := by
      have h7 : C ≤ |C| := le_abs_self C
      nlinarith
    have hC : C ≤ ‖x‖⁻¹ * r := by
      rw [le_inv_mul_iff₀ hxpos]; linarith
    rw [hr, ← EReal.coe_mul]
    exact EReal.coe_le_coe_iff.mpr hC

end RW118

theorem RW_chap_11_8
  (f : E → EReal)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  ((sInf (Set.range f) = - conjugate f (0 : E)) ∧
    ({x : E | ∀ (y : E), f x ≤ f y} =
      subdifferential (conjugate f) (0 : E))) ∧
  (∀ (x_bar : E),
    ({x : E | ∀ (y : E), f x ≤ f y} = {x_bar} ↔
      IsDifferentiableAtWithGradientEReal
        (conjugate f)
        (0 : E)
        x_bar)) ∧
  (IsLevelBounded f ↔
    (0 : E) ∈ interior (effDom (conjugate f))) ∧
  (IsOneCoerciveFun f ↔
    effDom (conjugate f) = Set.univ) := by
  refine ⟨⟨RW118.part_a f, RW118.part_b f hf_proper hf_lsc hf_convex⟩,
    fun x_bar => ⟨RW118.part_c_mp f hf_proper hf_lsc hf_convex x_bar,
      RW118.part_c_mpr f hf_proper hf_lsc hf_convex x_bar⟩,
    ⟨RW118.part_d_mp f hf_proper hf_lsc hf_convex, RW118.part_d_mpr f⟩,
    ⟨RW118.part_e_mp f hf_proper hf_lsc, RW118.part_e_mpr f⟩⟩

end RW_chap_11_8
