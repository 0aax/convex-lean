import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_3_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_3_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_3_5`, so the main result is `FCA_chap_C_1_3_5.FCA_chap_C_1_3_5`.
-/

namespace FCA_chap_C_1_3_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_3_5
  (σk : ℕ → (E → ℝ))
  (σ : E → ℝ)
  (hσk_sublinear : ∀ k, IsSublinear (liftRealtoEReal (σk k))) :
  List.TFAE [
    (∀ x, Filter.Tendsto (fun k => σk k x)
      Filter.atTop (𝓝 (σ x))),
    (∀ (K : Set E),
      IsCompact K →
      TendstoUniformlyOn σk σ Filter.atTop K),
    (∃ (hσ_sub : IsSublinear (liftRealtoEReal σ)),
      Filter.Tendsto
        (fun k => distOnFunctions (σk k) σ
          (hσk_sublinear k) hσ_sub)
        Filter.atTop (𝓝 0))
  ] := by
  -- characterization of sublinearity for real-valued functions
  have key : ∀ f : E → ℝ, IsSublinear (liftRealtoEReal f) ↔
      ((∀ x y, f (x + y) ≤ f x + f y) ∧ (∀ x (t : ℝ), 0 < t → f (t • x) = t * f x)) := by
    intro f
    constructor
    · rintro ⟨⟨_, _, hconv⟩, hhom⟩
      have hom : ∀ x (t : ℝ), 0 < t → f (t • x) = t * f x := by
        intro x t ht
        have := hhom x t ht
        simp only [liftRealtoEReal] at this
        exact_mod_cast this
      refine ⟨?_, hom⟩
      intro x y
      have hx : (x, f x) ∈ epigraph (liftRealtoEReal f) := by
        simp [epigraph, liftRealtoEReal]
      have hy : (y, f y) ∈ epigraph (liftRealtoEReal f) := by
        simp [epigraph, liftRealtoEReal]
      have hmid := hconv hx hy (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
        (by norm_num)
      simp only [epigraph, liftRealtoEReal, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add,
        Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hmid
      have hmid' : f ((1/2:ℝ) • x + (1/2:ℝ) • y) ≤ 1/2 * f x + 1/2 * f y := by
        exact_mod_cast hmid
      have h2 := hom ((1/2:ℝ) • x + (1/2:ℝ) • y) 2 (by norm_num)
      have : (2:ℝ) • ((1/2:ℝ) • x + (1/2:ℝ) • y) = x + y := by
        rw [smul_add, smul_smul, smul_smul]; norm_num
      rw [this] at h2
      rw [h2]; linarith
    · rintro ⟨hadd, hom⟩
      have h0 : f 0 = 0 := by
        have := hom 0 2 (by norm_num)
        rw [smul_zero] at this
        linarith
      have hom' : ∀ x (t : ℝ), 0 ≤ t → f (t • x) = t * f x := by
        intro x t ht
        rcases ht.lt_or_eq with ht | ht
        · exact hom x t ht
        · subst ht; simp [h0]
      refine ⟨⟨fun x => EReal.bot_lt_coe _, ⟨0, EReal.coe_lt_top _⟩, ?_⟩, ?_⟩
      · unfold ConvexEReal
        intro p hp q hq a b ha hb hab
        simp only [epigraph, liftRealtoEReal, Set.mem_setOf_eq, EReal.coe_le_coe_iff] at hp hq ⊢
        simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        calc f (a • p.1 + b • q.1) ≤ f (a • p.1) + f (b • q.1) := hadd _ _
          _ = a * f p.1 + b * f q.1 := by rw [hom' _ _ ha, hom' _ _ hb]
          _ ≤ a * p.2 + b * q.2 := by gcongr
      · intro x t ht
        simp only [liftRealtoEReal]
        rw [hom x t ht]
        exact_mod_cast rfl
  have hzero : ∀ f : E → ℝ, IsSublinear (liftRealtoEReal f) → f 0 = 0 := by
    intro f hf
    have := ((key f).1 hf).2 0 2 (by norm_num)
    rw [smul_zero] at this
    linarith
  -- an orthonormal basis
  let b := stdOrthonormalBasis ℝ E
  -- a bound on f from bounds at ± basis vectors
  have bound : ∀ f : E → ℝ, IsSublinear (liftRealtoEReal f) → ∀ B : ℝ, 0 ≤ B →
      (∀ i, f (b i) ≤ B ∧ f (-(b i)) ≤ B) →
      ∀ x, f x ≤ ((Module.finrank ℝ E : ℝ) * B) * ‖x‖ := by
    intro f hf B hB hfb x
    obtain ⟨hadd, hom⟩ := (key f).1 hf
    have h0 : f 0 = 0 := hzero f hf
    have hsmul : ∀ (c : ℝ) (v : E), f v ≤ B → f (-v) ≤ B → f (c • v) ≤ |c| * B := by
      intro c v h1 h2
      rcases lt_trichotomy c 0 with hc | hc | hc
      · have : c • v = (-c) • (-v) := by rw [smul_neg, neg_smul, neg_neg]
        rw [this, hom _ _ (neg_pos.mpr hc), abs_of_neg hc]
        exact mul_le_mul_of_nonneg_left h2 (neg_nonneg.mpr hc.le)
      · subst hc; simp [h0]
      · rw [hom _ _ hc, abs_of_pos hc]
        exact mul_le_mul_of_nonneg_left h1 hc.le
    calc f x = f (∑ i, inner ℝ (b i) x • b i) := by rw [b.sum_repr']
      _ ≤ ∑ i, f (inner ℝ (b i) x • b i) := Finset.le_sum_of_subadditive f h0.le hadd _ _
      _ ≤ ∑ i, |inner ℝ (b i) x| * B := Finset.sum_le_sum (fun i _ => hsmul _ _ (hfb i).1 (hfb i).2)
      _ ≤ ∑ i, ‖x‖ * B := Finset.sum_le_sum (fun i _ => by
            apply mul_le_mul_of_nonneg_right _ hB
            calc |inner ℝ (b i) x| ≤ ‖b i‖ * ‖x‖ := abs_real_inner_le_norm _ _
              _ = ‖x‖ := by rw [b.orthonormal.1 i, one_mul])
      _ = _ := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  -- a uniform bound for a family
  have fam_bound : ∀ g : ℕ → E → ℝ, (∀ k, IsSublinear (liftRealtoEReal (g k))) →
      (∀ v : E, ∃ B, ∀ k, g k v ≤ B) → ∃ C, 0 ≤ C ∧ ∀ k x, g k x ≤ C * ‖x‖ := by
    intro g hg hbdd
    choose B1 hB1 using fun i => hbdd (b i)
    choose B2 hB2 using fun i => hbdd (-(b i))
    refine ⟨(Module.finrank ℝ E : ℝ) * ∑ i, (|B1 i| + |B2 i|), by positivity, fun k x => ?_⟩
    apply bound (g k) (hg k) _ (by positivity)
    intro i
    have hle : |B1 i| + |B2 i| ≤ ∑ j, (|B1 j| + |B2 j|) :=
      Finset.single_le_sum (f := fun j => |B1 j| + |B2 j|) (fun j _ => by positivity)
        (Finset.mem_univ i)
    constructor
    · linarith [hB1 i k, le_abs_self (B1 i), abs_nonneg (B2 i)]
    · linarith [hB2 i k, le_abs_self (B2 i), abs_nonneg (B1 i)]
  -- Lipschitz estimate
  have lip : ∀ f : E → ℝ, IsSublinear (liftRealtoEReal f) → ∀ C : ℝ, (∀ x, f x ≤ C * ‖x‖) →
      ∀ x y, |f x - f y| ≤ C * ‖x - y‖ := by
    intro f hf C hC x y
    obtain ⟨hadd, _⟩ := (key f).1 hf
    have h1 : f x ≤ f y + C * ‖x - y‖ := by
      calc f x = f (y + (x - y)) := by congr 1; abel
        _ ≤ f y + f (x - y) := hadd _ _
        _ ≤ f y + C * ‖x - y‖ := by linarith [hC (x - y)]
    have h2 : f y ≤ f x + C * ‖x - y‖ := by
      have h3 := hC (y - x)
      rw [norm_sub_rev] at h3
      calc f y = f (x + (y - x)) := by congr 1; abel
        _ ≤ f x + f (y - x) := hadd _ _
        _ ≤ f x + C * ‖x - y‖ := by linarith
    rw [abs_le]; constructor <;> linarith
  -- the pointwise limit of sublinear functions is sublinear
  have limit_sub : (∀ x, Filter.Tendsto (fun k => σk k x) Filter.atTop (𝓝 (σ x))) →
      IsSublinear (liftRealtoEReal σ) := by
    intro h
    rw [key]
    constructor
    · intro x y
      apply le_of_tendsto_of_tendsto' (h (x + y)) ((h x).add (h y))
      intro k
      exact ((key _).1 (hσk_sublinear k)).1 x y
    · intro x t ht
      apply tendsto_nhds_unique (h (t • x))
      have : (fun k => σk k (t • x)) = fun k => t * σk k x := by
        funext k; exact ((key _).1 (hσk_sublinear k)).2 x t ht
      rw [this]
      exact (h x).const_mul t
  tfae_have 1 → 2 := by
    intro h K hK
    have hσ := limit_sub h
    have hbdd : ∀ v : E, ∃ B, ∀ k, σk k v ≤ B := by
      intro v
      obtain ⟨B, hB⟩ := (h v).bddAbove_range
      exact ⟨B, fun k => hB ⟨k, rfl⟩⟩
    obtain ⟨C, hC0, hCk⟩ := fam_bound σk hσk_sublinear hbdd
    have hCσ : ∀ x, σ x ≤ C * ‖x‖ := fun x => le_of_tendsto' (h x) (fun k => hCk k x)
    have lipk : ∀ k x y, |σk k x - σk k y| ≤ C * ‖x - y‖ :=
      fun k => lip _ (hσk_sublinear k) C (hCk k)
    have lipσ : ∀ x y, |σ x - σ y| ≤ C * ‖x - y‖ := lip _ hσ C hCσ
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    set δ := ε / (3 * (C + 1)) with hδ
    have hδpos : 0 < δ := by positivity
    have hCδ : (C + 1) * δ = ε / 3 := by rw [hδ]; field_simp
    obtain ⟨t, htK, htfin, hcover⟩ := hK.finite_cover_balls hδpos
    have hev : ∀ᶠ k in Filter.atTop, ∀ c ∈ t, |σk k c - σ c| < ε / 3 := by
      rw [Filter.eventually_all_finite htfin]
      intro c _
      have := Metric.tendsto_nhds.1 (h c) (ε / 3) (by positivity)
      filter_upwards [this] with k hk
      rwa [Real.dist_eq] at hk
    filter_upwards [hev] with k hk
    intro x hx
    obtain ⟨c, hct, hxc⟩ := Set.mem_iUnion₂.mp (hcover hx)
    rw [Metric.mem_ball, dist_eq_norm] at hxc
    rw [Real.dist_eq]
    have e1 := lipk k x c
    have e2 := lipσ x c
    have e3 := hk c hct
    have e4 : C * ‖x - c‖ ≤ C * δ := mul_le_mul_of_nonneg_left hxc.le hC0
    calc |σ x - σk k x| = |(σ x - σ c) + (σ c - σk k c) + (σk k c - σk k x)| := by ring_nf
      _ ≤ |σ x - σ c| + |σ c - σk k c| + |σk k c - σk k x| := abs_add_three _ _ _
      _ < ε := by
          rw [abs_sub_comm (σ c) (σk k c), abs_sub_comm (σk k c) (σk k x)]
          linarith
  tfae_have 2 → 3 := by
    intro h
    have hpt : ∀ x, Filter.Tendsto (fun k => σk k x) Filter.atTop (𝓝 (σ x)) := fun x =>
      (h {x} isCompact_singleton).tendsto_at (Set.mem_singleton x)
    refine ⟨limit_sub hpt, ?_⟩
    have hU := h (Metric.closedBall 0 1) (isCompact_closedBall 0 1)
    rw [Metric.tendstoUniformlyOn_iff] at hU
    rw [Metric.tendsto_nhds]
    intro ε hε
    filter_upwards [hU (ε/2) (half_pos hε)] with k hk
    unfold distOnFunctions
    set S := Set.image (fun x => AbsoluteValue.abs (σk k x - σ x)) {x : E | ‖x‖ ≤ 1} with hS
    have hne : S.Nonempty := ⟨_, ⟨0, by simp, rfl⟩⟩
    have hub : ∀ y ∈ S, y ≤ ε / 2 := by
      rintro y ⟨x, hx, rfl⟩
      have := hk x (by simpa using hx)
      rw [Real.dist_eq] at this
      simp only [AbsoluteValue.abs_apply]
      rw [abs_sub_comm]; exact this.le
    have hbdd : BddAbove S := ⟨ε/2, hub⟩
    have h1 : sSup S ≤ ε / 2 := csSup_le hne hub
    have h2 : 0 ≤ sSup S := by
      obtain ⟨y, hy⟩ := hne
      have : 0 ≤ y := by
        obtain ⟨x, _, rfl⟩ := hy; simp only [AbsoluteValue.abs_apply]; exact abs_nonneg _
      exact this.trans (le_csSup hbdd hy)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg h2]
    linarith
  tfae_have 3 → 1 := by
    rintro ⟨hσ, hlim⟩ x
    have habs : ∀ f : E → ℝ, IsSublinear (liftRealtoEReal f) →
        ∃ C, 0 ≤ C ∧ ∀ y, |f y| ≤ C * ‖y‖ := by
      intro f hf
      obtain ⟨C, hC0, hC⟩ := fam_bound (fun _ => f) (fun _ => hf) (fun v => ⟨f v, fun _ => le_rfl⟩)
      refine ⟨C, hC0, fun y => ?_⟩
      have := lip f hf C (hC 0) y 0
      rwa [hzero f hf, sub_zero, sub_zero] at this
    have hball : ∀ y : E, ‖y‖ ≤ 1 →
        Filter.Tendsto (fun k => σk k y) Filter.atTop (𝓝 (σ y)) := by
      intro y hy
      have hle : ∀ k, |σk k y - σ y| ≤ distOnFunctions (σk k) σ (hσk_sublinear k) hσ := by
        intro k
        obtain ⟨Ck, hCk0, hCk⟩ := habs _ (hσk_sublinear k)
        obtain ⟨C, hC0, hC⟩ := habs _ hσ
        unfold distOnFunctions
        apply le_csSup
        · refine ⟨Ck + C, ?_⟩
          rintro _ ⟨z, hz, rfl⟩
          simp only [AbsoluteValue.abs_apply]
          have hz' : ‖z‖ ≤ 1 := hz
          have a1 := hCk z
          have a2 := hC z
          have a3 : Ck * ‖z‖ ≤ Ck := by nlinarith [norm_nonneg z]
          have a4 : C * ‖z‖ ≤ C := by nlinarith [norm_nonneg z]
          calc |σk k z - σ z| ≤ |σk k z| + |σ z| := abs_sub _ _
            _ ≤ Ck + C := by linarith
        · exact ⟨y, hy, by simp⟩
      have h0 : Filter.Tendsto (fun k => |σk k y - σ y|) Filter.atTop (𝓝 0) :=
        squeeze_zero (fun k => abs_nonneg _) hle hlim
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa [Real.norm_eq_abs] using h0
    set t : ℝ := ‖x‖ + 1 with ht
    have htpos : 0 < t := by positivity
    have hxy : t • (t⁻¹ • x) = x := by rw [smul_smul, mul_inv_cancel₀ htpos.ne', one_smul]
    have hy : ‖t⁻¹ • x‖ ≤ 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos htpos]
      rw [inv_mul_le_iff₀ htpos]; linarith
    have hT := (hball _ hy).const_mul t
    have e1 : ∀ k, σk k x = t * σk k (t⁻¹ • x) := by
      intro k
      have := ((key _).1 (hσk_sublinear k)).2 (t⁻¹ • x) t htpos
      rwa [hxy] at this
    have e2 : σ x = t * σ (t⁻¹ • x) := by
      have := ((key _).1 hσ).2 (t⁻¹ • x) t htpos
      rwa [hxy] at this
    rw [e2]
    exact hT.congr (fun k => (e1 k).symm)
  tfae_finish

end FCA_chap_C_1_3_5
