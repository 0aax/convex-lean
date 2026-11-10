import ConvexStarLib.Defs

/-!
# `RW_chap_9_16`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_9_16` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_9_16`, so the main result is `RW_chap_9_16.RW_chap_9_16`.
-/

namespace RW_chap_9_16

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Auxiliary lemmas -/

set_option linter.unusedSectionVars false

lemma aux_coe_toReal {f : E → EReal} {O : Set E} (hf : IsFiniteOn f O) {x : E} (hx : x ∈ O) :
    f x = ((f x).toReal : EReal) := by
  obtain ⟨r, hr⟩ := hf x hx
  rw [hr, EReal.toReal_coe]

lemma aux_clarke_filter_eq {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O) :
    ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O} =
      (𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x := by
  apply inf_eq_left.mpr
  rw [Filter.le_principal_iff]
  exact Filter.mem_of_superset (Filter.prod_mem_prod Filter.univ_mem (hO.mem_nhds hx))
    (fun p hp => hp.2)

lemma aux_fApproach_eq {f : E → EReal} {x : E} (hc : ContinuousAt f x) :
    fApproach f x = 𝓝 x := by
  unfold fApproach
  exact inf_eq_left.mpr (Filter.tendsto_iff_comap.mp hc)

/-- 1D mean value inequality. -/
lemma aux_mvi_1d (g : ℝ → ℝ) (a c M : ℝ) (hac : a ≤ c)
    (hcont : ContinuousOn g (Set.Icc a c))
    (hder : ∀ s ∈ Set.Ico a c, ∃ d, d ≤ M ∧
      Filter.Tendsto (fun τ => (g (s + τ) - g s) / τ) (𝓝[>] 0) (𝓝 d)) :
    g c - g a ≤ M * (c - a) := by
  have key := image_le_of_liminf_slope_right_le_deriv_boundary (f := g) (a := a) (b := c) hcont
    (B := fun t => g a + M * (t - a)) (B' := fun _ => M) (by simp)
    (by fun_prop) (fun x _ => ?_) (fun x hx r hr => ?_) (x := c) ⟨hac, le_refl c⟩
  · simp only at key
    linarith
  · have := (((hasDerivWithinAt_id x (Set.Ici x)).sub_const a).const_mul M).const_add (g a)
    simpa using this
  · obtain ⟨d, hdM, hd⟩ := hder x hx
    have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), (g (x + τ) - g x) / τ < r :=
      hd (Iio_mem_nhds (lt_of_le_of_lt hdM hr))
    have hsh : Filter.Tendsto (fun z : ℝ => z - x) (𝓝[>] x) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Filter.Tendsto (fun z : ℝ => z - x) (𝓝 x) (𝓝 (x - x)) :=
          (continuous_id.sub continuous_const).tendsto x
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    have h2 : ∀ᶠ z in 𝓝[>] x, slope g x z < r := by
      filter_upwards [hsh.eventually h1] with z hz
      rw [slope_def_field]
      simpa using hz
    exact h2.frequently

/-- Continuity from existence of both one-sided derivatives. -/
lemma aux_cont_of_one_sided (g : ℝ → ℝ) (s : ℝ)
    (h1 : ∃ d, Filter.Tendsto (fun τ => (g (s + τ) - g s) / τ) (𝓝[>] 0) (𝓝 d))
    (h2 : ∃ d, Filter.Tendsto (fun τ => (g (s - τ) - g s) / τ) (𝓝[>] 0) (𝓝 d)) :
    ContinuousAt g s := by
  obtain ⟨d1, hd1⟩ := h1
  obtain ⟨d2, hd2⟩ := h2
  have hτ : Filter.Tendsto (fun τ : ℝ => τ) (𝓝[>] (0:ℝ)) (𝓝 0) := nhdsWithin_le_nhds
  -- right side
  have r1 : Filter.Tendsto (fun τ : ℝ => g (s + τ)) (𝓝[>] (0:ℝ)) (𝓝 (g s)) := by
    have hp := hτ.mul hd1
    rw [zero_mul] at hp
    have hp2 := hp.add_const (g s)
    rw [zero_add] at hp2
    apply hp2.congr'
    filter_upwards [self_mem_nhdsWithin] with τ hτpos
    have hne : τ ≠ 0 := ne_of_gt hτpos
    field_simp
    ring
  have r2 : Filter.Tendsto (fun τ : ℝ => g (s - τ)) (𝓝[>] (0:ℝ)) (𝓝 (g s)) := by
    have hp := hτ.mul hd2
    rw [zero_mul] at hp
    have hp2 := hp.add_const (g s)
    rw [zero_add] at hp2
    apply hp2.congr'
    filter_upwards [self_mem_nhdsWithin] with τ hτpos
    have hne : τ ≠ 0 := ne_of_gt hτpos
    field_simp
    ring
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · -- left: z → s from below, z = s - (s - z)
    have hsh : Filter.Tendsto (fun z : ℝ => s - z) (𝓝[<] s) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Filter.Tendsto (fun z : ℝ => s - z) (𝓝 s) (𝓝 (s - s)) :=
          (continuous_const.sub continuous_id).tendsto s
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    have := r2.comp hsh
    unfold ContinuousWithinAt
    apply this.congr'
    filter_upwards with z
    simp
  · have hsh : Filter.Tendsto (fun z : ℝ => z - s) (𝓝[>] s) (𝓝[>] 0) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have : Filter.Tendsto (fun z : ℝ => z - s) (𝓝 s) (𝓝 (s - s)) :=
          (continuous_id.sub continuous_const).tendsto s
        rw [sub_self] at this
        exact this.mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with z hz
        simpa using hz
    have := r1.comp hsh
    unfold ContinuousWithinAt
    apply this.congr'
    filter_upwards with z
    simp

lemma aux_dirDeriv_real_iff {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {x : E} (hx : x ∈ O) (w : E) (r : ℝ) :
    HasDirectionalDerivativeEReal f x w (r : EReal) ↔
      Filter.Tendsto (fun τ : ℝ => ((f (x + τ • w)).toReal - (f x).toReal) / τ)
        (𝓝[>] 0) (𝓝 r) := by
  have hcont : Filter.Tendsto (fun τ : ℝ => x + τ • w) (𝓝 0) (𝓝 x) := by
    have hc : Continuous (fun τ : ℝ => x + τ • w) := by fun_prop
    simpa using hc.tendsto 0
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), differenceQuotient f x w τ =
      ((((f (x + τ • w)).toReal - (f x).toReal) / τ : ℝ) : EReal) := by
    have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), x + τ • w ∈ O :=
      nhdsWithin_le_nhds (hcont (hO.mem_nhds hx))
    filter_upwards [h1] with τ hτ
    have e1 := aux_coe_toReal hf hτ
    have e2 := aux_coe_toReal hf hx
    unfold differenceQuotient
    calc (f (x + τ • w) - f x) / (τ : EReal)
        = (((f (x + τ • w)).toReal : EReal) - ((f x).toReal : EReal)) / (τ : EReal) := by
          rw [← e1, ← e2]
      _ = ((((f (x + τ • w)).toReal - (f x).toReal) / τ : ℝ) : EReal) := by
          rw [EReal.coe_div, EReal.coe_sub]
  unfold HasDirectionalDerivativeEReal
  exact (Filter.tendsto_congr' hev).trans EReal.tendsto_coe

lemma aux_h_real {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {x : E} (hx : x ∈ O) (w : E) :
    h x w = ((h x w).toReal : EReal) ∧
    Filter.Tendsto (fun τ : ℝ => ((f (x + τ • w)).toReal - (f x).toReal) / τ) (𝓝[>] 0)
      (𝓝 (h x w).toReal) := by
  obtain ⟨⟨r, hr⟩, hd⟩ := hh x hx w
  have e : h x w = ((h x w).toReal : EReal) := by rw [hr, EReal.toReal_coe]
  refine ⟨e, ?_⟩
  rw [e] at hd
  exact (aux_dirDeriv_real_iff hO hf hx w _).1 hd

lemma aux_usc_real {O : Set E} (hO : IsOpen O) {h : E → E → EReal}
    (hfin : ∀ x ∈ O, ∀ w, IsFiniteEReal (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ y in 𝓝 x, y ∈ O ∧ (h y w).toReal < (h x w).toReal + ε := by
  obtain ⟨r, hr⟩ := hfin x hx w
  have h1 : Filter.limsup (fun y => h y w) (𝓝[O] x) ≤ h x w := husc w x hx
  rw [hO.nhdsWithin_eq hx] at h1
  have hlt : Filter.limsup (fun y => h y w) (𝓝 x) < ((r + ε : ℝ) : EReal) := by
    calc Filter.limsup (fun y => h y w) (𝓝 x) ≤ h x w := h1
      _ = (r : EReal) := hr
      _ < ((r + ε : ℝ) : EReal) := EReal.coe_lt_coe_iff.mpr (by linarith)
  have h2 := Filter.eventually_lt_of_limsup_lt hlt
  filter_upwards [h2, hO.mem_nhds hx] with y hy hyO
  refine ⟨hyO, ?_⟩
  obtain ⟨s, hs⟩ := hfin y hyO w
  rw [hs] at hy ⊢
  rw [hr, EReal.toReal_coe, EReal.toReal_coe]
  exact EReal.coe_lt_coe_iff.mp hy

/-- Mean value inequality along a segment, using upper bounds on `h`. -/
lemma aux_seg_mvi {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (y w : E) (t M : ℝ) (ht : 0 ≤ t)
    (hseg : ∀ s ∈ Set.Icc (0:ℝ) t, y + s • w ∈ O)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) t, (h (y + s • w) w).toReal ≤ M) :
    (f (y + t • w)).toReal - (f y).toReal ≤ M * t := by
  set g : ℝ → ℝ := fun s => (f (y + s • w)).toReal with hg
  have key : ∀ s ∈ Set.Icc (0:ℝ) t, ∀ v : E,
      Filter.Tendsto (fun τ : ℝ => ((f ((y + s • w) + τ • v)).toReal - (f (y + s • w)).toReal) / τ)
        (𝓝[>] 0) (𝓝 (h (y + s • w) v).toReal) :=
    fun s hs v => (aux_h_real hO hf hh (hseg s hs) v).2
  have hcont : ContinuousOn g (Set.Icc 0 t) := by
    intro s hs
    apply ContinuousAt.continuousWithinAt
    apply aux_cont_of_one_sided
    · refine ⟨(h (y + s • w) w).toReal, ?_⟩
      refine (key s hs w).congr (fun τ => ?_)
      simp only [hg, add_smul, add_assoc]
    · refine ⟨(h (y + s • w) (-w)).toReal, ?_⟩
      refine (key s hs (-w)).congr (fun τ => ?_)
      simp only [hg, smul_neg, sub_eq_add_neg, add_smul, neg_smul, add_assoc]
  have hder : ∀ s ∈ Set.Ico (0:ℝ) t, ∃ d, d ≤ M ∧
      Filter.Tendsto (fun τ => (g (s + τ) - g s) / τ) (𝓝[>] 0) (𝓝 d) := by
    intro s hs
    have hs' : s ∈ Set.Icc (0:ℝ) t := Set.Ico_subset_Icc_self hs
    refine ⟨(h (y + s • w) w).toReal, hM s hs', ?_⟩
    refine (key s hs' w).congr (fun τ => ?_)
    simp only [hg, add_smul, add_assoc]
  have := aux_mvi_1d g 0 t M ht hcont hder
  simpa [hg] using this

/-- Helper (gD): two-sided bound along a line segment inside a convex set, nonnegative step. -/
lemma gD_line_nonneg {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {S : Set E} (hS : Convex ℝ S) (hSO : S ⊆ O) (u : E) (M : ℝ)
    (hMu : ∀ q ∈ S, (h q u).toReal ≤ M) (hMu' : ∀ q ∈ S, (h q (-u)).toReal ≤ M)
    (p : E) (t : ℝ) (ht : 0 ≤ t) (hp : p ∈ S) (hpt : p + t • u ∈ S) :
    |(f (p + t • u)).toReal - (f p).toReal| ≤ M * t := by
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) t, p + s • u ∈ S := by
    intro s hs
    rcases eq_or_lt_of_le ht with h0 | hpos
    · subst h0
      have : s = 0 := le_antisymm hs.2 hs.1
      subst this
      simpa using hp
    · have h1 : s / t ∈ Set.Icc (0:ℝ) 1 := ⟨div_nonneg hs.1 ht, (div_le_one hpos).2 hs.2⟩
      have := hS.add_smul_mem hp hpt h1
      rwa [smul_smul, div_mul_cancel₀ _ hpos.ne'] at this
  have hseg' : ∀ s ∈ Set.Icc (0:ℝ) t, (p + t • u) + s • (-u) ∈ S := by
    intro s hs
    have e : (p + t • u) + s • (-u) = p + (t - s) • u := by
      rw [smul_neg, sub_smul]; abel
    rw [e]
    exact hseg (t - s) ⟨sub_nonneg.2 hs.2, by linarith [hs.1]⟩
  have h1 := aux_seg_mvi hO hf hh p u t M ht (fun s hs => hSO (hseg s hs))
    (fun s hs => hMu _ (hseg s hs))
  have h2 := aux_seg_mvi hO hf hh (p + t • u) (-u) t M ht (fun s hs => hSO (hseg' s hs))
    (fun s hs => hMu' _ (hseg' s hs))
  have e : p + t • u + t • (-u) = p := by rw [smul_neg]; abel
  rw [e] at h2
  rw [abs_le]
  constructor <;> linarith

/-- Helper (gD): two-sided bound along a line segment inside a convex set. -/
lemma gD_line {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {S : Set E} (hS : Convex ℝ S) (hSO : S ⊆ O) (u : E) (M : ℝ)
    (hMu : ∀ q ∈ S, (h q u).toReal ≤ M) (hMu' : ∀ q ∈ S, (h q (-u)).toReal ≤ M)
    (p : E) (t : ℝ) (hp : p ∈ S) (hpt : p + t • u ∈ S) :
    |(f (p + t • u)).toReal - (f p).toReal| ≤ M * |t| := by
  rcases le_or_gt 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact gD_line_nonneg hO hf hh hS hSO u M hMu hMu' p t ht hp hpt
  · rw [abs_of_neg ht]
    have e : p + t • u = p + (-t) • (-u) := by rw [neg_smul_neg]
    rw [e] at hpt ⊢
    exact gD_line_nonneg hO hf hh hS hSO (-u) M hMu' (by simpa using hMu) p (-t)
      (by linarith) hp hpt

/-- Local Lipschitz continuity from the right-hand side conditions. -/
lemma aux_lip {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) :
    ∃ ρ > 0, Metric.ball x ρ ⊆ O ∧ ∃ L ≥ 0, ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖ := by
  classical
  set n := Module.finrank ℝ E with hn
  set b := stdOrthonormalBasis ℝ E with hb
  have hfin : ∀ x ∈ O, ∀ w, IsFiniteEReal (h x w) := fun x hx w => (hh x hx w).1
  -- a uniform upper bound for `h x (± b i)`
  obtain ⟨M0, hM0⟩ := Finite.exists_le
    (fun i : Fin n => max ((h x (b i)).toReal + 1) ((h x (-b i)).toReal + 1))
  set M := max M0 0 with hM
  have hMnn : 0 ≤ M := le_max_right _ _
  have hev : ∀ᶠ y in 𝓝 x, y ∈ O ∧
      ∀ i : Fin n, (h y (b i)).toReal ≤ M ∧ (h y (-b i)).toReal ≤ M := by
    have h1 : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
        (y ∈ O ∧ (h y (b i)).toReal < (h x (b i)).toReal + 1) ∧
        (y ∈ O ∧ (h y (-b i)).toReal < (h x (-b i)).toReal + 1) :=
      Filter.eventually_all.2 (fun i => (aux_usc_real hO hfin husc hx (b i) one_pos).and
        (aux_usc_real hO hfin husc hx (-b i) one_pos))
    filter_upwards [h1, hO.mem_nhds hx] with y hy hyO
    refine ⟨hyO, fun i => ⟨?_, ?_⟩⟩
    · have h2 := hM0 i
      have h3 := (hy i).1.2
      have h4 := le_max_left ((h x (b i)).toReal + 1) ((h x (-b i)).toReal + 1)
      have h5 := le_max_left M0 0
      linarith
    · have h2 := hM0 i
      have h3 := (hy i).2.2
      have h4 := le_max_right ((h x (b i)).toReal + 1) ((h x (-b i)).toReal + 1)
      have h5 := le_max_left M0 0
      linarith
  obtain ⟨ρ0, hρ0, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hnn : (0:ℝ) ≤ n := Nat.cast_nonneg n
  have hn0 : (0:ℝ) < 2 * n + 1 := by positivity
  have hsubO : Metric.ball x ρ0 ⊆ O := fun q hq => (hball q hq).1
  have hbd : ∀ q ∈ Metric.ball x ρ0, ∀ i : Fin n,
      (h q (b i)).toReal ≤ M ∧ (h q (-b i)).toReal ≤ M := fun q hq => (hball q hq).2
  set ρ := ρ0 / (2 * n + 1) with hρ
  have hρpos : 0 < ρ := div_pos hρ0 hn0
  have hρ0eq : ρ0 = ρ * (2 * n + 1) := by rw [hρ, div_mul_cancel₀ _ hn0.ne']
  have hρle : ρ ≤ ρ0 := by rw [hρ0eq]; nlinarith
  refine ⟨ρ, hρpos, (Metric.ball_subset_ball hρle).trans hsubO, n * M, by positivity, ?_⟩
  intro y hy z hz
  set c : Fin n → ℝ := fun i => inner ℝ (b i) (z - y) with hc_def
  have hc : ∀ i, |c i| ≤ ‖z - y‖ := by
    intro i
    calc |c i| ≤ ‖b i‖ * ‖z - y‖ := abs_real_inner_le_norm _ _
      _ = ‖z - y‖ := by rw [b.norm_eq_one i, one_mul]
  have hyx : ‖y - x‖ < ρ := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  have hzx : ‖z - x‖ < ρ := by rwa [← dist_eq_norm, ← Metric.mem_ball]
  have hzy : ‖z - y‖ < 2 * ρ := by
    calc ‖z - y‖ = ‖(z - x) - (y - x)‖ := by congr 1; abel
      _ ≤ ‖z - x‖ + ‖y - x‖ := norm_sub_le _ _
      _ < 2 * ρ := by linarith
  set P : Finset (Fin n) → E := fun s => y + ∑ i ∈ s, c i • b i with hP
  have hPmem : ∀ s, P s ∈ Metric.ball x ρ0 := by
    intro s
    rw [Metric.mem_ball, dist_eq_norm]
    calc ‖P s - x‖ = ‖(y - x) + ∑ i ∈ s, c i • b i‖ := by
          show ‖y + ∑ i ∈ s, c i • b i - x‖ = _
          congr 1; abel
      _ ≤ ‖y - x‖ + ‖∑ i ∈ s, c i • b i‖ := norm_add_le _ _
      _ ≤ ‖y - x‖ + ∑ i ∈ s, ‖c i • b i‖ := by gcongr; exact norm_sum_le _ _
      _ ≤ ‖y - x‖ + ∑ i ∈ s, ‖z - y‖ := by
          gcongr with i hi
          rw [norm_smul, b.norm_eq_one i, mul_one, Real.norm_eq_abs]
          exact hc i
      _ = ‖y - x‖ + s.card * ‖z - y‖ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ‖y - x‖ + n * ‖z - y‖ := by
          gcongr
          have := Finset.card_le_univ s
          simp only [Fintype.card_fin] at this
          exact_mod_cast this
      _ < ρ + n * (2 * ρ) := by
          have : n * ‖z - y‖ ≤ n * (2 * ρ) := by gcongr
          linarith
      _ = ρ0 := by rw [hρ0eq]; ring
  have key : ∀ s : Finset (Fin n),
      |(f (P s)).toReal - (f y).toReal| ≤ M * ∑ i ∈ s, |c i| := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [hP]
    | insert a s has ih =>
      have eP : P (insert a s) = P s + c a • b a := by
        rw [hP]
        simp only
        rw [Finset.sum_insert has]; abel
      have hmem := hPmem (insert a s)
      rw [eP] at hmem
      have hline := gD_line hO hf hh (convex_ball x ρ0) hsubO (b a) M
        (fun q hq => (hbd q hq a).1) (fun q hq => (hbd q hq a).2) (P s) (c a) (hPmem s) hmem
      rw [eP, Finset.sum_insert has, mul_add]
      calc |(f (P s + c a • b a)).toReal - (f y).toReal|
          ≤ |(f (P s + c a • b a)).toReal - (f (P s)).toReal|
            + |(f (P s)).toReal - (f y).toReal| := abs_sub_le _ _ _
        _ ≤ M * |c a| + M * ∑ i ∈ s, |c i| := add_le_add hline ih
  have hPuniv : P Finset.univ = z := by
    rw [hP]
    simp only [hc_def]
    rw [b.sum_repr']; abel
  have hsum : ∑ i, |c i| ≤ n * ‖z - y‖ := by
    calc ∑ i, |c i| ≤ ∑ _i : Fin n, ‖z - y‖ := Finset.sum_le_sum (fun i _ => hc i)
      _ = n * ‖z - y‖ := by simp
  have hk := key Finset.univ
  rw [hPuniv] at hk
  rw [abs_sub_comm, norm_sub_rev]
  calc |(f z).toReal - (f y).toReal| ≤ M * ∑ i, |c i| := hk
    _ ≤ M * (n * ‖z - y‖) := mul_le_mul_of_nonneg_left hsum hMnn
    _ = n * M * ‖z - y‖ := by ring

lemma aux_clarke_ev {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x, p.2 ∈ O ∧ p.2 + p.1 • w ∈ O ∧
      ((f (p.2 + p.1 • w)).toReal - (f p.2).toReal) / p.1 ≤ (h x w).toReal + ε := by
  have hfin : ∀ x ∈ O, ∀ w, IsFiniteEReal (h x w) := fun x hx w => (hh x hx w).1
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 (aux_usc_real hO hfin husc hx w hε)
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  set δ := r / (2 * (‖w‖ + 1)) with hδ
  have hδpos : 0 < δ := by positivity
  have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 δ := Ioo_mem_nhdsGT hδpos
  have h2 : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x (r/2) := Metric.ball_mem_nhds x (by positivity)
  filter_upwards [h1.prod_mk h2] with p hp
  obtain ⟨⟨hτ0, hτδ⟩, hy⟩ := hp
  have hδw : δ * ‖w‖ ≤ r / 2 := by
    have : δ * (‖w‖ + 1) = r / 2 := by
      rw [hδ]; field_simp
    nlinarith [norm_nonneg w]
  have hseg : ∀ s ∈ Set.Icc (0:ℝ) p.1, p.2 + s • w ∈ Metric.ball x r := by
    intro s hs
    rw [Metric.mem_ball] at hy ⊢
    have hsw : ‖s • w‖ ≤ r / 2 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
      calc s * ‖w‖ ≤ δ * ‖w‖ := by
            apply mul_le_mul_of_nonneg_right _ (norm_nonneg w)
            linarith [hs.2]
        _ ≤ r / 2 := hδw
    calc dist (p.2 + s • w) x = ‖(p.2 - x) + s • w‖ := by
          rw [dist_eq_norm]; congr 1; abel
      _ ≤ ‖p.2 - x‖ + ‖s • w‖ := norm_add_le _ _
      _ < r / 2 + r / 2 := by
          rw [← dist_eq_norm]
          exact add_lt_add_of_lt_of_le hy hsw
      _ = r := by ring
  refine ⟨(hball _ (by simpa using hseg 0 ⟨le_refl _, hτ0.le⟩)).1,
    (hball _ (hseg p.1 ⟨hτ0.le, le_refl _⟩)).1, ?_⟩
  rw [div_le_iff₀ hτ0]
  exact aux_seg_mvi hO hf hh p.2 w p.1 _ hτ0.le (fun s hs => (hball _ (hseg s hs)).1)
    (fun s hs => (hball _ (hseg s hs)).2.le)

lemma aux_clarke_eq {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    h x w = Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
          (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) := by
  rw [aux_clarke_filter_eq hO hx]
  obtain ⟨hreal, -⟩ := aux_h_real hO hf hh hx w
  apply le_antisymm
  · have hT : Filter.Tendsto (fun τ : ℝ => ((τ, x) : ℝ × E)) (𝓝[>] (0:ℝ))
        ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) :=
      Filter.tendsto_id.prodMk tendsto_const_nhds
    have hd : Filter.Tendsto (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) (𝓝 (h x w)) :=
      (hh x hx w).2
    calc h x w = Filter.limsup (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) :=
          hd.limsup_eq.symm
      _ = Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
            (Filter.map (fun τ : ℝ => ((τ, x) : ℝ × E)) (𝓝[>] (0:ℝ))) := by
          rw [← Filter.limsup_comp]; rfl
      _ ≤ _ := Filter.limsup_le_limsup_of_le hT
  · rw [hreal, ← EReal.le_of_forall_lt_iff_le]
    intro z hz
    have hz' : (h x w).toReal < z := EReal.coe_lt_coe_iff.1 hz
    have hε : 0 < z - (h x w).toReal := by linarith
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [aux_clarke_ev hO hf hh husc hx w hε] with p hp
    obtain ⟨hp2O, hpwO, hq⟩ := hp
    rw [aux_coe_toReal hf hp2O, aux_coe_toReal hf hpwO, ← EReal.coe_sub, ← EReal.coe_div,
      EReal.coe_le_coe_iff]
    linarith

lemma aux_H_lip_w {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {U : Set E} (hU : IsOpen U) (hUO : U ⊆ O) {L : ℝ}
    (hL : ∀ y ∈ U, ∀ z ∈ U, |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖)
    {x : E} (hx : x ∈ U) (w w' : E) :
    |(h x w').toReal - (h x w).toReal| ≤ L * ‖w' - w‖ := by
  have hxO : x ∈ O := hUO hx
  have h1 := (aux_h_real hO hf hh hxO w).2
  have h2 := (aux_h_real hO hf hh hxO w').2
  have hT := (h2.sub h1).abs
  have hcw : ∀ v : E, ∀ᶠ τ in 𝓝[>] (0:ℝ), x + τ • v ∈ U := by
    intro v
    apply nhdsWithin_le_nhds
    have hc : Continuous (fun τ : ℝ => x + τ • v) := by fun_prop
    have : (fun τ : ℝ => x + τ • v) 0 ∈ U := by simpa using hx
    exact hc.continuousAt.preimage_mem_nhds (hU.mem_nhds this)
  apply le_of_tendsto hT
  filter_upwards [hcw w, hcw w', self_mem_nhdsWithin] with τ hw hw' hτ
  have hτ' : (0:ℝ) < τ := hτ
  rw [div_sub_div_same, sub_sub_sub_cancel_right, abs_div, abs_of_pos hτ']
  rw [div_le_iff₀ hτ']
  calc |(f (x + τ • w')).toReal - (f (x + τ • w)).toReal|
        ≤ L * ‖(x + τ • w') - (x + τ • w)‖ := hL _ hw' _ hw
    _ = L * ‖w' - w‖ * τ := by
      rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hτ']
      ring

lemma aux_hadamard_real {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    Filter.Tendsto (fun p : ℝ × E => ((f (x + p.1 • p.2)).toReal - (f x).toReal) / p.1)
      ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (𝓝 (h x w).toReal) := by
  obtain ⟨ρ, hρ, hball, L, hL0, hL⟩ := aux_lip hO hf hh husc hx
  have hlim := (aux_h_real hO hf hh hx w).2
  have hle : (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w ≤ 𝓝 ((0:ℝ), w) := by
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hc : Continuous (fun p : ℝ × E => x + p.1 • p.2) := by fun_prop
  have hev1 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w, x + p.1 • p.2 ∈ Metric.ball x ρ := by
    apply hle
    apply hc.continuousAt.preimage_mem_nhds
    simp only [zero_smul, add_zero]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hc2 : Continuous (fun p : ℝ × E => x + p.1 • w) := by fun_prop
  have hev2 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w, x + p.1 • w ∈ Metric.ball x ρ := by
    apply hle
    apply hc2.continuousAt.preimage_mem_nhds
    simp only [zero_smul, add_zero]
    exact Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ)
  have hev3 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w, (0:ℝ) < p.1 :=
    Filter.mem_of_superset (Filter.prod_mem_prod self_mem_nhdsWithin Filter.univ_mem)
      (fun p hp => hp.1)
  have hA : Filter.Tendsto (fun p : ℝ × E => ((f (x + p.1 • w)).toReal - (f x).toReal) / p.1)
      ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (𝓝 (h x w).toReal) := hlim.comp Filter.tendsto_fst
  have hB : Filter.Tendsto (fun p : ℝ × E =>
      ((f (x + p.1 • p.2)).toReal - (f x).toReal) / p.1 -
        ((f (x + p.1 • w)).toReal - (f x).toReal) / p.1)
      ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (𝓝 0) := by
    have hC : Filter.Tendsto (fun p : ℝ × E => L * ‖p.2 - w‖) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 w) (𝓝 0) := by
      have : Filter.Tendsto (fun v : E => L * ‖v - w‖) (𝓝 w) (𝓝 (L * ‖w - w‖)) := by
        apply Filter.Tendsto.const_mul
        exact (Filter.tendsto_id.sub tendsto_const_nhds).norm
      simp only [sub_self, norm_zero, mul_zero] at this
      exact this.comp Filter.tendsto_snd
    apply squeeze_zero_norm' _ hC
    filter_upwards [hev1, hev2, hev3] with p h1 h2 h3
    rw [div_sub_div_same, sub_sub_sub_cancel_right, Real.norm_eq_abs, abs_div, abs_of_pos h3,
      div_le_iff₀ h3]
    calc |(f (x + p.1 • p.2)).toReal - (f (x + p.1 • w)).toReal|
          ≤ L * ‖(x + p.1 • p.2) - (x + p.1 • w)‖ := hL _ h1 _ h2
      _ = L * ‖p.2 - w‖ * p.1 := by
        rw [add_sub_add_left_eq_sub, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos h3]
        ring
  have := hA.add hB
  rw [add_zero] at this
  exact this.congr (fun p => by ring)

lemma aux_semidiff {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) :
    IsSemidifferentiableOnWith f O h := by
  intro x hx w
  unfold HasHadamardDirectionalDerivativeEReal
  have hT := EReal.tendsto_coe.2 (aux_hadamard_real hO hf hh husc hx w)
  rw [(aux_h_real hO hf hh hx w).1]
  apply hT.congr'
  have hle : (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w ≤ 𝓝 ((0:ℝ), w) := by
    rw [nhds_prod_eq]; exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hc : Continuous (fun p : ℝ × E => x + p.1 • p.2) := by fun_prop
  have hev1 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 w, x + p.1 • p.2 ∈ O := by
    apply hle
    apply hc.continuousAt.preimage_mem_nhds
    simp only [zero_smul, add_zero]
    exact hO.mem_nhds hx
  filter_upwards [hev1] with p hp
  show ((((f (x + p.1 • p.2)).toReal - (f x).toReal) / p.1 : ℝ) : EReal) =
    differenceQuotient f x p.2 p.1
  unfold differenceQuotient
  rw [EReal.coe_div, EReal.coe_sub, ← aux_coe_toReal hf hp, ← aux_coe_toReal hf hx]

lemma aux_subderiv_eq {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    h x w = subderivative f x w := by
  unfold subderivative
  have hT := aux_semidiff hO hf hh husc x hx w
  unfold HasHadamardDirectionalDerivativeEReal at hT
  exact hT.liminf_eq.symm

lemma aux_joint_usc {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) :
    IsUscOnEReal (fun (p : E × E) => h p.1 p.2) {p : E × E | p.1 ∈ O} := by
  rintro ⟨x, w⟩ hp0
  have hx : x ∈ O := hp0
  show Filter.limsup (fun p : E × E => h p.1 p.2) (𝓝[{p : E × E | p.1 ∈ O}] (x, w)) ≤ h x w
  have hfin : ∀ x ∈ O, ∀ w, IsFiniteEReal (h x w) := fun x hx w => (hh x hx w).1
  obtain ⟨ρ, hρ, hball, L, hL0, hL⟩ := aux_lip hO hf hh husc hx
  rw [(aux_h_real hO hf hh hx w).1]
  apply EReal.le_of_forall_lt_iff_le.1
  intro z hz
  have hz' : (h x w).toReal < z := EReal.coe_lt_coe_iff.1 hz
  set ε := (z - (h x w).toReal) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  have hev : ∀ᶠ p in 𝓝 (x, w), h p.1 p.2 ≤ (z : EReal) := by
    have hA : ∀ᶠ p : E × E in 𝓝 (x, w), p.1 ∈ Metric.ball x ρ ∧
        (p.1 ∈ O ∧ (h p.1 w).toReal < (h x w).toReal + ε) := by
      have := Filter.inter_mem (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hρ))
        (aux_usc_real hO hfin husc hx w hε)
      exact (continuous_fst.tendsto (x, w)).eventually this
    have hB : ∀ᶠ p : E × E in 𝓝 (x, w), L * ‖p.2 - w‖ < ε := by
      have hc : Continuous (fun p : E × E => L * ‖p.2 - w‖) := by fun_prop
      have : (fun p : E × E => L * ‖p.2 - w‖) (x, w) < ε := by simp [hε]
      exact hc.continuousAt.eventually_lt continuousAt_const this
    filter_upwards [hA, hB] with p hpA hpB
    obtain ⟨hp1, hp1O, hp1w⟩ := hpA
    have hlipw := aux_H_lip_w hO hf hh Metric.isOpen_ball hball hL hp1 w p.2
    have hle : (h p.1 p.2).toReal ≤ z := by
      have := (abs_le.1 hlipw).2
      linarith
    rw [(aux_h_real hO hf hh hp1O p.2).1]
    exact EReal.coe_le_coe_iff.2 hle
  exact Filter.limsup_le_of_le (by isBoundedDefault)
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev)

lemma aux_H_zero {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {x : E} (hx : x ∈ O) :
    (h x 0).toReal = 0 := by
  have h1 := (aux_h_real hO hf hh hx 0).2
  have h2 : (fun τ : ℝ => ((f (x + τ • (0:E))).toReal - (f x).toReal) / τ) = fun _ => (0:ℝ) := by
    funext τ
    simp only [smul_zero, add_zero, sub_self, zero_div]
  rw [h2] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

lemma aux_H_hom {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {x : E} (hx : x ∈ O) (c : ℝ) (hc : 0 < c) (w : E) :
    (h x (c • w)).toReal = c * (h x w).toReal := by
  have h1 := (aux_h_real hO hf hh hx w).2
  have h2 := (aux_h_real hO hf hh hx (c • w)).2
  have hmap : Filter.Tendsto (fun τ : ℝ => c * τ) (𝓝[>] 0) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have hc0 : Filter.Tendsto (fun τ : ℝ => c * τ) (𝓝 0) (𝓝 (c * 0)) :=
        (continuous_const.mul continuous_id).tendsto 0
      rw [mul_zero] at hc0
      exact hc0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact mul_pos hc hτ
  have h3 : Filter.Tendsto
      (fun τ : ℝ => c * (((f (x + (c * τ) • w)).toReal - (f x).toReal) / (c * τ)))
      (𝓝[>] 0) (𝓝 (c * (h x w).toReal)) :=
    (h1.comp hmap).const_mul c
  have h4 : ∀ᶠ τ in 𝓝[>] (0:ℝ),
      c * (((f (x + (c * τ) • w)).toReal - (f x).toReal) / (c * τ)) =
        ((f (x + τ • (c • w))).toReal - (f x).toReal) / τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτ' : τ ≠ 0 := ne_of_gt hτ
    have hc' : c ≠ 0 := ne_of_gt hc
    rw [smul_smul, mul_comm τ c]
    field_simp
  exact tendsto_nhds_unique h2 (h3.congr' h4)

lemma aux_H_add {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w1 w2 : E) :
    (h x (w1 + w2)).toReal ≤ (h x w1).toReal + (h x w2).toReal := by
  have h12 := (aux_h_real hO hf hh hx (w1 + w2)).2
  have h2 := (aux_h_real hO hf hh hx w2).2
  have hpath : Filter.Tendsto (fun τ : ℝ => (τ, x + τ • w2)) (𝓝[>] (0:ℝ))
      ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 x) := by
    refine Filter.tendsto_id.prodMk ?_
    have hc : Continuous (fun τ : ℝ => x + τ • w2) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have h0 := hc.tendsto 0
    simp only [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  refine _root_.le_of_forall_pos_le_add fun ε hε => ?_
  have hev := hpath.eventually (aux_clarke_ev hO hf hh husc hx w1 hε)
  have hle : ∀ᶠ τ in 𝓝[>] (0:ℝ), ((f (x + τ • (w1 + w2))).toReal - (f x).toReal) / τ ≤
      ((h x w1).toReal + ε) + ((f (x + τ • w2)).toReal - (f x).toReal) / τ := by
    filter_upwards [hev] with τ hτ
    obtain ⟨-, -, hq⟩ := hτ
    have e : x + τ • (w1 + w2) = x + τ • w2 + τ • w1 := by
      rw [smul_add]; abel
    rw [e]
    calc ((f (x + τ • w2 + τ • w1)).toReal - (f x).toReal) / τ
        = ((f (x + τ • w2 + τ • w1)).toReal - (f (x + τ • w2)).toReal) / τ
          + ((f (x + τ • w2)).toReal - (f x).toReal) / τ := by
          rw [← add_div]; ring_nf
      _ ≤ _ := add_le_add hq le_rfl
  have hlim := le_of_tendsto_of_tendsto h12 (tendsto_const_nhds.add h2) hle
  linarith

/-- Hahn–Banach: a linear minorant of `h x ·` that is exact at `w`. -/
lemma aux_HB {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    ∃ v : E, (∀ w', inner ℝ v w' ≤ (h x w').toReal) ∧ inner ℝ v w = (h x w).toReal := by
  set N : E → ℝ := fun w => (h x w).toReal with hN
  have N_hom : ∀ c : ℝ, 0 < c → ∀ y, N (c • y) = c * N y :=
    fun c hc y => aux_H_hom hO hf hh hx c hc y
  have N_add : ∀ y z, N (y + z) ≤ N y + N z := fun y z => aux_H_add hO hf hh husc hx y z
  have N_zero : N 0 = 0 := aux_H_zero hO hf hh hx
  have N_neg : ∀ y, 0 ≤ N y + N (-y) := by
    intro y
    have := N_add y (-y)
    rw [add_neg_cancel, N_zero] at this
    exact this
  have H : ∀ c : ℝ, c • w = 0 → c • N w = 0 := by
    intro c hc
    rcases smul_eq_zero.1 hc with h0 | h0
    · rw [h0, zero_smul]
    · rw [h0, N_zero, smul_zero]
  have hφle : ∀ y : (LinearPMap.mkSpanSingleton' w (N w) H).domain,
      (LinearPMap.mkSpanSingleton' w (N w) H) y ≤ N y := by
    rintro ⟨y, hy⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
    rw [LinearPMap.mkSpanSingleton'_apply, smul_eq_mul]
    change c * N w ≤ N (c • w)
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have e : c • w = (-c) • (-w) := (neg_smul_neg c w).symm
      rw [e, N_hom (-c) (neg_pos.2 hc) (-w)]
      nlinarith [N_neg w]
    · subst hc
      rw [zero_smul, N_zero, zero_mul]
    · rw [N_hom c hc w]
  obtain ⟨g, hg1, hg2⟩ := exists_extension_of_le_sublinear _ N N_hom N_add hφle
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g), ?_, ?_⟩
  · intro w'
    rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
    exact hg2 w'
  · rw [InnerProductSpace.toDual_symm_apply, LinearMap.coe_toContinuousLinearMap']
    have hw : w ∈ (LinearPMap.mkSpanSingleton' w (N w) H).domain :=
      Submodule.mem_span_singleton_self w
    have := hg1 ⟨w, hw⟩
    rw [LinearPMap.mkSpanSingleton'_apply_self] at this
    exact this

lemma aux_reg_le {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    {y : E} (hy : y ∈ O) {v : E} (hv : IsRegularSubgradientAt f y v) (w : E) :
    inner ℝ v w ≤ (h y w).toReal := by
  obtain ⟨-, -, r, hr, V, hV, hineq⟩ := hv
  have hlim := (aux_h_real hO hf hh hy w).2
  have hg : Filter.Tendsto (fun τ : ℝ => y + τ • w) (𝓝[>] 0) (𝓝 y) := by
    have : Filter.Tendsto (fun τ : ℝ => y + τ • w) (𝓝 0) (𝓝 (y + (0:ℝ) • w)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ τ in 𝓝[>] (0:ℝ), y + τ • w ∈ V ∧ y + τ • w ∈ O ∧ 0 < τ := by
    have h1 := hg.eventually (Filter.inter_mem hV (hO.mem_nhds hy))
    have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := self_mem_nhdsWithin
    filter_upwards [h1, h2] with τ h1 h2
    exact ⟨h1.1, h1.2, h2⟩
  have hro : (fun τ : ℝ => r (y + τ • w)) =o[𝓝[>] 0] (fun τ : ℝ => τ) := by
    have h1 := hr.comp_tendsto hg
    refine h1.trans_isBigO ?_
    refine Asymptotics.IsBigO.of_bound ‖w‖ (Filter.Eventually.of_forall fun τ => ?_)
    rw [Function.comp_apply, add_sub_cancel_left, norm_norm, norm_smul, mul_comm]
  have hr0 : Filter.Tendsto (fun τ : ℝ => r (y + τ • w) / τ) (𝓝[>] 0) (𝓝 0) :=
    hro.tendsto_div_nhds_zero
  have hlow : Filter.Tendsto (fun τ : ℝ => inner ℝ v w + r (y + τ • w) / τ) (𝓝[>] 0)
      (𝓝 (inner ℝ v w + 0)) := tendsto_const_nhds.add hr0
  rw [add_zero] at hlow
  refine le_of_tendsto_of_tendsto hlow hlim ?_
  filter_upwards [hev] with τ ⟨hV', hO', hτ⟩
  have h1 := hineq _ hV'
  obtain ⟨a, ha⟩ := hf y hy
  obtain ⟨b, hb⟩ := hf _ hO'
  rw [ha, hb, ← EReal.coe_add, EReal.coe_le_coe_iff, add_sub_cancel_left,
    inner_smul_right] at h1
  rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe, le_div_iff₀ hτ, add_mul,
    div_mul_cancel₀ _ hτ.ne']
  linarith

lemma gG_key {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) {v : E}
    (hv : ∀ w, inner ℝ v w ≤ (h x w).toReal) {c : ℝ} (hc : 0 < c) :
    ∀ᶠ z in 𝓝 x, -(c * ‖z - x‖) ≤ (f z).toReal - (f x).toReal - inner ℝ v (z - x) := by
  have hloc : ∀ u ∈ Metric.sphere (0:E) 1, ∀ᶠ p : ℝ × E in 𝓝 ((0:ℝ), u),
      0 < p.1 → -c < ((f (x + p.1 • p.2)).toReal - (f x).toReal) / p.1 - inner ℝ v p.2 := by
    intro u _
    have h1 := aux_hadamard_real hO hf hh husc hx u
    have h2 : Filter.Tendsto (fun p : ℝ × E => inner ℝ v p.2) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 u)
        (𝓝 (inner ℝ v u)) := tendsto_const_nhds.inner Filter.tendsto_snd
    have h3 := h1.sub h2
    have h4 := h3.eventually (lt_mem_nhds (show -c < (h x u).toReal - inner ℝ v u by
      linarith [hv u]))
    obtain ⟨pa, hpa, pb, hpb, himp⟩ := Filter.eventually_prod_iff.mp h4
    rw [nhds_prod_eq]
    refine Filter.eventually_prod_iff.mpr ⟨fun τ => 0 < τ → pa τ, ?_, pb, hpb, ?_⟩
    · exact eventually_nhdsWithin_iff.mp hpa
    · intro τ hτ y hy hpos
      exact himp (hτ hpos) hy
  have hK : ∀ᶠ τ in 𝓝 (0:ℝ), ∀ u ∈ Metric.sphere (0:E) 1,
      0 < τ → -c < ((f (x + τ • u)).toReal - (f x).toReal) / τ - inner ℝ v u :=
    (isCompact_sphere (0:E) 1).eventually_forall_of_forall_eventually hloc
  have hn : Filter.Tendsto (fun z : E => ‖z - x‖) (𝓝 x) (𝓝 0) := tendsto_norm_sub_self x
  filter_upwards [hn.eventually hK] with z hz
  by_cases hzx : z = x
  · rw [hzx]; simp
  · have hpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
    have hu : ‖z - x‖⁻¹ • (z - x) ∈ Metric.sphere (0:E) 1 := by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hpos.ne']
    have h1 := hz _ hu hpos
    have e1 : x + ‖z - x‖ • (‖z - x‖⁻¹ • (z - x)) = z := by
      rw [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul, add_sub_cancel]
    rw [e1, inner_smul_right] at h1
    have key : ((f z).toReal - (f x).toReal) / ‖z - x‖ - ‖z - x‖⁻¹ * inner ℝ v (z - x) =
        ((f z).toReal - (f x).toReal - inner ℝ v (z - x)) / ‖z - x‖ := by
      field_simp
    rw [key, lt_div_iff₀ hpos] at h1
    linarith

lemma aux_reg_of_le {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) {v : E}
    (hv : ∀ w, inner ℝ v w ≤ (h x w).toReal) :
    IsRegularSubgradientAt f x v := by
  obtain ⟨a, ha⟩ := hf x hx
  refine ⟨by rw [ha]; exact EReal.bot_lt_coe _, by rw [ha]; exact EReal.coe_lt_top _,
    fun z => min 0 ((f z).toReal - (f x).toReal - inner ℝ v (z - x)), ?_, O, hO.mem_nhds hx, ?_⟩
  · apply Asymptotics.IsLittleO.of_bound
    intro c hc
    filter_upwards [gG_key hO hf hh husc hx hv hc] with z hz
    rw [Real.norm_eq_abs, norm_norm]
    refine abs_le.mpr ⟨?_, ?_⟩
    · exact le_min (by nlinarith [norm_nonneg (z - x)]) hz
    · exact (min_le_left _ _).trans (by positivity)
  · intro z hz
    dsimp only
    obtain ⟨b, hb⟩ := hf z hz
    have := min_le_right (0:ℝ) ((f z).toReal - (f x).toReal - inner ℝ v (z - x))
    rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe] at this ⊢
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    linarith

lemma aux_char {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (v : E) :
    v ∈ subdifferential f x ↔ ∀ w, inner ℝ v w ≤ (h x w).toReal := by
  constructor
  · intro hv w
    obtain ⟨-, -, xs, vs, hxs, -, hvs, hreg⟩ := hv
    have hfin : ∀ y ∈ O, ∀ w, IsFiniteEReal (h y w) := fun y hy w => (hh y hy w).1
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hev := hxs.eventually (aux_usc_real hO hfin husc hx w hε)
    have hin : Filter.Tendsto (fun n => inner ℝ (vs n) w) Filter.atTop (𝓝 (inner ℝ v w)) :=
      hvs.inner tendsto_const_nhds
    refine le_of_tendsto hin ?_
    filter_upwards [hev] with n ⟨hn1, hn2⟩
    exact (aux_reg_le hO hf hh hn1 (hreg n) w).trans hn2.le
  · intro hv
    have hreg := aux_reg_of_le hO hf hh husc hx hv
    exact ⟨hreg.1, hreg.2.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
      tendsto_const_nhds, fun _ => hreg⟩

lemma aux_support {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    h x w = supportFunction (subdifferential f x) w := by
  have e : h x w = ((h x w).toReal : EReal) := (aux_h_real hO hf hh hx w).1
  unfold supportFunction
  apply le_antisymm
  · obtain ⟨v, hv1, hv2⟩ := aux_HB hO hf hh husc hx w
    have hvmem : v ∈ subdifferential f x := (aux_char hO hf hh husc hx v).2 hv1
    rw [e, ← hv2]
    exact le_sSup (Set.mem_image_of_mem _ hvmem)
  · apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    rw [e]
    exact EReal.coe_le_coe_iff.2 ((aux_char hO hf hh husc hx v).1 hv w)

lemma aux_nonempty_convex {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) :
    (subdifferential f x).Nonempty ∧ Convex ℝ (subdifferential f x) := by
  constructor
  · obtain ⟨v, hv1, -⟩ := aux_HB hO hf hh husc hx 0
    exact ⟨v, (aux_char hO hf hh husc hx v).2 hv1⟩
  · intro v1 hv1 v2 hv2 a b ha hb hab
    rw [aux_char hO hf hh husc hx] at hv1 hv2 ⊢
    intro w
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    calc a * inner ℝ v1 w + b * inner ℝ v2 w
        ≤ a * (h x w).toReal + b * (h x w).toReal :=
          add_le_add (mul_le_mul_of_nonneg_left (hv1 w) ha) (mul_le_mul_of_nonneg_left (hv2 w) hb)
      _ = (h x w).toReal := by rw [← add_mul, hab, one_mul]

lemma aux_osc {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) :
    IsOuterSemicontinuousOn (fun x => subdifferential f x) O := by
  intro x hx xseq vseq v hxO hxt hvs hvt
  have hfin : ∀ y ∈ O, ∀ w, IsFiniteEReal (h y w) := fun y hy w => (hh y hy w).1
  show v ∈ subdifferential f x
  rw [aux_char hO hf hh husc hx]
  intro w
  apply _root_.le_of_forall_pos_le_add
  intro ε hε
  have hev : ∀ᶠ y in 𝓝 x, y ∈ O ∧ (h y w).toReal < (h x w).toReal + ε :=
    aux_usc_real hO hfin husc hx w hε
  have hev' : ∀ᶠ n in Filter.atTop, (h (xseq n) w).toReal < (h x w).toReal + ε :=
    (hxt.eventually hev).mono (fun n hn => hn.2)
  have hin : Filter.Tendsto (fun n => inner ℝ (vseq n) w) Filter.atTop (𝓝 (inner ℝ v w)) :=
    hvt.inner tendsto_const_nhds
  refine le_of_tendsto hin (hev'.mono fun n hn => ?_)
  exact ((aux_char hO hf hh husc (hxO n) (vseq n)).1 (hvs n) w).trans hn.le

lemma aux_locbdd {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) :
    IsLocallyBoundedAt (fun y => subdifferential f y) x := by
  obtain ⟨ρ, hρ, hball, L, hL0, hL⟩ := aux_lip hO hf hh husc hx
  refine ⟨Metric.ball x ρ, Metric.ball_mem_nhds x hρ, L + 1, by linarith, ?_⟩
  intro y hy v hv
  have hyO : y ∈ O := hball hy
  have h1 : inner ℝ v v ≤ (h y v).toReal := (aux_char hO hf hh husc hyO v).1 hv v
  have h2 : |(h y v).toReal - (h y 0).toReal| ≤ L * ‖v - 0‖ :=
    aux_H_lip_w hO hf hh Metric.isOpen_ball hball hL hy 0 v
  have h3 : (h y 0).toReal = 0 := aux_H_zero hO hf hh hyO
  rw [h3, sub_zero, sub_zero] at h2
  have h4 : ‖v‖ ^ 2 ≤ L * ‖v‖ := by
    rw [← real_inner_self_eq_norm_sq]
    exact h1.trans ((le_abs_self _).trans h2)
  have h5 : ‖v‖ ≤ L := by
    rcases eq_or_lt_of_le (norm_nonneg v) with h0 | hpos
    · rw [← h0]; exact hL0
    · nlinarith
  linarith

/-! ### Clarke derivative facts (no `h` needed) -/

lemma aux_clarke_usc {f : E → EReal} {O : Set E} (hO : IsOpen O) (w : E) :
    IsUscOnEReal (fun x => Filter.limsup
      (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
      (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O})) O := by
  intro x hx
  apply le_of_forall_gt_imp_ge_of_dense
  intro b hb
  dsimp only at hb
  rw [aux_clarke_filter_eq hO hx] at hb
  have hev := Filter.eventually_lt_of_limsup_lt hb
  rcases Filter.eventually_prod_iff.1 hev with ⟨pa, hpa, pb, hpb, hpq⟩
  refine Filter.limsup_le_of_le (h := ?_)
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hpb.eventually_nhds] with y hy hyO
  rw [aux_clarke_filter_eq hO hyO]
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [hpa.prod_mk hy] with p hp
  exact (hpq hp.1 hp.2).le

lemma aux_clarke_finite_of_lip {f : E → EReal} {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {ρ L : ℝ} (hρ : 0 < ρ)
    (hfin : ∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal))
    (hlip : ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖)
    (w : E) :
    IsFiniteEReal (Filter.limsup
      (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
      (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O})) := by
  rw [aux_clarke_filter_eq hO hx]
  have hcont : Filter.Tendsto (fun p : ℝ × E => p.2 + p.1 • w) ((𝓝[>] (0:ℝ)) ×ˢ 𝓝 x) (𝓝 x) := by
    have h1 : Filter.Tendsto (fun p : ℝ × E => p.2 + p.1 • w) (𝓝 ((0:ℝ), x))
        (𝓝 (((0:ℝ), x).2 + ((0:ℝ), x).1 • w)) :=
      (continuous_snd.add (continuous_fst.smul continuous_const)).tendsto _
    simp only [zero_smul, add_zero] at h1
    refine h1.mono_left ?_
    rw [nhds_prod_eq]
    exact Filter.prod_mono nhdsWithin_le_nhds le_rfl
  have hball : Metric.ball x ρ ∈ 𝓝 x := Metric.ball_mem_nhds x hρ
  have hev : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x,
      (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal) =
        ((((f (p.2 + p.1 • w)).toReal - (f p.2).toReal) / p.1 : ℝ) : EReal) ∧
      |((f (p.2 + p.1 • w)).toReal - (f p.2).toReal) / p.1| ≤ L * ‖w‖ := by
    have e1 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x, p.2 ∈ Metric.ball x ρ :=
      Filter.Eventually.prod_inr hball _
    have e2 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x, p.2 + p.1 • w ∈ Metric.ball x ρ := hcont hball
    have e3 : ∀ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x, 0 < p.1 :=
      Filter.Eventually.prod_inl self_mem_nhdsWithin _
    filter_upwards [e1, e2, e3] with p hp1 hp2 hp3
    constructor
    · rw [EReal.coe_div, EReal.coe_sub, ← hfin _ hp1, ← hfin _ hp2]
    · have h := hlip _ hp2 _ hp1
      rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hp3] at h
      rw [abs_div, abs_of_pos hp3, div_le_iff₀ hp3]
      calc |(f (p.2 + p.1 • w)).toReal - (f p.2).toReal| ≤ L * (p.1 * ‖w‖) := h
        _ = L * ‖w‖ * p.1 := by ring
  have hup : Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
      ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ≤ ((L * ‖w‖ : ℝ) : EReal) := by
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [hev] with p hp
    rw [hp.1, EReal.coe_le_coe_iff]
    exact (abs_le.1 hp.2).2
  have hlo : (((-(L * ‖w‖)) : ℝ) : EReal) ≤
      Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) := by
    refine Filter.le_limsup_of_frequently_le ?_
    refine Filter.Eventually.frequently ?_
    filter_upwards [hev] with p hp
    rw [hp.1, EReal.coe_le_coe_iff]
    exact (abs_le.1 hp.2).1
  refine ⟨(Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x)).toReal, ?_⟩
  rw [EReal.coe_toReal]
  · exact ne_top_of_le_ne_top (EReal.coe_ne_top _) hup
  · exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlo

lemma aux_subderiv_le_lowerDini (f : E → EReal) (x w : E) :
    subderivative f x w ≤
      Filter.liminf (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) := by
  have hT : Filter.Tendsto (fun τ : ℝ => (τ, w)) (𝓝[>] (0:ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) :=
    Filter.tendsto_id.prodMk tendsto_const_nhds
  exact Filter.liminf_le_liminf_of_le hT

lemma aux_upperDini_le_clarke {f : E → EReal} {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (w : E) :
    Filter.limsup (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) ≤
      Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) := by
  rw [aux_clarke_filter_eq hO hx]
  have hT : Filter.Tendsto (fun τ : ℝ => (τ, x)) (𝓝[>] (0:ℝ)) (𝓝[>] (0 : ℝ) ×ˢ 𝓝 x) :=
    Filter.tendsto_id.prodMk tendsto_const_nhds
  exact Filter.limsup_le_limsup_of_le hT
    (u := fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))

lemma aux_clarke_le_regSubderiv {f : E → EReal} {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    {ρ L : ℝ} (hρ : 0 < ρ)
    (hfin : ∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal))
    (hlip : ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖)
    (w : E) :
    Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) ≤
      regularSubderivative f x w := by
  rw [aux_clarke_filter_eq hO hx]
  have hK0 : 0 ≤ |L| := abs_nonneg L
  have hlip' : ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ |L| * ‖y - z‖ := by
    intro y hy z hz
    exact (hlip y hy z hz).trans (mul_le_mul_of_nonneg_right (le_abs_self L) (norm_nonneg _))
  -- continuity of `f` at `x`
  have hcont : ContinuousAt f x := by
    have hFc : ContinuousAt (fun y => (f y).toReal) x := by
      rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero' (g := fun y => |L| * ‖y - x‖)
        (Filter.Eventually.of_forall fun y => norm_nonneg _) ?_ ?_
      · filter_upwards [Metric.ball_mem_nhds x hρ] with y hy
        rw [Real.norm_eq_abs]
        exact hlip' y hy x (Metric.mem_ball_self hρ)
      · have : Filter.Tendsto (fun y => |L| * ‖y - x‖) (𝓝 x) (𝓝 (|L| * ‖x - x‖)) :=
          ((continuous_const.mul (continuous_id.sub continuous_const).norm)).continuousAt
        simpa using this
    have heq : (fun y => (((f y).toReal : ℝ) : EReal)) =ᶠ[𝓝 x] f := by
      filter_upwards [Metric.ball_mem_nhds x hρ] with y hy
      exact (hfin y hy).symm
    exact ((continuous_coe_real_ereal.continuousAt).comp hFc).congr heq
  have hfa : fApproach f x = 𝓝 x := aux_fApproach_eq hcont
  unfold regularSubderivative
  rw [hfa]
  set Q : ℝ × E → EReal := fun p => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal) with hQ
  rw [← EReal.ge_of_forall_gt_iff_ge]
  intro b hb
  obtain ⟨c, hbc, hcC⟩ := EReal.exists_between_coe_real hb
  have hbc' : b < c := EReal.coe_lt_coe_iff.mp hbc
  have hfreq : ∃ᶠ p in (𝓝[>] (0:ℝ)) ×ˢ 𝓝 x, (c : EReal) < Q p :=
    Filter.frequently_lt_of_lt_limsup (h := hcC)
  have hfreq' : ∃ᶠ p in (𝓝 x) ×ˢ (𝓝[>] (0:ℝ)), (c : EReal) < Q p.swap := by
    rw [Filter.prod_comm] at hfreq
    exact Filter.frequently_map.mp hfreq
  have hev : ∀ᶠ p in (𝓝 x) ×ˢ (𝓝[>] (0:ℝ)),
      p.1 ∈ Metric.ball x (ρ / 2) ∧ (0 < p.2 ∧ p.2 * (‖w‖ + 1) < ρ / 2) := by
    have h0 : ∀ᶠ y in 𝓝 x, y ∈ Metric.ball x (ρ / 2) := Metric.ball_mem_nhds x (half_pos hρ)
    have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ := self_mem_nhdsWithin
    have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ < ρ / 2 / (‖w‖ + 1) :=
      nhdsWithin_le_nhds (eventually_lt_nhds (div_pos (half_pos hρ) (by positivity)))
    have h3 : ∀ᶠ τ in 𝓝[>] (0:ℝ), 0 < τ ∧ τ * (‖w‖ + 1) < ρ / 2 := by
      filter_upwards [h1, h2] with τ hτ1 hτ2
      refine ⟨hτ1, ?_⟩
      rwa [lt_div_iff₀ (by positivity)] at hτ2
    exact h0.prod_mk h3
  have hδev : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ ∧ δ ≤ 1 ∧ b + |L| * δ < c := by
    have h1 : ∀ᶠ δ in 𝓝[>] (0:ℝ), 0 < δ := self_mem_nhdsWithin
    have h2 : ∀ᶠ δ in 𝓝[>] (0:ℝ), δ < 1 := nhdsWithin_le_nhds (eventually_lt_nhds one_pos)
    have h3 : ∀ᶠ δ in 𝓝[>] (0:ℝ), b + |L| * δ < c := by
      apply nhdsWithin_le_nhds
      have : Filter.Tendsto (fun δ : ℝ => b + |L| * δ) (𝓝 0) (𝓝 (b + |L| * 0)) :=
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt
      rw [mul_zero, add_zero] at this
      exact this.eventually (eventually_lt_nhds hbc')
    filter_upwards [h1, h2, h3] with δ hδ1 hδ2 hδ3
    exact ⟨hδ1, hδ2.le, hδ3⟩
  refine Filter.le_limsup_of_frequently_le ?_
  refine Filter.Eventually.frequently ?_
  filter_upwards [hδev] with δ hδ
  obtain ⟨hδ0, hδ1, hδc⟩ := hδ
  refine Filter.le_limsup_of_frequently_le ?_
  refine (hfreq'.and_eventually hev).mono ?_
  rintro ⟨y, τ⟩ ⟨hQc, hy, hτ0, hτw⟩
  have hQc' : (c : EReal) < Q (τ, y) := hQc
  simp only at hy hτ0 hτw
  have hyρ : y ∈ Metric.ball x ρ := Metric.ball_subset_ball (by linarith) hy
  have hmem : ∀ w' ∈ Metric.closedBall w δ, y + τ • w' ∈ Metric.ball x ρ := by
    intro w' hw'
    rw [Metric.mem_ball, dist_eq_norm]
    rw [Metric.mem_closedBall, dist_eq_norm] at hw'
    rw [Metric.mem_ball, dist_eq_norm] at hy
    have hw'n : ‖w'‖ ≤ ‖w‖ + 1 := by
      calc ‖w'‖ = ‖(w' - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖w' - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + 1 := by linarith
    calc ‖y + τ • w' - x‖ = ‖(y - x) + τ • w'‖ := by congr 1; abel
      _ ≤ ‖y - x‖ + ‖τ • w'‖ := norm_add_le _ _
      _ = ‖y - x‖ + τ * ‖w'‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
      _ < ρ / 2 + τ * (‖w‖ + 1) := by
          have : τ * ‖w'‖ ≤ τ * (‖w‖ + 1) := mul_le_mul_of_nonneg_left hw'n hτ0.le
          linarith
      _ < ρ := by linarith
  have hval : ∀ w' ∈ Metric.closedBall w δ, delta f y τ w' =
      ((((f (y + τ • w')).toReal - (f y).toReal) / τ : ℝ) : EReal) := by
    intro w' hw'
    simp only [delta, differenceQuotient]
    rw [hfin _ (hmem w' hw'), hfin y hyρ, ← EReal.coe_sub, ← EReal.coe_div]
    simp only [EReal.toReal_coe]
  have hwmem : w ∈ Metric.closedBall w δ := Metric.mem_closedBall_self hδ0.le
  have hQval : Q (τ, y) = ((((f (y + τ • w)).toReal - (f y).toReal) / τ : ℝ) : EReal) :=
    hval w hwmem
  rw [hQval] at hQc'
  have hcq : c < ((f (y + τ • w)).toReal - (f y).toReal) / τ := EReal.coe_lt_coe_iff.mp hQc'
  apply le_sInf
  rintro _ ⟨w', hw', rfl⟩
  rw [hval w' hw', EReal.coe_le_coe_iff]
  have hl := hlip' (y + τ • w) (hmem w hwmem) (y + τ • w') (hmem w' hw')
  have hnorm : ‖(y + τ • w) - (y + τ • w')‖ ≤ τ * δ := by
    rw [show (y + τ • w) - (y + τ • w') = τ • (w - w') by rw [smul_sub]; abel]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hτ0]
    apply mul_le_mul_of_nonneg_left _ hτ0.le
    rw [← dist_eq_norm, _root_.dist_comm]
    exact hw'
  have h1 : (f (y + τ • w)).toReal - (f (y + τ • w')).toReal ≤ |L| * (τ * δ) :=
    (le_abs_self _).trans (hl.trans (mul_le_mul_of_nonneg_left hnorm hK0))
  rw [le_div_iff₀ hτ0]
  rw [lt_div_iff₀ hτ0] at hcq
  nlinarith

lemma aux_regSubderiv_le_clarke {f : E → EReal} {O : Set E} (hO : IsOpen O) {x : E} (hx : x ∈ O)
    (w : E) :
    regularSubderivative f x w ≤
      Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) := by
  rw [aux_clarke_filter_eq hO hx]
  set Q : ℝ × E → EReal := fun p => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal) with hQ
  have key : ∀ δ : ℝ, 0 < δ →
      Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x) ×ˢ (𝓝[>] (0 : ℝ))) ≤ Filter.limsup Q ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) := by
    intro δ hδ
    have h1 : ∀ p : E × ℝ,
        sInf ((delta f p.1 p.2) '' Metric.closedBall w δ) ≤ (Q ∘ Prod.swap) p := by
      intro p
      apply sInf_le
      exact ⟨w, Metric.mem_closedBall_self hδ.le, rfl⟩
    calc Filter.limsup (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
          ((fApproach f x) ×ˢ (𝓝[>] (0 : ℝ)))
        ≤ Filter.limsup (Q ∘ Prod.swap) ((fApproach f x) ×ˢ (𝓝[>] (0 : ℝ))) :=
          Filter.limsup_le_limsup (Filter.Eventually.of_forall h1)
      _ ≤ Filter.limsup (Q ∘ Prod.swap) ((𝓝 x) ×ˢ (𝓝[>] (0 : ℝ))) :=
          Filter.limsup_le_limsup_of_le (Filter.prod_mono inf_le_left le_rfl)
      _ = Filter.limsup Q ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) := by
          rw [Filter.limsup_comp, ← Filter.prod_comm]
  unfold regularSubderivative
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact key δ hδ

lemma aux_regSubderiv {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) (w : E) :
    h x w = regularSubderivative f x w := by
  rw [aux_clarke_eq hO hf hh husc hx w]
  obtain ⟨ρ, hρ, hball, L, _, hlip⟩ := aux_lip hO hf hh husc hx
  have hfin : ∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal) :=
    fun y hy => aux_coe_toReal hf (hball hy)
  exact le_antisymm (aux_clarke_le_regSubderiv hO hx hρ hfin hlip w)
    (aux_regSubderiv_le_clarke hO hx w)

lemma aux_lip_of_locLip {f : E → EReal} {x : E} (H : IsLocallyLipschitzNearEReal f x) :
    ∃ ρ > 0, ∃ L ≥ 0, (∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal)) ∧
      (∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
        |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖) := by
  obtain ⟨ρ, hρ, β, hβ0, hfin, hlip⟩ := H
  refine ⟨ρ, hρ, β, hβ0, fun y hy => (EReal.coe_toReal (hfin y hy).1 (hfin y hy).2).symm, ?_⟩
  intro y hy z hz
  have := hlip y z hy hz
  rwa [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm] at this

lemma aux_localLsc {f : E → EReal} {x : E} {ρ L : ℝ} (hρ : 0 < ρ)
    (hfin : ∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal))
    (hlip : ∀ y ∈ Metric.ball x ρ, ∀ z ∈ Metric.ball x ρ,
      |(f y).toReal - (f z).toReal| ≤ L * ‖y - z‖) :
    LocalLscAt f x := by
  have hx : x ∈ Metric.ball x ρ := Metric.mem_ball_self hρ
  have hsub : Metric.closedBall x (ρ / 2) ⊆ Metric.ball x ρ :=
    Metric.closedBall_subset_ball (by linarith)
  have hlipon : LipschitzOnWith (Real.toNNReal L) (fun y => (f y).toReal) (Metric.ball x ρ) := by
    apply LipschitzOnWith.of_dist_le'
    intro y hy z hz
    rw [Real.dist_eq, dist_eq_norm]
    exact hlip y hy z hz
  have hcont : ContinuousOn (fun y => (f y).toReal) (Metric.closedBall x (ρ / 2)) :=
    hlipon.continuousOn.mono hsub
  refine ⟨?_, ?_, ρ / 2, fun α _ => ⟨by positivity, ?_⟩⟩
  · rw [hfin x hx]; exact EReal.bot_lt_coe _
  · rw [hfin x hx]; exact EReal.coe_lt_top _
  · have : {y | y ∈ Metric.closedBall x (ρ / 2) ∧ f y ≤ (α : EReal)} =
        Metric.closedBall x (ρ / 2) ∩ (fun y => (f y).toReal) ⁻¹' Set.Iic α := by
      ext y
      simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage, Set.mem_Iic]
      constructor
      · rintro ⟨hy, hle⟩
        refine ⟨hy, ?_⟩
        rw [hfin y (hsub hy)] at hle
        exact EReal.coe_le_coe_iff.mp hle
      · rintro ⟨hy, hle⟩
        refine ⟨hy, ?_⟩
        rw [hfin y (hsub hy)]
        exact EReal.coe_le_coe_iff.mpr hle
    rw [this]
    exact hcont.preimage_isClosed_of_isClosed Metric.isClosed_closedBall isClosed_Iic

lemma aux_part1_mp {f : E → EReal} {O : Set E} (hO : IsOpen O)
    (H : ∀ x ∈ O, IsLocallyLipschitzNearEReal f x ∧ IsRegularAt f x) :
    ∃ (h : E → E → EReal),
      (∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w)) ∧
      (∀ (w : E), IsUscOnEReal (fun x => h x w) O) := by
  refine ⟨fun x w => Filter.limsup
      (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
      (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}), ?_,
      fun w => aux_clarke_usc hO w⟩
  intro x hx w
  obtain ⟨ρ, hρ, L, hL, hfin, hlip⟩ := aux_lip_of_locLip (H x hx).1
  refine ⟨aux_clarke_finite_of_lip hO hx hρ hfin hlip w, ?_⟩
  have hreg : subderivative f x w = regularSubderivative f x w := (H x hx).2.2.2 w
  have h1 := aux_subderiv_le_lowerDini f x w
  have h2 := aux_upperDini_le_clarke (f := f) hO hx w
  have h3 := aux_clarke_le_regSubderiv hO hx hρ hfin hlip w
  have hle : Filter.liminf (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) ≤
      Filter.limsup (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) := Filter.liminf_le_limsup
  have hinf : Filter.liminf (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) =
      Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) := by
    apply le_antisymm (hle.trans h2)
    calc _ ≤ regularSubderivative f x w := h3
        _ = subderivative f x w := hreg.symm
        _ ≤ _ := h1
  have hsup : Filter.limsup (fun τ : ℝ => differenceQuotient f x w τ) (𝓝[>] 0) =
      Filter.limsup (fun (p : ℝ × E) => (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
        (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓ Filter.principal {p : ℝ × E | p.2 ∈ O}) := by
    apply le_antisymm h2
    calc _ ≤ regularSubderivative f x w := h3
        _ = subderivative f x w := hreg.symm
        _ ≤ _ := h1
        _ ≤ _ := hle
  exact tendsto_of_liminf_eq_limsup hinf hsup

lemma aux_part1_mpr {f : E → EReal} {O : Set E} (hO : IsOpen O) (hf : IsFiniteOn f O)
    {h : E → E → EReal}
    (hh : ∀ x ∈ O, ∀ (w : E), IsFiniteEReal (h x w) ∧ HasDirectionalDerivativeEReal f x w (h x w))
    (husc : ∀ (w : E), IsUscOnEReal (fun x => h x w) O) {x : E} (hx : x ∈ O) :
    IsLocallyLipschitzNearEReal f x ∧ IsRegularAt f x := by
  obtain ⟨ρ, hρ, hball, L, hL, hlip⟩ := aux_lip hO hf hh husc hx
  have hfin : ∀ y ∈ Metric.ball x ρ, f y = ((f y).toReal : EReal) :=
    fun y hy => aux_coe_toReal hf (hball hy)
  refine ⟨⟨ρ, hρ, L, hL, fun y hy => ?_, fun y z hy hz => ?_⟩, ⟨?_, ?_⟩,
    aux_localLsc hρ hfin hlip, fun w => ?_⟩
  · rw [hfin y hy]; exact ⟨EReal.coe_ne_top _, EReal.coe_ne_bot _⟩
  · rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm]; exact hlip y hy z hz
  · rw [aux_coe_toReal hf hx]; exact EReal.bot_lt_coe _
  · rw [aux_coe_toReal hf hx]; exact EReal.coe_lt_top _
  · rw [← aux_subderiv_eq hO hf hh husc hx w, ← aux_regSubderiv hO hf hh husc hx w]

theorem RW_chap_9_16
  (f : E → EReal)
  (O : Set E)
  (hO_open : IsOpen O)
  (hf_finite_on : IsFiniteOn f O) :
  ((∀ x ∈ O,
      IsLocallyLipschitzNearEReal f x ∧ IsRegularAt f x) ↔
    ∃ (h : E → E → EReal),
      (∀ x ∈ O, ∀ (w : E),
        IsFiniteEReal (h x w) ∧
          HasDirectionalDerivativeEReal f x w (h x w)) ∧
      (∀ (w : E), IsUscOnEReal (fun x => h x w) O)) ∧
  (∀ (h : E → E → EReal),
    ((∀ x ∈ O, ∀ (w : E),
        IsFiniteEReal (h x w) ∧
          HasDirectionalDerivativeEReal f x w (h x w)) ∧
      (∀ (w : E), IsUscOnEReal (fun x => h x w) O)) →
      IsUscOnEReal
        (fun (p : E × E) => h p.1 p.2)
        {p : E × E | p.1 ∈ O} ∧
      IsSemidifferentiableOnWith f O h ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = Filter.liminf
          (fun (p : ℝ × E) =>
            (f (x + p.1 • p.2) - f x) / (p.1 : EReal))
          ((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 w)) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = Filter.limsup
          (fun (p : ℝ × E) =>
            (f (p.2 + p.1 • w) - f p.2) / (p.1 : EReal))
          (((𝓝[>] (0 : ℝ)) ×ˢ 𝓝 x) ⊓
            Filter.principal {p : ℝ × E | p.2 ∈ O})) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = subderivative f x w) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = regularSubderivative f x w) ∧
      (∀ x ∈ O, ∀ (w : E),
        h x w = supportFunction (subdifferential f x) w) ∧
      (∀ x ∈ O,
        (subdifferential f x).Nonempty ∧ Convex ℝ (subdifferential f x)) ∧
      IsOuterSemicontinuousOn (fun x => subdifferential f x) O ∧
      (∀ x ∈ O, IsLocallyBoundedAt (fun y => subdifferential f y) x)) := by
  constructor
  · constructor
    · intro H
      exact aux_part1_mp hO_open H
    · rintro ⟨h, hh, husc⟩ x hx
      exact aux_part1_mpr hO_open hf_finite_on hh husc hx
  · rintro h ⟨hh, husc⟩
    refine ⟨aux_joint_usc hO_open hf_finite_on hh husc, aux_semidiff hO_open hf_finite_on hh husc,
      fun x hx w => aux_subderiv_eq hO_open hf_finite_on hh husc hx w,
      fun x hx w => aux_clarke_eq hO_open hf_finite_on hh husc hx w,
      fun x hx w => aux_subderiv_eq hO_open hf_finite_on hh husc hx w,
      fun x hx w => aux_regSubderiv hO_open hf_finite_on hh husc hx w,
      fun x hx w => aux_support hO_open hf_finite_on hh husc hx w,
      fun x hx => aux_nonempty_convex hO_open hf_finite_on hh husc hx,
      aux_osc hO_open hf_finite_on hh husc,
      fun x hx => aux_locbdd hO_open hf_finite_on hh husc hx⟩

end RW_chap_9_16
