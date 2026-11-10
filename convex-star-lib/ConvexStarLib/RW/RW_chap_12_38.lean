import ConvexStarLib.Defs

/-!
# `RW_chap_12_38`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_38` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_38`, so the main result is `RW_chap_12_38.RW_chap_12_38`.
-/

namespace RW_chap_12_38

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

lemma rw1238_norm_le_of_inner_nonneg (p x a : E) (h : 0 ≤ inner ℝ (p - x) (x - a)) :
    ‖x - a‖ ≤ ‖p - a‖ := by
  have e : inner ℝ (p - x) (x - a) = inner ℝ (p - a) (x - a) - ‖x - a‖ ^ 2 := by
    rw [show p - x = (p - a) - (x - a) by abel, inner_sub_left, real_inner_self_eq_norm_sq]
  have h2 := real_inner_le_norm (p - a) (x - a)
  nlinarith [norm_nonneg (x - a), norm_nonneg (p - a)]

lemma rw1238_normal_of_not_locBdd (T : E → Set E) (hT : IsMonotone T) (x_bar : E)
    (h : ¬ IsLocallyBoundedAt T x_bar) :
    ∃ u : E, ‖u‖ = 1 ∧ ∀ a w, w ∈ T a → inner ℝ u (a - x_bar) ≤ 0 := by
  unfold IsLocallyBoundedAt at h
  push_neg at h
  have hseq : ∀ n : ℕ, ∃ x ∈ Metric.ball x_bar (1 / ((n : ℝ) + 1)), ∃ v ∈ T x,
      (n : ℝ) + 1 < ‖v‖ := fun n =>
    h _ (Metric.ball_mem_nhds _ (by positivity)) _ (by positivity)
  choose xs hxs vs hvs hvn using hseq
  have hvpos : ∀ n, 0 < ‖vs n‖ := fun n => lt_trans (by positivity) (hvn n)
  set us : ℕ → E := fun n => ‖vs n‖⁻¹ • vs n with hus
  have hus1 : ∀ n, us n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, hus]
    simp only
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (hvpos n).ne']
  obtain ⟨u, hu, sq, hsq, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hus1
  refine ⟨u, by simpa using hu, ?_⟩
  intro a w haw
  -- convergence of xs
  have hxlim : Filter.Tendsto xs Filter.atTop (𝓝 x_bar) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n => dist_nonneg) (fun n => (Metric.mem_ball.1 (hxs n)).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hinvlim : Filter.Tendsto (fun n => ‖vs n‖⁻¹) Filter.atTop (𝓝 0) := by
    refine squeeze_zero (fun n => (inv_pos.2 (hvpos n)).le) (fun n => ?_)
      tendsto_one_div_add_atTop_nhds_zero_nat
    rw [one_div]
    exact (inv_le_inv₀ (hvpos n) (by positivity)).2 (hvn n).le
  have hsqt := hsq.tendsto_atTop
  have hL : Filter.Tendsto (fun k => inner ℝ (us (sq k) - ‖vs (sq k)‖⁻¹ • w) (xs (sq k) - a))
      Filter.atTop (𝓝 (inner ℝ (u - (0 : ℝ) • w) (x_bar - a))) := by
    apply Filter.Tendsto.inner
    · exact hlim.sub ((hinvlim.comp hsqt).smul_const w)
    · exact (hxlim.comp hsqt).sub_const a
  have hnn : ∀ k, 0 ≤ inner ℝ (us (sq k) - ‖vs (sq k)‖⁻¹ • w) (xs (sq k) - a) := by
    intro k
    have hm := hT a (xs (sq k)) w (vs (sq k)) haw (hvs (sq k))
    rw [hus]
    simp only
    rw [← smul_sub, real_inner_smul_left]
    exact mul_nonneg (inv_nonneg.2 (norm_nonneg _)) hm
  have h0 := ge_of_tendsto' hL hnn
  rw [zero_smul, sub_zero] at h0
  have : inner ℝ u (a - x_bar) = - inner ℝ u (x_bar - a) := by
    rw [← inner_neg_right, neg_sub]
  linarith

lemma rw1238_minty_fin {ι : Type*} [Fintype ι] (a w : ι → E)
    (hmono : ∀ i j, 0 ≤ inner ℝ (w i - w j) (a i - a j)) (y : E) :
    ∃ x : E, ∀ i, 0 ≤ inner ℝ (y - x - w i) (x - a i) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · exact ⟨0, fun i => (IsEmpty.false i).elim⟩
  obtain ⟨m, hm⟩ : ∃ m : ι → E, ∀ i, m i = (1/2 : ℝ) • (y + a i - w i) := ⟨_, fun i => rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : ι → ℝ, ∀ i, k i = inner ℝ (y - w i) (a i) := ⟨_, fun i => rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : (ι → ℝ) → ℝ, ∀ μ, V μ = ‖∑ i, μ i • m i‖ ^ 2 - ∑ i, μ i * k i :=
    ⟨_, fun μ => rfl⟩
  have hVc : Continuous V := by
    rw [show V = fun μ => ‖∑ i, μ i • m i‖ ^ 2 - ∑ i, μ i * k i from funext hV]
    fun_prop
  obtain ⟨μ, hμS, hμmin⟩ := (isCompact_stdSimplex ι).exists_isMinOn
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩ hVc.continuousOn
  obtain ⟨x, hx⟩ : ∃ x : E, x = ∑ i, μ i • m i := ⟨_, rfl⟩
  obtain ⟨kμ, hkμ⟩ : ∃ kμ : ℝ, kμ = ∑ i, μ i * k i := ⟨_, rfl⟩
  have hVμ : V μ = ‖x‖ ^ 2 - kμ := by rw [hV, hx, hkμ]
  -- identity for φ
  have hphi : ∀ (z : E) j, inner ℝ (y - z - w j) (z - a j)
      = 2 * inner ℝ z (m j) - k j - ‖z‖ ^ 2 := by
    intro z j
    rw [hm, hk]
    simp only [real_inner_smul_right, inner_sub_left, inner_sub_right, inner_add_right,
      real_inner_self_eq_norm_sq, real_inner_comm z]
    ring
  -- V ≥ 0 on simplex
  have hV0 : ∀ ν ∈ stdSimplex ℝ ι, 0 ≤ V ν := by
    intro ν hν
    obtain ⟨hν0, hν1⟩ := hν
    obtain ⟨abar, habar⟩ : ∃ z : E, z = ∑ i, ν i • a i := ⟨_, rfl⟩
    obtain ⟨wbar, hwbar⟩ : ∃ z : E, z = ∑ i, ν i • w i := ⟨_, rfl⟩
    have hmν : ∑ i, ν i • m i = (1/2 : ℝ) • (y + abar - wbar) := by
      calc ∑ i, ν i • m i = (1/2 : ℝ) • ∑ i, (ν i • y + ν i • a i - ν i • w i) := by
            rw [Finset.smul_sum]
            apply Finset.sum_congr rfl
            intro i _
            rw [hm, smul_comm, smul_sub, smul_add]
        _ = (1/2 : ℝ) • (y + abar - wbar) := by
            rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.sum_smul, hν1, one_smul,
              habar, hwbar]
    have hkν : ∑ i, ν i * k i = inner ℝ y abar - ∑ i, ν i * inner ℝ (w i) (a i) := by
      rw [habar, inner_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      rw [hk, inner_sub_left, real_inner_smul_right]
      ring
    have t1 : ∑ i, ∑ j, ν i * ν j * inner ℝ (w i) (a i) = ∑ i, ν i * inner ℝ (w i) (a i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← Finset.sum_mul, ← Finset.mul_sum, hν1, mul_one]
    have t2 : ∑ i, ∑ j, ν i * ν j * inner ℝ (w j) (a j) = ∑ i, ν i * inner ℝ (w i) (a i) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [← Finset.sum_mul, ← Finset.sum_mul, hν1, one_mul]
    have t3 : ∑ i, ∑ j, ν i * ν j * inner ℝ (w i) (a j) = inner ℝ wbar abar := by
      rw [hwbar, habar, sum_inner]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_right]
      ring
    have t4 : ∑ i, ∑ j, ν i * ν j * inner ℝ (w j) (a i) = inner ℝ wbar abar := by
      rw [Finset.sum_comm, hwbar, habar, sum_inner]
      apply Finset.sum_congr rfl
      intro j _
      rw [real_inner_smul_left, inner_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [real_inner_smul_right]
      ring
    have hsum : 0 ≤ ∑ i, ∑ j, ν i * ν j * inner ℝ (w i - w j) (a i - a j) :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ =>
        mul_nonneg (mul_nonneg (hν0 i) (hν0 j)) (hmono i j)))
    have e1 : ∑ i, ∑ j, ν i * ν j * inner ℝ (w i - w j) (a i - a j)
        = 2 * (∑ i, ν i * inner ℝ (w i) (a i)) - 2 * inner ℝ wbar abar := by
      calc ∑ i, ∑ j, ν i * ν j * inner ℝ (w i - w j) (a i - a j)
          = ∑ i, ∑ j, (ν i * ν j * inner ℝ (w i) (a i) - ν i * ν j * inner ℝ (w i) (a j)
              - ν i * ν j * inner ℝ (w j) (a i) + ν i * ν j * inner ℝ (w j) (a j)) := by
            apply Finset.sum_congr rfl
            intro i _
            apply Finset.sum_congr rfl
            intro j _
            rw [inner_sub_left, inner_sub_right, inner_sub_right]
            ring
        _ = 2 * (∑ i, ν i * inner ℝ (w i) (a i)) - 2 * inner ℝ wbar abar := by
            simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            rw [t1, t2, t3, t4]
            ring
    have hcov : inner ℝ wbar abar ≤ ∑ i, ν i * inner ℝ (w i) (a i) := by linarith
    have hge : 2 * inner ℝ abar (∑ i, ν i • m i) - ‖abar‖ ^ 2 - ∑ i, ν i * k i ≤ V ν := by
      rw [hV]
      have := sq_nonneg ‖(∑ i, ν i • m i) - abar‖
      rw [norm_sub_sq_real, real_inner_comm] at this
      linarith
    have hval : 2 * inner ℝ abar (∑ i, ν i • m i) - ‖abar‖ ^ 2 - ∑ i, ν i * k i
        = ∑ i, ν i * inner ℝ (w i) (a i) - inner ℝ wbar abar := by
      rw [hmν, hkν, real_inner_smul_right, inner_sub_right, inner_add_right,
        real_inner_self_eq_norm_sq, real_inner_comm abar y, real_inner_comm abar wbar]
      ring
    linarith
  -- first order condition
  have hfoc : ∀ j, 0 ≤ 2 * inner ℝ x (m j - x) - k j + kμ := by
    intro j
    obtain ⟨d, hd⟩ : ∃ d : E, d = m j - x := ⟨_, rfl⟩
    rw [← hd]
    set A := 2 * inner ℝ x d - k j + kμ with hA
    have heS : (fun i => if j = i then (1 : ℝ) else 0) ∈ stdSimplex ℝ ι :=
      ite_eq_mem_stdSimplex ℝ j
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 → 0 ≤ A + t * ‖d‖ ^ 2 := by
      intro t ht0 ht1
      have hmem : (1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0) ∈ stdSimplex ℝ ι :=
        convex_stdSimplex ℝ ι hμS heS (by linarith) ht0.le (by ring)
      have hle : V μ ≤ V ((1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0)) :=
        hμmin hmem
      have hs1 : ∑ i, ((1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0)) i • m i
          = x + t • d := by
        have h1 : ∀ i, ((1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0)) i • m i
            = (1 - t) • (μ i • m i) + t • ((if j = i then (1 : ℝ) else 0) • m i) := by
          intro i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_smul, mul_smul]
        have h2 : ∑ i, (if j = i then (1 : ℝ) else 0) • m i = m j := by
          simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.smul_sum,
          ← Finset.smul_sum, h2, ← hx, hd, smul_sub, sub_smul, one_smul]
        abel
      have hs2 : ∑ i, ((1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0)) i * k i
          = (1 - t) * kμ + t * k j := by
        have h1 : ∀ i, ((1 - t) • μ + t • (fun i => if j = i then (1 : ℝ) else 0)) i * k i
            = (1 - t) * (μ i * k i) + t * ((if j = i then (1 : ℝ) else 0) * k i) := by
          intro i
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
          ring
        have h2 : ∑ i, (if j = i then (1 : ℝ) else 0) * k i = k j := by
          simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_add_distrib, ← Finset.mul_sum,
          ← Finset.mul_sum, h2, ← hkμ]
      rw [hVμ, hV, hs1, hs2, norm_add_sq_real, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, abs_of_pos ht0] at hle
      have h3 : 0 ≤ t * (A + t * ‖d‖ ^ 2) := by
        rw [hA]
        nlinarith
      by_contra hneg
      push_neg at hneg
      nlinarith [mul_neg_of_pos_of_neg ht0 hneg]
    by_contra hneg
    push_neg at hneg
    have hpos : 0 < -A / (2 * (‖d‖ ^ 2 + 1)) := div_pos (by linarith) (by positivity)
    have ht0 : 0 < min 1 (-A / (2 * (‖d‖ ^ 2 + 1))) := lt_min one_pos hpos
    have ht1 : min 1 (-A / (2 * (‖d‖ ^ 2 + 1))) ≤ 1 := min_le_left _ _
    have ht2 : min 1 (-A / (2 * (‖d‖ ^ 2 + 1))) ≤ -A / (2 * (‖d‖ ^ 2 + 1)) := min_le_right _ _
    have h4 := key _ ht0 ht1
    have h3 : min 1 (-A / (2 * (‖d‖ ^ 2 + 1))) * ‖d‖ ^ 2 ≤ -A / 2 := by
      calc min 1 (-A / (2 * (‖d‖ ^ 2 + 1))) * ‖d‖ ^ 2
          ≤ (-A / (2 * (‖d‖ ^ 2 + 1))) * ‖d‖ ^ 2 :=
            mul_le_mul_of_nonneg_right ht2 (by positivity)
        _ ≤ -A / 2 := by
            rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
            nlinarith [sq_nonneg ‖d‖]
    linarith
  refine ⟨x, fun j => ?_⟩
  rw [hphi]
  have h1 := hfoc j
  have h0 := hV0 μ hμS
  rw [hVμ] at h0
  rw [inner_sub_right, real_inner_self_eq_norm_sq] at h1
  linarith

lemma rw1238_minty_exists (T : E → Set E) (hT : IsMonotone T) (lam : ℝ) (hlam : 0 < lam)
    (y : E) : ∃ x : E, ∀ a w, w ∈ T a → 0 ≤ inner ℝ (y - x - lam • w) (x - a) := by
  classical
  rcases isEmpty_or_nonempty {p : E × E // p.2 ∈ T p.1} with hG | hne
  · exact ⟨0, fun a w haw => (hG.false ⟨(a, w), haw⟩).elim⟩
  obtain ⟨p₀⟩ := hne
  let K : {p : E × E // p.2 ∈ T p.1} → Set E :=
    fun p => {x | 0 ≤ inner ℝ (y - x - lam • p.1.2) (x - p.1.1)}
  have hKc : ∀ p, IsClosed (K p) := fun p => isClosed_le continuous_const (by fun_prop)
  have hK0 : IsCompact (K p₀) := by
    apply (isCompact_closedBall p₀.1.1 ‖(y - lam • p₀.1.2) - p₀.1.1‖).of_isClosed_subset (hKc p₀)
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    apply rw1238_norm_le_of_inner_nonneg
    have : 0 ≤ inner ℝ (y - x - lam • p₀.1.2) (x - p₀.1.1) := hx
    rwa [show y - x - lam • p₀.1.2 = (y - lam • p₀.1.2) - x by abel] at this
  have hfin : ∀ u : Finset {p : E × E // p.2 ∈ T p.1}, (K p₀ ∩ ⋂ i ∈ u, K i).Nonempty := by
    intro u
    let g : Option u → {p : E × E // p.2 ∈ T p.1} := fun o => o.elim p₀ (fun p => p.1)
    obtain ⟨x, hx⟩ := rw1238_minty_fin (fun o => (g o).1.1) (fun o => lam • (g o).1.2)
      (fun o₁ o₂ => by
        rw [← smul_sub, real_inner_smul_left]
        exact mul_nonneg hlam.le
          (hT (g o₂).1.1 (g o₁).1.1 (g o₂).1.2 (g o₁).1.2 (g o₂).2 (g o₁).2)) y
    refine ⟨x, hx none, ?_⟩
    rw [Set.mem_iInter₂]
    intro p hp
    exact hx (some ⟨p, hp⟩)
  obtain ⟨x, -, hx⟩ := hK0.inter_iInter_nonempty K hKc hfin
  refine ⟨x, fun a w haw => ?_⟩
  exact Set.mem_iInter.1 hx ⟨(a, w), haw⟩

theorem RW_chap_12_38
  (T : E → Set E)
  (hT : IsMaximalMonotone T) :
  let domT : Set E := {x | (T x).Nonempty}
  let D : Set E := closure domT
  (∀ x_bar, IsLocallyBoundedAt T x_bar ↔ x_bar ∉ frontier D) ∧
  (∀ x_bar, x_bar ∈ domT →
    (IsLocallyBoundedAt T x_bar ↔ Bornology.IsBounded (T x_bar))) := by
  intro domT D
  obtain ⟨hmono, hmax⟩ := hT
  have hDc : IsClosed D := isClosed_closure
  have hfr : frontier D = D \ interior D := hDc.frontier_eq
  have hmax' : ∀ x v, (∀ a w, w ∈ T a → 0 ≤ inner ℝ (v - w) (x - a)) → v ∈ T x := by
    intro x v h
    by_contra hv
    obtain ⟨a, w, hw, hlt⟩ := hmax x v hv
    exact absurd (h a w hw) (not_le.2 hlt)
  refine ⟨fun x_bar => ⟨fun hlb => ?_, fun hnf => ?_⟩,
    fun x_bar hx => ⟨fun hlb => ?_, fun hb => ?_⟩⟩
  · -- locally bounded → not in the frontier
    rw [hfr]
    rintro ⟨hxD, hxint⟩
    apply hxint
    obtain ⟨U, hU, R, hR, hUR⟩ := hlb
    obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 hU
    obtain ⟨x₀, hx₀dom, hx₀⟩ := Metric.mem_closure_iff.1 hxD (ρ / 4) (by positivity)
    obtain ⟨v₀, hv₀⟩ := hx₀dom
    have hx₀' : ‖x₀ - x_bar‖ < ρ / 4 := by rw [← dist_eq_norm, _root_.dist_comm]; exact hx₀
    have hv₀R : ‖v₀‖ ≤ R :=
      hUR x₀ (hρU (by rw [Metric.mem_ball, dist_eq_norm]; linarith)) v₀ hv₀
    rw [mem_interior_iff_mem_nhds, Metric.mem_nhds_iff]
    refine ⟨ρ / 4, by positivity, fun y hy => ?_⟩
    have hy' : ‖y - x_bar‖ < ρ / 4 := by rw [← dist_eq_norm]; exact hy
    by_contra hyD
    obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hDc.isOpen_compl y hyD
    obtain ⟨lam, hlam⟩ : ∃ lam : ℝ, lam = min (ρ / (4 * R)) (ε / (2 * R)) := ⟨_, rfl⟩
    have hlam0 : 0 < lam := by rw [hlam]; exact lt_min (by positivity) (by positivity)
    have hlamR1 : lam * R ≤ ρ / 4 := by
      have : lam ≤ ρ / (4 * R) := by rw [hlam]; exact min_le_left _ _
      calc lam * R ≤ ρ / (4 * R) * R := mul_le_mul_of_nonneg_right this hR.le
        _ = ρ / 4 := by field_simp
    have hlamR2 : lam * R ≤ ε / 2 := by
      have : lam ≤ ε / (2 * R) := by rw [hlam]; exact min_le_right _ _
      calc lam * R ≤ ε / (2 * R) * R := mul_le_mul_of_nonneg_right this hR.le
        _ = ε / 2 := by field_simp
    obtain ⟨xh, hxh⟩ := rw1238_minty_exists T hmono lam hlam0 y
    have hvhT : lam⁻¹ • (y - xh) ∈ T xh := by
      apply hmax'
      intro a w hw
      have e : lam⁻¹ • (y - xh - lam • w) = lam⁻¹ • (y - xh) - w := by
        rw [smul_sub (lam⁻¹) (y - xh) (lam • w), smul_smul, inv_mul_cancel₀ hlam0.ne', one_smul]
      rw [← e, real_inner_smul_left]
      exact mul_nonneg (inv_nonneg.2 hlam0.le) (hxh a w hw)
    have hxhD : xh ∈ D := subset_closure ⟨_, hvhT⟩
    have hdist : ε ≤ ‖y - xh‖ := by
      by_contra h
      push_neg at h
      exact hεD (by rw [Metric.mem_ball, dist_eq_norm, norm_sub_rev]; exact h) hxhD
    have hclose : ‖xh - x₀‖ ≤ ‖(y - lam • v₀) - x₀‖ := by
      apply rw1238_norm_le_of_inner_nonneg
      have := hxh x₀ v₀ hv₀
      rwa [show y - xh - lam • v₀ = (y - lam • v₀) - xh by abel] at this
    have hxhU : xh ∈ U := by
      apply hρU
      rw [Metric.mem_ball, dist_eq_norm]
      have h1 : ‖(y - lam • v₀) - x₀‖ ≤ ‖y - x_bar‖ + ‖x_bar - x₀‖ + lam * ‖v₀‖ := by
        calc ‖(y - lam • v₀) - x₀‖ = ‖(y - x_bar) + (x_bar - x₀) - lam • v₀‖ := by
              congr 1; abel
          _ ≤ ‖(y - x_bar) + (x_bar - x₀)‖ + ‖lam • v₀‖ := norm_sub_le _ _
          _ ≤ ‖y - x_bar‖ + ‖x_bar - x₀‖ + ‖lam • v₀‖ := by
              gcongr; exact norm_add_le _ _
          _ = ‖y - x_bar‖ + ‖x_bar - x₀‖ + lam * ‖v₀‖ := by
              rw [norm_smul, Real.norm_eq_abs, abs_of_pos hlam0]
      have h2 : ‖xh - x_bar‖ ≤ ‖xh - x₀‖ + ‖x₀ - x_bar‖ := by
        calc ‖xh - x_bar‖ = ‖(xh - x₀) + (x₀ - x_bar)‖ := by congr 1; abel
          _ ≤ _ := norm_add_le _ _
      have h3 : ‖x_bar - x₀‖ = ‖x₀ - x_bar‖ := norm_sub_rev _ _
      have h4 : lam * ‖v₀‖ ≤ lam * R := mul_le_mul_of_nonneg_left hv₀R hlam0.le
      linarith
    have hvhR := hUR xh hxhU _ hvhT
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hlam0, inv_mul_le_iff₀ hlam0] at hvhR
    linarith
  · -- not in the frontier → locally bounded
    by_cases hxD : x_bar ∈ D
    · have hint : x_bar ∈ interior D := by
        rw [hfr] at hnf
        by_contra h
        exact hnf ⟨hxD, h⟩
      by_contra hnlb
      obtain ⟨u, hu1, hu⟩ := rw1238_normal_of_not_locBdd T hmono x_bar hnlb
      have hcl : D ⊆ {a | inner ℝ u (a - x_bar) ≤ 0} := by
        apply closure_minimal
        · rintro a ⟨w, hw⟩
          exact hu a w hw
        · exact isClosed_le (by fun_prop) continuous_const
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 (mem_interior_iff_mem_nhds.1 hint)
      have hmem : x_bar + (ε / 2) • u ∈ D := by
        apply hball
        rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, hu1, mul_one,
          Real.norm_eq_abs, abs_of_pos (by positivity)]
        linarith
      have h1 := hcl hmem
      simp only [Set.mem_setOf_eq, add_sub_cancel_left, real_inner_smul_right,
        real_inner_self_eq_norm_sq, hu1] at h1
      linarith
    · refine ⟨Dᶜ, hDc.isOpen_compl.mem_nhds hxD, 1, one_pos, fun x hx v hv => ?_⟩
      exact absurd (subset_closure (show x ∈ domT from ⟨v, hv⟩)) hx
  · -- locally bounded → T x_bar bounded
    obtain ⟨U, hU, R, hR, hUR⟩ := hlb
    exact (Metric.isBounded_closedBall (x := (0 : E)) (r := R)).subset
      (fun v hv => by
        rw [Metric.mem_closedBall, _root_.dist_zero_right]
        exact hUR x_bar (mem_of_mem_nhds hU) v hv)
  · -- T x_bar bounded → locally bounded
    by_contra hnlb
    obtain ⟨u, hu1, hu⟩ := rw1238_normal_of_not_locBdd T hmono x_bar hnlb
    obtain ⟨v₀, hv₀⟩ := hx
    have hray : ∀ t : ℝ, 0 ≤ t → v₀ + t • u ∈ T x_bar := by
      intro t ht
      apply hmax'
      intro a w hw
      have h1 := hmono a x_bar w v₀ hw hv₀
      have h2 := hu a w hw
      have e1 : inner ℝ (v₀ + t • u - w) (x_bar - a)
          = inner ℝ (v₀ - w) (x_bar - a) + t * inner ℝ u (x_bar - a) := by
        rw [show v₀ + t • u - w = (v₀ - w) + t • u by abel, inner_add_left, real_inner_smul_left]
      have e2 : inner ℝ u (x_bar - a) = - inner ℝ u (a - x_bar) := by
        rw [← inner_neg_right, neg_sub]
      rw [e1, e2]
      nlinarith
    obtain ⟨C, hC⟩ := hb.subset_closedBall 0
    have hmem := hC (hray (|C| + ‖v₀‖ + 1) (by positivity))
    rw [Metric.mem_closedBall, _root_.dist_zero_right] at hmem
    have h4 : ‖(|C| + ‖v₀‖ + 1) • u‖ ≤ ‖v₀ + (|C| + ‖v₀‖ + 1) • u‖ + ‖v₀‖ := by
      calc ‖(|C| + ‖v₀‖ + 1) • u‖ = ‖(v₀ + (|C| + ‖v₀‖ + 1) • u) - v₀‖ := by congr 1; abel
        _ ≤ _ := norm_sub_le _ _
    rw [norm_smul, hu1, mul_one, Real.norm_eq_abs, abs_of_pos (by positivity)] at h4
    linarith [le_abs_self C]

end RW_chap_12_38
