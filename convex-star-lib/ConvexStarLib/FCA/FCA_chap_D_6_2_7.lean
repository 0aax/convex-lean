import ConvexStarLib.Defs

/-!
# `FCA_chap_D_6_2_7`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_6_2_7` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_6_2_7`, so the main result is `FCA_chap_D_6_2_7.FCA_chap_D_6_2_7`.
-/

namespace FCA_chap_D_6_2_7

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal Filter

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma aux_dq_eq (g : E → ℝ) (y d : E) (t : ℝ) :
    differenceQuotient (liftRealtoEReal g) y d t = (((g (y + t • d) - g y) / t : ℝ) : EReal) := by
  simp [differenceQuotient, liftRealtoEReal, EReal.coe_div, EReal.coe_sub]

omit [FiniteDimensional ℝ E] in
lemma aux_dq_mono (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (y d : E) :
    MonotoneOn (fun t : ℝ => (g (y + t • d) - g y) / t) (Set.Ioi 0) := by
  intro s hs t ht hst
  simp only [Set.mem_Ioi] at hs ht
  have key := hg.2 (Set.mem_univ y) (Set.mem_univ (y + t • d))
    (show (0:ℝ) ≤ 1 - s / t by rw [sub_nonneg, div_le_one ht]; exact hst)
    (show (0:ℝ) ≤ s / t by positivity) (by ring)
  have h1 : (1 - s / t) • y + (s / t) • (y + t • d) = y + s • d := by
    rw [smul_add, smul_smul, div_mul_cancel₀ _ ht.ne']; module
  rw [h1, smul_eq_mul, smul_eq_mul] at key
  show (g (y + s • d) - g y) / s ≤ (g (y + t • d) - g y) / t
  rw [div_le_div_iff₀ hs ht]
  have h2 : (g (y + s • d) - g y) * t ≤ ((1 - s / t) * g y + s / t * g (y + t • d) - g y) * t :=
    mul_le_mul_of_nonneg_right (by linarith) ht.le
  have h3 : ((1 - s / t) * g y + s / t * g (y + t • d) - g y) * t = (g (y + t • d) - g y) * s := by
    field_simp; ring
  linarith

omit [FiniteDimensional ℝ E] in
lemma aux_dd_eq (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (y d : E) :
    directionalDeriv (liftRealtoEReal g) y d =
      sInf ((fun t : ℝ => (((g (y + t • d) - g y) / t : ℝ) : EReal)) '' Set.Ioi 0) := by
  have hmono : MonotoneOn (fun t : ℝ => (((g (y + t • d) - g y) / t : ℝ) : EReal)) (Set.Ioi 0) :=
    fun s hs t ht hst => EReal.coe_le_coe_iff.mpr (aux_dq_mono g hg y d hs ht hst)
  have hfun : (fun t => differenceQuotient (liftRealtoEReal g) y d t) =
      (fun t : ℝ => (((g (y + t • d) - g y) / t : ℝ) : EReal)) := funext (aux_dq_eq g y d)
  unfold directionalDeriv
  rw [hfun]
  exact (hmono.tendsto_nhdsGT (OrderBot.bddBelow _)).limUnder_eq

omit [FiniteDimensional ℝ E] in
lemma aux_subgrad_of_mem (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (y s : E)
    (hs : s ∈ directionalSubdifferential (liftRealtoEReal g) y) (z : E) :
    g y + inner ℝ s (z - y) ≤ g z := by
  have h : ((inner ℝ s (z - y) : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal g) y (z - y) :=
    hs (z - y)
  rw [aux_dd_eq g hg] at h
  have h1 : sInf ((fun t : ℝ => (((g (y + t • (z - y)) - g y) / t : ℝ) : EReal)) '' Set.Ioi 0) ≤
      (((g (y + (1:ℝ) • (z - y)) - g y) / 1 : ℝ) : EReal) :=
    sInf_le ⟨1, by norm_num, rfl⟩
  have h2 := EReal.coe_le_coe_iff.mp (h.trans h1)
  simp only [one_smul, add_sub_cancel, div_one] at h2
  linarith

omit [FiniteDimensional ℝ E] in
lemma aux_mem_of_subgrad (g : E → ℝ) (hg : ConvexOn ℝ Set.univ g) (y s : E)
    (hs : ∀ z, g y + inner ℝ s (z - y) ≤ g z) :
    s ∈ directionalSubdifferential (liftRealtoEReal g) y := by
  intro d
  show ((inner ℝ s d : ℝ) : EReal) ≤ directionalDeriv (liftRealtoEReal g) y d
  rw [aux_dd_eq g hg]
  apply le_sInf
  rintro _ ⟨t, ht, rfl⟩
  apply EReal.coe_le_coe_iff.mpr
  rw [le_div_iff₀ ht]
  have := hs (y + t • d)
  rw [add_sub_cancel_left, real_inner_smul_right] at this
  linarith

theorem FCA_chap_D_6_2_7
  (fk : ℕ → (E → ℝ))
  (xk : ℕ → E)
  (f : E → ℝ)
  (x : E)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (fk i))
  (hf_pointwise : ∀ v, Filter.Tendsto (fun k => fk k v) Filter.atTop (𝓝 (f v)))
  (hx_limit : Filter.Tendsto xk Filter.atTop (𝓝 x)) :
  let subdiff_neighborhood := fun (eps : ℝ) =>
                              {v | ∃ w d, (‖d‖ ≤ eps) ∧
                              (w ∈ directionalSubdifferential (liftRealtoEReal f) x) ∧ (v = w + d)}
  ∀ eps > 0, ∃ (K : ℕ), ∀ k ≥ K,
  directionalSubdifferential (liftRealtoEReal (fk k)) (xk k) ⊆ subdiff_neighborhood eps := by
  intro subdiff_neighborhood eps heps
  -- the limit function is convex
  have hfc : ConvexOn ℝ Set.univ f := by
    refine ⟨convex_univ, fun a _ b _ α β hα hβ hαβ => ?_⟩
    have h1 := hf_pointwise (α • a + β • b)
    have h2 := ((hf_pointwise a).const_mul α).add ((hf_pointwise b).const_mul β)
    exact le_of_tendsto_of_tendsto' h1 h2
      (fun k => (hf_convex k).2 (Set.mem_univ a) (Set.mem_univ b) hα hβ hαβ)
  -- a simplex around x
  obtain ⟨bb, hxb, -⟩ :=
    exists_mem_interior_convexHull_affineBasis (Filter.univ_mem : (Set.univ : Set E) ∈ 𝓝 x)
  obtain ⟨r, hr, hrb⟩ := Metric.isOpen_iff.mp isOpen_interior x hxb
  -- uniform upper bound on the vertices
  have hMi : ∀ i, ∃ M, ∀ k, fk k (bb i) ≤ M := fun i => by
    obtain ⟨M, hM⟩ := (hf_pointwise (bb i)).bddAbove_range
    exact ⟨M, fun k => hM ⟨k, rfl⟩⟩
  choose Mi hMi using hMi
  obtain ⟨M, hM⟩ := (Set.finite_range Mi).bddAbove
  have hup : ∀ k, ∀ y ∈ Metric.ball x r, fk k y ≤ M := by
    intro k y hy
    obtain ⟨z, ⟨i, rfl⟩, hz⟩ :=
      (hf_convex k).exists_ge_of_mem_convexHull (Set.subset_univ _) (interior_subset (hrb hy))
    exact hz.trans ((hMi i k).trans (hM ⟨i, rfl⟩))
  obtain ⟨m, hm⟩ : ∃ m, ∀ k, m ≤ fk k x := by
    obtain ⟨m, hm⟩ := (hf_pointwise x).bddBelow_range
    exact ⟨m, fun k => hm ⟨k, rfl⟩⟩
  have hlow : ∀ k, ∀ y ∈ Metric.ball x r, 2 * m - M ≤ fk k y := by
    intro k y hy
    have hy' : (2:ℝ) • x - y ∈ Metric.ball x r := by
      rw [Metric.mem_ball, dist_eq_norm] at hy ⊢
      rw [show (2:ℝ) • x - y - x = -(y - x) by module, norm_neg]; exact hy
    have hc := (hf_convex k).2 (Set.mem_univ y) (Set.mem_univ ((2:ℝ) • x - y))
      (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    rw [show (1/2:ℝ) • y + (1/2:ℝ) • ((2:ℝ) • x - y) = x by module] at hc
    have := hup k _ hy'
    have := hm k
    simp only [smul_eq_mul] at hc
    linarith
  set M' := max |M| |2 * m - M| with hM'
  have hM'0 : 0 ≤ M' := le_max_of_le_left (abs_nonneg _)
  have habs : ∀ k, ∀ y, dist y x < r → |fk k y| ≤ M' := by
    intro k y hy
    rw [abs_le]
    constructor
    · have := hlow k y hy; have := neg_abs_le (2 * m - M)
      have := le_max_right |M| |2 * m - M|; linarith
    · have := hup k y hy; have := le_abs_self M; have := le_max_left |M| |2 * m - M|; linarith
  -- equi-Lipschitz on a smaller ball
  have hLip : ∀ k, LipschitzOnWith (2 * M' / (r/2)).toNNReal (fk k) (Metric.ball x (r - r/2)) :=
    fun k => ((hf_convex k).subset (Set.subset_univ _) (convex_ball x r)).lipschitzOnWith_of_abs_le
      (by positivity) (habs k)
  set L : ℝ := ((2 * M' / (r/2)).toNNReal : ℝ) with hL
  have hxk_ball : ∀ᶠ k in atTop, xk k ∈ Metric.ball x (r/4) :=
    hx_limit (Metric.ball_mem_nhds x (by positivity))
  -- f_k (x_k) → f x
  have hconv : Tendsto (fun k => fk k (xk k)) atTop (𝓝 (f x)) := by
    have h1 : Tendsto (fun k => fk k (xk k) - fk k x) atTop (𝓝 0) := by
      have h2 : Tendsto (fun k => L * dist (xk k) x) atTop (𝓝 0) := by
        have := (tendsto_iff_dist_tendsto_zero.mp hx_limit).const_mul L
        simpa using this
      apply squeeze_zero_norm' _ h2
      filter_upwards [hxk_ball] with k hk
      have hk' : xk k ∈ Metric.ball x (r - r/2) :=
        Metric.ball_subset_ball (by linarith) hk
      have hx' : x ∈ Metric.ball x (r - r/2) := Metric.mem_ball_self (by linarith)
      have := (hLip k).dist_le_mul (xk k) hk' x hx'
      rwa [Real.dist_eq, ← Real.norm_eq_abs] at this
    simpa using h1.add (hf_pointwise x)
  -- subgradients are eventually bounded
  have hbound : ∀ᶠ k in atTop, ∀ s ∈ directionalSubdifferential (liftRealtoEReal (fk k)) (xk k),
      ‖s‖ ≤ 4 * M' / r := by
    filter_upwards [hxk_ball] with k hk s hs
    rcases eq_or_ne s 0 with rfl | hs0
    · simp only [norm_zero]; positivity
    have hn : 0 < ‖s‖ := norm_pos_iff.mpr hs0
    set z := xk k + (r / 2 / ‖s‖) • s with hz
    have hzb : dist z x < r := by
      rw [dist_eq_norm]
      calc ‖z - x‖ = ‖(xk k - x) + (r / 2 / ‖s‖) • s‖ := by rw [hz]; congr 1; abel
        _ ≤ ‖xk k - x‖ + ‖(r / 2 / ‖s‖) • s‖ := norm_add_le _ _
        _ = ‖xk k - x‖ + r / 2 := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ hn.ne']
        _ < r / 4 + r / 2 := by
          gcongr
          rw [← dist_eq_norm]; exact Metric.mem_ball.mp hk
        _ < r := by linarith
    have hsub := aux_subgrad_of_mem (fk k) (hf_convex k) (xk k) s hs z
    have hinner : inner ℝ s (z - xk k) = r / 2 * ‖s‖ := by
      rw [hz, add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    rw [hinner] at hsub
    have h1 := habs k z hzb
    have h2 := habs k (xk k) (by have := Metric.mem_ball.mp hk; linarith)
    rw [abs_le] at h1 h2
    rw [le_div_iff₀ hr]
    nlinarith
  -- argue by contradiction
  by_contra hcon
  push_neg at hcon
  simp only [Set.not_subset] at hcon
  choose kk hkk s hs hns using hcon
  have hkk_tend : Tendsto kk atTop atTop := tendsto_atTop_mono hkk tendsto_id
  have hfreq : ∃ᶠ K in atTop, s K ∈ Metric.closedBall (0:E) (4 * M' / r) := by
    apply Filter.Eventually.frequently
    filter_upwards [hkk_tend.eventually hbound] with K hK
    rw [mem_closedBall_zero_iff]
    exact hK (s K) (hs K)
  obtain ⟨a, -, phi, hphi, hlim⟩ :=
    tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hfreq
  have hphit : Tendsto (kk ∘ phi) atTop atTop := hkk_tend.comp hphi.tendsto_atTop
  have ha : a ∈ directionalSubdifferential (liftRealtoEReal f) x := by
    apply aux_mem_of_subgrad f hfc x a
    intro z
    have h1 : Tendsto (fun n => fk (kk (phi n)) z) atTop (𝓝 (f z)) := (hf_pointwise z).comp hphit
    have h2 : Tendsto (fun n => fk (kk (phi n)) (xk (kk (phi n))) +
        inner ℝ (s (phi n)) (z - xk (kk (phi n)))) atTop (𝓝 (f x + inner ℝ a (z - x))) := by
      apply Tendsto.add (hconv.comp hphit)
      apply Tendsto.inner hlim
      exact tendsto_const_nhds.sub (hx_limit.comp hphit)
    exact le_of_tendsto_of_tendsto' h2 h1
      (fun n => aux_subgrad_of_mem _ (hf_convex _) _ _ (hs (phi n)) z)
  have hev : ∀ᶠ n in atTop, dist (s (phi n)) a < eps := (Metric.tendsto_nhds.mp hlim) eps heps
  obtain ⟨n, hn⟩ := hev.exists
  apply hns (phi n)
  exact (show ∃ w d, ‖d‖ ≤ eps ∧ w ∈ directionalSubdifferential (liftRealtoEReal f) x ∧
      s (phi n) = w + d from ⟨a, s (phi n) - a, by rw [← dist_eq_norm]; exact hn.le, ha, by abel⟩)

end FCA_chap_D_6_2_7
