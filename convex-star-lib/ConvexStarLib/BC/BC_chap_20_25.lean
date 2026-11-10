import ConvexStarLib.Defs

/-!
# `BC_chap_20_25`

Source: Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces.

Statement from the `convex-eval-v28-2h/BC_chap_20_25` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace BC_chap_20_25`, so the main result is `BC_chap_20_25.BC_chap_20_25`.
-/

namespace BC_chap_20_25

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem BC_chap_20_25
    (f : E → EReal)
    (hf : IsProperLSCConvex f) :
    IsMaximalMonotone (convexSubdifferential f) := by
  obtain ⟨⟨hbot, x₀, hx₀⟩, hlsc, hconv⟩ := hf
  have hx₀' : f x₀ < ⊤ := hx₀
  obtain ⟨F, hF⟩ : ∃ F : E → ℝ, ∀ x, f x < ⊤ → f x = (F x : EReal) :=
    ⟨fun x => (f x).toReal, fun x hx => (EReal.coe_toReal hx.ne (hbot x).ne').symm⟩
  -- subgradients only exist at points of the effective domain
  have hdom_of_sub : ∀ x s, s ∈ convexSubdifferential f x → f x < ⊤ := by
    intro x s hs
    by_contra hx
    rw [not_lt_top_iff] at hx
    have h1 : f x + ((inner ℝ s (x₀ - x) : ℝ) : EReal) ≤ f x₀ := hs x₀
    rw [hx, EReal.top_add_coe] at h1
    exact absurd (top_le_iff.1 h1) hx₀'.ne
  -- real-valued description of the subdifferential
  have hsub_iff : ∀ x s, f x < ⊤ → (s ∈ convexSubdifferential f x ↔
      ∀ y, f y < ⊤ → F x + inner ℝ s (y - x) ≤ F y) := by
    intro x s hx
    constructor
    · intro hs y hy
      have h1 : f x + ((inner ℝ s (y - x) : ℝ) : EReal) ≤ f y := hs y
      rw [hF x hx, hF y hy, ← EReal.coe_add] at h1
      exact EReal.coe_le_coe_iff.1 h1
    · intro h y
      show f x + ((inner ℝ s (y - x) : ℝ) : EReal) ≤ f y
      by_cases hy : f y < ⊤
      · rw [hF x hx, hF y hy, ← EReal.coe_add]
        exact EReal.coe_le_coe_iff.2 (h y hy)
      · rw [not_lt_top_iff.1 hy]
        exact le_top
  -- convexity inequality on the domain
  have hcvx : ∀ x y, f x < ⊤ → f y < ⊤ → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      f ((1 - t) • x + t • y) < ⊤ ∧ F ((1 - t) • x + t • y) ≤ (1 - t) * F x + t * F y := by
    intro x y hx hy t ht0 ht1
    have hpx : (x, F x) ∈ epigraph f := by
      show f x ≤ (F x : EReal)
      rw [hF x hx]
    have hpy : (y, F y) ∈ epigraph f := by
      show f y ≤ (F y : EReal)
      rw [hF y hy]
    have hconv' : Convex ℝ (epigraph f) := hconv
    have h := hconv' hpx hpy (sub_nonneg.2 ht1) ht0 (sub_add_cancel 1 t)
    have h' : f ((1 - t) • x + t • y) ≤ (((1 - t) * F x + t * F y : ℝ) : EReal) := h
    have hlt : f ((1 - t) • x + t • y) < ⊤ := lt_of_le_of_lt h' (EReal.coe_lt_top _)
    refine ⟨hlt, ?_⟩
    rw [hF _ hlt] at h'
    exact EReal.coe_le_coe_iff.1 h'
  -- a lower bound of the form `c - L ‖y - x₀‖`
  obtain ⟨c, L, hL0, hL⟩ : ∃ c L : ℝ, 0 ≤ L ∧ ∀ y, f y < ⊤ → c - L * ‖y - x₀‖ ≤ F y := by
    have h1 : (((F x₀ - 1 : ℝ)) : EReal) < f x₀ := by
      rw [hF x₀ hx₀']
      exact EReal.coe_lt_coe_iff.2 (by linarith)
    have h2 := lowerSemicontinuousAt_iff.1 (lowerSemicontinuous_iff.1 hlsc x₀) _ h1
    obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.1 h2
    refine ⟨F x₀ - 1, 2 / δ, by positivity, fun y hy => ?_⟩
    by_cases hyx : ‖y - x₀‖ < δ
    · have h3 := hball (by rwa [dist_eq_norm])
      rw [hF y hy] at h3
      have h4 := EReal.coe_lt_coe_iff.1 h3
      have : 0 ≤ 2 / δ * ‖y - x₀‖ := by positivity
      linarith
    · push_neg at hyx
      have hr : 0 < ‖y - x₀‖ := lt_of_lt_of_le hδ hyx
      set r := ‖y - x₀‖ with hr_def
      have hδ' : δ ≠ 0 := hδ.ne'
      have hr' : r ≠ 0 := hr.ne'
      set t := δ / (2 * r) with ht_def
      have ht0 : 0 < t := by positivity
      have ht1 : t ≤ 1 := by
        rw [ht_def, div_le_one (by positivity)]
        linarith
      obtain ⟨hw, hw'⟩ := hcvx x₀ y hx₀' hy t ht0.le ht1
      have htr : t * r = δ / 2 := by
        rw [ht_def]; field_simp
      have hdist : dist ((1 - t) • x₀ + t • y) x₀ < δ := by
        rw [dist_eq_norm]
        have : (1 - t) • x₀ + t • y - x₀ = t • (y - x₀) := by
          rw [smul_sub, sub_smul, one_smul]; abel
        rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, ← hr_def, htr]
        linarith
      have h3 := hball hdist
      rw [hF _ hw] at h3
      have h4 := EReal.coe_lt_coe_iff.1 h3
      have h5 : t * (F x₀ - F y) < 1 := by nlinarith
      have h6 : 2 / δ * r * t = 1 := by
        rw [ht_def]; field_simp
      nlinarith
  -- existence of a proximal point
  have hprox : ∀ z : E, ∃ p, f p < ⊤ ∧
      ∀ y, f y < ⊤ → F p + ‖p - z‖ ^ 2 / 2 ≤ F y + ‖y - z‖ ^ 2 / 2 := by
    intro z
    set S : Set ℝ := (fun y => F y + ‖y - z‖ ^ 2 / 2) '' {y | f y < ⊤} with hS
    have hSne : S.Nonempty := ⟨_, x₀, hx₀', rfl⟩
    have hSbdd : BddBelow S := by
      refine ⟨c - L * ‖z - x₀‖ - L ^ 2 / 2, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      have h1 := hL y hy
      have h2 : ‖y - x₀‖ ≤ ‖y - z‖ + ‖z - x₀‖ := by
        calc ‖y - x₀‖ = ‖(y - z) + (z - x₀)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖y - z‖ + ‖z - x₀‖ := norm_add_le _ _
      nlinarith [sq_nonneg (‖y - z‖ - L), mul_le_mul_of_nonneg_left h2 hL0]
    set μ := sInf S with hμ
    have hμle : ∀ y, f y < ⊤ → μ ≤ F y + ‖y - z‖ ^ 2 / 2 :=
      fun y hy => csInf_le hSbdd ⟨y, hy, rfl⟩
    have hseq : ∀ n : ℕ, ∃ y, f y < ⊤ ∧ F y + ‖y - z‖ ^ 2 / 2 < μ + 1 / ((n : ℝ) + 1) := by
      intro n
      have : μ < μ + 1 / ((n : ℝ) + 1) := lt_add_of_pos_right _ Nat.one_div_pos_of_nat
      obtain ⟨_, ⟨y, hy, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hSne this
      exact ⟨y, hy, hlt⟩
    choose u hu hu' using hseq
    have hmid : ∀ a b, f a < ⊤ → f b < ⊤ →
        ‖a - b‖ ^ 2 ≤ 4 * (F a + ‖a - z‖ ^ 2 / 2 - μ) + 4 * (F b + ‖b - z‖ ^ 2 / 2 - μ) := by
      intro a b ha hb
      obtain ⟨hm, hm'⟩ := hcvx a b ha hb (1 / 2) (by norm_num) (by norm_num)
      have h1 := hμle _ hm
      have h2 : ‖(1 - 1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b - z‖ ^ 2
          = ‖a - z‖ ^ 2 / 2 + ‖b - z‖ ^ 2 / 2 - ‖a - b‖ ^ 2 / 4 := by
        have e : (1 - 1 / 2 : ℝ) • a + (1 / 2 : ℝ) • b - z = (1 / 2 : ℝ) • ((a - z) + (b - z)) := by
          module
        have hp := parallelogram_law_with_norm ℝ (a - z) (b - z)
        have e2 : (a - z) - (b - z) = a - b := sub_sub_sub_cancel_right a b z
        rw [e2] at hp
        rw [e, norm_smul, mul_pow, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
        linear_combination (1 / 4 : ℝ) * hp
      rw [h2] at h1
      norm_num at hm'
      linarith
    have hcauchy : CauchySeq u := by
      refine cauchySeq_of_le_tendsto_0 (fun N : ℕ => Real.sqrt (8 * (1 / ((N : ℝ) + 1)))) ?_ ?_
      · intro n m N hn hm
        rw [dist_eq_norm]
        have h1 := hmid (u n) (u m) (hu n) (hu m)
        have h2 := hu' n
        have h3 := hu' m
        have h4 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hn
        have h5 : 1 / ((m : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := Nat.one_div_le_one_div hm
        rw [← Real.sqrt_sq (norm_nonneg (u n - u m))]
        apply Real.sqrt_le_sqrt
        linarith
      · have h : Filter.Tendsto (fun N : ℕ => 8 * (1 / ((N : ℝ) + 1))) Filter.atTop (𝓝 (8 * 0)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.const_mul 8
        rw [mul_zero] at h
        have h' := h.sqrt
        rwa [Real.sqrt_zero] at h'
    obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hcauchy
    have hpμ : f p ≤ ((μ - ‖p - z‖ ^ 2 / 2 : ℝ) : EReal) := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨c', hc'1, hc'2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
      have hc'1' : μ - ‖p - z‖ ^ 2 / 2 < c' := EReal.coe_lt_coe_iff.1 hc'1
      have ev1 : ∀ᶠ n in Filter.atTop, (c' : EReal) < f (u n) :=
        hp.eventually (lowerSemicontinuousAt_iff.1 (lowerSemicontinuous_iff.1 hlsc p) _ hc'2)
      have hcont : Filter.Tendsto (fun n => ‖u n - z‖ ^ 2 / 2) Filter.atTop (𝓝 (‖p - z‖ ^ 2 / 2)) :=
        ((hp.sub_const z).norm.pow 2).div_const 2
      have ev2 : ∀ᶠ n in Filter.atTop,
          ‖p - z‖ ^ 2 / 2 - (c' - (μ - ‖p - z‖ ^ 2 / 2)) / 2 < ‖u n - z‖ ^ 2 / 2 :=
        hcont.eventually (lt_mem_nhds (by linarith))
      have ev3 : ∀ᶠ n : ℕ in Filter.atTop, 1 / ((n : ℝ) + 1) < (c' - (μ - ‖p - z‖ ^ 2 / 2)) / 2 :=
        tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds (by linarith))
      obtain ⟨n, h1, h2, h3⟩ := (ev1.and (ev2.and ev3)).exists
      rw [hF _ (hu n)] at h1
      have h1' := EReal.coe_lt_coe_iff.1 h1
      have h4 := hu' n
      linarith
    have hpdom : f p < ⊤ := lt_of_le_of_lt hpμ (EReal.coe_lt_top _)
    rw [hF p hpdom] at hpμ
    have hpμ' := EReal.coe_le_coe_iff.1 hpμ
    exact ⟨p, hpdom, fun y hy => by linarith [hμle y hy]⟩
  -- optimality condition for the proximal point
  have hopt : ∀ z p, f p < ⊤ →
      (∀ y, f y < ⊤ → F p + ‖p - z‖ ^ 2 / 2 ≤ F y + ‖y - z‖ ^ 2 / 2) →
      z - p ∈ convexSubdifferential f p := by
    intro z p hp hmin
    rw [hsub_iff p (z - p) hp]
    intro y hy
    by_contra hcon
    push_neg at hcon
    have hK0 : 0 ≤ ‖y - p‖ ^ 2 := by positivity
    have key : ∀ t : ℝ, 0 < t → t ≤ 1 →
        t * (F p + inner ℝ (z - p) (y - p) - F y) ≤ t * t * ‖y - p‖ ^ 2 / 2 := by
      intro t ht0 ht1
      obtain ⟨hw, hw'⟩ := hcvx p y hp hy t ht0.le ht1
      have h1 := hmin _ hw
      have e : (1 - t) • p + t • y - z = (p - z) + t • (y - p) := by
        module
      have h2 : ‖(1 - t) • p + t • y - z‖ ^ 2
          = ‖p - z‖ ^ 2 - 2 * t * inner ℝ (z - p) (y - p) + t * t * ‖y - p‖ ^ 2 := by
        rw [e, norm_add_sq_real, inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0,
          mul_pow]
        have h3 : inner ℝ (p - z) (y - p) = - inner ℝ (z - p) (y - p) := by
          rw [← inner_neg_left, neg_sub]
        rw [h3]
        ring
      rw [h2] at h1
      nlinarith
    set g := F p + inner ℝ (z - p) (y - p) - F y with hg
    have hg0 : 0 < g := by linarith
    have hK1 : 0 < ‖y - p‖ ^ 2 + 1 := by linarith
    set t := min 1 (g / (‖y - p‖ ^ 2 + 1)) with ht
    have ht0 : 0 < t := lt_min one_pos (div_pos hg0 hK1)
    have ht1 : t ≤ 1 := min_le_left _ _
    have ht2 : t ≤ g / (‖y - p‖ ^ 2 + 1) := min_le_right _ _
    have ht3 : t * (‖y - p‖ ^ 2 + 1) ≤ g := by rwa [le_div_iff₀ hK1] at ht2
    have h := key t ht0 ht1
    nlinarith [mul_le_mul_of_nonneg_left ht3 ht0.le, mul_pos ht0 ht0,
      mul_nonneg (mul_nonneg ht0.le ht0.le) hK0]
  refine ⟨?_, ?_⟩
  · intro a b va vb ha hb
    have hadom := hdom_of_sub a va ha
    have hbdom := hdom_of_sub b vb hb
    have h1 := (hsub_iff a va hadom).1 ha b hbdom
    have h2 := (hsub_iff b vb hbdom).1 hb a hadom
    have e1 : inner ℝ (vb - va) (b - a) = inner ℝ vb (b - a) - inner ℝ va (b - a) :=
      inner_sub_left _ _ _
    have e2 : inner ℝ vb (a - b) = - inner ℝ vb (b - a) := by
      rw [← inner_neg_right, neg_sub]
    rw [e1]
    linarith
  · intro xh vh hnot
    obtain ⟨p, hp, hmin⟩ := hprox (xh + vh)
    have hsub := hopt (xh + vh) p hp hmin
    refine ⟨p, xh + vh - p, hsub, ?_⟩
    have hne : xh ≠ p := by
      rintro rfl
      apply hnot
      simpa using hsub
    have e : vh - (xh + vh - p) = -(xh - p) := by abel
    rw [e, inner_neg_left, real_inner_self_eq_norm_sq]
    have : 0 < ‖xh - p‖ := norm_pos_iff.2 (sub_ne_zero.2 hne)
    nlinarith

end BC_chap_20_25
