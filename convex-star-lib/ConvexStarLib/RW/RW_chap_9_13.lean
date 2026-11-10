import ConvexStarLib.Defs

/-!
# `RW_chap_9_13`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_9_13` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_9_13`, so the main result is `RW_chap_9_13.RW_chap_9_13`.
-/

namespace RW_chap_9_13

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Auxiliary lemmas -/

lemma norm_add_le_quad (a h : E) (ha : a ≠ 0) (hh : ‖h‖ ≤ ‖a‖ / 2) :
    ‖a + h‖ ≤ ‖a‖ + inner ℝ a h / ‖a‖ + ‖h‖ ^ 2 / ‖a‖ := by
  have hd : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hs : |inner ℝ a h| ≤ ‖a‖ * ‖h‖ := abs_real_inner_le_norm a h
  have hsq : ‖a + h‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a h + ‖h‖ ^ 2 := norm_add_sq_real a h
  have hR : ‖a‖ + inner ℝ a h / ‖a‖ + ‖h‖ ^ 2 / ‖a‖
      = (‖a‖ ^ 2 + inner ℝ a h + ‖h‖ ^ 2) / ‖a‖ := by
    field_simp
  rw [hR]
  have hnum : 0 ≤ ‖a‖ ^ 2 + inner ℝ a h + ‖h‖ ^ 2 := by
    have h1 := neg_abs_le (inner ℝ a h)
    have h2 : ‖a‖ * ‖h‖ ≤ ‖a‖ * (‖a‖ / 2) := mul_le_mul_of_nonneg_left hh hd.le
    nlinarith [norm_nonneg h, sq_nonneg ‖h‖]
  have hRnn : 0 ≤ (‖a‖ ^ 2 + inner ℝ a h + ‖h‖ ^ 2) / ‖a‖ := div_nonneg hnum hd.le
  rw [← pow_le_pow_iff_left₀ (norm_nonneg _) hRnn two_ne_zero, hsq, div_pow,
    le_div_iff₀ (by positivity)]
  nlinarith [sq_nonneg (inner ℝ a h + ‖h‖ ^ 2), sq_nonneg (‖a‖ * ‖h‖)]

lemma regsub_of_quad (f : E → EReal) (x0 ζ : E) (C : ℝ)
    (hfin : ⊥ < f x0 ∧ f x0 < ⊤) (V : Set E) (hV : V ∈ 𝓝 x0)
    (h : ∀ x ∈ V, f x0 + (((inner ℝ ζ (x - x0) - C * ‖x - x0‖ ^ 2 : ℝ)) : EReal) ≤ f x) :
    IsRegularSubgradientAt f x0 ζ := by
  refine ⟨hfin.1, hfin.2, fun x => -(C * ‖x - x0‖ ^ 2), ?_, V, hV, ?_⟩
  · rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hpos : 0 < c / (|C| + 1) := by positivity
    filter_upwards [Metric.ball_mem_nhds x0 hpos] with x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have ht : 0 ≤ ‖x - x0‖ := norm_nonneg _
    have h1 : ‖x - x0‖ * (|C| + 1) < c := by
      rwa [lt_div_iff₀ (by positivity)] at hx
    have h2 : |C| * ‖x - x0‖ ≤ c := by nlinarith [abs_nonneg C]
    have e1 : ‖-(C * ‖x - x0‖ ^ 2)‖ = |C| * ‖x - x0‖ ^ 2 := by
      rw [norm_neg, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg ht 2)]
    rw [e1, norm_norm]
    calc |C| * ‖x - x0‖ ^ 2 = (|C| * ‖x - x0‖) * ‖x - x0‖ := by ring
      _ ≤ c * ‖x - x0‖ := mul_le_mul_of_nonneg_right h2 ht
  · intro x hx
    have e : inner ℝ ζ (x - x0) + -(C * ‖x - x0‖ ^ 2)
        = inner ℝ ζ (x - x0) - C * ‖x - x0‖ ^ 2 := by ring
    show f x0 + (((inner ℝ ζ (x - x0) + -(C * ‖x - x0‖ ^ 2)) : ℝ) : EReal) ≤ f x
    rw [e]
    exact h x hx

lemma MIN_sub_lt_of_lt_add (a : EReal) (β t : ℝ) (h : (β : EReal) < a + (t : EReal)) :
    ((β - t : ℝ) : EReal) < a := by
  induction a with
  | bot => simp at h
  | top => exact EReal.coe_lt_top _
  | coe r =>
    rw [← EReal.coe_add] at h
    have h' : β < r + t := by exact_mod_cast h
    exact_mod_cast (by linarith : β - t < r)

lemma exists_min_localLsc (f : E → EReal) (x_bar : E) (ε : ℝ)
    (hε : ∀ α : ℝ, (α : EReal) ≤ f x_bar + (ε : EReal) →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)})
    (S : Set E) (hS : IsCompact S) (hSsub : S ⊆ Metric.closedBall x_bar ε)
    (g : E → ℝ) (hg : Continuous g) (hg0 : ∀ x ∈ S, 0 ≤ g x)
    (y : E) (hy : y ∈ S) (hfy : f y + ((g y : ℝ) : EReal) < f x_bar + (ε : EReal)) :
    ∃ x ∈ S, ∀ x' ∈ S, f x + ((g x : ℝ) : EReal) ≤ f x' + ((g x' : ℝ) : EReal) := by
  let Φ : E → EReal := fun x => f x + ((g x : ℝ) : EReal)
  let c : EReal := Φ y
  let L : EReal := f x_bar + (ε : EReal)
  have hcL : c < L := hfy
  let Ψ : E → EReal := fun x => min (Φ x) c
  have hlsc : LowerSemicontinuousOn Ψ S := by
    intro x hx b hb
    have hb1 : b < Φ x := lt_of_lt_of_le hb (min_le_left _ _)
    have hb2 : b < c := lt_of_lt_of_le hb (min_le_right _ _)
    have hbL : b < L := hb2.trans hcL
    obtain ⟨β, hbβ, hβ⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_min hb1 hbL)
    have hβΦ : (β : EReal) < Φ x := lt_of_lt_of_le hβ (min_le_left _ _)
    have hβL : (β : EReal) < L := lt_of_lt_of_le hβ (min_le_right _ _)
    have h1 : ((β - g x : ℝ) : EReal) < f x := MIN_sub_lt_of_lt_add (f x) β (g x) hβΦ
    have h2 : ((β - g x : ℝ) : EReal) < L := by
      have h3 : ((β - g x : ℝ) : EReal) ≤ (β : EReal) := by
        exact_mod_cast (by linarith [hg0 x hx] : β - g x ≤ β)
      exact lt_of_le_of_lt h3 hβL
    obtain ⟨α, hα1, hα2⟩ := EReal.lt_iff_exists_real_btwn.mp (lt_min h1 h2)
    have hαf : (α : EReal) < f x := lt_of_lt_of_le hα2 (min_le_left _ _)
    have hαL : (α : EReal) ≤ L := (lt_of_lt_of_le hα2 (min_le_right _ _)).le
    have hα1' : β - g x < α := by exact_mod_cast hα1
    have hT := hε α hαL
    have hxT : x ∉ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)} := by
      rintro ⟨_, h⟩
      exact absurd h (not_le.mpr hαf)
    have hev1 : ∀ᶠ x' in 𝓝 x,
        x' ∉ {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)} :=
      hT.isOpen_compl.mem_nhds hxT
    have hev2 : ∀ᶠ x' in 𝓝 x, β - α < g x' :=
      (hg.tendsto x).eventually (lt_mem_nhds (by linarith))
    filter_upwards [nhdsWithin_le_nhds hev1, nhdsWithin_le_nhds hev2, self_mem_nhdsWithin]
      with x' h1' h2' h3'
    have hfx' : (α : EReal) < f x' := by
      by_contra hcon
      exact h1' ⟨hSsub h3', not_lt.mp hcon⟩
    have h5 : (α : EReal) + ((g x' : ℝ) : EReal) < f x' + ((g x' : ℝ) : EReal) :=
      EReal.add_lt_add_right_coe hfx' _
    have h4 : (β : EReal) ≤ (α : EReal) + ((g x' : ℝ) : EReal) := by
      rw [← EReal.coe_add]
      exact_mod_cast (by linarith : β ≤ α + g x')
    exact lt_min (lt_of_lt_of_le hbβ (h4.trans h5.le)) hb2
  obtain ⟨x0, hx0, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn ⟨y, hy⟩ hS hlsc
  rw [isMinOn_iff] at hmin
  by_cases hcase : Φ x0 ≤ c
  · refine ⟨x0, hx0, fun x' hx' => ?_⟩
    have h2 : Ψ x0 = Φ x0 := min_eq_left hcase
    calc Φ x0 = Ψ x0 := h2.symm
      _ ≤ Ψ x' := hmin x' hx'
      _ ≤ Φ x' := min_le_left _ _
  · push_neg at hcase
    refine ⟨y, hy, fun x' hx' => ?_⟩
    have h2 : Ψ x0 = c := min_eq_right hcase.le
    calc Φ y = c := rfl
      _ = Ψ x0 := h2.symm
      _ ≤ Ψ x' := hmin x' hx'
      _ ≤ Φ x' := min_le_left _ _

lemma KL_g_ineq (a h : E) (K' M : ℝ) (ha : a ≠ 0) (hh : ‖h‖ ≤ ‖a‖ / 2) (hK'0 : 0 ≤ K') :
    K' * ‖a + h‖ + M * ‖a + h‖ ^ 2 ≤ K' * ‖a‖ + M * ‖a‖ ^ 2
      + (K' / ‖a‖ + 2 * M) * inner ℝ a h + (K' / ‖a‖ + M) * ‖h‖ ^ 2 := by
  have hq := norm_add_le_quad a h ha hh
  have e1 : K' * ‖a + h‖ ≤ K' * (‖a‖ + inner ℝ a h / ‖a‖ + ‖h‖ ^ 2 / ‖a‖) :=
    mul_le_mul_of_nonneg_left hq hK'0
  have e2 : ‖a + h‖ ^ 2 = ‖a‖ ^ 2 + 2 * inner ℝ a h + ‖h‖ ^ 2 := norm_add_sq_real a h
  calc K' * ‖a + h‖ + M * ‖a + h‖ ^ 2
      ≤ K' * (‖a‖ + inner ℝ a h / ‖a‖ + ‖h‖ ^ 2 / ‖a‖)
          + M * (‖a‖ ^ 2 + 2 * inner ℝ a h + ‖h‖ ^ 2) := by
        rw [e2]; linarith [e1]
    _ = K' * ‖a‖ + M * ‖a‖ ^ 2
          + (K' / ‖a‖ + 2 * M) * inner ℝ a h + (K' / ‖a‖ + M) * ‖h‖ ^ 2 := by ring

lemma KL_min_regsub (f : E → EReal) (xs z : E) (c K' M δ : ℝ) (hc : f xs = (c : EReal))
    (hK'0 : 0 < K') (hM : 0 ≤ M) (hxz : xs ≠ z) (hδ : 0 < δ)
    (hmin : ∀ x ∈ Metric.ball xs δ,
      f xs + (((K' * ‖xs - z‖ + M * ‖xs - z‖ ^ 2 : ℝ)) : EReal) ≤
        f x + (((K' * ‖x - z‖ + M * ‖x - z‖ ^ 2 : ℝ)) : EReal)) :
    ∃ ζ ∈ regularSubdifferential f xs, K' ≤ ‖ζ‖ := by
  have ha : xs - z ≠ 0 := sub_ne_zero.mpr hxz
  have hd : 0 < ‖xs - z‖ := norm_pos_iff.mpr ha
  have hA : 0 < K' / ‖xs - z‖ + 2 * M := by
    have := div_pos hK'0 hd
    linarith
  refine ⟨-(K' / ‖xs - z‖ + 2 * M) • (xs - z), ?_, ?_⟩
  · refine regsub_of_quad f xs _ (K' / ‖xs - z‖ + M)
      ⟨by rw [hc]; exact EReal.bot_lt_coe c, by rw [hc]; exact EReal.coe_lt_top c⟩
      (Metric.ball xs (min δ (‖xs - z‖ / 2)))
      (Metric.ball_mem_nhds _ (lt_min hδ (half_pos hd))) ?_
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm] at hx
    have hx1 : ‖x - xs‖ < δ := lt_of_lt_of_le hx (min_le_left _ _)
    have hx2 : ‖x - xs‖ ≤ ‖xs - z‖ / 2 := le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
    have hm := hmin x (by rw [Metric.mem_ball, dist_eq_norm]; exact hx1)
    have hxz' : (xs - z) + (x - xs) = x - z := by abel
    have key := KL_g_ineq (xs - z) (x - xs) K' M ha hx2 hK'0.le
    rw [hxz'] at key
    rw [real_inner_smul_left, hc]
    rw [hc] at hm
    by_cases htop : f x = ⊤
    · rw [htop]; exact le_top
    by_cases hbot : f x = ⊥
    · rw [hbot, EReal.bot_add, le_bot_iff, ← EReal.coe_add] at hm
      exact absurd hm (EReal.coe_ne_bot _)
    obtain ⟨e, he⟩ : ∃ e : ℝ, f x = e := ⟨_, (EReal.coe_toReal htop hbot).symm⟩
    rw [he] at hm ⊢
    have hm' : c + (K' * ‖xs - z‖ + M * ‖xs - z‖ ^ 2) ≤
        e + (K' * ‖x - z‖ + M * ‖x - z‖ ^ 2) := by
      exact_mod_cast hm
    rw [← EReal.coe_add]
    exact_mod_cast (by linarith : c + (-(K' / ‖xs - z‖ + 2 * M) * inner ℝ (xs - z) (x - xs)
      - (K' / ‖xs - z‖ + M) * ‖x - xs‖ ^ 2) ≤ e)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hA, add_mul,
      div_mul_cancel₀ _ hd.ne']
    have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hM) hd.le
    linarith

lemma KL_claim (f : E → EReal) (x_bar : E) (ε : ℝ)
    (hεc : ∀ α : ℝ, (α : EReal) ≤ f x_bar + (ε : EReal) →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)})
    (m : ℝ) (hm : f x_bar = (m : EReal))
    (η₁ : ℝ) (_hη₁ : 0 < η₁) (hη₁ε : η₁ ≤ ε)
    (K K' : ℝ) (hK' : K < K') (hK'0 : 0 < K')
    (hK₁ : ∀ x : E, ‖x - x_bar‖ < η₁ → ((m - η₁ : ℝ) : EReal) < f x →
      f x < ((m + η₁ : ℝ) : EReal) → ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K)
    (ρ₁ : ℝ) (hρ₁ε : ρ₁ ≤ ε)
    (hlow : ∀ x : E, ‖x - x_bar‖ < ρ₁ → ((m - η₁ / 4 : ℝ) : EReal) < f x)
    (R M : ℝ) (hR : 0 < R) (hM : 0 ≤ M) (hMR : M * R ^ 2 = η₁)
    (hR1 : 3 * R ≤ ρ₁) (hR2 : 3 * R ≤ η₁) (hR3 : 8 * (K' * R) ≤ η₁)
    (y z : E) (hy : ‖y - x_bar‖ < R / 4) (hz : ‖z - x_bar‖ < R / 4)
    (b : ℝ) (hb : f y = (b : EReal)) (hb2 : b ≤ m + η₁ / 4) :
    f z ≤ ((b + K' * ‖z - y‖ + M * ‖z - y‖ ^ 2 : ℝ) : EReal) := by
  by_contra hcon
  rw [not_le] at hcon
  have hK'R : 0 < K' * R := mul_pos hK'0 hR
  obtain ⟨g, hg_def⟩ : ∃ g : E → ℝ, g = fun x => K' * ‖x - z‖ + M * ‖x - z‖ ^ 2 := ⟨_, rfl⟩
  have hgx : ∀ x, g x = K' * ‖x - z‖ + M * ‖x - z‖ ^ 2 := fun x => by rw [hg_def]
  have hg_cont : Continuous g := by rw [hg_def]; fun_prop
  have hg0 : ∀ x, 0 ≤ g x := fun x => by rw [hgx]; positivity
  have hyz : ‖y - z‖ < R / 2 := by
    calc ‖y - z‖ = ‖(y - x_bar) - (z - x_bar)‖ := by congr 1; abel
      _ ≤ ‖y - x_bar‖ + ‖z - x_bar‖ := norm_sub_le _ _
      _ < R / 4 + R / 4 := add_lt_add hy hz
      _ = R / 2 := by ring
  have hS : IsCompact (Metric.closedBall z R) := isCompact_closedBall z R
  have hSball : ∀ x ∈ Metric.closedBall z R, ‖x - x_bar‖ < 2 * R := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm] at hx
    calc ‖x - x_bar‖ = ‖(x - z) + (z - x_bar)‖ := by congr 1; abel
      _ ≤ ‖x - z‖ + ‖z - x_bar‖ := norm_add_le _ _
      _ < R + R / 4 := by linarith
      _ ≤ 2 * R := by linarith
  have hSsub : Metric.closedBall z R ⊆ Metric.closedBall x_bar ε := by
    intro x hx
    rw [Metric.mem_closedBall, dist_eq_norm]
    linarith [hSball x hx]
  have hyS : y ∈ Metric.closedBall z R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; linarith
  have hgy : g y ≤ η₁ / 4 + η₁ / 16 := by
    rw [hgx]
    have h1 : K' * ‖y - z‖ ≤ K' * (R / 2) := mul_le_mul_of_nonneg_left hyz.le hK'0.le
    have h2 : ‖y - z‖ ^ 2 ≤ (R / 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hyz.le 2
    have h3 : M * ‖y - z‖ ^ 2 ≤ M * (R / 2) ^ 2 := mul_le_mul_of_nonneg_left h2 hM
    have h4 : M * (R / 2) ^ 2 = η₁ / 4 := by rw [← hMR]; ring
    linarith
  have hfy : f y + ((g y : ℝ) : EReal) < f x_bar + (ε : EReal) := by
    rw [hb, hm, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_lt_coe_iff]
    linarith
  obtain ⟨xs, hxsS, hmin⟩ := exists_min_localLsc f x_bar ε hεc (Metric.closedBall z R) hS
    hSsub g hg_cont (fun x _ => hg0 x) y hyS hfy
  have hxs_low := hlow xs (by linarith [hSball xs hxsS])
  have hxs_le := hmin y hyS
  have hxs_top : f xs ≠ ⊤ := by
    intro h
    rw [h, hb, EReal.top_add_coe, top_le_iff, ← EReal.coe_add] at hxs_le
    exact EReal.coe_ne_top _ hxs_le
  have hxs_bot : f xs ≠ ⊥ := ne_bot_of_gt hxs_low
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f xs = c := ⟨_, (EReal.coe_toReal hxs_top hxs_bot).symm⟩
  rw [hc, hb] at hxs_le
  have hxs_le' : c + g xs ≤ b + g y := by exact_mod_cast hxs_le
  rw [hc] at hxs_low
  have hxs_low' : m - η₁ / 4 < c := by exact_mod_cast hxs_low
  have hxsz : xs ≠ z := by
    intro hxz
    have hfz : f z = (c : EReal) := by rw [← hxz]; exact hc
    rw [hfz] at hcon
    have h1 : b + K' * ‖z - y‖ + M * ‖z - y‖ ^ 2 < c := by exact_mod_cast hcon
    have hgxs : g xs = 0 := by rw [hgx, hxz]; simp
    have hgy' : g y = K' * ‖z - y‖ + M * ‖z - y‖ ^ 2 := by rw [hgx, norm_sub_rev]
    linarith
  have hxsR : ‖xs - z‖ < R := by
    by_contra hge
    rw [not_lt] at hge
    have h1 : K' * R ≤ K' * ‖xs - z‖ := mul_le_mul_of_nonneg_left hge hK'0.le
    have h2 : R ^ 2 ≤ ‖xs - z‖ ^ 2 := pow_le_pow_left₀ hR.le hge 2
    have h3 : M * R ^ 2 ≤ M * ‖xs - z‖ ^ 2 := mul_le_mul_of_nonneg_left h2 hM
    have h4 := hgx xs
    linarith
  obtain ⟨ζ, hζ, hζK'⟩ := KL_min_regsub f xs z c K' M (R - ‖xs - z‖) hc hK'0 hM hxsz
    (by linarith) (by
      intro x hx
      have hxS : x ∈ Metric.closedBall z R := by
        rw [Metric.mem_ball, dist_eq_norm] at hx
        rw [Metric.mem_closedBall, dist_eq_norm]
        calc ‖x - z‖ = ‖(x - xs) + (xs - z)‖ := by congr 1; abel
          _ ≤ ‖x - xs‖ + ‖xs - z‖ := norm_add_le _ _
          _ ≤ R := by linarith
      have := hmin x hxS
      rw [hgx, hgx] at this
      exact this)
  have hζK := hK₁ xs (by linarith [hSball xs hxsS])
    (by rw [hc]; exact_mod_cast (by linarith : m - η₁ < c))
    (by rw [hc]; exact_mod_cast (by linarith [hg0 xs] : c < m + η₁)) ζ hζ
  linarith

lemma key_lemma (f : E → EReal) (x_bar : E) (hf_lsc : LocalLscAt f x_bar)
    (η K : ℝ) (hη : 0 < η)
    (hK : ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K)
    (K' : ℝ) (hK' : K < K') (hK'0 : 0 < K') :
    ∃ r > (0:ℝ), ∃ M : ℝ, 0 ≤ M ∧
      (∀ y ∈ Metric.ball x_bar r, f y ≠ ⊤ ∧ f y ≠ ⊥) ∧
      (∀ y ∈ Metric.ball x_bar r, ∀ z ∈ Metric.ball x_bar r,
        (f z).toReal ≤ (f y).toReal + K' * ‖z - y‖ + M * ‖z - y‖ ^ 2) := by
  obtain ⟨hbot, htop, ε, hε⟩ := hf_lsc
  obtain ⟨m, hm⟩ : ∃ m : ℝ, f x_bar = (m : EReal) :=
    ⟨_, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  have hmt : (f x_bar).toReal = m := by rw [hm, EReal.toReal_coe]
  rw [hmt] at hK
  have hεpos : 0 < ε := (hε (m + ε) (le_of_eq (by rw [hm, EReal.coe_add]))).1
  have hεc : ∀ α : ℝ, (α : EReal) ≤ f x_bar + (ε : EReal) →
      IsClosed {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ (α : EReal)} :=
    fun α hα => (hε α hα).2
  obtain ⟨η₁, hη₁, hη₁η, hη₁ε⟩ : ∃ η₁ : ℝ, 0 < η₁ ∧ η₁ ≤ η ∧ η₁ ≤ ε :=
    ⟨min η ε, lt_min hη hεpos, min_le_left _ _, min_le_right _ _⟩
  have hK₁ : ∀ x : E, ‖x - x_bar‖ < η₁ → ((m - η₁ : ℝ) : EReal) < f x →
      f x < ((m + η₁ : ℝ) : EReal) → ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K := by
    intro x hx h1 h2 v hv
    refine hK x (lt_of_lt_of_le hx hη₁η) ?_ ?_ v hv
    · exact lt_of_le_of_lt (by exact_mod_cast (by linarith : m - η ≤ m - η₁)) h1
    · exact lt_of_lt_of_le h2 (by exact_mod_cast (by linarith : m + η₁ ≤ m + η))
  obtain ⟨ρ₁, hρ₁, hρ₁ε, hlow⟩ : ∃ ρ₁ > (0:ℝ), ρ₁ ≤ ε ∧
      ∀ x : E, ‖x - x_bar‖ < ρ₁ → ((m - η₁ / 4 : ℝ) : EReal) < f x := by
    have hC := hεc (m - η₁ / 4) (by
      rw [hm, ← EReal.coe_add]
      exact_mod_cast (by linarith : m - η₁ / 4 ≤ m + ε))
    have hxb : x_bar ∈
        {x | x ∈ Metric.closedBall x_bar ε ∧ f x ≤ ((m - η₁ / 4 : ℝ) : EReal)}ᶜ := by
      rintro ⟨-, h⟩
      rw [hm] at h
      have : m ≤ m - η₁ / 4 := by exact_mod_cast h
      linarith
    obtain ⟨ρ₀, hρ₀, hball⟩ := Metric.isOpen_iff.mp hC.isOpen_compl x_bar hxb
    refine ⟨min ρ₀ ε, lt_min hρ₀ hεpos, min_le_right _ _, ?_⟩
    intro x hx
    have hx0 : x ∈ Metric.ball x_bar ρ₀ := by
      rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_lt_of_le hx (min_le_left _ _)
    have hxε : x ∈ Metric.closedBall x_bar ε := by
      rw [Metric.mem_closedBall, dist_eq_norm]
      exact le_of_lt (lt_of_lt_of_le hx (min_le_right _ _))
    have h := hball hx0
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_and, not_le] at h
    exact h hxε
  obtain ⟨R, hR, hR1, hR2, hR3⟩ : ∃ R : ℝ, 0 < R ∧ 3 * R ≤ ρ₁ ∧ 3 * R ≤ η₁ ∧
      8 * (K' * R) ≤ η₁ := by
    refine ⟨min (min (ρ₁ / 3) (η₁ / 3)) (η₁ / (8 * K')), ?_, ?_, ?_, ?_⟩
    · exact lt_min (lt_min (by linarith) (by linarith)) (div_pos hη₁ (by linarith))
    · linarith [min_le_left (min (ρ₁ / 3) (η₁ / 3)) (η₁ / (8 * K')),
        min_le_left (ρ₁ / 3) (η₁ / 3)]
    · linarith [min_le_left (min (ρ₁ / 3) (η₁ / 3)) (η₁ / (8 * K')),
        min_le_right (ρ₁ / 3) (η₁ / 3)]
    · have h1 := min_le_right (min (ρ₁ / 3) (η₁ / 3)) (η₁ / (8 * K'))
      have h2 := mul_le_mul_of_nonneg_left h1 hK'0.le
      have hK'ne : K' ≠ 0 := hK'0.ne'
      have h3 : K' * (η₁ / (8 * K')) = η₁ / 8 := by field_simp
      linarith
  obtain ⟨M, hM, hMR⟩ : ∃ M : ℝ, 0 ≤ M ∧ M * R ^ 2 = η₁ :=
    ⟨η₁ / R ^ 2, by positivity, div_mul_cancel₀ η₁ (pow_ne_zero 2 hR.ne')⟩
  have hfin : ∀ z : E, ‖z - x_bar‖ < R / 4 →
      ∃ c : ℝ, f z = (c : EReal) ∧ c ≤ m + η₁ / 4 := by
    intro z hz
    have h1 := KL_claim f x_bar ε hεc m hm η₁ hη₁ hη₁ε K K' hK' hK'0 hK₁ ρ₁ hρ₁ε hlow
      R M hR hM hMR hR1 hR2 hR3 x_bar z (by rw [sub_self, norm_zero]; linarith) hz m hm
      (by linarith)
    have h2 := hlow z (by linarith)
    have htop' : f z ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
    have hbot' : f z ≠ ⊥ := ne_bot_of_gt h2
    obtain ⟨c, hc⟩ : ∃ c : ℝ, f z = (c : EReal) := ⟨_, (EReal.coe_toReal htop' hbot').symm⟩
    refine ⟨c, hc, ?_⟩
    rw [hc] at h1
    have h1' : c ≤ m + K' * ‖z - x_bar‖ + M * ‖z - x_bar‖ ^ 2 := by exact_mod_cast h1
    have h3 : K' * ‖z - x_bar‖ ≤ K' * (R / 4) := mul_le_mul_of_nonneg_left hz.le hK'0.le
    have h4 : ‖z - x_bar‖ ^ 2 ≤ (R / 4) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz.le 2
    have h5 : M * ‖z - x_bar‖ ^ 2 ≤ M * (R / 4) ^ 2 := mul_le_mul_of_nonneg_left h4 hM
    have h6 : M * (R / 4) ^ 2 = η₁ / 16 := by rw [← hMR]; ring
    linarith
  refine ⟨R / 4, by linarith, M, hM, ?_, ?_⟩
  · intro y hy
    rw [Metric.mem_ball, dist_eq_norm] at hy
    obtain ⟨c, hc, -⟩ := hfin y hy
    rw [hc]
    exact ⟨EReal.coe_ne_top c, EReal.coe_ne_bot c⟩
  · intro y hy z hz
    rw [Metric.mem_ball, dist_eq_norm] at hy hz
    obtain ⟨b, hb, hb2⟩ := hfin y hy
    obtain ⟨c, hc, -⟩ := hfin z hz
    have h := KL_claim f x_bar ε hεc m hm η₁ hη₁ hη₁ε K K' hK' hK'0 hK₁ ρ₁ hρ₁ε hlow
      R M hR hM hMR hR1 hR2 hR3 y z hy hz b hb hb2
    rw [hc] at h
    rw [hc, hb, EReal.toReal_coe, EReal.toReal_coe]
    exact_mod_cast h

lemma fatt_imp_lip (f : E → EReal) (x_bar : E) (hf_lsc : LocalLscAt f x_bar)
    (η K : ℝ) (hη : 0 < η)
    (hK : ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K) :
    IsLocallyLipschitzNearEReal f x_bar := by
  have hm0 : 0 ≤ max K 0 := le_max_right K 0
  have hmK : K ≤ max K 0 := le_max_left K 0
  obtain ⟨r, hr, M, hM, hfin, hest⟩ := key_lemma f x_bar hf_lsc η K hη hK (max K 0 + 1)
    (by linarith) (by linarith)
  have hMr : 0 ≤ 2 * M * r := by positivity
  refine ⟨r, hr, max K 0 + 1 + 2 * M * r, ?_, hfin, ?_⟩
  · linarith
  · intro y z hy hz
    have h1 := hest y hy z hz
    have h2 := hest z hz y hy
    have hyz : ‖y - z‖ = ‖z - y‖ := norm_sub_rev y z
    rw [hyz] at h2
    have hdist : dist y z = ‖z - y‖ := by rw [dist_eq_norm, hyz]
    have hy' : ‖y - x_bar‖ < r := by rw [← dist_eq_norm]; exact hy
    have hz' : ‖z - x_bar‖ < r := by rw [← dist_eq_norm]; exact hz
    have hzy : ‖z - y‖ < 2 * r := by
      calc ‖z - y‖ = ‖(z - x_bar) - (y - x_bar)‖ := by congr 1; abel
        _ ≤ ‖z - x_bar‖ + ‖y - x_bar‖ := norm_sub_le _ _
        _ < 2 * r := by linarith
    have hn : 0 ≤ ‖z - y‖ := norm_nonneg _
    have hsq : M * ‖z - y‖ ^ 2 ≤ 2 * M * r * ‖z - y‖ := by
      have h3 : M * ‖z - y‖ * ‖z - y‖ ≤ M * ‖z - y‖ * (2 * r) :=
        mul_le_mul_of_nonneg_left hzy.le (by positivity)
      nlinarith
    rw [smul_eq_mul, hdist, Real.norm_eq_abs, abs_le]
    constructor <;> nlinarith

lemma fatt_imp_lipMod_le (f : E → EReal) (x_bar : E) (hf_lsc : LocalLscAt f x_bar)
    (η K : ℝ) (hη : 0 < η) (hK0 : 0 ≤ K)
    (hK : ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K) :
    lipModulusEReal f x_bar ≤ (K : EReal) := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro κ hκ
  have hκK : K < κ := EReal.coe_lt_coe_iff.mp hκ
  obtain ⟨K', hKK', hK'κ⟩ : ∃ K' : ℝ, K < K' ∧ K' < κ :=
    ⟨(K + κ) / 2, by linarith, by linarith⟩
  have hK'0 : 0 < K' := by linarith
  obtain ⟨r, hr, M, hM, hfin, hest⟩ := key_lemma f x_bar hf_lsc η K hη hK K' hKK' hK'0
  obtain ⟨δ, hδ0, hδr, hδ2⟩ : ∃ δ : ℝ, 0 < δ ∧ δ ≤ r ∧ 2 * (M + 1) * δ ≤ κ - K' := by
    refine ⟨min r ((κ - K') / (2 * (M + 1))), ?_, min_le_left _ _, ?_⟩
    · exact lt_min hr (div_pos (by linarith) (by positivity))
    · have h4 : min r ((κ - K') / (2 * (M + 1))) ≤ (κ - K') / (2 * (M + 1)) :=
        min_le_right _ _
      rw [le_div_iff₀ (by positivity)] at h4
      linarith
  unfold lipModulusEReal
  apply sInf_le
  refine ⟨κ, ⟨by linarith, Metric.ball x_bar δ, Metric.ball_mem_nhds x_bar hδ0, ?_⟩, rfl⟩
  intro x hx y hy
  have hxr : x ∈ Metric.ball x_bar r := Metric.ball_subset_ball hδr hx
  have hyr : y ∈ Metric.ball x_bar r := Metric.ball_subset_ball hδr hy
  obtain ⟨hx1, hx2⟩ := hfin x hxr
  obtain ⟨hy1, hy2⟩ := hfin y hyr
  have hx' : ‖x - x_bar‖ < δ := by rw [← dist_eq_norm]; exact hx
  have hy' : ‖y - x_bar‖ < δ := by rw [← dist_eq_norm]; exact hy
  have hyx : ‖y - x‖ < 2 * δ := by
    calc ‖y - x‖ = ‖(y - x_bar) - (x - x_bar)‖ := by congr 1; abel
      _ ≤ ‖y - x_bar‖ + ‖x - x_bar‖ := norm_sub_le _ _
      _ < 2 * δ := by linarith
  have hn : 0 ≤ ‖y - x‖ := norm_nonneg _
  have h5 : (M + 1) * ‖y - x‖ ≤ κ - K' := by
    have h6 : (M + 1) * ‖y - x‖ ≤ (M + 1) * (2 * δ) :=
      mul_le_mul_of_nonneg_left hyx.le (by linarith)
    linarith
  have hsq : M * ‖y - x‖ ^ 2 ≤ (κ - K') * ‖y - x‖ := by
    have h7 : (M + 1) * ‖y - x‖ * ‖y - x‖ ≤ (κ - K') * ‖y - x‖ :=
      mul_le_mul_of_nonneg_right h5 hn
    nlinarith
  have e1 := hest x hxr y hyr
  have e2 := hest y hyr x hxr
  rw [norm_sub_rev x y] at e2
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal hx1 hx2).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f y = b := ⟨(f y).toReal, (EReal.coe_toReal hy1 hy2).symm⟩
  simp only [ha, hb, EReal.toReal_coe] at e1 e2
  rw [ha, hb]
  refine ⟨⟨a, rfl⟩, ⟨b, rfl⟩, ?_, ?_⟩
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith
  · rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    nlinarith

lemma lip_regsub_bdd (f : E → EReal) (x_bar : E) (ρ β : ℝ)
    (h : IsLipschitzEReal f (Metric.ball x_bar ρ) β) (x : E) (hx : x ∈ Metric.ball x_bar ρ)
    (v : E) (hv : IsRegularSubgradientAt f x v) : ‖v‖ ≤ β := by
  obtain ⟨hβ0, hfin, hlip⟩ := h
  obtain ⟨_, _, r, hr, V, hV, hineq⟩ := hv
  by_cases hv0 : v = 0
  · simp [hv0, hβ0]
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  set u : E := ‖v‖⁻¹ • v with hudef
  have hu : ‖u‖ = 1 := by
    rw [hudef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn.ne']
  have hinner : inner ℝ v u = ‖v‖ := by
    rw [hudef, inner_smul_right, real_inner_self_eq_norm_sq]
    field_simp
  apply _root_.le_of_forall_pos_le_add
  intro c hc
  have hr' := hr.def hc
  have hball : Metric.ball x_bar ρ ∈ 𝓝 x := Metric.isOpen_ball.mem_nhds hx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ V ∧ y ∈ Metric.ball x_bar ρ ∧ ‖r y‖ ≤ c * ‖‖y - x‖‖ := by
    filter_upwards [hV, hball, hr'] with y h1 h2 h3
    exact ⟨h1, h2, h3⟩
  have htend : Filter.Tendsto (fun t : ℝ => x + t • u) (𝓝[>] (0:ℝ)) (𝓝 x) := by
    have : Filter.Tendsto (fun t : ℝ => x + t • u) (𝓝 (0:ℝ)) (𝓝 (x + (0:ℝ) • u)) :=
      ((continuous_const.add (continuous_id.smul continuous_const)).tendsto 0)
    rw [zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hev2 : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ (x + t • u ∈ V ∧ x + t • u ∈ Metric.ball x_bar ρ ∧
      ‖r (x + t • u)‖ ≤ c * ‖‖x + t • u - x‖‖) := by
    filter_upwards [self_mem_nhdsWithin, htend.eventually hev] with t ht1 ht2
    exact ⟨ht1, ht2⟩
  obtain ⟨t, ht0, hyV, hyB, hry⟩ := hev2.exists
  have hyx : x + t • u - x = t • u := by abel
  have hnorm : ‖x + t • u - x‖ = t := by
    rw [hyx, norm_smul, hu, mul_one, Real.norm_eq_abs, abs_of_pos ht0]
  have h1 := hineq (x + t • u) hyV
  obtain ⟨hfx1, hfx2⟩ := hfin x hx
  obtain ⟨hfy1, hfy2⟩ := hfin (x + t • u) hyB
  have hL := hlip (x + t • u) x hyB hx
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal hfx1 hfx2).symm⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, f (x + t • u) = b :=
    ⟨(f (x + t • u)).toReal, (EReal.coe_toReal hfy1 hfy2).symm⟩
  rw [ha, hb] at h1
  rw [ha, hb, EReal.toReal_coe, EReal.toReal_coe] at hL
  have h1' : a + (inner ℝ v (x + t • u - x) + r (x + t • u)) ≤ b := by exact_mod_cast h1
  rw [hyx, inner_smul_right, hinner] at h1'
  rw [norm_norm, hnorm] at hry
  rw [dist_eq_norm, hnorm, smul_eq_mul, Real.norm_eq_abs] at hL
  rw [Real.norm_eq_abs] at hry
  have hrabs : -(c * t) ≤ r (x + t • u) := by
    have := neg_abs_le (r (x + t • u))
    linarith
  have hba : b - a ≤ β * t := by
    have := le_abs_self (b - a)
    linarith
  have key : t * ‖v‖ ≤ t * (β + c) := by nlinarith
  exact le_of_mul_le_mul_left key ht0

lemma regsub_imp_sub (f : E → EReal) (x v : E) (hv : IsRegularSubgradientAt f x v) :
    IsSubgradientAt f x v :=
  ⟨hv.1, hv.2.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds,
    tendsto_const_nhds, fun _ => hv⟩

lemma lip_sub_bdd (f : E → EReal) (x_bar : E) (ρ β : ℝ)
    (h : IsLipschitzEReal f (Metric.ball x_bar ρ) β) (x : E) (hx : x ∈ Metric.ball x_bar ρ)
    (v : E) (hv : IsSubgradientAt f x v) : ‖v‖ ≤ β := by
  obtain ⟨_, _, xs, vs, hxs, _, hvs, hreg⟩ := hv
  have hev : ∀ᶠ n in Filter.atTop, xs n ∈ Metric.ball x_bar ρ :=
    hxs.eventually (Metric.isOpen_ball.mem_nhds hx)
  have hev2 : ∀ᶠ n in Filter.atTop, ‖vs n‖ ≤ β :=
    hev.mono fun n hn => lip_regsub_bdd f x_bar ρ β h (xs n) hn (vs n) (hreg n)
  exact le_of_tendsto hvs.norm hev2

lemma lip_imp_regsub_bdd (f : E → EReal) (x_bar : E) (hL : IsLocallyLipschitzNearEReal f x_bar) :
    IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar := by
  obtain ⟨ρ, hρ, β, hβ⟩ := hL
  refine ⟨Metric.ball x_bar ρ, Metric.ball_mem_nhds x_bar hρ, β + 1, by linarith [hβ.1], ?_⟩
  intro x hx v hv
  have := lip_regsub_bdd f x_bar ρ β hβ x hx v hv
  linarith

lemma lip_imp_sub_bdd (f : E → EReal) (x_bar : E) (hL : IsLocallyLipschitzNearEReal f x_bar) :
    IsLocallyBoundedAt (fun x => subdifferential f x) x_bar := by
  obtain ⟨ρ, hρ, β, hβ⟩ := hL
  refine ⟨Metric.ball x_bar ρ, Metric.ball_mem_nhds x_bar hρ, β + 1, by linarith [hβ.1], ?_⟩
  intro x hx v hv
  have := lip_sub_bdd f x_bar ρ β hβ x hx v hv
  linarith

lemma sub_bdd_imp_regsub_bdd (f : E → EReal) (x_bar : E)
    (h : IsLocallyBoundedAt (fun x => subdifferential f x) x_bar) :
    IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar := by
  obtain ⟨U, hU, R, hR, hb⟩ := h
  exact ⟨U, hU, R, hR, fun x hx v hv => hb x hx v (regsub_imp_sub f x v hv)⟩

lemma regsub_bdd_imp_fatt (f : E → EReal) (x_bar : E)
    (h : IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar) :
    ∃ η > (0:ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K := by
  obtain ⟨U, hU, R, hR, hb⟩ := h
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨η, hη, R, hR.le, ?_⟩
  intro x hx _ _ v hv
  have hxU : x ∈ U := hball (by rw [Metric.mem_ball, dist_eq_norm]; exact hx)
  exact hb x hxU v hv

lemma B_lip_continuousOn (f : E → EReal) (A : Set E) (β : ℝ)
    (h : IsLipschitzEReal f A β) : ContinuousOn (fun y => (f y).toReal) A := by
  obtain ⟨hβ, _, hlip⟩ := h
  have hL : LipschitzOnWith (Real.toNNReal β) (fun y => (f y).toReal) A := by
    apply LipschitzOnWith.of_dist_le_mul
    intro y hy z hz
    rw [Real.dist_eq, Real.coe_toNNReal _ hβ]
    have := hlip y z hy hz
    rwa [Real.norm_eq_abs, smul_eq_mul] at this
  exact hL.continuousOn

lemma lip_tendsto (f : E → EReal) (x_bar : E) (ρ β : ℝ)
    (h : IsLipschitzEReal f (Metric.ball x_bar ρ) β) (x : E) (hx : x ∈ Metric.ball x_bar ρ) :
    Filter.Tendsto f (𝓝 x) (𝓝 (f x)) := by
  have hfin := h.2.1
  have hgx : Filter.Tendsto (fun y => (f y).toReal) (𝓝 x) (𝓝 ((f x).toReal)) :=
    (B_lip_continuousOn f _ β h).continuousAt (Metric.isOpen_ball.mem_nhds hx)
  have hcoe : Filter.Tendsto (fun y => (((f y).toReal : ℝ) : EReal)) (𝓝 x)
      (𝓝 (((f x).toReal : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp hgx
  rw [EReal.coe_toReal (hfin x hx).1 (hfin x hx).2] at hcoe
  refine hcoe.congr' ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact EReal.coe_toReal (hfin y hy).1 (hfin y hy).2

lemma lip_exists_regsub_seq (f : E → EReal) (x_bar : E) (ρ β : ℝ) (hρ : 0 < ρ)
    (h : IsLipschitzEReal f (Metric.ball x_bar ρ) β) :
    ∃ x : ℕ → E, ∃ v : ℕ → E, Filter.Tendsto x Filter.atTop (𝓝 x_bar) ∧
      ∀ n, IsRegularSubgradientAt f (x n) (v n) := by
  have hgcont0 := B_lip_continuousOn f _ β h
  obtain ⟨hβ, hfin, hlip⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : E → ℝ, g = fun y => (f y).toReal := ⟨_, rfl⟩
  have hgcont : ContinuousOn g (Metric.ball x_bar ρ) := by rw [hg]; exact hgcont0
  have hfg : ∀ y ∈ Metric.ball x_bar ρ, f y = (g y : EReal) := by
    intro y hy
    rw [hg]
    exact (EReal.coe_toReal (hfin y hy).1 (hfin y hy).2).symm
  have hglip : ∀ y ∈ Metric.ball x_bar ρ, ∀ z ∈ Metric.ball x_bar ρ,
      |g y - g z| ≤ β * ‖y - z‖ := by
    intro y hy z hz
    have := hlip y z hy hz
    rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm] at this
    rw [hg]
    exact this
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ρ / 2 := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hr_def]; positivity
  have hrρ : r < ρ := by rw [hr_def]; linarith
  have hKsub : Metric.closedBall x_bar r ⊆ Metric.ball x_bar ρ :=
    Metric.closedBall_subset_ball hrρ
  obtain ⟨M, hM_def⟩ : ∃ M : ℝ, M = (β + 1) / r := ⟨_, rfl⟩
  have hMpos : 0 < M := by rw [hM_def]; positivity
  have hMr : M * r = β + 1 := by rw [hM_def]; field_simp
  have hex : ∀ n : ℕ, ∃ y ∈ Metric.closedBall x_bar r,
      IsMinOn (fun z => g z + (((n:ℝ) + 1) * M) * ‖z - x_bar‖ ^ 2)
        (Metric.closedBall x_bar r) y := by
    intro n
    apply (isCompact_closedBall x_bar r).exists_isMinOn
    · exact ⟨x_bar, Metric.mem_closedBall_self hr.le⟩
    · apply ContinuousOn.add (hgcont.mono hKsub)
      exact (continuous_const.mul ((continuous_id.sub continuous_const).norm.pow 2)).continuousOn
  choose xs hxs hmin using hex
  have hxs_ball : ∀ n, xs n ∈ Metric.ball x_bar ρ := fun n => hKsub (hxs n)
  have hbound : ∀ n : ℕ, (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ ≤ β := by
    intro n
    have hc : 0 < ((n:ℝ) + 1) * M := by positivity
    have h1 : g (xs n) + (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ ^ 2
        ≤ g x_bar + (((n:ℝ) + 1) * M) * ‖x_bar - x_bar‖ ^ 2 :=
      isMinOn_iff.mp (hmin n) x_bar (Metric.mem_closedBall_self hr.le)
    have h0 : ‖x_bar - x_bar‖ ^ 2 = 0 := by simp
    rw [h0, mul_zero, add_zero] at h1
    have h2 := hglip (xs n) (hxs_ball n) x_bar (Metric.mem_ball_self hρ)
    have h3 := neg_abs_le (g (xs n) - g x_bar)
    have h4 : (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ ^ 2 ≤ β * ‖xs n - x_bar‖ := by linarith
    rcases (norm_nonneg (xs n - x_bar)).eq_or_lt with h5 | h5
    · rw [← h5, mul_zero]
      exact hβ
    · have h6 : ((((n:ℝ) + 1) * M) * ‖xs n - x_bar‖) * ‖xs n - x_bar‖
          ≤ β * ‖xs n - x_bar‖ := by
        calc ((((n:ℝ) + 1) * M) * ‖xs n - x_bar‖) * ‖xs n - x_bar‖
            = (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ ^ 2 := by ring
          _ ≤ β * ‖xs n - x_bar‖ := h4
      exact le_of_mul_le_mul_right h6 h5
  have hnear : ∀ n : ℕ, ‖xs n - x_bar‖ < r := by
    intro n
    have hb := hbound n
    have ht := norm_nonneg (xs n - x_bar)
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have h5 : M * ‖xs n - x_bar‖ ≤ (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ := by
      have : M ≤ ((n:ℝ) + 1) * M := by nlinarith
      exact mul_le_mul_of_nonneg_right this ht
    by_contra hcon
    push_neg at hcon
    have : M * r ≤ M * ‖xs n - x_bar‖ := mul_le_mul_of_nonneg_left hcon hMpos.le
    linarith
  have htend : Filter.Tendsto xs Filter.atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hlim : Filter.Tendsto (fun n : ℕ => (β / M) * (1 / ((n:ℝ) + 1)))
        Filter.atTop (𝓝 0) := by
      have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (β / M)
      simpa only [mul_zero] using this
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hlim
    have hb := hbound n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    rw [_root_.div_mul_div_comm, _root_.mul_one, le_div_iff₀ (by positivity)]
    linarith
  refine ⟨xs, fun n => (-(2 * (((n:ℝ) + 1) * M))) • (xs n - x_bar), htend, fun n => ?_⟩
  show IsRegularSubgradientAt f (xs n) ((-(2 * (((n:ℝ) + 1) * M))) • (xs n - x_bar))
  have hxn_fin : ⊥ < f (xs n) ∧ f (xs n) < ⊤ := by
    rw [hfg (xs n) (hxs_ball n)]
    exact ⟨EReal.bot_lt_coe _, EReal.coe_lt_top _⟩
  have hV : Metric.ball x_bar r ∈ 𝓝 (xs n) := by
    apply Metric.isOpen_ball.mem_nhds
    rw [Metric.mem_ball, dist_eq_norm]
    exact hnear n
  apply regsub_of_quad f (xs n) _ (((n:ℝ) + 1) * M) hxn_fin (Metric.ball x_bar r) hV
  intro x hx
  have hxK : x ∈ Metric.closedBall x_bar r := Metric.ball_subset_closedBall hx
  have hxρ : x ∈ Metric.ball x_bar ρ := hKsub hxK
  rw [hfg x hxρ, hfg (xs n) (hxs_ball n), ← EReal.coe_add, EReal.coe_le_coe_iff]
  have hm : g (xs n) + (((n:ℝ) + 1) * M) * ‖xs n - x_bar‖ ^ 2
      ≤ g x + (((n:ℝ) + 1) * M) * ‖x - x_bar‖ ^ 2 :=
    isMinOn_iff.mp (hmin n) x hxK
  have hexp : ‖x - x_bar‖ ^ 2 = ‖x - xs n‖ ^ 2
      + 2 * inner ℝ (xs n - x_bar) (x - xs n) + ‖xs n - x_bar‖ ^ 2 := by
    have e : x - x_bar = (x - xs n) + (xs n - x_bar) := by abel
    rw [e, norm_add_sq_real, real_inner_comm]
  rw [hexp] at hm
  rw [real_inner_smul_left]
  nlinarith [hm]

lemma lip_horizon (f : E → EReal) (x_bar : E) (hL : IsLocallyLipschitzNearEReal f x_bar) :
    horizonSubdifferential f x_bar = {(0 : E)} := by
  obtain ⟨ρ, hρ, β, hβ⟩ := hL
  have hxb : x_bar ∈ Metric.ball x_bar ρ := Metric.mem_ball_self hρ
  have hfin := hβ.2.1 x_bar hxb
  have hbot : ⊥ < f x_bar := bot_lt_iff_ne_bot.mpr hfin.2
  have htop : f x_bar < ⊤ := lt_top_iff_ne_top.mpr hfin.1
  -- key fact: if x n → x_bar, regular subgradients v n at x n, and l n → 0, then l n • v n → 0
  have hzero : ∀ (x : ℕ → E) (vs : ℕ → E) (l : ℕ → ℝ),
      Filter.Tendsto x Filter.atTop (𝓝 x_bar) →
      Filter.Tendsto l Filter.atTop (𝓝 0) →
      (∀ n, IsRegularSubgradientAt f (x n) (vs n)) →
      Filter.Tendsto (fun n => l n • vs n) Filter.atTop (𝓝 0) := by
    intro x vs l hx hl hreg
    have hev : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball x_bar ρ :=
      hx (Metric.ball_mem_nhds x_bar hρ)
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hlim : Filter.Tendsto (fun n => |l n| * β) Filter.atTop (𝓝 0) := by
      have := (hl.abs).mul_const β
      simpa using this
    refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hlim
    filter_upwards [hev] with n hn
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (lip_regsub_bdd f x_bar ρ β hβ (x n) hn (vs n) (hreg n))
      (abs_nonneg _)
  ext v
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨-, -, x, vseq, l, hx, -, hl, hlv, hreg⟩
    have hl0 : Filter.Tendsto l Filter.atTop (𝓝 0) := hl.mono_right nhdsWithin_le_nhds
    exact tendsto_nhds_unique hlv (hzero x vseq l hx hl0 hreg)
  · rintro rfl
    refine ⟨hbot, htop, ?_⟩
    obtain ⟨x, w, hx, hw⟩ := lip_exists_regsub_seq f x_bar ρ β hρ hβ
    have hl : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    refine ⟨x, w, fun n : ℕ => 1 / ((n : ℝ) + 1), hx, ?_, ?_, hzero x w _ hx hl hw, hw⟩
    · exact (lip_tendsto f x_bar ρ β hβ x_bar hxb).comp hx
    · rw [tendsto_nhdsWithin_iff]
      refine ⟨hl, Filter.Eventually.of_forall fun n => ?_⟩
      show (0 : ℝ) < 1 / ((n : ℝ) + 1)
      positivity

lemma horizon_imp_fatt (f : E → EReal) (x_bar : E) (hfin : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hH : horizonSubdifferential f x_bar = {(0 : E)}) :
    ∃ η > (0:ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K := by
  by_contra hcon
  have key : ∀ n : ℕ, ∃ x : E, ∃ v : E, ‖x - x_bar‖ < 1 / ((n:ℝ) + 1) ∧
      ((((f x_bar).toReal - 1 / ((n:ℝ) + 1) : ℝ)) : EReal) < f x ∧
      f x < ((((f x_bar).toReal + 1 / ((n:ℝ) + 1) : ℝ)) : EReal) ∧
      IsRegularSubgradientAt f x v ∧ (n:ℝ) + 1 < ‖v‖ := by
    intro n
    by_contra hn
    push_neg at hn
    apply hcon
    refine ⟨1 / ((n:ℝ) + 1), by positivity, (n:ℝ) + 1, by positivity, ?_⟩
    intro x h1 h2 h3 v hv
    exact hn x v h1 h2 h3 hv
  choose x v hx1 hx2 hx3 hreg hv using key
  set m := (f x_bar).toReal with hm
  have hfm : f x_bar = (m : EReal) := (EReal.coe_toReal hfin.2.ne hfin.1.ne').symm
  have hε : Filter.Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) Filter.atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  -- x n → x_bar
  have hxlim : Filter.Tendsto x Filter.atTop (𝓝 x_bar) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => (hx1 n).le) hε
  -- f (x n) → f x_bar
  have hflim : Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) := by
    rw [hfm]
    have hlow : Filter.Tendsto (fun n : ℕ => (((m - 1 / ((n:ℝ) + 1)) : ℝ) : EReal))
        Filter.atTop (𝓝 (m : EReal)) := by
      have : Filter.Tendsto (fun n : ℕ => m - 1 / ((n:ℝ) + 1)) Filter.atTop (𝓝 m) := by
        simpa using (tendsto_const_nhds (x := m)).sub hε
      exact (continuous_coe_real_ereal.tendsto m).comp this
    have hup : Filter.Tendsto (fun n : ℕ => (((m + 1 / ((n:ℝ) + 1)) : ℝ) : EReal))
        Filter.atTop (𝓝 (m : EReal)) := by
      have : Filter.Tendsto (fun n : ℕ => m + 1 / ((n:ℝ) + 1)) Filter.atTop (𝓝 m) := by
        simpa using (tendsto_const_nhds (x := m)).add hε
      exact (continuous_coe_real_ereal.tendsto m).comp this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun n => (hx2 n).le)
      (fun n => (hx3 n).le)
  -- norms
  have hvpos : ∀ n, 0 < ‖v n‖ := fun n => lt_trans (by positivity) (hv n)
  have hvtop : Filter.Tendsto (fun n => ‖v n‖) Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop_mono (fun n => (hv n).le) ?_
    exact Filter.tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
  have hl : Filter.Tendsto (fun n => ‖v n‖⁻¹) Filter.atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_inv_atTop_nhdsGT_zero.comp hvtop
  have hu1 : ∀ n, (fun n => ‖v n‖⁻¹ • v n) n ∈ Metric.sphere (0 : E) 1 := by
    intro n
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (hvpos n).ne'
  obtain ⟨a, ha, sq, hsm, hlim⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq hu1
  have hst := hsm.tendsto_atTop
  have hmem : a ∈ horizonSubdifferential f x_bar :=
    ⟨hfin.1, hfin.2, x ∘ sq, v ∘ sq, (fun n => ‖v n‖⁻¹) ∘ sq, hxlim.comp hst, hflim.comp hst,
      hl.comp hst, hlim, fun n => hreg (sq n)⟩
  rw [hH, Set.mem_singleton_iff] at hmem
  rw [hmem, mem_sphere_zero_iff_norm, norm_zero] at ha
  exact zero_ne_one ha

lemma sub_closed (f : E → EReal) (x_bar : E) : IsClosed (subdifferential f x_bar) := by
  set G : Set (E × EReal × E) :=
    {p | p.2.1 = f p.1 ∧ IsRegularSubgradientAt f p.1 p.2.2} with hG
  have key : subdifferential f x_bar =
      {_v : E | ⊥ < f x_bar ∧ f x_bar < ⊤} ∩
        (fun v : E => ((x_bar, f x_bar, v) : E × EReal × E)) ⁻¹' closure G := by
    ext v
    constructor
    · rintro ⟨h1, h2, x, vseq, hx, hfx, hv, hreg⟩
      refine ⟨⟨h1, h2⟩, ?_⟩
      show ((x_bar, f x_bar, v) : E × EReal × E) ∈ closure G
      refine mem_closure_of_tendsto (f := fun n => ((x n, f (x n), vseq n) : E × EReal × E))
        (b := Filter.atTop) ?_ ?_
      · exact hx.prodMk_nhds (hfx.prodMk_nhds hv)
      · exact Filter.Eventually.of_forall (fun n => ⟨rfl, hreg n⟩)
    · rintro ⟨⟨h1, h2⟩, hmem⟩
      obtain ⟨s, hsG, hs⟩ := mem_closure_iff_seq_limit.1 hmem
      refine ⟨h1, h2, fun n => (s n).1, fun n => (s n).2.2, ?_, ?_, ?_, fun n => (hsG n).2⟩
      · exact (continuous_fst.tendsto _).comp hs
      · have h3 : Filter.Tendsto (fun n => (s n).2.1) Filter.atTop (𝓝 (f x_bar)) :=
          ((continuous_fst.comp continuous_snd).tendsto _).comp hs
        exact h3.congr (fun n => (hsG n).1)
      · exact ((continuous_snd.comp continuous_snd).tendsto _).comp hs
  rw [key]
  exact isClosed_const.inter (isClosed_closure.preimage (by fun_prop))

lemma lip_sub_nonempty (f : E → EReal) (x_bar : E) (hL : IsLocallyLipschitzNearEReal f x_bar) :
    (subdifferential f x_bar).Nonempty := by
  obtain ⟨ρ, hρ, β, hβ⟩ := hL
  obtain ⟨x, v, hx, hreg⟩ := lip_exists_regsub_seq f x_bar ρ β hρ hβ
  have hxb : x_bar ∈ Metric.ball x_bar ρ := Metric.mem_ball_self hρ
  have hev : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball x_bar ρ :=
    hx.eventually (Metric.ball_mem_nhds x_bar hρ)
  have hfreq : ∃ᶠ n in Filter.atTop, v n ∈ Metric.closedBall (0 : E) β := by
    refine (hev.mono fun n hn => ?_).frequently
    have := lip_regsub_bdd f x_bar ρ β hβ (x n) hn (v n) (hreg n)
    simpa [Metric.mem_closedBall, dist_zero_right] using this
  obtain ⟨a, -, ns, hns, hva⟩ :=
    tendsto_subseq_of_frequently_bounded (Metric.isBounded_closedBall) hfreq
  have hfin := (hβ.2.1 x_bar hxb)
  have hxns : Filter.Tendsto (x ∘ ns) Filter.atTop (𝓝 x_bar) := hx.comp hns.tendsto_atTop
  refine ⟨a, ?_⟩
  refine ⟨bot_lt_iff_ne_bot.2 hfin.2, lt_top_iff_ne_top.2 hfin.1, x ∘ ns, v ∘ ns, hxns, ?_, hva,
    fun i => hreg (ns i)⟩
  exact (lip_tendsto f x_bar ρ β hβ x_bar hxb).comp hxns

lemma H_fApproach_neBot (f : E → EReal) (x_bar : E) : (fApproach f x_bar).NeBot := by
  have h : (pure x_bar : Filter E) ≤ fApproach f x_bar :=
    le_inf (pure_le_nhds x_bar) (tendsto_pure_nhds f x_bar).le_comap
  exact Filter.neBot_of_le h

lemma H_regSubderiv_le_of_forall (f : E → EReal) (x_bar w : E) (c : EReal) (s : ℝ) (hs : 0 < s)
    (h : ∀ x ∈ Metric.ball x_bar s, ∀ τ : ℝ, 0 < τ → τ < s → delta f x τ w ≤ c) :
    regularSubderivative f x_bar w ≤ c := by
  unfold regularSubderivative
  have hinner : ∀ δ : ℝ, 0 ≤ δ → Filter.limsup (fun p : E × ℝ =>
      sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) ≤ c := by
    intro δ hδ
    have h1 : ∀ᶠ x in fApproach f x_bar, x ∈ Metric.ball x_bar s :=
      (inf_le_left : fApproach f x_bar ≤ 𝓝 x_bar) (Metric.ball_mem_nhds x_bar hs)
    have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 s := Ioo_mem_nhdsGT hs
    refine Filter.limsup_le_of_le (h := ?_)
    filter_upwards [h1.prod_mk h2] with p hp
    obtain ⟨hx, hτ0, hτs⟩ := hp
    calc sInf ((delta f p.1 p.2) '' Metric.closedBall w δ) ≤ delta f p.1 p.2 w :=
          sInf_le ⟨w, Metric.mem_closedBall_self hδ, rfl⟩
      _ ≤ c := h p.1 hx p.2 hτ0 hτs
  refine Filter.limsup_le_of_le (h := ?_)
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  exact hinner δ (le_of_lt hδ)

lemma H_le_regSubderiv_of_forall (f : E → EReal) (x_bar w : E) (c : EReal) (s : ℝ) (hs : 0 < s)
    (h : ∀ x ∈ Metric.ball x_bar s, ∀ τ : ℝ, 0 < τ → τ < s →
      ∀ w' ∈ Metric.closedBall w 1, c ≤ delta f x τ w') :
    c ≤ regularSubderivative f x_bar w := by
  unfold regularSubderivative
  haveI := H_fApproach_neBot f x_bar
  have hinner : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → c ≤ Filter.limsup (fun p : E × ℝ =>
      sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
    intro δ hδ0 hδ1
    have h1 : ∀ᶠ x in fApproach f x_bar, x ∈ Metric.ball x_bar s :=
      (inf_le_left : fApproach f x_bar ≤ 𝓝 x_bar) (Metric.ball_mem_nhds x_bar hs)
    have h2 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 s := Ioo_mem_nhdsGT hs
    apply Filter.le_limsup_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [h1.prod_mk h2] with p hp
    obtain ⟨hx, hτ0, hτs⟩ := hp
    apply le_sInf
    rintro _ ⟨w', hw', rfl⟩
    exact h p.1 hx p.2 hτ0 hτs w' (Metric.closedBall_subset_closedBall hδ1 hw')
  apply Filter.le_limsup_of_frequently_le'
  apply Filter.Eventually.frequently
  filter_upwards [Ioc_mem_nhdsGT one_pos] with δ hδ
  exact hinner δ hδ.1 hδ.2

lemma H_delta_coe (f : E → EReal) (x d : E) (t a b : ℝ) (ha : f x = a)
    (hb : f (x + t • d) = b) :
    delta f x t d = (((b - a) / t : ℝ) : EReal) := by
  simp only [delta, differenceQuotient, ha, hb]
  rw [EReal.coe_div, EReal.coe_sub]

lemma lip_regSubderiv_finite (f : E → EReal) (x_bar : E)
    (hL : IsLocallyLipschitzNearEReal f x_bar) (w : E) :
    IsFiniteEReal (regularSubderivative f x_bar w) := by
  obtain ⟨ρ, hρ, β, hβ0, hfin, hlip⟩ := hL
  have key : ∀ x ∈ Metric.ball x_bar (ρ / 2), ∀ τ : ℝ, 0 < τ → ∀ d : E, τ * ‖d‖ < ρ / 2 →
      ∃ a b : ℝ, f x = a ∧ f (x + τ • d) = b ∧ |b - a| ≤ β * (τ * ‖d‖) := by
    intro x hx τ hτ d hd
    have hxB : x ∈ Metric.ball x_bar ρ := Metric.ball_subset_ball (by linarith) hx
    have hdist : dist (x + τ • d) x = τ * ‖d‖ := by
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
    have hyB : x + τ • d ∈ Metric.ball x_bar ρ := by
      rw [Metric.mem_ball] at hx ⊢
      calc dist (x + τ • d) x_bar ≤ dist (x + τ • d) x + dist x x_bar := dist_triangle _ _ _
        _ < ρ / 2 + ρ / 2 := by rw [hdist]; exact add_lt_add hd hx
        _ = ρ := by ring
    obtain ⟨hx1, hx2⟩ := hfin x hxB
    obtain ⟨hy1, hy2⟩ := hfin _ hyB
    refine ⟨(f x).toReal, (f (x + τ • d)).toReal, (EReal.coe_toReal hx1 hx2).symm,
      (EReal.coe_toReal hy1 hy2).symm, ?_⟩
    have := hlip _ _ hyB hxB
    rw [Real.norm_eq_abs, smul_eq_mul, hdist] at this
    exact this
  set s : ℝ := ρ / (2 * (‖w‖ + 2)) with hs_def
  have hw0 : 0 ≤ ‖w‖ := norm_nonneg w
  have hs : 0 < s := by positivity
  have hsρ : s * (‖w‖ + 2) = ρ / 2 := by
    rw [hs_def]; field_simp
  have hsρ' : s ≤ ρ / 2 := by nlinarith
  have hub : regularSubderivative f x_bar w ≤ ((β * ‖w‖ : ℝ) : EReal) := by
    apply H_regSubderiv_le_of_forall f x_bar w _ s hs
    intro x hx τ hτ0 hτs
    have hx' : x ∈ Metric.ball x_bar (ρ / 2) := Metric.ball_subset_ball hsρ' hx
    have hd : τ * ‖w‖ < ρ / 2 := by nlinarith
    obtain ⟨a, b, ha, hb, hab⟩ := key x hx' τ hτ0 w hd
    rw [H_delta_coe f x w τ a b ha hb, EReal.coe_le_coe_iff, div_le_iff₀ hτ0]
    have := (abs_le.1 hab).2
    linarith
  have hlb : (((-(β * (‖w‖ + 1))) : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
    apply H_le_regSubderiv_of_forall f x_bar w _ s hs
    intro x hx τ hτ0 hτs w' hw'
    have hx' : x ∈ Metric.ball x_bar (ρ / 2) := Metric.ball_subset_ball hsρ' hx
    have hw'n : ‖w'‖ ≤ ‖w‖ + 1 := by
      have h1 : ‖w' - w‖ ≤ 1 := by rw [← dist_eq_norm]; exact Metric.mem_closedBall.1 hw'
      have h2 := norm_sub_norm_le w' w
      linarith
    have hd : τ * ‖w'‖ < ρ / 2 := by nlinarith [norm_nonneg w']
    obtain ⟨a, b, ha, hb, hab⟩ := key x hx' τ hτ0 w' hd
    rw [H_delta_coe f x w' τ a b ha hb, EReal.coe_le_coe_iff, le_div_iff₀ hτ0]
    have h3 := (abs_le.1 hab).1
    have h4 : β * τ * ‖w'‖ ≤ β * τ * (‖w‖ + 1) :=
      mul_le_mul_of_nonneg_left hw'n (mul_nonneg hβ0 hτ0.le)
    nlinarith
  have hne_top : regularSubderivative f x_bar w ≠ ⊤ :=
    ne_top_of_le_ne_top (EReal.coe_ne_top _) hub
  have hne_bot : regularSubderivative f x_bar w ≠ ⊥ :=
    ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hlb
  exact ⟨(regularSubderivative f x_bar w).toReal, (EReal.coe_toReal hne_top hne_bot).symm⟩

-- [H] Block 2: replaces the sorried regSubderiv_le_lipMod.

lemma regsub_dq_lower (f : E → EReal) (x v : E) (hv : IsRegularSubgradientAt f x v)
    (ε B : ℝ) (hε : 0 < ε) :
    ∃ τ₀ > (0:ℝ), ∀ τ : ℝ, 0 < τ → τ < τ₀ → ∀ w : E, ‖w‖ ≤ B →
      (((inner ℝ v w - ε : ℝ)) : EReal) ≤ differenceQuotient f x w τ := by
  obtain ⟨hbot, htop, r, hr, V, hV, hfV⟩ := hv
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal htop.ne hbot.ne').symm⟩
  set B' : ℝ := max B 1 with hB'
  have hB'pos : 0 < B' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc : 0 < ε / B' := div_pos hε hB'pos
  obtain ⟨δ₁, hδ₁, hδ₁'⟩ := Metric.eventually_nhds_iff.mp (hr.def hc)
  obtain ⟨δ₂, hδ₂, hδ₂'⟩ := Metric.mem_nhds_iff.mp hV
  refine ⟨min δ₁ δ₂ / B', div_pos (lt_min hδ₁ hδ₂) hB'pos, ?_⟩
  intro τ hτ hτ₀ w hw
  have hwB' : ‖w‖ ≤ B' := le_trans hw (le_max_left _ _)
  have hyx : (x + τ • w) - x = τ • w := by abel
  have hnorm : ‖(x + τ • w) - x‖ = τ * ‖w‖ := by
    rw [hyx, norm_smul, Real.norm_eq_abs, abs_of_pos hτ]
  have hdist : dist (x + τ • w) x < min δ₁ δ₂ := by
    rw [dist_eq_norm, hnorm]
    calc τ * ‖w‖ ≤ τ * B' := by gcongr
      _ < min δ₁ δ₂ / B' * B' := by gcongr
      _ = min δ₁ δ₂ := by field_simp
  have hyV : x + τ • w ∈ V :=
    hδ₂' (by simpa [Metric.mem_ball] using lt_of_lt_of_le hdist (min_le_right _ _))
  have hry : ‖r (x + τ • w)‖ ≤ ε / B' * ‖‖(x + τ • w) - x‖‖ :=
    hδ₁' (lt_of_lt_of_le hdist (min_le_left _ _))
  rw [norm_norm, hnorm, Real.norm_eq_abs] at hry
  have hfy := hfV (x + τ • w) hyV
  rw [ha, hyx, inner_smul_right] at hfy
  have hreal : a + (inner ℝ v w - ε) * τ ≤ a + (τ * inner ℝ v w + r (x + τ • w)) := by
    have h1 : ε / B' * (τ * ‖w‖) ≤ ε * τ := by
      calc ε / B' * (τ * ‖w‖) ≤ ε / B' * (τ * B') := by gcongr
        _ = ε * τ := by field_simp
    have h2 := neg_abs_le (r (x + τ • w))
    nlinarith
  unfold differenceQuotient
  rw [ha, EReal.le_div_iff_mul_le (by exact_mod_cast hτ) (EReal.coe_ne_top τ),
    EReal.le_sub_iff_add_le (Or.inl (EReal.coe_ne_bot a)) (Or.inl (EReal.coe_ne_top a))]
  refine le_trans ?_ hfy
  rw [add_comm]
  exact_mod_cast hreal

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
lemma I_fApproach (f : E → EReal) (x_bar : E) (hfin : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (p : E → Prop) (h : ∀ᶠ x in fApproach f x_bar, p x) :
    ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      p x := by
  unfold fApproach at h
  rw [Filter.eventually_inf] at h
  obtain ⟨s, hs, t, ht, hst⟩ := h
  obtain ⟨N, hN, hNt⟩ := Filter.mem_comap.1 ht
  have hfm : f x_bar = (((f x_bar).toReal : ℝ) : EReal) :=
    (EReal.coe_toReal hfin.2.ne hfin.1.ne').symm
  rw [hfm] at hN
  have hN' : (fun r : ℝ => (r : EReal)) ⁻¹' N ∈ 𝓝 ((f x_bar).toReal) :=
    continuous_coe_real_ereal.continuousAt.preimage_mem_nhds hN
  obtain ⟨ε₁, hε₁, hball₁⟩ := Metric.mem_nhds_iff.1 hs
  obtain ⟨ε₂, hε₂, hball₂⟩ := Metric.mem_nhds_iff.1 hN'
  filter_upwards [Ioo_mem_nhdsGT (lt_min hε₁ hε₂)] with η hη
  intro x hx h1 h2
  have hη1 : η < ε₁ := lt_of_lt_of_le hη.2 (min_le_left _ _)
  have hη2 : η < ε₂ := lt_of_lt_of_le hη.2 (min_le_right _ _)
  apply hst x
  refine ⟨hball₁ ?_, hNt ?_⟩
  · rw [Metric.mem_ball, dist_eq_norm]
    exact lt_trans hx hη1
  · have hne1 : f x ≠ ⊤ := (lt_of_lt_of_le h2 le_top).ne
    have hne2 : f x ≠ ⊥ := (lt_of_le_of_lt bot_le h1).ne'
    obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a := ⟨(f x).toReal, (EReal.coe_toReal hne1 hne2).symm⟩
    rw [ha] at h1 h2
    have h1' : (f x_bar).toReal - η < a := by exact_mod_cast h1
    have h2' : a < (f x_bar).toReal + η := by exact_mod_cast h2
    show f x ∈ N
    rw [ha]
    have hmem : a ∈ Metric.ball ((f x_bar).toReal) ε₂ := by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    exact hball₂ hmem

lemma I_dir (f : E → EReal) (x_bar : E) (hfin : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (w : E) (M : ℝ) (hM : regularSubderivative f x_bar w < (M : EReal))
    (δ₀ : ℝ) (hδ₀ : 0 < δ₀) :
    ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, inner ℝ v w ≤ M + 1 + δ₀ * ‖v‖ := by
  unfold regularSubderivative at hM
  have h1 := Filter.eventually_lt_of_limsup_lt hM
  obtain ⟨δ, hδM, hδ⟩ := (h1.and (Ioc_mem_nhdsGT hδ₀)).exists
  have h2 := Filter.eventually_lt_of_limsup_lt hδM
  rw [Filter.eventually_prod_iff] at h2
  obtain ⟨pa, hpa, pb, hpb, hp⟩ := h2
  filter_upwards [I_fApproach f x_bar hfin pa hpa] with η hη
  intro x hx h1x h2x v hv
  obtain ⟨τ₀, hτ₀, hτ₀'⟩ := regsub_dq_lower f x v hv 1 (‖w‖ + δ) one_pos
  obtain ⟨τ, hτpb, hτ⟩ := (hpb.and (Ioo_mem_nhdsGT hτ₀)).exists
  have h3 := hp (hη x hx h1x h2x) hτpb
  rw [sInf_lt_iff] at h3
  obtain ⟨b, ⟨w', hw', rfl⟩, hb⟩ := h3
  have hw'd : ‖w' - w‖ ≤ δ := by
    rw [Metric.mem_closedBall, dist_eq_norm] at hw'
    exact hw'
  have hw'n : ‖w'‖ ≤ ‖w‖ + δ := by
    calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
      _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
      _ ≤ ‖w‖ + δ := by linarith
  have h4 := hτ₀' τ hτ.1 hτ.2 w' hw'n
  have h5 : ((inner ℝ v w' - 1 : ℝ) : EReal) < (M : EReal) := lt_of_le_of_lt h4 hb
  have h6 : inner ℝ v w' - 1 < M := by exact_mod_cast h5
  have h7 : inner ℝ v (w - w') ≤ ‖v‖ * δ := by
    calc inner ℝ v (w - w') ≤ ‖v‖ * ‖w - w'‖ := real_inner_le_norm _ _
      _ ≤ ‖v‖ * δ := by
        apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
        rw [norm_sub_rev]; exact hw'd
  have h8 : inner ℝ v w = inner ℝ v w' + inner ℝ v (w - w') := by
    rw [← inner_add_right]; congr 1; abel
  have h9 : ‖v‖ * δ ≤ δ₀ * ‖v‖ := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hδ.2 (norm_nonneg _)
  linarith

lemma regSubderiv_finite_imp_fatt (f : E → EReal) (x_bar : E) (hfin : ⊥ < f x_bar ∧ f x_bar < ⊤)
    (hD : ∀ w : E, IsFiniteEReal (regularSubderivative f x_bar w)) :
    ∃ η > (0:ℝ), ∃ K : ℝ, 0 ≤ K ∧ ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K := by
  choose r hr using hD
  obtain ⟨n, b, -⟩ : ∃ n : ℕ, ∃ _ : OrthonormalBasis (Fin n) ℝ E, True :=
    ⟨_, stdOrthonormalBasis ℝ E, trivial⟩
  set δ₀ : ℝ := 1 / (2 * ((n : ℝ) + 1)) with hδ₀def
  have hδ₀ : 0 < δ₀ := by positivity
  have hnδ : (n : ℝ) * δ₀ ≤ 1 / 2 := by
    rw [hδ₀def, mul_one_div, div_le_iff₀ (by positivity)]
    linarith
  have hM : ∀ w : E, regularSubderivative f x_bar w < ((r w + 1 : ℝ) : EReal) := by
    intro w
    rw [hr w]
    exact_mod_cast (by linarith : r w < r w + 1)
  have hall : ∀ᶠ η in 𝓝[>] (0:ℝ), ∀ i : Fin n,
      (∀ x : E, ‖x - x_bar‖ < η →
        (((f x_bar).toReal - η : ℝ) : EReal) < f x →
        f x < (((f x_bar).toReal + η : ℝ) : EReal) →
        ∀ v ∈ regularSubdifferential f x, inner ℝ v (b i) ≤ (r (b i) + 1) + 1 + δ₀ * ‖v‖) ∧
      (∀ x : E, ‖x - x_bar‖ < η →
        (((f x_bar).toReal - η : ℝ) : EReal) < f x →
        f x < (((f x_bar).toReal + η : ℝ) : EReal) →
        ∀ v ∈ regularSubdifferential f x,
          inner ℝ v (-(b i)) ≤ (r (-(b i)) + 1) + 1 + δ₀ * ‖v‖) := by
    rw [Filter.eventually_all]
    intro i
    exact (I_dir f x_bar hfin (b i) _ (hM (b i)) δ₀ hδ₀).and
      (I_dir f x_bar hfin (-(b i)) _ (hM (-(b i))) δ₀ hδ₀)
  obtain ⟨η, hη, hηpos⟩ := (hall.and self_mem_nhdsWithin).exists
  refine ⟨η, hηpos, 2 * ∑ i : Fin n, (|r (b i)| + |r (-(b i))| + 2), ?_, ?_⟩
  · have : 0 ≤ ∑ i : Fin n, (|r (b i)| + |r (-(b i))| + 2) :=
      Finset.sum_nonneg (fun i _ => by positivity)
    linarith
  · intro x hx h1 h2 v hv
    have hi : ∀ i : Fin n, |inner ℝ (b i) v| ≤ (|r (b i)| + |r (-(b i))| + 2) + δ₀ * ‖v‖ := by
      intro i
      have hp := (hη i).1 x hx h1 h2 v hv
      have hm := (hη i).2 x hx h1 h2 v hv
      rw [inner_neg_right] at hm
      rw [real_inner_comm, abs_le]
      have e1 := le_abs_self (r (b i))
      have e2 := le_abs_self (r (-(b i)))
      have e3 := abs_nonneg (r (b i))
      have e4 := abs_nonneg (r (-(b i)))
      constructor <;> linarith
    have hsum : ‖v‖ ≤ ∑ i : Fin n, |inner ℝ (b i) v| := by
      calc ‖v‖ = ‖∑ i : Fin n, inner ℝ (b i) v • b i‖ := by rw [b.sum_repr' v]
        _ ≤ ∑ i : Fin n, ‖inner ℝ (b i) v • b i‖ := norm_sum_le _ _
        _ = ∑ i : Fin n, |inner ℝ (b i) v| := by
          apply Finset.sum_congr rfl
          intro i _
          rw [norm_smul, b.orthonormal.1 i, mul_one, Real.norm_eq_abs]
    have hsum2 : ∑ i : Fin n, |inner ℝ (b i) v| ≤
        ∑ i : Fin n, (|r (b i)| + |r (-(b i))| + 2) + (n : ℝ) * δ₀ * ‖v‖ := by
      calc ∑ i : Fin n, |inner ℝ (b i) v|
          ≤ ∑ i : Fin n, ((|r (b i)| + |r (-(b i))| + 2) + δ₀ * ‖v‖) :=
            Finset.sum_le_sum (fun i _ => hi i)
        _ = ∑ i : Fin n, (|r (b i)| + |r (-(b i))| + 2) + (n : ℝ) * δ₀ * ‖v‖ := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          ring
    have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
    have hprod : (n : ℝ) * δ₀ * ‖v‖ ≤ 1 / 2 * ‖v‖ := mul_le_mul_of_nonneg_right hnδ hv0
    linarith

lemma lip_imp_six (f : E → EReal) (x_bar : E) (hL : IsLocallyLipschitzNearEReal f x_bar) :
    IsFiniteAround f x_bar ∧
      ∀ w : E, IsLocallyBoundedAboveAtEReal (fun x => subderivative f x w) x_bar := by
  obtain ⟨ρ, hρ, β, hβ0, hfin, hlip⟩ := hL
  refine ⟨⟨Metric.ball x_bar ρ, Metric.ball_mem_nhds _ hρ, fun x hx =>
    ⟨(f x).toReal, (EReal.coe_toReal (hfin x hx).1 (hfin x hx).2).symm⟩⟩, ?_⟩
  intro w
  refine ⟨Metric.ball x_bar (ρ / 2), Metric.ball_mem_nhds _ (by linarith), β * (‖w‖ + 1), ?_⟩
  intro x hx
  have hx' : x ∈ Metric.ball x_bar ρ := Metric.ball_subset_ball (by linarith) hx
  have hw1 : 0 < ‖w‖ + 1 := by positivity
  obtain ⟨τ₁, hτ₁pos, hτ₁⟩ : ∃ τ₁ : ℝ, 0 < τ₁ ∧ τ₁ * (‖w‖ + 1) = ρ / 2 :=
    ⟨ρ / 2 / (‖w‖ + 1), by positivity, by field_simp⟩
  obtain ⟨a, ha⟩ : ∃ a : ℝ, f x = a :=
    ⟨(f x).toReal, (EReal.coe_toReal (hfin x hx').1 (hfin x hx').2).symm⟩
  show Filter.liminf (fun p : ℝ × E => differenceQuotient f x p.2 p.1)
    (𝓝[>] (0 : ℝ) ×ˢ 𝓝 w) ≤ _
  apply Filter.liminf_le_of_frequently_le'
  apply Filter.Eventually.frequently
  have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 τ₁ := Ioo_mem_nhdsGT hτ₁pos
  have h2 : ∀ᶠ w' in 𝓝 w, ‖w'‖ < ‖w‖ + 1 :=
    (continuous_norm.tendsto w).eventually_lt_const (by linarith)
  filter_upwards [h1.prod_mk h2] with p hp
  obtain ⟨τ, w'⟩ := p
  obtain ⟨⟨hp1, hp2⟩, hp3⟩ := hp
  simp only at hp1 hp2 hp3 ⊢
  have hstep : ‖(x + τ • w') - x‖ = τ * ‖w'‖ := by
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos hp1]
  have hτw : τ * ‖w'‖ ≤ τ₁ * (‖w‖ + 1) := mul_le_mul hp2.le hp3.le (norm_nonneg _) hτ₁pos.le
  have hy : x + τ • w' ∈ Metric.ball x_bar ρ := by
    rw [Metric.mem_ball] at hx ⊢
    calc dist (x + τ • w') x_bar ≤ dist (x + τ • w') x + dist x x_bar := dist_triangle _ _ _
      _ = τ * ‖w'‖ + dist x x_bar := by rw [dist_eq_norm (x + τ • w') x, hstep]
      _ < ρ := by linarith
  obtain ⟨c, hc⟩ : ∃ c : ℝ, f (x + τ • w') = c :=
    ⟨_, (EReal.coe_toReal (hfin _ hy).1 (hfin _ hy).2).symm⟩
  have hl := hlip (x + τ • w') x hy hx'
  rw [ha, hc, EReal.toReal_coe, EReal.toReal_coe, smul_eq_mul, dist_eq_norm, hstep,
    Real.norm_eq_abs] at hl
  have hreal : (c - a) / τ ≤ β * (‖w‖ + 1) := by
    rw [div_le_iff₀ hp1]
    have h3 := le_abs_self (c - a)
    have h4 : β * (τ * ‖w'‖) ≤ β * (τ * (‖w‖ + 1)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hp3.le hp1.le) hβ0
    nlinarith
  unfold differenceQuotient
  rw [ha, hc, ← EReal.coe_sub, ← EReal.coe_div]
  exact_mod_cast hreal

lemma G_inner_le_subderivative (f : E → EReal) (x v : E) (hv : IsRegularSubgradientAt f x v)
    (w : E) : ((inner ℝ v w : ℝ) : EReal) ≤ subderivative f x w := by
  unfold subderivative
  refine EReal.ge_of_forall_gt_iff_ge.mp ?_
  intro z hz
  have hz' : z < inner ℝ v w := by exact_mod_cast hz
  set ε : ℝ := (inner ℝ v w - z) / 2 with hε_def
  have hε : 0 < ε := by rw [hε_def]; linarith
  obtain ⟨τ₀, hτ₀, hτ⟩ := regsub_dq_lower f x v hv ε (‖w‖ + 1) hε
  refine Filter.le_liminf_of_le (h := ?_)
  have h1 : ∀ᶠ τ in 𝓝[>] (0:ℝ), τ ∈ Set.Ioo 0 τ₀ := Ioo_mem_nhdsGT hτ₀
  have h2 : ∀ᶠ w' in 𝓝 w, ‖w'‖ < ‖w‖ + 1 :=
    (continuous_norm.tendsto w).eventually_lt_const (by linarith)
  have hcont : Continuous (fun w' : E => inner ℝ v w') := continuous_const.inner continuous_id
  have hcont' : Filter.Tendsto (fun w' : E => inner ℝ v w') (𝓝 w) (𝓝 (inner ℝ v w)) :=
    hcont.tendsto w
  have h3 : ∀ᶠ w' in 𝓝 w, inner ℝ v w - ε < inner ℝ v w' :=
    hcont'.eventually_const_lt (by linarith)
  filter_upwards [h1.prod_mk (h2.and h3)] with p hp
  obtain ⟨⟨hp1, hp2⟩, hp3, hp4⟩ := hp
  have := hτ p.1 hp1 hp2 p.2 hp3.le
  refine le_trans ?_ this
  exact_mod_cast (show z ≤ inner ℝ v p.2 - ε by linarith)

lemma six_imp_regsub_bdd (f : E → EReal) (x_bar : E)
    (h6 : IsFiniteAround f x_bar ∧
      ∀ w : E, IsLocallyBoundedAboveAtEReal (fun x => subderivative f x w) x_bar) :
    IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar := by
  obtain ⟨-, hbdd⟩ := h6
  set b := stdOrthonormalBasis ℝ E with hb
  have hb1 : ∀ i, ∃ U ∈ 𝓝 x_bar, ∃ M : ℝ, ∀ x ∈ U, subderivative f x (b i) ≤ (M : EReal) :=
    fun i => hbdd (b i)
  have hb2 : ∀ i, ∃ U ∈ 𝓝 x_bar, ∃ M : ℝ, ∀ x ∈ U, subderivative f x (-(b i)) ≤ (M : EReal) :=
    fun i => hbdd (-(b i))
  choose U1 hU1 M1 hM1 using hb1
  choose U2 hU2 M2 hM2 using hb2
  refine ⟨⋂ i, (U1 i ∩ U2 i), Filter.iInter_mem.mpr (fun i => Filter.inter_mem (hU1 i) (hU2 i)),
    ∑ i, (|M1 i| + |M2 i|) + 1, ?_, ?_⟩
  · have : 0 ≤ ∑ i, (|M1 i| + |M2 i|) := Finset.sum_nonneg (fun i _ => by positivity)
    linarith
  · intro x hx v hv
    have hx' := Set.mem_iInter.mp hx
    have hcoord : ∀ i, |inner ℝ (b i) v| ≤ |M1 i| + |M2 i| := by
      intro i
      have h1 : ((inner ℝ v (b i) : ℝ) : EReal) ≤ (M1 i : EReal) :=
        le_trans (G_inner_le_subderivative f x v hv (b i)) (hM1 i x (hx' i).1)
      have h2 : ((inner ℝ v (-(b i)) : ℝ) : EReal) ≤ (M2 i : EReal) :=
        le_trans (G_inner_le_subderivative f x v hv (-(b i))) (hM2 i x (hx' i).2)
      have h1' : inner ℝ v (b i) ≤ M1 i := by exact_mod_cast h1
      have h2' : inner ℝ v (-(b i)) ≤ M2 i := by exact_mod_cast h2
      rw [inner_neg_right] at h2'
      rw [real_inner_comm, abs_le]
      constructor
      · linarith [le_abs_self (M1 i), le_abs_self (M2 i), abs_nonneg (M1 i), abs_nonneg (M2 i)]
      · linarith [le_abs_self (M1 i), le_abs_self (M2 i), abs_nonneg (M1 i), abs_nonneg (M2 i)]
    calc ‖v‖ = ‖∑ i, inner ℝ (b i) v • b i‖ := by rw [b.sum_repr' v]
      _ ≤ ∑ i, ‖inner ℝ (b i) v • b i‖ := norm_sum_le _ _
      _ = ∑ i, |inner ℝ (b i) v| := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [norm_smul, b.norm_eq_one i, mul_one, Real.norm_eq_abs]
      _ ≤ ∑ i, (|M1 i| + |M2 i|) := Finset.sum_le_sum (fun i _ => hcoord i)
      _ ≤ ∑ i, (|M1 i| + |M2 i|) + 1 := by linarith

lemma regSubderiv_le_lipMod (f : E → EReal) (x_bar : E) (w : E) (hw : ‖w‖ = 1) :
    regularSubderivative f x_bar w ≤ lipModulusEReal f x_bar := by
  unfold lipModulusEReal
  apply le_sInf
  rintro _ ⟨κ, ⟨hκ0, U, hU, hUprop⟩, rfl⟩
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.1 hU
  have hs : 0 < r / 2 := half_pos hr
  apply H_regSubderiv_le_of_forall f x_bar w _ (r / 2) hs
  intro x hx τ hτ0 hτs
  have hdist : dist (x + τ • w) x = τ := by
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, hw, Real.norm_eq_abs, abs_of_pos hτ0,
      mul_one]
  have hxU : x ∈ U := hrU (Metric.ball_subset_ball (by linarith) hx)
  have hyU : x + τ • w ∈ U := by
    apply hrU
    rw [Metric.mem_ball] at hx ⊢
    calc dist (x + τ • w) x_bar ≤ dist (x + τ • w) x + dist x x_bar := dist_triangle _ _ _
      _ < r / 2 + r / 2 := by rw [hdist]; exact add_lt_add hτs hx
      _ = r := by ring
  obtain ⟨hfx, hfy, hle1, -⟩ := hUprop x hxU (x + τ • w) hyU
  obtain ⟨a, ha⟩ := hfx
  obtain ⟨b, hb⟩ := hfy
  rw [H_delta_coe f x w τ a b ha hb]
  rw [ha, hb, add_sub_cancel_left, norm_smul, hw, Real.norm_eq_abs, abs_of_pos hτ0, mul_one,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hle1
  rw [EReal.coe_le_coe_iff, div_le_iff₀ hτ0]
  linarith

lemma sub_inner_le_regSubderiv (f : E → EReal) (x_bar v : E) (hv : v ∈ subdifferential f x_bar)
    (w : E) : ((inner ℝ v w : ℝ) : EReal) ≤ regularSubderivative f x_bar w := by
  obtain ⟨-, -, x, vseq, hx, hfx, hvseq, hreg⟩ := hv
  have hτ₀ : ∀ n : ℕ, ∃ τ₀ > (0:ℝ), ∀ τ : ℝ, 0 < τ → τ < τ₀ → ∀ w' : E, ‖w'‖ ≤ ‖w‖ + 1 →
      (((inner ℝ (vseq n) w' - 1 / ((n:ℝ) + 1) : ℝ)) : EReal) ≤
        differenceQuotient f (x n) w' τ :=
    fun n => regsub_dq_lower f (x n) (vseq n) (hreg n) (1 / ((n:ℝ) + 1)) (‖w‖ + 1)
      (by positivity)
  choose τ₀ hτ₀pos hτ₀ using hτ₀
  set τ : ℕ → ℝ := fun n => min (τ₀ n / 2) (1 / ((n:ℝ) + 1)) with hτ_def
  have hτpos : ∀ n, 0 < τ n := fun n =>
    lt_min (by linarith [hτ₀pos n]) (by positivity)
  have hτlt : ∀ n, τ n < τ₀ n := fun n =>
    lt_of_le_of_lt (min_le_left _ _) (by linarith [hτ₀pos n])
  have hτle : ∀ n, τ n ≤ 1 / ((n:ℝ) + 1) := fun n => min_le_right _ _
  have hτ_tend : Filter.Tendsto τ Filter.atTop (𝓝[>] (0:ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, Filter.Eventually.of_forall hτpos⟩
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat (fun n => (hτpos n).le) hτle
  have hx_tend : Filter.Tendsto x Filter.atTop (fApproach f x_bar) := by
    unfold fApproach
    exact Filter.tendsto_inf.2 ⟨hx, Filter.tendsto_comap_iff.2 hfx⟩
  have hp_tend : Filter.Tendsto (fun n => (x n, τ n)) Filter.atTop
      ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := hx_tend.prodMk hτ_tend
  -- main step: lower bound for the inner limsup
  have key : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → ∀ c : ℝ, c < inner ℝ v w - ‖v‖ * δ →
      (c : EReal) ≤ Filter.limsup
        (fun p : E × ℝ => sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
        ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))) := by
    intro δ hδ hδ1 c hc
    have ha : Filter.Tendsto
        (fun n : ℕ => inner ℝ (vseq n) w - ‖vseq n‖ * δ - 1 / ((n:ℝ) + 1))
        Filter.atTop (𝓝 (inner ℝ v w - ‖v‖ * δ - 0)) := by
      refine Filter.Tendsto.sub (Filter.Tendsto.sub ?_ ?_)
        tendsto_one_div_add_atTop_nhds_zero_nat
      · exact hvseq.inner tendsto_const_nhds
      · exact hvseq.norm.mul_const δ
    rw [sub_zero] at ha
    have hev : ∀ᶠ n in Filter.atTop,
        c < inner ℝ (vseq n) w - ‖vseq n‖ * δ - 1 / ((n:ℝ) + 1) :=
      ha.eventually_const_lt hc
    apply Filter.le_limsup_of_frequently_le'
    apply hp_tend.frequently
    apply Filter.Eventually.frequently
    filter_upwards [hev] with n hn
    apply le_sInf
    rintro _ ⟨w', hw', rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm] at hw'
    have hw'n : ‖w'‖ ≤ ‖w‖ + 1 := by
      calc ‖w'‖ = ‖w + (w' - w)‖ := by congr 1; abel
        _ ≤ ‖w‖ + ‖w' - w‖ := norm_add_le _ _
        _ ≤ ‖w‖ + 1 := by linarith
    have h1 := hτ₀ n (τ n) (hτpos n) (hτlt n) w' hw'n
    have h2 : inner ℝ (vseq n) w - ‖vseq n‖ * δ ≤ inner ℝ (vseq n) w' := by
      have h5 : inner ℝ (vseq n) w' = inner ℝ (vseq n) w + inner ℝ (vseq n) (w' - w) := by
        rw [← inner_add_right]; congr 1; abel
      have h3 : - (‖vseq n‖ * ‖w' - w‖) ≤ inner ℝ (vseq n) (w' - w) := by
        have := abs_real_inner_le_norm (vseq n) (w' - w)
        linarith [neg_abs_le (inner ℝ (vseq n) (w' - w))]
      have h4 : ‖vseq n‖ * ‖w' - w‖ ≤ ‖vseq n‖ * δ :=
        mul_le_mul_of_nonneg_left hw' (norm_nonneg _)
      linarith
    have h6 : c ≤ inner ℝ (vseq n) w' - 1 / ((n:ℝ) + 1) := by linarith
    calc (c : EReal) ≤ ((inner ℝ (vseq n) w' - 1 / ((n:ℝ) + 1) : ℝ) : EReal) := by
          exact_mod_cast h6
      _ ≤ differenceQuotient f (x n) w' (τ n) := h1
  -- final step: pass to the outer limsup
  unfold regularSubderivative
  by_contra hcon
  push_neg at hcon
  obtain ⟨c, hc1, hc2⟩ := EReal.lt_iff_exists_real_btwn.1 hcon
  have hc2' : c < inner ℝ v w := by exact_mod_cast hc2
  have hgap : 0 < inner ℝ v w - c := by linarith
  have hv1 : 0 < ‖v‖ + 1 := by positivity
  set δ₀ := min 1 ((inner ℝ v w - c) / (‖v‖ + 1)) with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min one_pos (by positivity)
  have hlim : (c : EReal) ≤ Filter.limsup
      (fun (δ : ℝ) =>
        Filter.limsup
          (fun p : E × ℝ =>
            sInf ((delta f p.1 p.2) '' Metric.closedBall w δ))
          ((fApproach f x_bar) ×ˢ (𝓝[>] (0 : ℝ))))
      (𝓝[>] (0 : ℝ)) := by
    apply Filter.le_limsup_of_frequently_le'
    apply Filter.Eventually.frequently
    filter_upwards [Ioo_mem_nhdsGT hδ₀pos] with δ hδ
    have hδ1 : δ ≤ 1 := le_trans hδ.2.le (min_le_left _ _)
    have hδ2 : δ < (inner ℝ v w - c) / (‖v‖ + 1) := lt_of_lt_of_le hδ.2 (min_le_right _ _)
    rw [lt_div_iff₀ hv1] at hδ2
    have hδpos : 0 < δ := hδ.1
    apply key δ hδpos hδ1 c
    nlinarith
  exact absurd hc1 (not_lt.2 hlim)

lemma lipMod_le_sSup_sub (f : E → EReal) (x_bar : E) (hf_lsc : LocalLscAt f x_bar)
    (hL : IsLocallyLipschitzNearEReal f x_bar) :
    lipModulusEReal f x_bar ≤
      sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) '' subdifferential f x_bar) := by
  obtain ⟨ρ, hρ, β, hβ⟩ := hL
  have hL' : IsLocallyLipschitzNearEReal f x_bar := ⟨ρ, hρ, β, hβ⟩
  obtain ⟨hfbot, hftop, -⟩ := id hf_lsc
  have hS0 : (0 : EReal) ≤
      sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) '' subdifferential f x_bar) := by
    obtain ⟨v, hv⟩ := lip_sub_nonempty f x_bar hL'
    exact le_trans (EReal.coe_nonneg.mpr (norm_nonneg v)) (le_sSup ⟨v, hv, rfl⟩)
  rw [← EReal.le_of_forall_lt_iff_le]
  intro K hK
  have hK0 : 0 ≤ K := by
    have h0 : (0:EReal) < K := lt_of_le_of_lt hS0 hK
    exact_mod_cast h0.le
  have hfatt : ∃ η > (0:ℝ), ∀ x : E, ‖x - x_bar‖ < η →
      (((f x_bar).toReal - η : ℝ) : EReal) < f x → f x < (((f x_bar).toReal + η : ℝ) : EReal) →
      ∀ v ∈ regularSubdifferential f x, ‖v‖ ≤ K := by
    by_contra hcon
    push_neg at hcon
    choose x hx1 hx2 hx3 v hv hvK using fun n : ℕ => hcon (1 / ((n:ℝ) + 1)) (by positivity)
    have hxlim : Filter.Tendsto x Filter.atTop (𝓝 x_bar) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx1 n).le) ?_
      exact tendsto_one_div_add_atTop_nhds_zero_nat
    have hflim : Filter.Tendsto (fun n => f (x n)) Filter.atTop (𝓝 (f x_bar)) :=
      (lip_tendsto f x_bar ρ β hβ x_bar (Metric.mem_ball_self hρ)).comp hxlim
    have hev : ∀ᶠ n in Filter.atTop, v n ∈ Metric.closedBall (0:E) β := by
      have hxev : ∀ᶠ n in Filter.atTop, x n ∈ Metric.ball x_bar ρ :=
        hxlim.eventually (Metric.ball_mem_nhds x_bar hρ)
      filter_upwards [hxev] with n hn
      rw [mem_closedBall_zero_iff]
      exact lip_regsub_bdd f x_bar ρ β hβ (x n) hn (v n) (hv n)
    obtain ⟨w, -, g, hg, hvg⟩ :=
      tendsto_subseq_of_frequently_bounded Metric.isBounded_closedBall hev.frequently
    have hglim : Filter.Tendsto g Filter.atTop Filter.atTop := hg.tendsto_atTop
    have hw : w ∈ subdifferential f x_bar := by
      refine ⟨hfbot, hftop, x ∘ g, v ∘ g, hxlim.comp hglim, hflim.comp hglim, hvg, ?_⟩
      intro i
      exact hv (g i)
    have hwK : K ≤ ‖w‖ := by
      have hnorm : Filter.Tendsto (fun n => ‖(v ∘ g) n‖) Filter.atTop (𝓝 ‖w‖) :=
        (continuous_norm.tendsto w).comp hvg
      exact ge_of_tendsto' hnorm (fun n => (hvK (g n)).le)
    have h1 : ((‖w‖ : ℝ) : EReal) ≤
        sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) '' subdifferential f x_bar) :=
      le_sSup ⟨w, hw, rfl⟩
    have h2 : (K : EReal) ≤ ((‖w‖ : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hwK
    exact lt_irrefl _ (lt_of_le_of_lt (h2.trans h1) hK)
  obtain ⟨η, hη, hηK⟩ := hfatt
  exact fatt_imp_lipMod_le f x_bar hf_lsc η K hη hK0 hηK

theorem RW_chap_9_13
  [Nontrivial E]
  (f : E → EReal)
  (x_bar : E)
  (hf_lsc : LocalLscAt f x_bar)
  (hf_finite : ⊥ < f x_bar ∧ f x_bar < ⊤) :
  List.TFAE [
    IsLocallyLipschitzNearEReal f x_bar,
    horizonSubdifferential f x_bar = {(0 : E)},
    IsLocallyBoundedAt (fun x => regularSubdifferential f x) x_bar,
    IsLocallyBoundedAt (fun x => subdifferential f x) x_bar,
    ∀ (w : E), IsFiniteEReal (regularSubderivative f x_bar w),
    IsFiniteAround f x_bar ∧
      ∀ (w : E),
        IsLocallyBoundedAboveAtEReal
          (fun x => subderivative f x w) x_bar ] ∧
  (IsLocallyLipschitzNearEReal f x_bar →
    ((subdifferential f x_bar).Nonempty ∧
      IsCompact (subdifferential f x_bar)) ∧
    (lipModulusEReal f x_bar =
      sSup ((fun (w : E) => regularSubderivative f x_bar w) ''
            {w : E | ‖w‖ = 1})) ∧
    (sSup ((fun (w : E) => regularSubderivative f x_bar w) ''
            {w : E | ‖w‖ = 1}) =
      sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) ''
            subdifferential f x_bar))) := by
  have hfin := hf_finite
  refine ⟨?_, ?_⟩
  · tfae_have 1 → 2 := lip_horizon f x_bar
    tfae_have 1 → 3 := lip_imp_regsub_bdd f x_bar
    tfae_have 1 → 4 := lip_imp_sub_bdd f x_bar
    tfae_have 1 → 5 := fun hL w => lip_regSubderiv_finite f x_bar hL w
    tfae_have 1 → 6 := lip_imp_six f x_bar
    tfae_have 2 → 1 := by
      intro hH
      obtain ⟨η, hη, K, _, hK⟩ := horizon_imp_fatt f x_bar hfin hH
      exact fatt_imp_lip f x_bar hf_lsc η K hη hK
    tfae_have 3 → 1 := by
      intro h3
      obtain ⟨η, hη, K, _, hK⟩ := regsub_bdd_imp_fatt f x_bar h3
      exact fatt_imp_lip f x_bar hf_lsc η K hη hK
    tfae_have 4 → 3 := sub_bdd_imp_regsub_bdd f x_bar
    tfae_have 5 → 1 := by
      intro h5
      obtain ⟨η, hη, K, _, hK⟩ := regSubderiv_finite_imp_fatt f x_bar hfin h5
      exact fatt_imp_lip f x_bar hf_lsc η K hη hK
    tfae_have 6 → 3 := six_imp_regsub_bdd f x_bar
    tfae_finish
  · intro hL
    obtain ⟨ρ, hρ, β, hβ⟩ := hL
    have hL' : IsLocallyLipschitzNearEReal f x_bar := ⟨ρ, hρ, β, hβ⟩
    have hbdd : ∀ v ∈ subdifferential f x_bar, ‖v‖ ≤ β := fun v hv =>
      lip_sub_bdd f x_bar ρ β hβ x_bar (Metric.mem_ball_self hρ) v hv
    refine ⟨⟨lip_sub_nonempty f x_bar hL', ?_⟩, ?_⟩
    · refine Metric.isCompact_of_isClosed_isBounded (sub_closed f x_bar) ?_
      refine (Metric.isBounded_closedBall (x := (0:E)) (r := β)).subset ?_
      intro v hv
      simpa [Metric.mem_closedBall, dist_zero_right] using hbdd v hv
    · have h1 : sSup ((fun (w : E) => regularSubderivative f x_bar w) '' {w : E | ‖w‖ = 1})
          ≤ lipModulusEReal f x_bar := by
        apply sSup_le
        rintro _ ⟨w, hw, rfl⟩
        exact regSubderiv_le_lipMod f x_bar w hw
      have h2 := lipMod_le_sSup_sub f x_bar hf_lsc hL'
      have h3 : sSup ((fun (v : E) => ((‖v‖ : ℝ) : EReal)) '' subdifferential f x_bar) ≤
          sSup ((fun (w : E) => regularSubderivative f x_bar w) '' {w : E | ‖w‖ = 1}) := by
        apply sSup_le
        rintro _ ⟨v, hv, rfl⟩
        by_cases hv0 : v = 0
        · obtain ⟨w, hw⟩ := exists_norm_eq E (zero_le_one : (0:ℝ) ≤ 1)
          have := sub_inner_le_regSubderiv f x_bar v hv w
          refine le_trans ?_ (le_sSup ⟨w, hw, rfl⟩)
          simpa [hv0] using this
        · have hvn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
          set w : E := ‖v‖⁻¹ • v with hwdef
          have hw : ‖w‖ = 1 := by
            rw [hwdef, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hvn]
          have hinner : inner ℝ v w = ‖v‖ := by
            rw [hwdef, inner_smul_right, real_inner_self_eq_norm_sq]
            field_simp
          have := sub_inner_le_regSubderiv f x_bar v hv w
          rw [hinner] at this
          exact le_trans this (le_sSup ⟨w, hw, rfl⟩)
      exact ⟨le_antisymm (h2.trans h3) h1, le_antisymm (h1.trans h2) h3⟩

end RW_chap_9_13
