import ConvexStarLib.Defs

/-!
# `saddle_point_mirror_prox_bound`

Source: Bubeck, Convex Optimization: Algorithms and Complexity.

Statement from the `convex-eval-v28-2h/saddle_point_mirror_prox_bound` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace saddle_point_mirror_prox_bound`, so the main result is `saddle_point_mirror_prox_bound.saddle_point_mirror_prox_bound`.
-/

namespace saddle_point_mirror_prox_bound

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma spmp_slope_le_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : G → ℝ} {f' : G →L[ℝ] ℝ} {p d : G} (hf : HasFDerivAt f f' p) {A B : ℝ}
    (h : ∀ r : ℝ, 0 < r → r ≤ 1 → f (p + r • d) - f p ≤ r * (A + r * B)) :
    f' d ≤ A := by
  have hline : HasDerivAt (fun r : ℝ => p + r • d) d 0 := by
    have := ((hasDerivAt_id (0:ℝ)).smul_const d).const_add p
    simpa using this
  have h1 : HasDerivAt (fun r : ℝ => f (p + r • d)) (f' d) 0 := by
    have hf' : HasFDerivAt f f' (p + (0:ℝ) • d) := by simpa using hf
    exact hf'.comp_hasDerivAt (0:ℝ) hline
  have h2 := h1.tendsto_slope_zero_right
  have h3 : Filter.Tendsto (fun r : ℝ => A + r * B) (𝓝[>] 0) (𝓝 A) := by
    have : Filter.Tendsto (fun r : ℝ => A + r * B) (𝓝 0) (𝓝 (A + 0 * B)) :=
      tendsto_const_nhds.add (Filter.tendsto_id.mul tendsto_const_nhds)
    rw [zero_mul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto_of_tendsto h2 h3 ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with r hr
  obtain ⟨hr0, hr1⟩ := hr
  have := h r hr0 hr1.le
  simp only [zero_add, zero_smul, add_zero, smul_eq_mul]
  rw [inv_mul_le_iff₀ hr0]
  linarith

lemma spmp_first_order_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} (hS : Convex ℝ S) {h : G → ℝ} {h' : G →L[ℝ] ℝ} {w : G} (hw : w ∈ S)
    (hmin : IsMinOn h S w) (hd : HasFDerivAt h h' w) (z : G) (hz : z ∈ S) :
    0 ≤ h' (z - w) := by
  have key := spmp_slope_le_aux (f := fun x => -h x) (f' := -h') (p := w) (d := z - w)
    hd.fun_neg (A := 0) (B := 0) ?_
  · simp only [ContinuousLinearMap.neg_apply] at key
    linarith
  · intro r hr0 hr1
    have hmem : w + r • (z - w) ∈ S := by
      have := hS hw hz (by linarith : (0:ℝ) ≤ 1 - r) hr0.le (by ring)
      convert this using 1
      simp only [smul_sub, sub_smul, one_smul]
      abel
    have := isMinOn_iff.1 hmin _ hmem
    simp only
    linarith

lemma spmp_convex_fderiv_le_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} {f : G → ℝ} {f' : G →L[ℝ] ℝ} (hf : ConvexOn ℝ S f) {u x : G}
    (hu : u ∈ S) (hx : x ∈ S) (hd : HasFDerivAt f f' u) : f' (x - u) ≤ f x - f u := by
  apply spmp_slope_le_aux hd (B := 0)
  intro r hr0 hr1
  have := hf.2 hu hx (by linarith : (0:ℝ) ≤ 1 - r) hr0.le (by ring)
  have e : u + r • (x - u) = (1 - r) • u + r • x := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  simp only [smul_eq_mul] at this
  nlinarith

lemma spmp_concave_fderiv_le_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} {f : G → ℝ} {f' : G →L[ℝ] ℝ} (hf : ConcaveOn ℝ S f) {u x : G}
    (hu : u ∈ S) (hx : x ∈ S) (hd : HasFDerivAt f f' u) : f x - f u ≤ f' (x - u) := by
  have := spmp_convex_fderiv_le_aux (f := fun z => -f z) (f' := -f') hf.neg hu hx hd.fun_neg
  simp only [ContinuousLinearMap.neg_apply] at this
  linarith

lemma spmp_strong_fderiv_le_aux {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {S : Set G} {f : G → ℝ} {f' : G →L[ℝ] ℝ} (hf : StrongConvexOn S 1 f) {u x : G}
    (hu : u ∈ S) (hx : x ∈ S) (hd : HasFDerivAt f f' u) :
    f' (x - u) ≤ f x - f u - ‖x - u‖ ^ 2 / 2 := by
  apply spmp_slope_le_aux hd (B := ‖x - u‖ ^ 2 / 2)
  intro r hr0 hr1
  have := hf.2 hu hx (by linarith : (0:ℝ) ≤ 1 - r) hr0.le (by ring)
  have e : u + r • (x - u) = (1 - r) • u + r • x := by
    simp only [smul_sub, sub_smul, one_smul]
    abel
  rw [e]
  simp only [smul_eq_mul] at this
  rw [norm_sub_rev] at this
  nlinarith

lemma spmp_opt_aux {G H : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    {S1 : Set G} {S2 : Set H} (hS1 : Convex ℝ S1) (hS2 : Convex ℝ S2)
    {phix : G → ℝ} {phiy : H → ℝ} {a b η : ℝ} (L1 : G →L[ℝ] ℝ) (L2 : H →L[ℝ] ℝ)
    {p w1 : G} {q w2 : H} (hw1 : w1 ∈ S1) (hw2 : w2 ∈ S2)
    (hp : DifferentiableAt ℝ phix p) (hq : DifferentiableAt ℝ phiy q)
    (hw1d : DifferentiableAt ℝ phix w1) (hw2d : DifferentiableAt ℝ phiy w2)
    (hmin : IsMinOn (fun z : G × H => η * (L1 z.1 + L2 z.2) +
      prodBregmanDivergence (fun x => a * phix x) (fun y => b * phiy y) z (p, q))
      (S1 ×ˢ S2) (w1, w2)) :
    (∀ x ∈ S1, 0 ≤ η * L1 (x - w1) +
        a * (fderiv ℝ phix w1 (x - w1) - fderiv ℝ phix p (x - w1))) ∧
    (∀ y ∈ S2, 0 ≤ η * L2 (y - w2) +
        b * (fderiv ℝ phiy w2 (y - w2) - fderiv ℝ phiy q (y - w2))) := by
  have hc1 : fderiv ℝ (fun x => a * phix x) p = a • fderiv ℝ phix p := fderiv_const_mul hp a
  have hc2 : fderiv ℝ (fun y => b * phiy y) q = b • fderiv ℝ phiy q := fderiv_const_mul hq b
  constructor
  · have hminx : IsMinOn (fun x => η * L1 x + a * phix x - a * fderiv ℝ phix p x) S1 w1 := by
      refine isMinOn_iff.2 (fun x hx => ?_)
      have h := isMinOn_iff.1 hmin (x, w2) ⟨hx, hw2⟩
      simp only [prodBregmanDivergence, bregmanDivergence, hc1, hc2,
        ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at h ⊢
      linarith
    have hd : HasFDerivAt (fun x => η * L1 x + a * phix x - a * fderiv ℝ phix p x)
        (η • L1 + a • fderiv ℝ phix w1 - a • fderiv ℝ phix p) w1 := by
      have h1 := (L1.hasFDerivAt (x := w1)).const_mul η
      have h2 := hw1d.hasFDerivAt.const_mul a
      have h3 := ((fderiv ℝ phix p).hasFDerivAt (x := w1)).const_mul a
      exact (h1.add h2).sub h3
    intro x hx
    have := spmp_first_order_aux hS1 hw1 hminx hd x hx
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at this
    linarith
  · have hminy : IsMinOn (fun y => η * L2 y + b * phiy y - b * fderiv ℝ phiy q y) S2 w2 := by
      refine isMinOn_iff.2 (fun y hy => ?_)
      have h := isMinOn_iff.1 hmin (w1, y) ⟨hw1, hy⟩
      simp only [prodBregmanDivergence, bregmanDivergence, hc1, hc2,
        ContinuousLinearMap.smul_apply, smul_eq_mul, map_sub] at h ⊢
      linarith
    have hd : HasFDerivAt (fun y => η * L2 y + b * phiy y - b * fderiv ℝ phiy q y)
        (η • L2 + b • fderiv ℝ phiy w2 - b • fderiv ℝ phiy q) w2 := by
      have h1 := (L2.hasFDerivAt (x := w2)).const_mul η
      have h2 := hw2d.hasFDerivAt.const_mul b
      have h3 := ((fderiv ℝ phiy q).hasFDerivAt (x := w2)).const_mul b
      exact (h1.add h2).sub h3
    intro y hy
    have := spmp_first_order_aux hS2 hw2 hminy hd y hy
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul] at this
    linarith

lemma spmp_nl_aux {Rx Ry β₁₁ β₁₂ β₂₂ β₂₁ M η a b A B C D : ℝ}
    (hRx : 0 < Rx) (hRy : 0 < Ry)
    (hM1 : β₁₁ * Rx ^ 2 ≤ M) (hM2 : β₂₂ * Ry ^ 2 ≤ M) (hM3 : β₁₂ * Rx * Ry ≤ M)
    (hM4 : β₂₁ * Rx * Ry ≤ M) (hη : η * (2 * M) = 1) (hηpos : 0 < η)
    (ha : a * Rx ^ 2 = 1) (hb : b * Ry ^ 2 = 1)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hD : 0 ≤ D) :
    η * ((β₁₁ * A + β₁₂ * B) * C + (β₂₂ * B + β₂₁ * A) * D) ≤
      a * (C ^ 2 + A ^ 2) / 2 + b * (D ^ 2 + B ^ 2) / 2 := by
  obtain ⟨p, hp, rfl⟩ : ∃ p, 0 ≤ p ∧ A = p * Rx :=
    ⟨A / Rx, div_nonneg hA hRx.le, by field_simp⟩
  obtain ⟨q, hq, rfl⟩ : ∃ q, 0 ≤ q ∧ B = q * Ry :=
    ⟨B / Ry, div_nonneg hB hRy.le, by field_simp⟩
  obtain ⟨r, hr, rfl⟩ : ∃ r, 0 ≤ r ∧ C = r * Rx :=
    ⟨C / Rx, div_nonneg hC hRx.le, by field_simp⟩
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ D = s * Ry :=
    ⟨D / Ry, div_nonneg hD hRy.le, by field_simp⟩
  have h1 : β₁₁ * Rx ^ 2 * (p * r) ≤ M * (p * r) :=
    mul_le_mul_of_nonneg_right hM1 (by positivity)
  have h2 : β₂₂ * Ry ^ 2 * (q * s) ≤ M * (q * s) :=
    mul_le_mul_of_nonneg_right hM2 (by positivity)
  have h3 : β₁₂ * Rx * Ry * (q * r) ≤ M * (q * r) :=
    mul_le_mul_of_nonneg_right hM3 (by positivity)
  have h4 : β₂₁ * Rx * Ry * (p * s) ≤ M * (p * s) :=
    mul_le_mul_of_nonneg_right hM4 (by positivity)
  have hinner : (β₁₁ * (p * Rx) + β₁₂ * (q * Ry)) * (r * Rx) +
      (β₂₂ * (q * Ry) + β₂₁ * (p * Rx)) * (s * Ry) ≤ M * ((p + q) * (r + s)) := by
    linarith
  have hL : η * ((β₁₁ * (p * Rx) + β₁₂ * (q * Ry)) * (r * Rx) +
      (β₂₂ * (q * Ry) + β₂₁ * (p * Rx)) * (s * Ry)) ≤ (p + q) * (r + s) / 2 := by
    calc _ ≤ η * (M * ((p + q) * (r + s))) := mul_le_mul_of_nonneg_left hinner hηpos.le
      _ = (p + q) * (r + s) / 2 := by linear_combination ((p + q) * (r + s) / 2) * hη
  have hR : a * ((r * Rx) ^ 2 + (p * Rx) ^ 2) / 2 + b * ((s * Ry) ^ 2 + (q * Ry) ^ 2) / 2 =
      (r ^ 2 + p ^ 2) / 2 + (s ^ 2 + q ^ 2) / 2 := by
    linear_combination ((r ^ 2 + p ^ 2) / 2) * ha + ((s ^ 2 + q ^ 2) / 2) * hb
  rw [hR]
  nlinarith [sq_nonneg (p - r), sq_nonneg (p - s), sq_nonneg (q - r), sq_nonneg (q - s)]

set_option linter.unusedVariables false in
theorem saddle_point_mirror_prox_bound
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] {t : ℕ}
  (𝓧 : Set E)
  (𝓓x : Set E)
  (𝓨 : Set F)
  (𝓓y : Set F)
  (phi : E → F → ℝ)
  (phix : E → ℝ)
  (phiy : F → ℝ)
  (x_seq : ℕ → E)
  (y_seq : ℕ → F)
  (u_seq : ℕ → E)
  (v_seq : ℕ → F)
  (a b η : ℝ)
  (Rx Ry β₁₁ β₁₂ β₂₂ β₂₁ : ℝ)
  (hRx_sq : Rx ^ 2 = sSup {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v})
  (hRy_sq : Ry ^ 2 = sSup {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v})
  (hRx_pos : Rx > 0) (hRy_pos : Ry > 0)
  (hβ₁₁_nonneg : β₁₁ > 0) (hβ₁₂_nonneg : β₁₂ > 0)
  (hβ₂₂_nonneg : β₂₂ > 0) (hβ₂₁_nonneg : β₂₁ > 0)
  (ht : t ≥ 1)
  (hx_0 : x_seq 0 ∈ 𝓧 ∩ 𝓓x)
  (hy_0 : y_seq 0 ∈ 𝓨 ∩ 𝓓y)
  (ha_val : a = 1 / Rx ^ 2)
  (hb_val : b = 1 / Ry ^ 2)
  (hη_val : η =
    1 / (2 * max (max (β₁₁ * Rx ^ 2) (β₂₂ * Ry ^ 2))
                 (max (β₁₂ * Rx * Ry) (β₂₁ * Rx * Ry))))
  (h_spmp_seq :
    IsSPMPSequence 𝓧 𝓓x 𝓨 𝓓y phi phix phiy a b η
      x_seq y_seq u_seq v_seq)
  (h𝓧_compact : IsCompact 𝓧)
  (h𝓧_convex : Convex ℝ 𝓧)
  (h𝓧_nonempty : Set.Nonempty 𝓧)
  (h𝓓x_convex : Convex ℝ 𝓓x)
  (h𝓓x_open : IsOpen 𝓓x)
  (h𝓓x_contains : 𝓧 ⊆ closure 𝓓x)
  (h_interx_nonempty : Set.Nonempty (𝓧 ∩ 𝓓x))
  (h𝓨_compact : IsCompact 𝓨)
  (h𝓨_convex : Convex ℝ 𝓨)
  (h𝓨_nonempty : Set.Nonempty 𝓨)
  (h𝓓y_convex : Convex ℝ 𝓓y)
  (h𝓓y_open : IsOpen 𝓓y)
  (h𝓓y_contains : 𝓨 ⊆ closure 𝓓y)
  (h_intery_nonempty : Set.Nonempty (𝓨 ∩ 𝓓y))
  (hphix_diff : DifferentiableOn ℝ phix 𝓓x)
  (hphix_mirror : IsMirrorMap 𝓓x phix)
  (hphix_strong : StrongConvexOn (𝓧 ∩ 𝓓x) 1 phix)
  (hphiy_diff : DifferentiableOn ℝ phiy 𝓓y)
  (hphiy_mirror : IsMirrorMap 𝓓y phiy)
  (hphiy_strong : StrongConvexOn (𝓨 ∩ 𝓓y) 1 phiy)
  (hphi_convex_x : ∀ y ∈ 𝓨, ConvexOn ℝ 𝓧 (fun x => phi x y))
  (hphi_concave_y : ∀ x ∈ 𝓧, ConcaveOn ℝ 𝓨 (fun y => phi x y))
  (hphi_diff_x : ∀ y ∈ 𝓨, DifferentiableOn ℝ (fun x => phi x y) 𝓧)
  (hphi_diff_y : ∀ x ∈ 𝓧, DifferentiableOn ℝ (fun y => phi x y) 𝓨)
  (hphi_grad_x : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, DifferentiableAt ℝ (fun z => phi z y) x)
  (hphi_grad_y : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, DifferentiableAt ℝ (fun w => phi x w) y)
  (hsmooth_xx : ∀ x ∈ 𝓧, ∀ x' ∈ 𝓧, ∀ y ∈ 𝓨,
    ‖fderiv ℝ (fun z => phi z y) x - fderiv ℝ (fun z => phi z y) x'‖ ≤
    β₁₁ * ‖x - x'‖)
  (hsmooth_xy : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, ∀ y' ∈ 𝓨,
    ‖fderiv ℝ (fun z => phi z y) x - fderiv ℝ (fun z => phi z y') x‖ ≤
    β₁₂ * ‖y - y'‖)
  (hsmooth_yy : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, ∀ y' ∈ 𝓨,
    ‖fderiv ℝ (fun w => phi x w) y - fderiv ℝ (fun w => phi x w) y'‖ ≤
    β₂₂ * ‖y - y'‖)
  (hsmooth_yx : ∀ x ∈ 𝓧, ∀ x' ∈ 𝓧, ∀ y ∈ 𝓨,
    ‖fderiv ℝ (fun w => phi x w) y - fderiv ℝ (fun w => phi x' w) y‖ ≤
    β₂₁ * ‖x - x'‖) :
  sSup ((fun y => phi ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, u_seq (s + 1)) y) '' 𝓨) -
  sInf ((fun x => phi x ((1 / (t : ℝ)) • ∑ s ∈ Finset.range t, v_seq (s + 1))) '' 𝓧) ≤
  max (max (β₁₁ * Rx ^ 2) (β₂₂ * Ry ^ 2)) (max (β₁₂ * Rx * Ry) (β₂₁ * Rx * Ry)) *
  (4 / (t : ℝ)) := by
  obtain ⟨h0, hmemw, hstep1, hmemz, hstep2⟩ := h_spmp_seq
  set M := max (max (β₁₁ * Rx ^ 2) (β₂₂ * Ry ^ 2)) (max (β₁₂ * Rx * Ry) (β₂₁ * Rx * Ry))
    with hM_def
  have hM1 : β₁₁ * Rx ^ 2 ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : β₂₂ * Ry ^ 2 ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM3 : β₁₂ * Rx * Ry ≤ M := le_trans (le_max_left _ _) (le_max_right _ _)
  have hM4 : β₂₁ * Rx * Ry ≤ M := le_trans (le_max_right _ _) (le_max_right _ _)
  have hMpos : 0 < M := lt_of_lt_of_le (by positivity) hM1
  have ha_pos : 0 < a := by rw [ha_val]; positivity
  have hb_pos : 0 < b := by rw [hb_val]; positivity
  have hη_pos : 0 < η := by rw [hη_val]; positivity
  have hηM : η * (2 * M) = 1 := by rw [hη_val]; field_simp
  have haR : a * Rx ^ 2 = 1 := by rw [ha_val]; field_simp
  have hbR : b * Ry ^ 2 = 1 := by rw [hb_val]; field_simp
  have htpos : (0:ℝ) < t := by exact_mod_cast ht
  have hS1c : Convex ℝ (𝓧 ∩ 𝓓x) := h𝓧_convex.inter h𝓓x_convex
  have hS2c : Convex ℝ (𝓨 ∩ 𝓓y) := h𝓨_convex.inter h𝓓y_convex
  have hphix_da : ∀ x ∈ 𝓓x, DifferentiableAt ℝ phix x :=
    fun x hx => hphix_diff.differentiableAt (h𝓓x_open.mem_nhds hx)
  have hphiy_da : ∀ y ∈ 𝓓y, DifferentiableAt ℝ phiy y :=
    fun y hy => hphiy_diff.differentiableAt (h𝓓y_open.mem_nhds hy)
  have hu_mem : ∀ s, u_seq s ∈ 𝓧 ∩ 𝓓x := fun s => (hmemw s).1
  have hv_mem : ∀ s, v_seq s ∈ 𝓨 ∩ 𝓓y := fun s => (hmemw s).2
  have hx_mem : ∀ s, x_seq s ∈ 𝓧 ∩ 𝓓x := fun s => (hmemz s).1
  have hy_mem : ∀ s, y_seq s ∈ 𝓨 ∩ 𝓓y := fun s => (hmemz s).2
  set ubar := (1 / (t : ℝ)) • ∑ s ∈ Finset.range t, u_seq (s + 1) with hubar
  set vbar := (1 / (t : ℝ)) • ∑ s ∈ Finset.range t, v_seq (s + 1) with hvbar
  have hw_sum : ∑ s ∈ Finset.range t, (1 / (t:ℝ)) = 1 := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    field_simp
  have hubar_mem : ubar ∈ 𝓧 := by
    rw [hubar, Finset.smul_sum]
    exact h𝓧_convex.sum_mem (fun _ _ => by positivity) hw_sum (fun s _ => (hu_mem (s+1)).1)
  have hvbar_mem : vbar ∈ 𝓨 := by
    rw [hvbar, Finset.smul_sum]
    exact h𝓨_convex.sum_mem (fun _ _ => by positivity) hw_sum (fun s _ => (hv_mem (s+1)).1)
  -- optimality of the starting point
  have hx0min : IsMinOn phix (𝓧 ∩ 𝓓x) (x_seq 0) := by
    refine isMinOn_iff.2 (fun x hx => ?_)
    have h := isMinOn_iff.1 h0 (x, y_seq 0) ⟨hx, hy_0⟩
    simp only at h
    have h' : a * phix (x_seq 0) ≤ a * phix x := by linarith
    exact le_of_mul_le_mul_left h' ha_pos
  have hy0min : IsMinOn phiy (𝓨 ∩ 𝓓y) (y_seq 0) := by
    refine isMinOn_iff.2 (fun y hy => ?_)
    have h := isMinOn_iff.1 h0 (x_seq 0, y) ⟨hx_0, hy⟩
    simp only at h
    have h' : b * phiy (y_seq 0) ≤ b * phiy y := by linarith
    exact le_of_mul_le_mul_left h' hb_pos
  have hx0_fo : ∀ x ∈ 𝓧 ∩ 𝓓x, 0 ≤ fderiv ℝ phix (x_seq 0) (x - x_seq 0) := fun x hx =>
    spmp_first_order_aux hS1c hx_0 hx0min (hphix_da _ hx_0.2).hasFDerivAt x hx
  have hy0_fo : ∀ y ∈ 𝓨 ∩ 𝓓y, 0 ≤ fderiv ℝ phiy (y_seq 0) (y - y_seq 0) := fun y hy =>
    spmp_first_order_aux hS2c hy_0 hy0min (hphiy_da _ hy_0.2).hasFDerivAt y hy
  have hRx_bd : ∀ x ∈ 𝓧 ∩ 𝓓x, phix x - phix (x_seq 0) ≤ Rx ^ 2 := by
    intro x hx
    by_cases hbdd : BddAbove {v | ∃ z ∈ 𝓧 ∩ 𝓓x, phix z - phix (x_seq 0) = v}
    · rw [hRx_sq]; exact le_csSup hbdd ⟨x, hx, rfl⟩
    · rw [Real.sSup_of_not_bddAbove hbdd] at hRx_sq
      exact absurd hRx_sq (pow_pos hRx_pos 2).ne'
  have hRy_bd : ∀ y ∈ 𝓨 ∩ 𝓓y, phiy y - phiy (y_seq 0) ≤ Ry ^ 2 := by
    intro y hy
    by_cases hbdd : BddAbove {v | ∃ z ∈ 𝓨 ∩ 𝓓y, phiy z - phiy (y_seq 0) = v}
    · rw [hRy_sq]; exact le_csSup hbdd ⟨y, hy, rfl⟩
    · rw [Real.sSup_of_not_bddAbove hbdd] at hRy_sq
      exact absurd hRy_sq (pow_pos hRy_pos 2).ne'
  -- main bound on the feasible set
  have key : ∀ x ∈ 𝓧 ∩ 𝓓x, ∀ y ∈ 𝓨 ∩ 𝓓y, phi ubar y - phi x vbar ≤ M * (4 / t) := by
    intro x hx y hy
    obtain ⟨Φ, hΦ⟩ : ∃ Φ : ℕ → ℝ, Φ = fun s =>
        a * (phix x - phix (x_seq s) - fderiv ℝ phix (x_seq s) (x - x_seq s)) +
        b * (phiy y - phiy (y_seq s) - fderiv ℝ phiy (y_seq s) (y - y_seq s)) := ⟨_, rfl⟩
    obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, T = fun s =>
        fderiv ℝ (fun z => phi z (v_seq (s+1))) (u_seq (s+1)) (u_seq (s+1) - x) -
        fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) (v_seq (s+1) - y) := ⟨_, rfl⟩
    have stepC : ∀ s, η * T s ≤ Φ s - Φ (s+1) := by
      intro s
      simp only [hΦ, hT]
      have hxs := hx_mem s
      have hys := hy_mem s
      have hu := hu_mem (s+1)
      have hv := hv_mem (s+1)
      have hx' := hx_mem (s+1)
      have hy' := hy_mem (s+1)
      obtain ⟨O1x, O1y⟩ := spmp_opt_aux hS1c hS2c _ _ hu hv (hphix_da _ hxs.2)
        (hphiy_da _ hys.2) (hphix_da _ hu.2) (hphiy_da _ hv.2) (hstep1 s)
      obtain ⟨O2x, O2y⟩ := spmp_opt_aux hS1c hS2c _ _ hx' hy' (hphix_da _ hxs.2)
        (hphiy_da _ hys.2) (hphix_da _ hx'.2) (hphiy_da _ hy'.2) (hstep2 s)
      have o1x := O1x _ hx'
      have o1y := O1y _ hy'
      have o2x := O2x _ hx
      have o2y := O2y _ hy
      have hneg1 : fderiv ℝ (fun y => -phi (x_seq s) y) (y_seq s) =
          -fderiv ℝ (fun w => phi (x_seq s) w) (y_seq s) := fderiv_fun_neg
      have hneg2 : fderiv ℝ (fun y => -phi (u_seq (s+1)) y) (v_seq (s+1)) =
          -fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) := fderiv_fun_neg
      rw [hneg1] at o1y
      rw [hneg2] at o2y
      have sc1 := spmp_strong_fderiv_le_aux hphix_strong hu hx' (hphix_da _ hu.2).hasFDerivAt
      have sc2 := spmp_strong_fderiv_le_aux hphix_strong hxs hu (hphix_da _ hxs.2).hasFDerivAt
      have sc3 := spmp_strong_fderiv_le_aux hphiy_strong hv hy' (hphiy_da _ hv.2).hasFDerivAt
      have sc4 := spmp_strong_fderiv_le_aux hphiy_strong hys hv (hphiy_da _ hys.2).hasFDerivAt
      have hn1 : ‖fderiv ℝ (fun z => phi z (v_seq (s+1))) (u_seq (s+1)) -
          fderiv ℝ (fun z => phi z (y_seq s)) (x_seq s)‖ ≤
          β₁₁ * ‖u_seq (s+1) - x_seq s‖ + β₁₂ * ‖v_seq (s+1) - y_seq s‖ := by
        have e : fderiv ℝ (fun z => phi z (v_seq (s+1))) (u_seq (s+1)) -
            fderiv ℝ (fun z => phi z (y_seq s)) (x_seq s) =
            (fderiv ℝ (fun z => phi z (v_seq (s+1))) (u_seq (s+1)) -
              fderiv ℝ (fun z => phi z (v_seq (s+1))) (x_seq s)) +
            (fderiv ℝ (fun z => phi z (v_seq (s+1))) (x_seq s) -
              fderiv ℝ (fun z => phi z (y_seq s)) (x_seq s)) := by abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact hsmooth_xx _ hu.1 _ hxs.1 _ hv.1
        · exact hsmooth_xy _ hxs.1 _ hv.1 _ hys.1
      have hn2 : ‖fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) -
          fderiv ℝ (fun w => phi (x_seq s) w) (y_seq s)‖ ≤
          β₂₂ * ‖v_seq (s+1) - y_seq s‖ + β₂₁ * ‖u_seq (s+1) - x_seq s‖ := by
        have e : fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) -
            fderiv ℝ (fun w => phi (x_seq s) w) (y_seq s) =
            (fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) -
              fderiv ℝ (fun w => phi (u_seq (s+1)) w) (y_seq s)) +
            (fderiv ℝ (fun w => phi (u_seq (s+1)) w) (y_seq s) -
              fderiv ℝ (fun w => phi (x_seq s) w) (y_seq s)) := by abel
        rw [e]
        refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · exact hsmooth_yy _ hu.1 _ hv.1 _ hys.1
        · exact hsmooth_yx _ hu.1 _ hxs.1 _ hys.1
      have sm1 : (fderiv ℝ (fun z => phi z (v_seq (s+1))) (u_seq (s+1)) -
          fderiv ℝ (fun z => phi z (y_seq s)) (x_seq s)) (u_seq (s+1) - x_seq (s+1)) ≤
          (β₁₁ * ‖u_seq (s+1) - x_seq s‖ + β₁₂ * ‖v_seq (s+1) - y_seq s‖) *
            ‖x_seq (s+1) - u_seq (s+1)‖ := by
        refine (Real.le_norm_self _).trans ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
        rw [norm_sub_rev (u_seq (s+1))]
        exact mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
      have sm2 : -((fderiv ℝ (fun w => phi (u_seq (s+1)) w) (v_seq (s+1)) -
          fderiv ℝ (fun w => phi (x_seq s) w) (y_seq s)) (v_seq (s+1) - y_seq (s+1))) ≤
          (β₂₂ * ‖v_seq (s+1) - y_seq s‖ + β₂₁ * ‖u_seq (s+1) - x_seq s‖) *
            ‖y_seq (s+1) - v_seq (s+1)‖ := by
        refine ((neg_le_abs _).trans (Real.norm_eq_abs _).ge).trans
          ((ContinuousLinearMap.le_opNorm _ _).trans ?_)
        rw [norm_sub_rev (v_seq (s+1))]
        exact mul_le_mul_of_nonneg_right hn2 (norm_nonneg _)
      have nl := spmp_nl_aux hRx_pos hRy_pos hM1 hM2 hM3 hM4 hηM hη_pos haR hbR
        (norm_nonneg (u_seq (s+1) - x_seq s)) (norm_nonneg (v_seq (s+1) - y_seq s))
        (norm_nonneg (x_seq (s+1) - u_seq (s+1))) (norm_nonneg (y_seq (s+1) - v_seq (s+1)))
      have sm1' := mul_le_mul_of_nonneg_left sm1 hη_pos.le
      have sm2' := mul_le_mul_of_nonneg_left sm2 hη_pos.le
      have sc1' := mul_le_mul_of_nonneg_left sc1 ha_pos.le
      have sc2' := mul_le_mul_of_nonneg_left sc2 ha_pos.le
      have sc3' := mul_le_mul_of_nonneg_left sc3 hb_pos.le
      have sc4' := mul_le_mul_of_nonneg_left sc4 hb_pos.le
      simp only [map_sub, ContinuousLinearMap.sub_apply, ContinuousLinearMap.neg_apply]
        at o1x o1y o2x o2y sc1' sc2' sc3' sc4' sm1' sm2' ⊢
      linarith only [o1x, o1y, o2x, o2y, sc1', sc2', sc3', sc4', sm1', sm2', nl]
    have hΦt : 0 ≤ Φ t := by
      have h1 := spmp_strong_fderiv_le_aux hphix_strong (hx_mem t) hx
        (hphix_da _ (hx_mem t).2).hasFDerivAt
      have h2 := spmp_strong_fderiv_le_aux hphiy_strong (hy_mem t) hy
        (hphiy_da _ (hy_mem t).2).hasFDerivAt
      simp only [hΦ]
      have h3 : 0 ≤ phix x - phix (x_seq t) - fderiv ℝ phix (x_seq t) (x - x_seq t) := by
        linarith only [h1, sq_nonneg ‖x - x_seq t‖]
      have h4 : 0 ≤ phiy y - phiy (y_seq t) - fderiv ℝ phiy (y_seq t) (y - y_seq t) := by
        linarith only [h2, sq_nonneg ‖y - y_seq t‖]
      positivity
    have hΦ0 : Φ 0 ≤ 2 := by
      simp only [hΦ]
      have h1 := hx0_fo x hx
      have h2 := hy0_fo y hy
      have h3 := hRx_bd x hx
      have h4 := hRy_bd y hy
      have h5 : phix x - phix (x_seq 0) - fderiv ℝ phix (x_seq 0) (x - x_seq 0) ≤ Rx ^ 2 := by
        linarith only [h1, h3]
      have h6 : phiy y - phiy (y_seq 0) - fderiv ℝ phiy (y_seq 0) (y - y_seq 0) ≤ Ry ^ 2 := by
        linarith only [h2, h4]
      have h7 := mul_le_mul_of_nonneg_left h5 ha_pos.le
      have h8 := mul_le_mul_of_nonneg_left h6 hb_pos.le
      linarith only [h7, h8, haR, hbR]
    have hsumT : η * ∑ s ∈ Finset.range t, T s ≤ 2 := by
      have : η * ∑ s ∈ Finset.range t, T s ≤ Φ 0 - Φ t := by
        rw [Finset.mul_sum, ← Finset.sum_range_sub' Φ t]
        exact Finset.sum_le_sum (fun s _ => stepC s)
      linarith
    have hsumT' : ∑ s ∈ Finset.range t, T s ≤ 4 * M := by
      have e : ∑ s ∈ Finset.range t, T s = (2 * M) * (η * ∑ s ∈ Finset.range t, T s) := by
        linear_combination (-(∑ s ∈ Finset.range t, T s)) * hηM
      rw [e]
      have := mul_le_mul_of_nonneg_left hsumT (by positivity : (0:ℝ) ≤ 2 * M)
      linarith
    have hgap : ∀ s, phi (u_seq (s+1)) y - phi x (v_seq (s+1)) ≤ T s := by
      intro s
      have hu := hu_mem (s+1)
      have hv := hv_mem (s+1)
      have h1 := spmp_convex_fderiv_le_aux (hphi_convex_x _ hv.1) hu.1 hx.1
        (hphi_grad_x _ hu.1 _ hv.1).hasFDerivAt
      have h2 := spmp_concave_fderiv_le_aux (hphi_concave_y _ hu.1) hv.1 hy.1
        (hphi_grad_y _ hu.1 _ hv.1).hasFDerivAt
      simp only [hT, map_sub] at h1 h2 ⊢
      linarith only [h1, h2]
    have hjx : phi ubar y ≤ ∑ s ∈ Finset.range t, (1/(t:ℝ)) * phi (u_seq (s+1)) y := by
      have h := (hphi_convex_x y hy.1).map_sum_le (t := Finset.range t)
        (w := fun _ => 1/(t:ℝ)) (p := fun s => u_seq (s+1)) (fun _ _ => by positivity) hw_sum
        (fun s _ => (hu_mem (s+1)).1)
      simp only [smul_eq_mul] at h
      rw [hubar, Finset.smul_sum]
      exact h
    have hjy : ∑ s ∈ Finset.range t, (1/(t:ℝ)) * phi x (v_seq (s+1)) ≤ phi x vbar := by
      have h := (hphi_concave_y x hx.1).le_map_sum (t := Finset.range t)
        (w := fun _ => 1/(t:ℝ)) (p := fun s => v_seq (s+1)) (fun _ _ => by positivity) hw_sum
        (fun s _ => (hv_mem (s+1)).1)
      simp only [smul_eq_mul] at h
      rw [hvbar, Finset.smul_sum]
      exact h
    have hcomb : phi ubar y - phi x vbar ≤ (1/(t:ℝ)) * ∑ s ∈ Finset.range t, T s := by
      have : ∑ s ∈ Finset.range t, (1/(t:ℝ)) * phi (u_seq (s+1)) y -
          ∑ s ∈ Finset.range t, (1/(t:ℝ)) * phi x (v_seq (s+1)) ≤
          (1/(t:ℝ)) * ∑ s ∈ Finset.range t, T s := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro s _
        rw [← mul_sub]
        exact mul_le_mul_of_nonneg_left (hgap s) (by positivity)
      linarith
    calc phi ubar y - phi x vbar ≤ (1/(t:ℝ)) * ∑ s ∈ Finset.range t, T s := hcomb
      _ ≤ (1/(t:ℝ)) * (4 * M) := mul_le_mul_of_nonneg_left hsumT' (by positivity)
      _ = M * (4 / t) := by ring
  -- extension to the closure
  have hY_sub : 𝓨 ⊆ closure (𝓨 ∩ 𝓓y) := by
    intro y hy
    obtain ⟨y0, hy0Y, hy0D⟩ := h_intery_nonempty
    have h1 : openSegment ℝ y0 y ⊆ 𝓨 ∩ 𝓓y := by
      intro w hw
      refine ⟨h𝓨_convex.openSegment_subset hy0Y hy hw, ?_⟩
      have := h𝓓y_convex.openSegment_interior_closure_subset_interior
        (by rwa [h𝓓y_open.interior_eq]) (h𝓓y_contains hy) hw
      rwa [h𝓓y_open.interior_eq] at this
    exact closure_mono h1 (segment_subset_closure_openSegment (right_mem_segment ℝ y0 y))
  have hX_sub : 𝓧 ⊆ closure (𝓧 ∩ 𝓓x) := by
    intro x hx
    obtain ⟨x0, hx0X, hx0D⟩ := h_interx_nonempty
    have h1 : openSegment ℝ x0 x ⊆ 𝓧 ∩ 𝓓x := by
      intro w hw
      refine ⟨h𝓧_convex.openSegment_subset hx0X hx hw, ?_⟩
      have := h𝓓x_convex.openSegment_interior_closure_subset_interior
        (by rwa [h𝓓x_open.interior_eq]) (h𝓓x_contains hx) hw
      rwa [h𝓓x_open.interior_eq] at this
    exact closure_mono h1 (segment_subset_closure_openSegment (right_mem_segment ℝ x0 x))
  have hYcl : closure (𝓨 ∩ 𝓓y) ⊆ 𝓨 :=
    closure_minimal Set.inter_subset_left h𝓨_compact.isClosed
  have hXcl : closure (𝓧 ∩ 𝓓x) ⊆ 𝓧 :=
    closure_minimal Set.inter_subset_left h𝓧_compact.isClosed
  have key2 : ∀ x ∈ 𝓧 ∩ 𝓓x, ∀ y ∈ 𝓨, phi ubar y ≤ M * (4 / t) + phi x vbar := by
    intro x hx y hy
    have hcont : ContinuousOn (fun y => phi ubar y) (closure (𝓨 ∩ 𝓓y)) :=
      ((hphi_diff_y ubar hubar_mem).continuousOn).mono hYcl
    exact le_on_closure (f := fun y => phi ubar y) (g := fun _ => M * (4 / t) + phi x vbar)
      (fun y' hy' => by have := key x hx y' hy'; simp only; linarith) hcont
      continuousOn_const (hY_sub hy)
  have key3 : ∀ x ∈ 𝓧, ∀ y ∈ 𝓨, phi ubar y - M * (4 / t) ≤ phi x vbar := by
    intro x hx y hy
    have hcont : ContinuousOn (fun x => phi x vbar) (closure (𝓧 ∩ 𝓓x)) :=
      ((hphi_diff_x vbar hvbar_mem).continuousOn).mono hXcl
    exact le_on_closure (f := fun _ => phi ubar y - M * (4 / t)) (g := fun x => phi x vbar)
      (fun x' hx' => by have := key2 x' hx' y hy; simp only; linarith) continuousOn_const
      hcont (hX_sub hx)
  have hne1 : ((fun y => phi ubar y) '' 𝓨).Nonempty := h𝓨_nonempty.image _
  have hne2 : ((fun x => phi x vbar) '' 𝓧).Nonempty := h𝓧_nonempty.image _
  have hfinal : sSup ((fun y => phi ubar y) '' 𝓨) ≤
      M * (4 / t) + sInf ((fun x => phi x vbar) '' 𝓧) := by
    apply csSup_le hne1
    rintro _ ⟨y, hy, rfl⟩
    have : phi ubar y - M * (4 / t) ≤ sInf ((fun x => phi x vbar) '' 𝓧) := by
      apply le_csInf hne2
      rintro _ ⟨x, hx, rfl⟩
      exact key3 x hx y hy
    linarith
  linarith

end saddle_point_mirror_prox_bound
