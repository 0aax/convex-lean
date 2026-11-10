import ConvexStarLib.Defs

/-!
# `RW_chap_12_19`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_12_19` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_12_19`, so the main result is `RW_chap_12_19.RW_chap_12_19`.
-/

namespace RW_chap_12_19

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

-- ===== ag1 =====

lemma prox_mem_iff (f : E → EReal) (lam : ℝ) (x w : E) :
    w ∈ proximalMapping f lam x ↔ f w < ⊤ ∧ ∀ z, f w + (((2 * lam)⁻¹ * ‖w - x‖ ^ 2 : ℝ) : EReal)
      ≤ f z + (((2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
  unfold proximalMapping
  simp only [Set.mem_setOf_eq]
  norm_cast

lemma lsc_add_cont (F : E → EReal) (hlsc : LowerSemicontinuous F) (q : E → ℝ) (hq : Continuous q) :
    LowerSemicontinuous (fun z => F z + ((q z : ℝ) : EReal)) := by
  have hq' : Continuous (fun z => ((q z : ℝ) : EReal)) := continuous_coe_real_ereal.comp hq
  refine LowerSemicontinuous.add' hlsc hq'.lowerSemicontinuous ?_
  intro z
  exact EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))

lemma ag1_exists_real (a : EReal) (hb : ⊥ < a) (ht : a < ⊤) : ∃ r : ℝ, a = (r : EReal) :=
  ⟨a.toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩

lemma ag1_part1_real (x₀ x₁ v₀ v₁ : E) (c : ℝ) (hc : 0 < c) (A B : ℝ)
    (h0 : A + c * ‖v₀ - x₀‖ ^ 2 ≤ B + c * ‖v₁ - x₀‖ ^ 2)
    (h1 : B + c * ‖v₁ - x₁‖ ^ 2 ≤ A + c * ‖v₀ - x₁‖ ^ 2) :
    0 ≤ inner ℝ (v₁ - v₀) (x₁ - x₀) := by
  have key : ‖v₀ - x₀‖ ^ 2 + ‖v₁ - x₁‖ ^ 2 ≤ ‖v₁ - x₀‖ ^ 2 + ‖v₀ - x₁‖ ^ 2 := by
    have : c * (‖v₀ - x₀‖ ^ 2 + ‖v₁ - x₁‖ ^ 2) ≤ c * (‖v₁ - x₀‖ ^ 2 + ‖v₀ - x₁‖ ^ 2) := by linarith
    exact le_of_mul_le_mul_left this hc
  rw [norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real, norm_sub_sq_real] at key
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  linarith

lemma part1 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (h_lam : 0 < lam) :
    IsMonotone (proximalMapping f lam) := by
  intro x₀ x₁ v₀ v₁ hv₀ hv₁
  rw [prox_mem_iff] at hv₀ hv₁
  obtain ⟨A, hA⟩ := ag1_exists_real (f v₀) (hf_proper.1 v₀) hv₀.1
  obtain ⟨B, hB⟩ := ag1_exists_real (f v₁) (hf_proper.1 v₁) hv₁.1
  have h0 := hv₀.2 v₁
  have h1 := hv₁.2 v₀
  rw [hA, hB] at h0 h1
  norm_cast at h0 h1
  exact ag1_part1_real x₀ x₁ v₀ v₁ _ (by positivity) A B h0 h1

lemma ag1_norm_sq_convex (z₁ z₂ : E) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    ‖a • z₁ + b • z₂‖ ^ 2 ≤ a * ‖z₁‖ ^ 2 + b * ‖z₂‖ ^ 2 := by
  have h1 : ‖a • z₁ + b • z₂‖ ^ 2
      = a ^ 2 * ‖z₁‖ ^ 2 + 2 * (a * b) * inner ℝ z₁ z₂ + b ^ 2 * ‖z₂‖ ^ 2 := by
    rw [norm_add_sq_real, norm_smul, norm_smul, real_inner_smul_left, real_inner_smul_right,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    ring
  have h2 : ‖z₁ - z₂‖ ^ 2 = ‖z₁‖ ^ 2 - 2 * inner ℝ z₁ z₂ + ‖z₂‖ ^ 2 := norm_sub_sq_real z₁ z₂
  have h3 : 0 ≤ a * b * ‖z₁ - z₂‖ ^ 2 := by positivity
  rw [h2] at h3
  rw [h1]
  have hb' : b = 1 - a := by linarith
  subst hb'
  nlinarith [h3]

lemma ag1_add_le_iff (x : EReal) (r s : ℝ) :
    x + (r : EReal) ≤ (s : EReal) ↔ x ≤ ((s - r : ℝ) : EReal) := by
  induction x using EReal.rec with
  | bot => simp
  | top => simp only [EReal.top_add_coe, top_le_iff, EReal.coe_ne_top]
  | coe x =>
    norm_cast
    constructor <;> intro h <;> linarith

lemma convex_proxPerturbed (f : E → EReal) (lam : ℝ) (h_lam : 0 < lam) (hf : ConvexEReal f) :
    ConvexEReal (proxPerturbedFun f lam) := by
  unfold ConvexEReal at *
  intro p hp q hq a b ha hb hab
  obtain ⟨z₁, t₁⟩ := p
  obtain ⟨z₂, t₂⟩ := q
  simp only [epigraph, proxPerturbedFun, Set.mem_setOf_eq] at hp hq ⊢
  have hc0 : 0 ≤ (2 * lam)⁻¹ := by positivity
  rw [ag1_add_le_iff] at hp hq
  have hmem := hf (show (z₁, t₁ - (2 * lam)⁻¹ * ‖z₁‖ ^ 2) ∈ epigraph f from hp)
    (show (z₂, t₂ - (2 * lam)⁻¹ * ‖z₂‖ ^ 2) ∈ epigraph f from hq) ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmem
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  rw [ag1_add_le_iff]
  refine le_trans hmem ?_
  rw [EReal.coe_le_coe_iff]
  have h1 := ag1_norm_sq_convex z₁ z₂ a b ha hb hab
  have h2 := mul_le_mul_of_nonneg_left h1 hc0
  nlinarith

lemma ag1_prox_g_real (lam : ℝ) (h_lam : 0 < lam) (x w z : E) :
    (2 * lam)⁻¹ * ‖z - x‖ ^ 2 - (2 * lam)⁻¹ * ‖w - x‖ ^ 2
      = (2 * lam)⁻¹ * ‖z‖ ^ 2 - (2 * lam)⁻¹ * ‖w‖ ^ 2 - inner ℝ (lam⁻¹ • x) (z - w) := by
  rw [norm_sub_sq_real, norm_sub_sq_real, real_inner_smul_left, inner_sub_right]
  rw [real_inner_comm x z, real_inner_comm x w]
  field_simp
  ring

lemma prox_iff_g (f : E → EReal) (lam : ℝ) (h_lam : 0 < lam) (hbot : ∀ z, ⊥ < f z) (x w : E) :
    w ∈ proximalMapping f lam x ↔ f w < ⊤ ∧ ∀ z, proxPerturbedFun f lam w
      + ((inner ℝ (lam⁻¹ • x) (z - w) : ℝ) : EReal) ≤ proxPerturbedFun f lam z := by
  rw [prox_mem_iff]
  unfold proxPerturbedFun
  refine and_congr_right (fun hwt => forall_congr' (fun z => ?_))
  obtain ⟨A, hA⟩ := ag1_exists_real (f w) (hbot w) hwt
  rw [hA]
  have hzb := hbot z
  generalize f z = y at hzb ⊢
  induction y using EReal.rec with
  | bot => exact absurd hzb (lt_irrefl _)
  | top => simp only [EReal.top_add_coe, le_top]
  | coe B =>
    norm_cast
    have := ag1_prox_g_real lam h_lam x w z
    constructor <;> intro h <;> linarith

lemma ag1_key_identity (lam : ℝ) (h_lam : 0 < lam) (x w z : E) :
    inner ℝ (lam⁻¹ • (x - w)) (z - w) + (2 * lam)⁻¹ * ‖z - x‖ ^ 2
      = (2 * lam)⁻¹ * ‖z - w‖ ^ 2 + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 := by
  have h1 : z - x = (z - w) + (w - x) := by abel
  have h2 : ‖z - x‖ ^ 2 = ‖z - w‖ ^ 2 + 2 * inner ℝ (z - w) (w - x) + ‖w - x‖ ^ 2 := by
    rw [h1, norm_add_sq_real]
  have h3 : inner ℝ (lam⁻¹ • (x - w)) (z - w) = - lam⁻¹ * inner ℝ (z - w) (w - x) := by
    rw [real_inner_smul_left, real_inner_comm, ← neg_sub w x, inner_neg_right]
    ring
  rw [h2, h3]
  field_simp
  ring

lemma prox_of_sub (f : E → EReal) (lam : ℝ) (h_lam : 0 < lam) (x w : E) (hw1 : ⊥ < f w) (hw2 : f w < ⊤)
    (hsub : ∀ z, f w + ((inner ℝ (lam⁻¹ • (x - w)) (z - w) : ℝ) : EReal) ≤ f z) :
    w ∈ proximalMapping f lam x := by
  rw [prox_mem_iff]
  refine ⟨hw2, fun z => ?_⟩
  obtain ⟨A, hA⟩ := ag1_exists_real (f w) hw1 hw2
  have h : f w + ((inner ℝ (lam⁻¹ • (x - w)) (z - w) : ℝ) : EReal)
      + (((2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) ≤ f z + (((2 * lam)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
    gcongr
    exact hsub z
  refine le_trans ?_ h
  rw [hA]
  norm_cast
  have h1 := ag1_key_identity lam h_lam x w z
  have h2 : 0 ≤ (2 * lam)⁻¹ * ‖z - w‖ ^ 2 := by positivity
  linarith

lemma global_sub_mono (F : E → EReal) (w₀ w₁ u₀ u₁ : E) (h0b : ⊥ < F w₀) (h0t : F w₀ < ⊤)
    (h1b : ⊥ < F w₁) (h1t : F w₁ < ⊤)
    (h0 : ∀ z, F w₀ + ((inner ℝ u₀ (z - w₀) : ℝ) : EReal) ≤ F z)
    (h1 : ∀ z, F w₁ + ((inner ℝ u₁ (z - w₁) : ℝ) : EReal) ≤ F z) :
    0 ≤ inner ℝ (u₁ - u₀) (w₁ - w₀) := by
  obtain ⟨A, hA⟩ := ag1_exists_real (F w₀) h0b h0t
  obtain ⟨B, hB⟩ := ag1_exists_real (F w₁) h1b h1t
  have a := h0 w₁
  have b := h1 w₀
  rw [hA, hB] at a b
  norm_cast at a b
  have e1 : inner ℝ (u₁ - u₀) (w₁ - w₀) = inner ℝ u₁ (w₁ - w₀) - inner ℝ u₀ (w₁ - w₀) :=
    inner_sub_left _ _ _
  have e2 : inner ℝ u₁ (w₀ - w₁) = - inner ℝ u₁ (w₁ - w₀) := by
    rw [← inner_neg_right, neg_sub]
  linarith

lemma reg_of_global (F : E → EReal) (x v : E) (hb : ⊥ < F x) (ht : F x < ⊤)
    (h : ∀ z, F x + ((inner ℝ v (z - x) : ℝ) : EReal) ≤ F z) : IsRegularSubgradientAt F x v := by
  refine ⟨hb, ht, fun _ => 0, Asymptotics.isLittleO_zero _ _, Set.univ, Filter.univ_mem,
    fun z _ => ?_⟩
  simpa using h z

lemma lim_of_reg (F : E → EReal) (x v : E) (h : IsRegularSubgradientAt F x v) :
    IsSubgradientAt F x v :=
  ⟨h.1, h.2.1, fun _ => x, fun _ => v, tendsto_const_nhds, tendsto_const_nhds, tendsto_const_nhds,
    fun _ => h⟩

lemma ag1_sq_isLittleO (w : E) (c : ℝ) :
    (fun z : E => -(c * ‖z - w‖ ^ 2)) =o[𝓝 w] (fun z => ‖z - w‖) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  rw [Metric.eventually_nhds_iff]
  refine ⟨ε / (|c| + 1), by positivity, fun z hz => ?_⟩
  rw [dist_eq_norm, lt_div_iff₀ (by positivity)] at hz
  simp only [norm_neg, norm_mul, norm_pow, Real.norm_eq_abs, abs_norm]
  have ht : 0 ≤ ‖z - w‖ := norm_nonneg _
  have hc : 0 ≤ |c| := abs_nonneg c
  nlinarith [mul_nonneg ht (sub_nonneg.2 hz.le), mul_nonneg ht ht]

lemma prox_reg_sub (f : E → EReal) (lam : ℝ) (h_lam : 0 < lam) (hbot : ∀ z, ⊥ < f z) (x w : E)
    (hw : w ∈ proximalMapping f lam x) : IsRegularSubgradientAt f w (lam⁻¹ • (x - w)) := by
  rw [prox_mem_iff] at hw
  obtain ⟨hwt, hw⟩ := hw
  refine ⟨hbot w, hwt, fun z => -((2 * lam)⁻¹ * ‖z - w‖ ^ 2), ag1_sq_isLittleO w _, Set.univ,
    Filter.univ_mem, fun z _ => ?_⟩
  obtain ⟨A, hA⟩ := ag1_exists_real (f w) (hbot w) hwt
  have hz := hw z
  have hzb := hbot z
  rw [hA] at hz ⊢
  generalize f z = y at hz hzb ⊢
  induction y using EReal.rec with
  | bot => exact absurd hzb (lt_irrefl _)
  | top => exact le_top
  | coe B =>
    norm_cast at hz ⊢
    have := ag1_key_identity lam h_lam x w z
    linarith



-- ===== ag2 =====

lemma ag2_conv_le (F : E → EReal) (hF : ConvexEReal F) (x z : E) (s t : ℝ)
    (hx : F x ≤ (s : EReal)) (hz : F z ≤ (t : EReal)) (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ ≤ 1) :
    F (x + θ • (z - x)) ≤ (((1 - θ) * s + θ * t : ℝ) : EReal) := by
  have hx' : ((x, s) : E × ℝ) ∈ epigraph F := hx
  have hz' : ((z, t) : E × ℝ) ∈ epigraph F := hz
  have hc := hF hx' hz' (by linarith : (0:ℝ) ≤ 1 - θ) h0 (by ring)
  simp only [epigraph, Set.mem_setOf_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hc
  have heq : x + θ • (z - x) = (1 - θ) • x + θ • z := by
    simp only [smul_sub, sub_smul, one_smul]; abel
  rw [heq]; exact hc

lemma ag2_le_of_forall_real (A B : EReal) (h : ∀ s : ℝ, B ≤ (s : EReal) → A ≤ (s : EReal)) :
    A ≤ B := by
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  exact h z hz.le

lemma ag2_real_lim (A B C : ℝ) (h : ∀ t : ℝ, 0 < t → t ≤ 1 → A ≤ B + t * C) : A ≤ B := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hC : 0 < |C| + 1 := by positivity
  set t := min 1 (ε / (|C| + 1)) with ht
  have ht0 : 0 < t := lt_min one_pos (div_pos hε hC)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ ε / (|C| + 1) := min_le_right _ _
  have h1 := h t ht0 ht1
  have h2 : t * C ≤ ε := by
    have h4 : t * C ≤ t * |C| := mul_le_mul_of_nonneg_left (le_abs_self C) ht0.le
    have h3 : t * (|C| + 1) ≤ ε := by rwa [le_div_iff₀ hC] at ht2
    nlinarith [abs_nonneg C]
  linarith

lemma convex_min_sub (F : E → EReal) (hF : ConvexEReal F) (w : E) (hw1 : ⊥ < F w) (hw2 : F w < ⊤)
    (a b : ℝ) (x : E)
    (hmin : ∀ z, F w + ((a * ‖w - x‖ ^ 2 + b * ‖w‖ ^ 2 : ℝ) : EReal)
      ≤ F z + ((a * ‖z - x‖ ^ 2 + b * ‖z‖ ^ 2 : ℝ) : EReal)) :
    ∀ z, F w + ((inner ℝ ((2 * a) • (x - w) - (2 * b) • w) (z - w) : ℝ) : EReal) ≤ F z := by
  intro z
  apply ag2_le_of_forall_real
  intro s hs
  obtain ⟨fw, hFw⟩ : ∃ fw : ℝ, F w = (fw : EReal) :=
    ⟨(F w).toReal, (EReal.coe_toReal hw2.ne hw1.ne').symm⟩
  rw [hFw, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have e3 : inner ℝ ((2 * a) • (x - w) - (2 * b) • w) (z - w)
      = -(2 * a) * inner ℝ (w - x) (z - w) - 2 * b * inner ℝ w (z - w) := by
    rw [inner_sub_left, real_inner_smul_left, real_inner_smul_left, ← neg_sub w x, inner_neg_left]
    ring
  rw [e3]
  have key : ∀ t : ℝ, 0 < t → t ≤ 1 → fw ≤ (s + (2 * a) * inner ℝ (w - x) (z - w)
      + 2 * b * inner ℝ w (z - w)) + t * ((a + b) * ‖z - w‖ ^ 2) := by
    intro t ht0 ht1
    have hc := ag2_conv_le F hF w z fw s (le_of_eq hFw) hs t ht0.le ht1
    have hm := hmin (w + t • (z - w))
    rw [hFw, ← EReal.coe_add] at hm
    have hm2 := hm.trans (add_le_add hc le_rfl)
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at hm2
    have e1 : ‖w + t • (z - w) - x‖ ^ 2
        = ‖w - x‖ ^ 2 + 2 * t * inner ℝ (w - x) (z - w) + t ^ 2 * ‖z - w‖ ^ 2 := by
      rw [show w + t • (z - w) - x = (w - x) + t • (z - w) by abel, norm_add_sq_real,
        real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      ring
    have e2 : ‖w + t • (z - w)‖ ^ 2
        = ‖w‖ ^ 2 + 2 * t * inner ℝ w (z - w) + t ^ 2 * ‖z - w‖ ^ 2 := by
      rw [norm_add_sq_real, real_inner_smul_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
      ring
    rw [e1, e2] at hm2
    have h5 : t * fw ≤ t * ((s + (2 * a) * inner ℝ (w - x) (z - w)
      + 2 * b * inner ℝ w (z - w)) + t * ((a + b) * ‖z - w‖ ^ 2)) := by
      linarith
    exact le_of_mul_le_mul_left h5 ht0
  have := ag2_real_lim _ _ _ key
  linarith

lemma reg_global_of_convex (F : E → EReal) (hF : ConvexEReal F) (x v : E)
    (h : IsRegularSubgradientAt F x v) :
    ∀ z, F x + ((inner ℝ v (z - x) : ℝ) : EReal) ≤ F z := by
  obtain ⟨hb, ht, r, hr, V, hV, hVr⟩ := h
  intro z
  apply ag2_le_of_forall_real
  intro s hs
  obtain ⟨fx, hFx⟩ : ∃ fx : ℝ, F x = (fx : EReal) :=
    ⟨(F x).toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩
  rw [hFx, ← EReal.coe_add, EReal.coe_le_coe_iff]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hzx : 0 < ‖z - x‖ + 1 := by positivity
  set δ := ε / (‖z - x‖ + 1) with hδ
  have hδpos : 0 < δ := div_pos hε hzx
  have hev : ∀ᶠ y in 𝓝 x, y ∈ V ∧ ‖r y‖ ≤ δ * ‖‖y - x‖‖ :=
    Filter.Eventually.and hV (hr.bound hδpos)
  have htend : Filter.Tendsto (fun t : ℝ => x + t • (z - x)) (𝓝[>] 0) (𝓝 x) := by
    have h0 : Filter.Tendsto (fun t : ℝ => x + t • (z - x)) (𝓝 0) (𝓝 (x + (0:ℝ) • (z - x))) :=
      (continuous_const.add (continuous_id.smul continuous_const)).tendsto 0
    rw [zero_smul, add_zero] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hev2 := htend.eventually hev
  have hev3 : ∀ᶠ t in 𝓝[>] (0:ℝ), t ∈ Set.Ioo (0:ℝ) 1 := Ioo_mem_nhdsGT one_pos
  obtain ⟨t, ⟨ht0, ht1⟩, hyV, hry⟩ := (hev3.and hev2).exists
  have hc := ag2_conv_le F hF x z fx s (le_of_eq hFx) hs t ht0.le ht1.le
  have hm := hVr _ hyV
  rw [hFx, ← EReal.coe_add] at hm
  have hm2 := hm.trans hc
  rw [EReal.coe_le_coe_iff, add_sub_cancel_left, real_inner_smul_right] at hm2
  rw [add_sub_cancel_left, norm_norm, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos ht0] at hry
  have hr_abs : -(r (x + t • (z - x))) ≤ δ * (t * ‖z - x‖) := by
    linarith [neg_abs_le (r (x + t • (z - x)))]
  have h1 : t * (fx + inner ℝ v (z - x) - s) ≤ t * (δ * ‖z - x‖) := by nlinarith
  have h2 : fx + inner ℝ v (z - x) - s ≤ δ * ‖z - x‖ := le_of_mul_le_mul_left h1 ht0
  have h3 : δ * ‖z - x‖ ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ hzx]
    nlinarith [norm_nonneg (z - x)]
  linarith

lemma lim_global_of_convex (F : E → EReal) (hF : ConvexEReal F) (x v : E)
    (h : IsSubgradientAt F x v) :
    ∀ z, F x + ((inner ℝ v (z - x) : ℝ) : EReal) ≤ F z := by
  obtain ⟨hb, ht, xs, vs, hx, hFx, hv, hreg⟩ := h
  intro z
  have hle : ∀ n, F (xs n) + ((inner ℝ (vs n) (z - xs n) : ℝ) : EReal) ≤ F z :=
    fun n => reg_global_of_convex F hF (xs n) (vs n) (hreg n) z
  have hinner : Filter.Tendsto (fun n => ((inner ℝ (vs n) (z - xs n) : ℝ) : EReal))
      Filter.atTop (𝓝 ((inner ℝ v (z - x) : ℝ) : EReal)) :=
    (continuous_coe_real_ereal.tendsto _).comp (hv.inner (tendsto_const_nhds.sub hx))
  have hca := EReal.continuousAt_add (p := (F x, ((inner ℝ v (z - x) : ℝ) : EReal)))
    (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
  have hsum : Filter.Tendsto (fun n => F (xs n) + ((inner ℝ (vs n) (z - xs n) : ℝ) : EReal))
      Filter.atTop (𝓝 (F x + ((inner ℝ v (z - x) : ℝ) : EReal))) :=
    hca.tendsto.comp (hFx.prodMk_nhds hinner)
  exact le_of_tendsto' hsum hle

lemma ag2_sq_littleO (x : E) (c : ℝ) :
    (fun y : E => c * ‖y - x‖ ^ 2) =o[𝓝 x] (fun y => ‖y - x‖) := by
  have h1 := Asymptotics.isLittleO_pow_sub_pow_sub x (by norm_num : 1 < 2)
  simp only [pow_one] at h1
  exact h1.const_mul_left c

lemma reg_add_quad (F : E → EReal) (c : ℝ) (x v : E) (h : IsRegularSubgradientAt F x v) :
    IsRegularSubgradientAt (fun z => F z + ((c * ‖z‖ ^ 2 : ℝ) : EReal)) x (v + (2 * c) • x) := by
  obtain ⟨hb, ht, r, hr, V, hV, hVr⟩ := h
  obtain ⟨fx, hFx⟩ : ∃ fx : ℝ, F x = (fx : EReal) :=
    ⟨(F x).toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩
  refine ⟨?_, ?_, fun y => r y + c * ‖y - x‖ ^ 2, hr.add (ag2_sq_littleO x c), V, hV,
    fun y hy => ?_⟩
  · simp only [hFx, ← EReal.coe_add]; exact EReal.bot_lt_coe _
  · simp only [hFx, ← EReal.coe_add]; exact EReal.coe_lt_top _
  · have h1 := hVr y hy
    simp only
    rw [hFx] at h1 ⊢
    rw [← EReal.coe_add] at h1
    rw [← EReal.coe_add, ← EReal.coe_add]
    have key : fx + c * ‖x‖ ^ 2 + (inner ℝ (v + (2 * c) • x) (y - x) + (r y + c * ‖y - x‖ ^ 2))
        = (fx + (inner ℝ v (y - x) + r y)) + c * ‖y‖ ^ 2 := by
      have hy2 : ‖y‖ ^ 2 = ‖x‖ ^ 2 + 2 * inner ℝ x (y - x) + ‖y - x‖ ^ 2 := by
        rw [← norm_add_sq_real, add_sub_cancel]
      rw [hy2, inner_add_left, real_inner_smul_left]
      ring
    rw [key, EReal.coe_add]
    exact add_le_add h1 le_rfl

lemma lim_add_quad (F : E → EReal) (c : ℝ) (x v : E) (h : IsSubgradientAt F x v) :
    IsSubgradientAt (fun z => F z + ((c * ‖z‖ ^ 2 : ℝ) : EReal)) x (v + (2 * c) • x) := by
  obtain ⟨hb, ht, xs, vs, hx, hFx, hv, hreg⟩ := h
  obtain ⟨fx, hfx⟩ : ∃ fx : ℝ, F x = (fx : EReal) :=
    ⟨(F x).toReal, (EReal.coe_toReal ht.ne hb.ne').symm⟩
  refine ⟨?_, ?_, xs, fun n => vs n + (2 * c) • xs n, hx, ?_, hv.add (hx.const_smul (2 * c)),
    fun i => reg_add_quad F c (xs i) (vs i) (hreg i)⟩
  · simp only [hfx, ← EReal.coe_add]; exact EReal.bot_lt_coe _
  · simp only [hfx, ← EReal.coe_add]; exact EReal.coe_lt_top _
  · have hq : Filter.Tendsto (fun n => ((c * ‖xs n‖ ^ 2 : ℝ) : EReal)) Filter.atTop
        (𝓝 ((c * ‖x‖ ^ 2 : ℝ) : EReal)) :=
      (continuous_coe_real_ereal.tendsto _).comp (((hx.norm).pow 2).const_mul c)
    have hca := EReal.continuousAt_add (p := (F x, ((c * ‖x‖ ^ 2 : ℝ) : EReal)))
      (Or.inr (EReal.coe_ne_bot _)) (Or.inr (EReal.coe_ne_top _))
    exact hca.tendsto.comp (hFx.prodMk_nhds hq)



-- ===== ag3 =====

/-! ## ag3 lemmas -/

lemma ag3_norm_bound (a B κ M r : ℝ) (hκ : 0 < κ) (hr : 0 ≤ r)
    (h : a - B * r + κ * r ^ 2 ≤ M) : r ≤ (|B| + |a| + |M| + 1) / κ + 1 := by
  rw [div_add_one hκ.ne', le_div_iff₀ hκ]
  rcases le_or_gt r 1 with h1 | h1
  · nlinarith [abs_nonneg B, abs_nonneg a, abs_nonneg M]
  · have hr0 : 0 < r := by linarith
    have hB : B * r ≤ |B| * r := mul_le_mul_of_nonneg_right (le_abs_self B) hr
    have ha : -a ≤ |a| := neg_le_abs a
    have hM : M ≤ |M| := le_abs_self M
    have h2 : κ * r ^ 2 ≤ |M| + |a| + |B| * r := by linarith
    have h3 : |M| + |a| ≤ (|M| + |a|) * r := by nlinarith [abs_nonneg M, abs_nonneg a]
    have h4 : (κ * r) * r ≤ (|M| + |a| + |B|) * r := by nlinarith
    have h5 : κ * r ≤ |M| + |a| + |B| := le_of_mul_le_mul_right h4 hr0
    nlinarith [abs_nonneg B, abs_nonneg a, abs_nonneg M]

lemma exists_min_of_coercive (F : E → EReal) (hlsc : LowerSemicontinuous F) (z₀ : E) (hz₀ : F z₀ < ⊤)
    (a B κ : ℝ) (hκ : 0 < κ) (hbd : ∀ z, ((a - B * ‖z‖ + κ * ‖z‖ ^ 2 : ℝ) : EReal) ≤ F z) :
    ∃ w, ∀ z, F w ≤ F z := by
  set S : Set E := F ⁻¹' Set.Iic (F z₀) with hS
  have hSc : IsClosed S := hlsc.isClosed_preimage (F z₀)
  have hbot : ⊥ < F z₀ := lt_of_lt_of_le (EReal.bot_lt_coe _) (hbd z₀)
  have hFM : F z₀ = ((F z₀).toReal : EReal) := (EReal.coe_toReal hz₀.ne hbot.ne').symm
  have hSb : Bornology.IsBounded S := by
    rw [Metric.isBounded_iff_subset_closedBall (0 : E)]
    refine ⟨(|B| + |a| + |(F z₀).toReal| + 1) / κ + 1, ?_⟩
    intro z hz
    rw [mem_closedBall_zero_iff]
    have hz' : F z ≤ F z₀ := hz
    have h1 : ((a - B * ‖z‖ + κ * ‖z‖ ^ 2 : ℝ) : EReal) ≤ (((F z₀).toReal : ℝ) : EReal) :=
      (hbd z).trans (hz'.trans hFM.le)
    exact ag3_norm_bound a B κ _ _ hκ (norm_nonneg z) (EReal.coe_le_coe_iff.mp h1)
  have hScpt : IsCompact S := Metric.isCompact_of_isClosed_isBounded hSc hSb
  have hne : S.Nonempty := ⟨z₀, le_refl (F z₀)⟩
  obtain ⟨w, hwS, hwmin⟩ :=
    LowerSemicontinuousOn.exists_isMinOn hne hScpt (hlsc.lowerSemicontinuousOn S)
  refine ⟨w, fun z => ?_⟩
  by_cases hz : z ∈ S
  · exact isMinOn_iff.mp hwmin z hz
  · have hz' : ¬ F z ≤ F z₀ := hz
    have hwz₀ : F w ≤ F z₀ := hwS
    exact hwz₀.trans (le_of_lt (not_le.mp hz'))

lemma ag3_epi_closed (F : E → EReal) (hlsc : LowerSemicontinuous F) : IsClosed (epigraph F) := by
  have h1 : IsClosed {p : E × EReal | F p.1 ≤ p.2} := hlsc.isClosed_epigraph
  have h2 : Continuous (fun p : E × ℝ => (p.1, ((p.2 : ℝ) : EReal))) :=
    continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd)
  exact h1.preimage h2

lemma affine_minorant (F : E → EReal) (hF : ConvexEReal F) (hlsc : LowerSemicontinuous F)
    (hbot : ∀ z, ⊥ < F z) (z₀ : E) (hz₀ : F z₀ < ⊤) :
    ∃ a B : ℝ, ∀ z, ((a - B * ‖z‖ : ℝ) : EReal) ≤ F z := by
  set M := (F z₀).toReal with hM
  have hFM : F z₀ = (M : EReal) := (EReal.coe_toReal hz₀.ne (hbot z₀).ne').symm
  have hp₀ : ((z₀, M - 1) : E × ℝ) ∉ epigraph F := by
    intro h
    have h' : F z₀ ≤ ((M - 1 : ℝ) : EReal) := h
    rw [hFM, EReal.coe_le_coe_iff] at h'
    linarith
  obtain ⟨ℓ, u, hℓ0, hℓ⟩ := geometric_hahn_banach_point_closed hF (ag3_epi_closed F hlsc) hp₀
  have hdec : ∀ (z : E) (t : ℝ), ℓ (z, t) = ℓ (z, 0) + t * ℓ (0, 1) := by
    intro z t
    have : ((z, t) : E × ℝ) = (z, 0) + t • ((0 : E), (1 : ℝ)) := by
      ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
  have hq₁ : ((z₀, M) : E × ℝ) ∈ epigraph F := by
    show F z₀ ≤ ((M : ℝ) : EReal)
    rw [hFM]
  have h1 := hℓ _ hq₁
  rw [hdec] at h1 hℓ0
  have hs : 0 < ℓ (0, 1) := by nlinarith
  set L := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hL
  refine ⟨u / ℓ (0, 1), ‖L‖ / ℓ (0, 1), fun z => ?_⟩
  by_cases htop : F z = ⊤
  · rw [htop]; exact le_top
  have hFz : F z = ((F z).toReal : EReal) := (EReal.coe_toReal htop (hbot z).ne').symm
  have hmem : ((z, (F z).toReal) : E × ℝ) ∈ epigraph F := by
    show F z ≤ (((F z).toReal : ℝ) : EReal)
    exact hFz.le
  have h2 := hℓ _ hmem
  rw [hdec] at h2
  have hLz : ℓ (z, 0) ≤ ‖L‖ * ‖z‖ := by
    have h3 := L.le_opNorm z
    rw [Real.norm_eq_abs] at h3
    have h' : L z = ℓ (z, 0) := rfl
    rw [h'] at h3
    exact (le_abs_self _).trans h3
  rw [hFz, EReal.coe_le_coe_iff,
    show u / ℓ (0, 1) - ‖L‖ / ℓ (0, 1) * ‖z‖ = (u - ‖L‖ * ‖z‖) / ℓ (0, 1) by ring,
    div_le_iff₀ hs]
  linarith

lemma ag3_sq_bound (z x : E) : ‖z‖ ^ 2 - 2 * ‖x‖ * ‖z‖ ≤ ‖z - x‖ ^ 2 := by
  have h1 := abs_norm_sub_norm_le z x
  have h2 : (‖z‖ - ‖x‖) ^ 2 ≤ ‖z - x‖ ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  nlinarith [sq_nonneg ‖x‖]

lemma prox_exists (F : E → EReal) (hlsc : LowerSemicontinuous F) (z₀ : E) (hz₀ : F z₀ < ⊤)
    (a B c μ : ℝ) (hμ : 0 < μ) (hc : c < (2 * μ)⁻¹)
    (hbd : ∀ z, ((a - B * ‖z‖ - c * ‖z‖ ^ 2 : ℝ) : EReal) ≤ F z) (x : E) :
    ∃ w, w ∈ proximalMapping F μ x := by
  have hk0 : 0 < (2 * μ)⁻¹ := by positivity
  have hψlsc : LowerSemicontinuous (fun z => F z + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal)) :=
    lsc_add_cont F hlsc (fun z => (2 * μ)⁻¹ * ‖z - x‖ ^ 2) (by fun_prop)
  have hψz₀ : F z₀ + (((2 * μ)⁻¹ * ‖z₀ - x‖ ^ 2 : ℝ) : EReal) < ⊤ :=
    EReal.add_lt_top hz₀.ne (EReal.coe_ne_top _)
  have hψbd : ∀ z, ((a - (B + 2 * (2 * μ)⁻¹ * ‖x‖) * ‖z‖ + ((2 * μ)⁻¹ - c) * ‖z‖ ^ 2 : ℝ) : EReal) ≤
      F z + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
    intro z
    have h1 : ((a - B * ‖z‖ - c * ‖z‖ ^ 2 : ℝ) : EReal) + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) ≤
        F z + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := add_le_add (hbd z) le_rfl
    refine le_trans ?_ h1
    rw [← EReal.coe_add, EReal.coe_le_coe_iff]
    have h2 := ag3_sq_bound z x
    have h3 : (2 * μ)⁻¹ * (‖z‖ ^ 2 - 2 * ‖x‖ * ‖z‖) ≤ (2 * μ)⁻¹ * ‖z - x‖ ^ 2 :=
      mul_le_mul_of_nonneg_left h2 hk0.le
    nlinarith
  obtain ⟨w, hw⟩ := exists_min_of_coercive _ hψlsc z₀ hψz₀ a (B + 2 * (2 * μ)⁻¹ * ‖x‖)
    ((2 * μ)⁻¹ - c) (by linarith) hψbd
  refine ⟨w, (prox_mem_iff F μ x w).mpr ⟨?_, hw⟩⟩
  by_contra hne
  have htop : F w = ⊤ := not_lt_top_iff.mp hne
  have h4 := (hw z₀).trans_lt hψz₀
  rw [htop, EReal.top_add_coe] at h4
  exact lt_irrefl _ h4


-- ===== ag4 =====

lemma ag4_ereal_le (x : EReal) (a b : ℝ) :
    ((a : EReal) ≤ x + (b : EReal)) ↔ (((a - b : ℝ) : EReal) ≤ x) := by
  induction x using EReal.rec with
  | bot =>
    rw [EReal.bot_add]; simp only [le_bot_iff, EReal.coe_ne_bot]
  | top => simp
  | coe c =>
    rw [← EReal.coe_add, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
    constructor <;> intro h <;> linarith

lemma ag4_fermat (F : E → EReal) (S : E → ℝ) (z₀ v : E) (D : E →L[ℝ] ℝ) (hS : HasFDerivAt S D z₀)
    (hD : ∀ y, D y = - inner ℝ v y) (hb : ⊥ < F z₀) (ht : F z₀ < ⊤) (U : Set E) (hU : U ∈ 𝓝 z₀)
    (hmin : ∀ z ∈ U, F z₀ + ((S z₀ : ℝ) : EReal) ≤ F z + ((S z : ℝ) : EReal)) :
    IsRegularSubgradientAt F z₀ v := by
  refine ⟨hb, ht, fun z => -(S z - S z₀ - D (z - z₀)), ?_, U, hU, fun z hz => ?_⟩
  · exact hS.isLittleO.neg_left.norm_right
  · have h1 := hmin z hz
    have hFa : F z₀ = ((F z₀).toReal : EReal) := (EReal.coe_toReal ht.ne hb.ne').symm
    rw [hFa] at h1 ⊢
    rw [← EReal.coe_add] at h1 ⊢
    rw [ag4_ereal_le] at h1
    have : (F z₀).toReal + (inner ℝ v (z - z₀) + -(S z - S z₀ - D (z - z₀)))
        = (F z₀).toReal + S z₀ - S z := by
      rw [hD]; ring
    rw [this]; exact h1

lemma ag4_lb (G : E → EReal) (hG : LowerSemicontinuous G) (hbot : ∀ z, ⊥ < G z) (K : Set E)
    (hK : IsCompact K) : ∃ m : ℝ, ∀ z ∈ K, (m : EReal) ≤ G z := by
  rcases K.eq_empty_or_nonempty with h | h
  · exact ⟨0, by simp [h]⟩
  · obtain ⟨zm, hzm, hmin⟩ := (hG.lowerSemicontinuousOn K).exists_isMinOn h hK
    rw [isMinOn_iff] at hmin
    by_cases htop : G zm = ⊤
    · refine ⟨0, fun z hz => ?_⟩
      have := hmin z hz
      rw [htop] at this
      exact le_trans le_top this
    · refine ⟨(G zm).toReal, fun z hz => ?_⟩
      rw [EReal.coe_toReal htop (hbot zm).ne']
      exact hmin z hz

-- derivative of the penalized function
lemma ag4_deriv (u c z : E) (κ A : ℝ) (n : ℕ) :
    HasFDerivAt (fun z : E => -inner ℝ u z + κ * ‖z - c‖ ^ 2 + A * (‖z - c‖ ^ 2) ^ n)
      (-(innerSL ℝ u) + κ • (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ E))
        + A • ((n • (‖z - c‖ ^ 2) ^ (n - 1)) • (2 • (innerSL ℝ (z - c)).comp
          (ContinuousLinearMap.id ℝ E)))) z := by
  have h1 : HasFDerivAt (fun z : E => z - c) (ContinuousLinearMap.id ℝ E) z :=
    (hasFDerivAt_id z).sub_const c
  have h2 := h1.norm_sq
  have h3 := h2.pow n
  have h4 := (innerSL ℝ u).hasFDerivAt (x := z)
  have := ((h4.neg).add (h2.const_mul κ)).add (h3.const_mul A)
  convert this using 1

lemma ag4_deriv_apply (u c z : E) (κ A : ℝ) (n : ℕ) (y : E) :
    (-(innerSL ℝ u) + κ • (2 • (innerSL ℝ (z - c)).comp (ContinuousLinearMap.id ℝ E))
        + A • ((n • (‖z - c‖ ^ 2) ^ (n - 1)) • (2 • (innerSL ℝ (z - c)).comp
          (ContinuousLinearMap.id ℝ E)))) y
      = - inner ℝ (u - (2 * κ + A * n * (‖z - c‖ ^ 2) ^ (n - 1) * 2) • (z - c)) y := by
  simp [inner_sub_left, real_inner_smul_left]
  ring

lemma ag4_pml_real (F : E → EReal) (hlsc : LowerSemicontinuous F) (hbot : ∀ z, ⊥ < F z)
    (u c p : E) (R κ η : ℝ) (hR : 0 < R) (hη : 0 < η) (hp : ‖p - c‖ < R)
    (hpt : F p < ⊤) :
    ∃ z β, ‖z - c‖ < R ∧ 2 * κ ≤ β ∧
      (F z).toReal - inner ℝ u z + κ * ‖z - c‖ ^ 2
        ≤ (F p).toReal - inner ℝ u p + κ * ‖p - c‖ ^ 2 + η ∧
      IsRegularSubgradientAt F z (u - β • (z - c)) := by
  obtain ⟨T, hT⟩ : ∃ T : E → ℝ, T = fun z => -inner ℝ u z + κ * ‖z - c‖ ^ 2 := ⟨_, rfl⟩
  have hTc : Continuous T := by rw [hT]; fun_prop
  have hTz : ∀ z, T z = -inner ℝ u z + κ * ‖z - c‖ ^ 2 := fun z => by rw [hT]
  obtain ⟨m, hm⟩ := ag4_lb (fun z => F z + ((T z : ℝ) : EReal)) (lsc_add_cont F hlsc T hTc)
    (fun z => EReal.bot_lt_add_iff.mpr ⟨hbot z, EReal.bot_lt_coe _⟩) (Metric.closedBall c R)
    (isCompact_closedBall c R)
  have hpK : p ∈ Metric.closedBall c R := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hp.le
  have hFp : F p = ((F p).toReal : EReal) := (EReal.coe_toReal hpt.ne (hbot p).ne').symm
  obtain ⟨V₀, hV₀⟩ : ∃ V₀ : ℝ, V₀ = (F p).toReal + T p := ⟨_, rfl⟩
  have hmV : m ≤ V₀ := by
    have := hm p hpK
    simp only at this
    rw [hFp, ← EReal.coe_add, EReal.coe_le_coe_iff] at this
    rw [hV₀]; exact this
  obtain ⟨K₀, hK₀⟩ : ∃ K₀ : ℝ, K₀ = V₀ + η - m + 1 := ⟨_, rfl⟩
  have hK₀pos : 0 < K₀ := by rw [hK₀]; linarith
  have hR0 : R ≠ 0 := hR.ne'
  have hρ1 : ‖p - c‖ ^ 2 / R ^ 2 < 1 := by
    rw [div_lt_one (by positivity)]
    exact pow_lt_pow_left₀ hp (norm_nonneg _) two_ne_zero
  obtain ⟨n, hn⟩ := _root_.exists_pow_lt_of_lt_one (div_pos hη hK₀pos) hρ1
  obtain ⟨A, hA⟩ : ∃ A : ℝ, A = K₀ / (R ^ 2) ^ n := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  obtain ⟨S, hS⟩ : ∃ S : E → ℝ, S = fun z => -inner ℝ u z + κ * ‖z - c‖ ^ 2
      + A * (‖z - c‖ ^ 2) ^ n := ⟨_, rfl⟩
  have hSc : Continuous S := by rw [hS]; fun_prop
  have hST : ∀ z, S z = T z + A * (‖z - c‖ ^ 2) ^ n := fun z => by rw [hS, hT]
  -- minimize F + S on the closed ball
  obtain ⟨zs, hzsK, hmin⟩ := ((lsc_add_cont F hlsc S hSc).lowerSemicontinuousOn
    (Metric.closedBall c R)).exists_isMinOn ⟨p, hpK⟩ (isCompact_closedBall c R)
  rw [isMinOn_iff] at hmin
  have hPp : A * (‖p - c‖ ^ 2) ^ n < η := by
    have : A * (‖p - c‖ ^ 2) ^ n = K₀ * (‖p - c‖ ^ 2 / R ^ 2) ^ n := by
      rw [hA, div_pow]; field_simp
    rw [this]
    calc K₀ * (‖p - c‖ ^ 2 / R ^ 2) ^ n < K₀ * (η / K₀) := mul_lt_mul_of_pos_left hn hK₀pos
      _ = η := by field_simp
  have hHp : F p + ((S p : ℝ) : EReal) = ((V₀ + A * (‖p - c‖ ^ 2) ^ n : ℝ) : EReal) := by
    rw [hFp, ← EReal.coe_add, hST, hV₀]; congr 1; ring
  have hzs_le := hmin p hpK
  simp only at hzs_le
  rw [hHp] at hzs_le
  have hzst : F zs < ⊤ := by
    rcases lt_or_eq_of_le (le_top : F zs ≤ ⊤) with h | h
    · exact h
    · rw [h, EReal.top_add_coe] at hzs_le
      exact absurd hzs_le (not_le.mpr (EReal.coe_lt_top _))
  have hFzs : F zs = ((F zs).toReal : EReal) := (EReal.coe_toReal hzst.ne (hbot zs).ne').symm
  have hzs_real : (F zs).toReal + S zs ≤ V₀ + A * (‖p - c‖ ^ 2) ^ n := by
    rw [hFzs, ← EReal.coe_add, EReal.coe_le_coe_iff] at hzs_le
    exact hzs_le
  have hzs_in : ‖zs - c‖ < R := by
    have h1 : ‖zs - c‖ ≤ R := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hzsK; exact hzsK
    rcases h1.lt_or_eq with h1 | h1
    · exact h1
    · exfalso
      have h2 := hm zs hzsK
      simp only at h2
      rw [hFzs, ← EReal.coe_add, EReal.coe_le_coe_iff] at h2
      have h3 : A * (‖zs - c‖ ^ 2) ^ n = K₀ := by
        rw [h1, hA]; field_simp
      rw [hST, h3] at hzs_real
      linarith
  refine ⟨zs, 2 * κ + A * n * (‖zs - c‖ ^ 2) ^ (n - 1) * 2, hzs_in, ?_, ?_, ?_⟩
  · have : 0 ≤ A * n * (‖zs - c‖ ^ 2) ^ (n - 1) * 2 := by positivity
    linarith
  · have hP0 : 0 ≤ A * (‖zs - c‖ ^ 2) ^ n := by positivity
    rw [hST, hTz] at hzs_real
    rw [hV₀, hTz] at hzs_real
    linarith
  · have hd := ag4_deriv u c zs κ A n
    rw [← hS] at hd
    refine ag4_fermat F S zs _ _ hd (ag4_deriv_apply u c zs κ A n) (hbot zs) hzst
      (Metric.ball c R) (Metric.isOpen_ball.mem_nhds ?_) ?_
    · rw [Metric.mem_ball, dist_eq_norm]; exact hzs_in
    · intro z hz
      exact hmin z (Metric.ball_subset_closedBall hz)

lemma ag4_pml (F : E → EReal) (hlsc : LowerSemicontinuous F) (hbot : ∀ z, ⊥ < F z)
    (u c p : E) (R κ η : ℝ) (hR : 0 < R) (hη : 0 < η) (hp : ‖p - c‖ < R)
    (hpt : F p < ⊤) :
    ∃ (z : E) (β : ℝ), ‖z - c‖ < R ∧ 2 * κ ≤ β ∧
      F z + ((- inner ℝ u z + κ * ‖z - c‖ ^ 2 : ℝ) : EReal)
        ≤ F p + ((- inner ℝ u p + κ * ‖p - c‖ ^ 2 + η : ℝ) : EReal) ∧
      IsRegularSubgradientAt F z (u - β • (z - c)) := by
  obtain ⟨z, β, hzR, hβ, hval, hreg⟩ := ag4_pml_real F hlsc hbot u c p R κ η hR hη hp hpt
  refine ⟨z, β, hzR, hβ, ?_, hreg⟩
  have hFz : F z = ((F z).toReal : EReal) := (EReal.coe_toReal hreg.2.1.ne (hbot z).ne').symm
  have hFp : F p = ((F p).toReal : EReal) := (EReal.coe_toReal hpt.ne (hbot p).ne').symm
  rw [hFz, hFp, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

lemma ag4_global (F : E → EReal) (hlsc : LowerSemicontinuous F) (hbot : ∀ z, ⊥ < F z)
    (hmono : ∀ x₀ x₁ u₀ u₁, IsRegularSubgradientAt F x₀ u₀ → IsRegularSubgradientAt F x₁ u₁ →
      0 ≤ inner ℝ (u₁ - u₀) (x₁ - x₀))
    (w u : E) (hwu : IsRegularSubgradientAt F w u) :
    ∀ z, F w + ((inner ℝ u (z - w) : ℝ) : EReal) ≤ F z := by
  intro z₁
  by_contra hlt
  push_neg at hlt
  have hwt := hwu.2.1
  have hFw : F w = ((F w).toReal : EReal) := (EReal.coe_toReal hwt.ne (hbot w).ne').symm
  have hz₁t : F z₁ < ⊤ := lt_of_lt_of_le hlt (by rw [hFw, ← EReal.coe_add]; exact le_top)
  have hFz₁ : F z₁ = ((F z₁).toReal : EReal) := (EReal.coe_toReal hz₁t.ne (hbot z₁).ne').symm
  rw [hFw, hFz₁, ← EReal.coe_add, EReal.coe_lt_coe_iff] at hlt
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (F w).toReal + inner ℝ u (z₁ - w) - (F z₁).toReal := ⟨_, rfl⟩
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hd0 : 0 < ‖z₁ - w‖ ^ 2 + 1 := by positivity
  obtain ⟨zs, β, hzsR, hβ, hval, hreg⟩ := ag4_pml_real F hlsc hbot u w z₁ (‖z₁ - w‖ + 1)
    (δ / (4 * (‖z₁ - w‖ ^ 2 + 1))) (δ / 4) (by positivity) (by positivity)
    (by linarith) hz₁t
  have hκle : δ / (4 * (‖z₁ - w‖ ^ 2 + 1)) * ‖z₁ - w‖ ^ 2 ≤ δ / 4 := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hne : zs ≠ w := by
    intro heq
    rw [heq, sub_self, norm_zero] at hval
    rw [inner_sub_right] at hδ
    have : δ / (4 * (‖z₁ - w‖ ^ 2 + 1)) * (0:ℝ) ^ 2 = 0 := by ring
    rw [this] at hval
    linarith
  have hm := hmono w zs u (u - β • (zs - w)) hwu hreg
  have e : inner ℝ (u - β • (zs - w) - u) (zs - w) = -β * ‖zs - w‖ ^ 2 := by
    rw [sub_sub_cancel_left, inner_neg_left, real_inner_smul_left, real_inner_self_eq_norm_sq]
    ring
  rw [e] at hm
  have hβpos : 0 < β := by
    have : 0 < δ / (4 * (‖z₁ - w‖ ^ 2 + 1)) := by positivity
    linarith
  have hnpos : 0 < ‖zs - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have : 0 < β * ‖zs - w‖ ^ 2 := by positivity
  linarith

lemma ag4_conv_ineq (F : E → EReal) (hlsc : LowerSemicontinuous F) (hbot : ∀ z, ⊥ < F z)
    (hmono : ∀ x₀ x₁ u₀ u₁, IsRegularSubgradientAt F x₀ u₀ → IsRegularSubgradientAt F x₁ u₁ →
      0 ≤ inner ℝ (u₁ - u₀) (x₁ - x₀))
    (z₀ z₁ : E) (h0 : F z₀ < ⊤) (h1 : F z₁ < ⊤) (t : ℝ) (ht0 : 0 < t) (ht1 : t < 1) :
    F ((1 - t) • z₀ + t • z₁) ≤ (((1 - t) * (F z₀).toReal + t * (F z₁).toReal : ℝ) : EReal) := by
  obtain ⟨zt, hzt⟩ : ∃ zt : E, zt = (1 - t) • z₀ + t • z₁ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = (1 - t) * (F z₀).toReal + t * (F z₁).toReal := ⟨_, rfl⟩
  rw [← hzt, ← hM]
  by_contra hlt
  push_neg at hlt
  have hev := hlsc zt M hlt
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp hev
  obtain ⟨m, hm⟩ := ag4_lb F hlsc hbot (Metric.closedBall zt (‖z₀ - zt‖ + 1))
    (isCompact_closedBall _ _)
  obtain ⟨k, hk⟩ : ∃ k : ℝ, k = (|M - m| + 1) / ε ^ 2 := ⟨_, rfl⟩
  have hkpos : 0 < k := by rw [hk]; positivity
  obtain ⟨w, β, hwR, hβ, -, hreg⟩ := ag4_pml_real F hlsc hbot 0 zt z₀ (‖z₀ - zt‖ + 1) k 1
    (by positivity) one_pos (by linarith) h0
  have hglob := ag4_global F hlsc hbot hmono w _ hreg
  have hwt := hreg.2.1
  have hFw : F w = ((F w).toReal : EReal) := (EReal.coe_toReal hwt.ne (hbot w).ne').symm
  have hF0 : F z₀ = ((F z₀).toReal : EReal) := (EReal.coe_toReal h0.ne (hbot z₀).ne').symm
  have hF1 : F z₁ = ((F z₁).toReal : EReal) := (EReal.coe_toReal h1.ne (hbot z₁).ne').symm
  have g0 := hglob z₀
  have g1 := hglob z₁
  rw [hFw, hF0, ← EReal.coe_add, EReal.coe_le_coe_iff] at g0
  rw [hFw, hF1, ← EReal.coe_add, EReal.coe_le_coe_iff] at g1
  have e : (1 - t) * inner ℝ (0 - β • (w - zt)) (z₀ - w) + t * inner ℝ (0 - β • (w - zt)) (z₁ - w)
      = β * ‖w - zt‖ ^ 2 := by
    have hsum : (1 - t) • (z₀ - w) + t • (z₁ - w) = zt - w := by
      rw [hzt, smul_sub, smul_sub, sub_smul, one_smul, sub_smul, one_smul]; abel
    calc _ = inner ℝ (0 - β • (w - zt)) ((1 - t) • (z₀ - w) + t • (z₁ - w)) := by
            rw [inner_add_right, real_inner_smul_right, real_inner_smul_right]
      _ = inner ℝ (0 - β • (w - zt)) (zt - w) := by rw [hsum]
      _ = β * ‖w - zt‖ ^ 2 := by
            rw [zero_sub, inner_neg_left, real_inner_smul_left, ← neg_sub w zt, inner_neg_right,
              real_inner_self_eq_norm_sq]
            ring
  have key : (F w).toReal + β * ‖w - zt‖ ^ 2 ≤ M := by
    have p0 := mul_le_mul_of_nonneg_left g0 (by linarith : (0:ℝ) ≤ 1 - t)
    have p1 := mul_le_mul_of_nonneg_left g1 ht0.le
    rw [hM]
    nlinarith
  have hwK : w ∈ Metric.closedBall zt (‖z₀ - zt‖ + 1) := by
    rw [Metric.mem_closedBall, dist_eq_norm]; exact hwR.le
  have hmw := hm w hwK
  rw [hFw, EReal.coe_le_coe_iff] at hmw
  have hd2 : 0 ≤ ‖w - zt‖ ^ 2 := by positivity
  have hkε : k * ε ^ 2 = |M - m| + 1 := by rw [hk]; field_simp
  have habs : M - m ≤ |M - m| := le_abs_self _
  have h2k : 2 * k * ‖w - zt‖ ^ 2 ≤ β * ‖w - zt‖ ^ 2 := mul_le_mul_of_nonneg_right hβ hd2
  have hlt2 : k * (2 * ‖w - zt‖ ^ 2) < k * ε ^ 2 := by nlinarith
  have hlt3 : 2 * ‖w - zt‖ ^ 2 < ε ^ 2 := lt_of_mul_lt_mul_left hlt2 hkpos.le
  have hdist : ‖w - zt‖ < ε := by
    by_contra hcon
    push_neg at hcon
    nlinarith
  have hMw : (M : EReal) < F w := hball (by rw [dist_eq_norm]; exact hdist)
  rw [hFw, EReal.coe_lt_coe_iff] at hMw
  have : 0 ≤ β * ‖w - zt‖ ^ 2 := by
    have : 0 ≤ β := by linarith
    positivity
  linarith

lemma mono_convex (F : E → EReal) (hlsc : LowerSemicontinuous F) (hbot : ∀ z, ⊥ < F z)
    (hmono : ∀ x₀ x₁ u₀ u₁, IsRegularSubgradientAt F x₀ u₀ → IsRegularSubgradientAt F x₁ u₁ →
      0 ≤ inner ℝ (u₁ - u₀) (x₁ - x₀)) :
    ConvexEReal F := by
  unfold ConvexEReal
  intro x hx y hy a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq] at hx hy ⊢
  simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hb.lt_or_eq with hb' | hb'
    · have hx0 : F x.1 < ⊤ := lt_of_le_of_lt hx (EReal.coe_lt_top _)
      have hy0 : F y.1 < ⊤ := lt_of_le_of_lt hy (EReal.coe_lt_top _)
      have ha2 : 1 - b = a := by linarith
      have key := ag4_conv_ineq F hlsc hbot hmono x.1 y.1 hx0 hy0 b hb' (by linarith)
      rw [ha2] at key
      refine le_trans key ?_
      rw [EReal.coe_le_coe_iff]
      have hxe : F x.1 = ((F x.1).toReal : EReal) := (EReal.coe_toReal hx0.ne (hbot _).ne').symm
      have hye : F y.1 = ((F y.1).toReal : EReal) := (EReal.coe_toReal hy0.ne (hbot _).ne').symm
      rw [hxe, EReal.coe_le_coe_iff] at hx
      rw [hye, EReal.coe_le_coe_iff] at hy
      exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)
    · subst hb'
      have : a = 1 := by linarith
      subst this
      simpa using hx
  · subst ha'
    have : b = 1 := by linarith
    subst this
    simpa using hy



-- ===== ag5 =====

/-- If `h ≤ g`, `h` is convex and `g ≤ h` wherever `h` is finite, then `g` is convex. -/
lemma ag5_convex_of_le (g h : E → EReal) (hle : ∀ z, h z ≤ g z) (hconv : ConvexEReal h)
    (hkey : ∀ z, h z < ⊤ → g z ≤ h z) : ConvexEReal g := by
  intro p hp q hq a b ha hb hab
  have hp' : p ∈ epigraph h := le_trans (hle p.1) hp
  have hq' : q ∈ epigraph h := le_trans (hle q.1) hq
  have h1 : h (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal) := hconv hp' hq' ha hb hab
  show g (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal)
  exact le_trans (hkey _ (lt_of_le_of_lt h1 (EReal.coe_lt_top _))) h1

/-- Real arithmetic: the choice of `κ` forces `d < ε`. -/
lemma ag5_close (B C ε d κ : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) (hd : 0 ≤ d)
    (hκ : κ = (B * ε + |C| + 1) / ε ^ 2) (h : κ * d ^ 2 ≤ C + B * d) : d < ε := by
  have hκε : κ * ε ^ 2 = B * ε + |C| + 1 := by
    rw [hκ]; field_simp
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hC : C ≤ |C| := le_abs_self C
  have h2 : (κ * ε - B) * ε = |C| + 1 := by linear_combination hκε
  have hκB : 0 < κ * ε - B := by
    by_contra hc
    push_neg at hc
    nlinarith [mul_nonneg (neg_nonneg.mpr hc) hε.le, abs_nonneg C]
  by_contra hcon
  push_neg at hcon
  nlinarith [mul_nonneg hκpos.le (mul_nonneg (sub_nonneg.mpr hcon) hd),
    mul_nonneg (sub_nonneg.mpr hcon) hκB.le]

/-- A finite EReal plus a real is the coercion of its `toReal`. -/
lemma ag5_fin (u : EReal) (r : ℝ) (h1 : ⊥ < u) (h2 : u < ⊤) :
    u + (r : EReal) = (((u + (r : EReal)).toReal : ℝ) : EReal) := by
  rw [← EReal.coe_toReal h2.ne h1.ne', ← EReal.coe_add, EReal.toReal_coe]

/-- Key abstract claim: `g ≤ h` wherever `h` is finite. -/
lemma ag5_key (g h : E → EReal) (hg_lsc : LowerSemicontinuous g) (hh_lsc : LowerSemicontinuous h)
    (hconv : ConvexEReal h) (a B : ℝ) (hB : 0 ≤ B) (hmin : ∀ z, ((a - B * ‖z‖ : ℝ) : EReal) ≤ h z)
    (hclos : ∀ w s, ⊥ < h w → h w < ⊤ →
      (∀ z, h w + ((inner ℝ s (z - w) : ℝ) : EReal) ≤ h z) → g w ≤ h w)
    (zb : E) (hzb : h zb < ⊤) : g zb ≤ h zb := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨y, hy1, hy2⟩ := EReal.lt_iff_exists_real_btwn.mp hcon
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff.mp (hg_lsc zb (y : EReal) hy2)
  have hzb_bot : ⊥ < h zb := lt_of_lt_of_le (EReal.bot_lt_coe _) (hmin zb)
  obtain ⟨H, hH⟩ : ∃ H : ℝ, h zb = (H : EReal) :=
    ⟨(h zb).toReal, (EReal.coe_toReal hzb.ne hzb_bot.ne').symm⟩
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = H - a + B * ‖zb‖ := ⟨_, rfl⟩
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (B * ε + |C| + 1) / ε ^ 2 := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hΦ_lsc : LowerSemicontinuous (fun z => h z + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal)) :=
    lsc_add_cont h hh_lsc (fun z => κ * ‖z - zb‖ ^ 2) (by fun_prop)
  have hΦzb : h zb + ((κ * ‖zb - zb‖ ^ 2 : ℝ) : EReal) = h zb := by simp
  have hΦ_bd : ∀ z, ((a - (B + 2 * κ * ‖zb‖) * ‖z‖ + κ * ‖z‖ ^ 2 : ℝ) : EReal) ≤
      h z + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal) := by
    intro z
    have hreal : a - (B + 2 * κ * ‖zb‖) * ‖z‖ + κ * ‖z‖ ^ 2 ≤ (a - B * ‖z‖) + κ * ‖z - zb‖ ^ 2 := by
      rw [norm_sub_sq_real]
      nlinarith [mul_nonneg hκpos.le (sq_nonneg ‖zb‖),
        mul_nonneg hκpos.le (sub_nonneg.mpr (real_inner_le_norm z zb))]
    calc ((a - (B + 2 * κ * ‖zb‖) * ‖z‖ + κ * ‖z‖ ^ 2 : ℝ) : EReal)
        ≤ (((a - B * ‖z‖) + κ * ‖z - zb‖ ^ 2 : ℝ) : EReal) := EReal.coe_le_coe_iff.mpr hreal
      _ = ((a - B * ‖z‖ : ℝ) : EReal) + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal) := EReal.coe_add _ _
      _ ≤ h z + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal) := add_le_add (hmin z) le_rfl
  obtain ⟨w, hw⟩ := exists_min_of_coercive (fun z => h z + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal))
    hΦ_lsc zb (by simp only []; rw [hΦzb]; exact hzb) a (B + 2 * κ * ‖zb‖) κ hκpos hΦ_bd
  have hw' : ∀ z, h w + ((κ * ‖w - zb‖ ^ 2 : ℝ) : EReal) ≤ h z + ((κ * ‖z - zb‖ ^ 2 : ℝ) : EReal) :=
    hw
  have hw_le : h w + ((κ * ‖w - zb‖ ^ 2 : ℝ) : EReal) ≤ h zb := hΦzb ▸ hw' zb
  have hhw_le_Φ : h w ≤ h w + ((κ * ‖w - zb‖ ^ 2 : ℝ) : EReal) := by
    calc h w = h w + ((0 : ℝ) : EReal) := by simp
      _ ≤ h w + ((κ * ‖w - zb‖ ^ 2 : ℝ) : EReal) :=
          add_le_add le_rfl (EReal.coe_le_coe_iff.mpr (by positivity))
  have hw_top : h w < ⊤ := lt_of_le_of_lt (le_trans hhw_le_Φ hw_le) hzb
  have hw_bot : ⊥ < h w := lt_of_lt_of_le (EReal.bot_lt_coe _) (hmin w)
  obtain ⟨Hw, hHw⟩ : ∃ Hw : ℝ, h w = (Hw : EReal) :=
    ⟨(h w).toReal, (EReal.coe_toReal hw_top.ne hw_bot.ne').symm⟩
  have hineq1 : Hw + κ * ‖w - zb‖ ^ 2 ≤ H := by
    have : ((Hw + κ * ‖w - zb‖ ^ 2 : ℝ) : EReal) ≤ (H : EReal) := by
      rw [EReal.coe_add, ← hHw, ← hH]; exact hw_le
    exact EReal.coe_le_coe_iff.mp this
  have hineq2 : a - B * ‖w‖ ≤ Hw := by
    have := hmin w
    rw [hHw] at this
    exact EReal.coe_le_coe_iff.mp this
  have hnorm : ‖w‖ ≤ ‖zb‖ + ‖w - zb‖ := by
    have := norm_sub_norm_le w zb; linarith
  have hBn : B * ‖w‖ ≤ B * ‖zb‖ + B * ‖w - zb‖ := by
    rw [← mul_add]; exact mul_le_mul_of_nonneg_left hnorm hB
  have hdist : ‖w - zb‖ < ε := by
    apply ag5_close B C ε ‖w - zb‖ κ hB hε (norm_nonneg _) hκ
    rw [hC]
    linarith
  have hgw : (y : EReal) < g w := hball (by rw [dist_eq_norm]; exact hdist)
  have hsub0 := convex_min_sub h hconv w hw_bot hw_top κ 0 zb (by
    intro z
    have := hw' z
    simp only [zero_mul, add_zero]
    exact this)
  have hsub : ∀ z, h w + ((inner ℝ ((2 * κ) • (zb - w)) (z - w) : ℝ) : EReal) ≤ h z := by
    intro z
    have := hsub0 z
    simp only [mul_zero, zero_smul, sub_zero] at this
    exact this
  have hgw_le := hclos w ((2 * κ) • (zb - w)) hw_bot hw_top hsub
  have hlt : g w < (y : EReal) :=
    lt_of_le_of_lt hgw_le (lt_of_le_of_lt (le_trans hhw_le_Φ hw_le) hy1)
  exact absurd (lt_trans hgw hlt) (lt_irrefl _)

/-- Closure property: a global subgradient of `h` at `w` gives (by maximality) `w ∈ P (lam • s)`,
hence `g w ≤ h w`. -/
lemma ag5_clos (f : E → EReal) (lam : ℝ) (h_lam : 0 < lam) (hbot : ∀ z, ⊥ < f z)
    (hmax : IsMaximalMonotone (proximalMapping f lam)) (h : E → EReal)
    (hle : ∀ z, h z ≤ proxPerturbedFun f lam z)
    (hA : ∀ x p, p ∈ proximalMapping f lam x → ∀ z,
        (((proxPerturbedFun f lam p).toReal + inner ℝ (lam⁻¹ • x) (z - p) : ℝ) : EReal) ≤ h z)
    (w s : E) (hw1 : ⊥ < h w) (hw2 : h w < ⊤)
    (hsub : ∀ z, h w + ((inner ℝ s (z - w) : ℝ) : EReal) ≤ h z) :
    proxPerturbedFun f lam w ≤ h w := by
  obtain ⟨Hw, hHw⟩ : ∃ Hw : ℝ, h w = (Hw : EReal) :=
    ⟨(h w).toReal, (EReal.coe_toReal hw2.ne hw1.ne').symm⟩
  have gfin : ∀ x p, p ∈ proximalMapping f lam x →
      proxPerturbedFun f lam p = (((proxPerturbedFun f lam p).toReal : ℝ) : EReal) := by
    intro x p hp
    exact ag5_fin (f p) _ (hbot p) hp.1
  have hrel : ∀ x p, p ∈ proximalMapping f lam x → 0 ≤ inner ℝ (w - p) (lam • s - x) := by
    intro x p hp
    have h1 := hA x p hp w
    have h3 := le_trans (hsub p) (hle p)
    rw [hHw] at h1 h3
    rw [gfin x p hp, ← EReal.coe_add] at h3
    have r1 := EReal.coe_le_coe_iff.mp h1
    have r2 := EReal.coe_le_coe_iff.mp h3
    have e1 : inner ℝ (lam⁻¹ • x) (w - p) = lam⁻¹ * inner ℝ (w - p) x := by
      rw [real_inner_smul_left, real_inner_comm (w - p) x]
    have e2 : inner ℝ s (p - w) = - inner ℝ (w - p) s := by
      rw [← neg_sub w p, inner_neg_right, real_inner_comm (w - p) s]
    have e3 : inner ℝ (w - p) (lam • s - x) = lam * inner ℝ (w - p) s - inner ℝ (w - p) x := by
      rw [inner_sub_right, real_inner_smul_right]
    rw [e3]
    rw [e1] at r1
    rw [e2] at r2
    have key : lam⁻¹ * inner ℝ (w - p) x ≤ inner ℝ (w - p) s := by linarith
    have := mul_le_mul_of_nonneg_left key h_lam.le
    rw [← mul_assoc, mul_inv_cancel₀ h_lam.ne', one_mul] at this
    linarith
  have hwP : w ∈ proximalMapping f lam (lam • s) := by
    by_contra hnot
    obtain ⟨xt, vt, hvt, hlt⟩ := hmax.2 (lam • s) w hnot
    have := hrel xt vt hvt
    linarith
  have := hA (lam • s) w hwP w
  simp only [sub_self, inner_zero_right, add_zero] at this
  rw [gfin _ _ hwP]
  exact this

lemma maxmono_convex (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) (hmax : IsMaximalMonotone (proximalMapping f lam)) :
    ConvexEReal (proxPerturbedFun f lam) := by
  have hbot : ∀ z, ⊥ < f z := hf_proper.1
  have hg_lsc : LowerSemicontinuous (proxPerturbedFun f lam) :=
    lsc_add_cont f hf_lsc (fun z => (2 * lam)⁻¹ * ‖z‖ ^ 2) (by fun_prop)
  have gfin : ∀ x p, p ∈ proximalMapping f lam x →
      proxPerturbedFun f lam p = (((proxPerturbedFun f lam p).toReal : ℝ) : EReal) := by
    intro x p hp
    exact ag5_fin (f p) _ (hbot p) hp.1
  -- the family of exact affine minorants indexed by the graph of the proximal mapping
  let A : {q : E × E // q.2 ∈ proximalMapping f lam q.1} → E → ℝ := fun q z =>
    (proxPerturbedFun f lam q.1.2).toReal + inner ℝ (lam⁻¹ • q.1.1) (z - q.1.2)
  obtain ⟨h, hh⟩ : ∃ h : E → EReal, h = fun z => ⨆ q, ((A q z : ℝ) : EReal) := ⟨_, rfl⟩
  have hA_le_h : ∀ q z, ((A q z : ℝ) : EReal) ≤ h z := by
    intro q z
    rw [hh]
    exact le_iSup (fun q => ((A q z : ℝ) : EReal)) q
  have hA_le_g : ∀ q z, ((A q z : ℝ) : EReal) ≤ proxPerturbedFun f lam z := by
    intro q z
    have := ((prox_iff_g f lam h_lam hbot q.1.1 q.1.2).mp q.2).2 z
    rw [gfin q.1.1 q.1.2 q.2, ← EReal.coe_add] at this
    exact this
  have hle : ∀ z, h z ≤ proxPerturbedFun f lam z := by
    intro z
    rw [hh]
    exact iSup_le (fun q => hA_le_g q z)
  have hh_lsc : LowerSemicontinuous h := by
    rw [hh]
    apply lowerSemicontinuous_iSup
    intro q
    apply Continuous.lowerSemicontinuous
    apply continuous_coe_real_ereal.comp
    show Continuous (fun z => (proxPerturbedFun f lam q.1.2).toReal + inner ℝ (lam⁻¹ • q.1.1) (z - q.1.2))
    fun_prop
  have hconv : ConvexEReal h := by
    intro p hp q hq a b ha hb hab
    have hp' : h p.1 ≤ (p.2 : EReal) := hp
    have hq' : h q.1 ≤ (q.2 : EReal) := hq
    show h (a • p + b • q).1 ≤ ((a • p + b • q).2 : EReal)
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    rw [hh]
    apply iSup_le
    intro i
    have h1 := EReal.coe_le_coe_iff.mp (le_trans (hA_le_h i p.1) hp')
    have h2 := EReal.coe_le_coe_iff.mp (le_trans (hA_le_h i q.1) hq')
    apply EReal.coe_le_coe_iff.mpr
    have hlin : A i (a • p.1 + b • q.1) = a * A i p.1 + b * A i q.1 := by
      simp only [A, inner_sub_right, inner_add_right, real_inner_smul_right]
      linear_combination (inner ℝ (lam⁻¹ • i.1.1) i.1.2 - (proxPerturbedFun f lam i.1.2).toReal) * hab
    rw [hlin]
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  -- the graph of the proximal mapping is nonempty
  obtain ⟨x₀, p₀, hp₀⟩ : ∃ x p, p ∈ proximalMapping f lam x := by
    by_cases h0 : (0 : E) ∈ proximalMapping f lam 0
    · exact ⟨0, 0, h0⟩
    · obtain ⟨xt, vt, hvt, _⟩ := hmax.2 0 0 h0
      exact ⟨xt, vt, hvt⟩
  -- an affine minorant of `h`
  have hmin : ∀ z, ((((proxPerturbedFun f lam p₀).toReal - inner ℝ (lam⁻¹ • x₀) p₀)
      - ‖lam⁻¹ • x₀‖ * ‖z‖ : ℝ) : EReal) ≤ h z := by
    intro z
    refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hA_le_h ⟨(x₀, p₀), hp₀⟩ z)
    show (proxPerturbedFun f lam p₀).toReal - inner ℝ (lam⁻¹ • x₀) p₀ - ‖lam⁻¹ • x₀‖ * ‖z‖
      ≤ (proxPerturbedFun f lam p₀).toReal + inner ℝ (lam⁻¹ • x₀) (z - p₀)
    rw [inner_sub_right]
    have := (abs_le.mp (abs_real_inner_le_norm (lam⁻¹ • x₀) z)).1
    linarith
  have hkey : ∀ z, h z < ⊤ → proxPerturbedFun f lam z ≤ h z := by
    intro z hz
    refine ag5_key (proxPerturbedFun f lam) h hg_lsc hh_lsc hconv
      ((proxPerturbedFun f lam p₀).toReal - inner ℝ (lam⁻¹ • x₀) p₀) ‖lam⁻¹ • x₀‖ (norm_nonneg _)
      hmin ?_ z hz
    intro w s hw1 hw2 hsub
    exact ag5_clos f lam h_lam hbot hmax h hle (fun x p hp z => hA_le_h ⟨(x, p), hp⟩ z)
      w s hw1 hw2 hsub
  exact ag5_convex_of_le (proxPerturbedFun f lam) h hle hconv hkey



-- ===== ag6 =====

lemma ag6_key (x y u v : E) (α γ : ℝ) (hα : 0 ≤ α)
    (h : 0 ≤ inner ℝ ((α • (y - v) - γ • v) - (α • (x - u) - γ • u)) (v - u)) :
    (α + γ) * ‖v - u‖ ≤ α * ‖y - x‖ := by
  have e : (α • (y - v) - γ • v) - (α • (x - u) - γ • u) = α • (y - x) - (α + γ) • (v - u) := by
    simp only [smul_sub, add_smul]; abel
  rw [e, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq] at h
  have h2 := real_inner_le_norm (y - x) (v - u)
  have hn : 0 ≤ ‖v - u‖ := norm_nonneg _
  have hm : 0 ≤ ‖y - x‖ := norm_nonneg _
  rcases hn.lt_or_eq with hpos | hz
  · have h3 : (α + γ) * ‖v - u‖ * ‖v - u‖ ≤ α * ‖y - x‖ * ‖v - u‖ := by nlinarith
    exact le_of_mul_le_mul_right h3 hpos
  · rw [← hz]; simp only [mul_zero]; positivity

lemma ag6_ereal_sub_le (X : EReal) (r s : ℝ) (hX : ⊥ < X) (h : (r : EReal) ≤ X + (s : EReal)) :
    ((r - s : ℝ) : EReal) ≤ X := by
  rcases eq_or_ne X ⊤ with hXt | hXt
  · rw [hXt]; exact le_top
  · have e : X = ((X.toReal : ℝ) : EReal) := (EReal.coe_toReal hXt hX.ne').symm
    rw [e] at h ⊢
    rw [← EReal.coe_add, EReal.coe_le_coe_iff] at h
    rw [EReal.coe_le_coe_iff]
    linarith

lemma ag6_g_bot (f : E → EReal) (lam : ℝ) (hbot : ∀ z, ⊥ < f z) (z : E) :
    ⊥ < proxPerturbedFun f lam z := by
  unfold proxPerturbedFun
  exact EReal.bot_lt_add_iff.mpr ⟨hbot z, EReal.bot_lt_coe _⟩

lemma ag6_g_top (f : E → EReal) (lam : ℝ) (z : E) (hz : f z < ⊤) :
    proxPerturbedFun f lam z < ⊤ := by
  unfold proxPerturbedFun
  exact EReal.add_lt_top hz.ne (EReal.coe_ne_top _)

lemma ag6_f_top (f : E → EReal) (lam : ℝ) (z : E) (hz : proxPerturbedFun f lam z < ⊤) :
    f z < ⊤ := by
  unfold proxPerturbedFun at hz
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h, EReal.top_add_coe] at hz
  exact lt_irrefl _ hz

lemma ag6_g_lsc (f : E → EReal) (lam : ℝ) (hf_lsc : LowerSemicontinuous f) :
    LowerSemicontinuous (proxPerturbedFun f lam) :=
  lsc_add_cont f hf_lsc (fun z => (2 * lam)⁻¹ * ‖z‖ ^ 2) (by fun_prop)

lemma nonexp_of_convex (F : E → EReal) (μ : ℝ) (hbot : ∀ z, ⊥ < F z) (hF : ConvexEReal F) (hμ : 0 < μ) :
    IsNonexpansive (proximalMapping F μ) := by
  intro z₀ z₁ w₀ w₁ h0 h1
  rw [prox_mem_iff] at h0 h1
  obtain ⟨h0t, h0m⟩ := h0
  obtain ⟨h1t, h1m⟩ := h1
  have hs0 := convex_min_sub F hF w₀ (hbot w₀) h0t ((2 * μ)⁻¹) 0 z₀ (by
    intro z; simp only [zero_mul, add_zero]; exact h0m z)
  have hs1 := convex_min_sub F hF w₁ (hbot w₁) h1t ((2 * μ)⁻¹) 0 z₁ (by
    intro z; simp only [zero_mul, add_zero]; exact h1m z)
  have hmono := global_sub_mono F w₀ w₁ _ _ (hbot w₀) h0t (hbot w₁) h1t hs0 hs1
  have hk := ag6_key z₀ z₁ w₀ w₁ (2 * (2 * μ)⁻¹) (2 * 0) (by positivity) hmono
  simp only [mul_zero, add_zero] at hk
  exact le_of_mul_le_mul_left hk (by positivity)

lemma convex_maxmono (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) (hg : ConvexEReal (proxPerturbedFun f lam)) :
    IsMaximalMonotone (proximalMapping f lam) := by
  refine ⟨part1 f lam hf_proper h_lam, ?_⟩
  intro xh vh hvh
  obtain ⟨hbot, z₀, hz₀⟩ := hf_proper
  have g_lsc := ag6_g_lsc f lam hf_lsc
  have g_bot := ag6_g_bot f lam hbot
  have g_z₀ := ag6_g_top f lam z₀ hz₀
  obtain ⟨a, B, hab⟩ := affine_minorant _ hg g_lsc g_bot z₀ g_z₀
  obtain ⟨vt, hvt⟩ := prox_exists _ g_lsc z₀ g_z₀ a B 0 lam h_lam (by positivity)
    (by intro z; simp only [zero_mul, sub_zero]; exact hab z) (xh + vh)
  rw [prox_mem_iff] at hvt
  obtain ⟨hvtt, hvtm⟩ := hvt
  have hsub := convex_min_sub _ hg vt (g_bot vt) hvtt ((2 * lam)⁻¹) 0 (xh + vh) (by
    intro z; simp only [zero_mul, add_zero]; exact hvtm z)
  have hmem : vt ∈ proximalMapping f lam (xh + vh - vt) := by
    rw [prox_iff_g f lam h_lam hbot]
    refine ⟨ag6_f_top f lam vt hvtt, fun z => ?_⟩
    have e : (2 * (2 * lam)⁻¹) • (xh + vh - vt) - (2 * 0 : ℝ) • vt = lam⁻¹ • (xh + vh - vt) := by
      have : (2 * (2 * lam)⁻¹) = lam⁻¹ := by field_simp
      rw [this, mul_zero, zero_smul, sub_zero]
    have := hsub z
    rw [e] at this
    exact this
  refine ⟨xh + vh - vt, vt, hmem, ?_⟩
  have e2 : xh - (xh + vh - vt) = -(vh - vt) := by abel
  rw [e2, inner_neg_right, real_inner_self_eq_norm_sq]
  have hne : vh - vt ≠ 0 := by
    intro h
    have hv : vh = vt := sub_eq_zero.mp h
    apply hvh
    have e3 : xh + vh - vt = xh := by rw [hv]; abel
    rw [e3] at hmem
    rw [hv]; exact hmem
  have : 0 < ‖vh - vt‖ := norm_pos_iff.mpr hne
  have : 0 < ‖vh - vt‖ ^ 2 := by positivity
  linarith

lemma part4 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) (hconv : ConvexEReal f) : IsSingleValued (proximalMapping f lam) := by
  intro x
  obtain ⟨hbot, z₀, hz₀⟩ := hf_proper
  obtain ⟨a, B, hab⟩ := affine_minorant f hconv hf_lsc hbot z₀ hz₀
  obtain ⟨w, hw⟩ := prox_exists f hf_lsc z₀ hz₀ a B 0 lam h_lam (by positivity)
    (by intro z; simp only [zero_mul, sub_zero]; exact hab z) x
  refine ⟨w, hw, fun w' hw' => ?_⟩
  have h := nonexp_of_convex f lam hbot hconv h_lam x x w w' hw hw'
  rw [sub_self, norm_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)

lemma part9 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) : (ConvexEReal (proxPerturbedFun f lam) →
    ∀ (μ : ℝ), 0 < μ → μ < lam →
      IsSingleValued (proximalMapping f μ) ∧
      ∀ (x y : E), ∀ u ∈ proximalMapping f μ x, ∀ v ∈ proximalMapping f μ y,
        ‖u - v‖ ≤ (lam / (lam - μ)) * ‖x - y‖) := by
  intro hg μ hμ hμlam
  obtain ⟨hbot, z₀, hz₀⟩ := hf_proper
  have g_lsc := ag6_g_lsc f lam hf_lsc
  have g_bot := ag6_g_bot f lam hbot
  have g_z₀ := ag6_g_top f lam z₀ hz₀
  obtain ⟨a, B, hab⟩ := affine_minorant _ hg g_lsc g_bot z₀ g_z₀
  have hbd : ∀ z, ((a - B * ‖z‖ - (2 * lam)⁻¹ * ‖z‖ ^ 2 : ℝ) : EReal) ≤ f z := by
    intro z
    exact ag6_ereal_sub_le (f z) _ _ (hbot z) (hab z)
  have hc : (2 * lam)⁻¹ < (2 * μ)⁻¹ := by
    rw [inv_lt_inv₀ (by positivity) (by positivity)]; linarith
  have key : ∀ z x : E, proxPerturbedFun f lam z
      + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 + -(2 * lam)⁻¹ * ‖z‖ ^ 2 : ℝ) : EReal)
      = f z + (((2 * μ)⁻¹ * ‖z - x‖ ^ 2 : ℝ) : EReal) := by
    intro z x
    unfold proxPerturbedFun
    rw [add_assoc, ← EReal.coe_add]
    congr 2
    ring
  have hsubg : ∀ x u : E, u ∈ proximalMapping f μ x → ∀ z, proxPerturbedFun f lam u
      + ((inner ℝ ((2 * (2 * μ)⁻¹) • (x - u) - (2 * -(2 * lam)⁻¹) • u) (z - u) : ℝ) : EReal)
      ≤ proxPerturbedFun f lam z := by
    intro x u hu
    rw [prox_mem_iff] at hu
    obtain ⟨hut, hum⟩ := hu
    exact convex_min_sub _ hg u (g_bot u) (ag6_g_top f lam u hut) ((2 * μ)⁻¹) (-(2 * lam)⁻¹) x
      (by intro z; rw [key, key]; exact hum z)
  have hlip : ∀ (x y : E), ∀ u ∈ proximalMapping f μ x, ∀ v ∈ proximalMapping f μ y,
      ‖u - v‖ ≤ (lam / (lam - μ)) * ‖x - y‖ := by
    intro x y u hu v hv
    have hmono := global_sub_mono _ u v _ _ (g_bot u) (ag6_g_top f lam u hu.1)
      (g_bot v) (ag6_g_top f lam v hv.1) (hsubg x u hu) (hsubg y v hv)
    have e1 : 2 * (2 * μ)⁻¹ + 2 * -(2 * lam)⁻¹ = (lam - μ) / (μ * lam) := by
      field_simp; ring
    have e2 : 2 * (2 * μ)⁻¹ = lam / (μ * lam) := by
      field_simp
    have hk := ag6_key x y u v (2 * (2 * μ)⁻¹) (2 * -(2 * lam)⁻¹) (by positivity) hmono
    rw [e1, e2] at hk
    rw [norm_sub_rev u v, norm_sub_rev x y]
    have hml : 0 < μ * lam := by positivity
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hml] at hk
    rw [div_mul_eq_mul_div, le_div_iff₀ (by linarith)]
    linarith
  refine ⟨fun x => ?_, hlip⟩
  obtain ⟨w, hw⟩ := prox_exists f hf_lsc z₀ hz₀ a B ((2 * lam)⁻¹) μ hμ hc hbd x
  refine ⟨w, hw, fun w' hw' => ?_⟩
  have h := hlip x x w' hw' w hw
  rw [sub_self, norm_zero, mul_zero] at h
  exact sub_eq_zero.mp (norm_le_zero_iff.mp h)



-- ===== ag7 =====

/-- `conjugate f v ≤ t` iff all the terms are `≤ t`. -/
lemma ag7_conj_le_iff (f : E → EReal) (v : E) (t : EReal) :
    conjugate f v ≤ t ↔ ∀ x, ((inner ℝ v x : ℝ) : EReal) - f x ≤ t := by
  unfold conjugate
  rw [sSup_le_iff]
  simp

lemma ag7_le_conj (f : E → EReal) (v x : E) :
    ((inner ℝ v x : ℝ) : EReal) - f x ≤ conjugate f v := by
  unfold conjugate
  exact le_sSup ⟨x, Set.mem_univ _, rfl⟩

lemma conjugate_convex (f : E → EReal) : ConvexEReal (conjugate f) := by
  intro p hp q hq a b ha hb hab
  simp only [epigraph, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at hp hq ⊢
  rw [ag7_conj_le_iff] at hp hq ⊢
  intro x
  have h1 := hp x
  have h2 := hq x
  by_cases hbot : f x = ⊥
  · rw [hbot, EReal.coe_sub_bot] at h1
    exact absurd h1 (by simp)
  by_cases htop : f x = ⊤
  · rw [htop, EReal.sub_top]
    exact bot_le
  have hfx : f x = ((f x).toReal : EReal) := (EReal.coe_toReal htop hbot).symm
  rw [hfx, ← EReal.coe_sub] at h1 h2 ⊢
  rw [EReal.coe_le_coe_iff] at h1 h2 ⊢
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  have e1 := mul_le_mul_of_nonneg_left h1 ha
  have e2 := mul_le_mul_of_nonneg_left h2 hb
  have : a * inner ℝ p.1 x + b * inner ℝ q.1 x - (f x).toReal
      = a * (inner ℝ p.1 x - (f x).toReal) + b * (inner ℝ q.1 x - (f x).toReal) := by
    rw [← sub_eq_zero]
    have : b = 1 - a := by linarith
    subst this
    ring
  rw [this]
  linarith

lemma conjugate_bot (f : E → EReal) (hf : IsProper f) : ∀ v, ⊥ < conjugate f v := by
  intro v
  obtain ⟨x₀, hx₀⟩ := hf.2
  have htop : f x₀ ≠ ⊤ := ne_of_lt hx₀
  have hbot : f x₀ ≠ ⊥ := ne_of_gt (hf.1 x₀)
  refine lt_of_lt_of_le ?_ (ag7_le_conj f v x₀)
  rw [← EReal.coe_toReal htop hbot, ← EReal.coe_sub]
  exact EReal.bot_lt_coe _


/-- A minimizer `p` of the prox problem (λ = 1) of a convex function gives a global subgradient
`x - p` at `p`. -/
lemma ag7_glob (f : E → EReal) (hbot : ∀ z, ⊥ < f z) (hconv : ConvexEReal f) (x p : E)
    (hp : p ∈ proximalMapping f 1 x) :
    ∀ y, f p + ((inner ℝ (x - p) (y - p) : ℝ) : EReal) ≤ f y := by
  rw [prox_mem_iff] at hp
  obtain ⟨hpt, hpmin⟩ := hp
  have h := convex_min_sub f hconv p (hbot p) hpt ((2 * 1)⁻¹) 0 x (by
    intro z
    have e1 : ((2:ℝ) * 1)⁻¹ * ‖p - x‖ ^ 2 + 0 * ‖p‖ ^ 2 = (2 * 1)⁻¹ * ‖p - x‖ ^ 2 := by ring
    have e2 : ((2:ℝ) * 1)⁻¹ * ‖z - x‖ ^ 2 + 0 * ‖z‖ ^ 2 = (2 * 1)⁻¹ * ‖z - x‖ ^ 2 := by ring
    rw [e1, e2]
    exact hpmin z)
  intro y
  have hy := h y
  have h2 : (2:ℝ) * (2 * 1)⁻¹ = 1 := by norm_num
  rw [h2, one_smul, mul_zero, zero_smul, sub_zero] at hy
  exact hy

/-- If `p = P_f(x)` (λ = 1, f convex) then `x - p ∈ P_{f*}(x)`. -/
lemma ag7_sub_mem (f : E → EReal) (hbot : ∀ z, ⊥ < f z) (hconv : ConvexEReal f) (x p : E)
    (hp : p ∈ proximalMapping f 1 x) :
    x - p ∈ proximalMapping (conjugate f) 1 x := by
  have hglob := ag7_glob f hbot hconv x p hp
  have hpt : f p < ⊤ := hp.1
  obtain ⟨c, hfp⟩ : ∃ c : ℝ, f p = (c : EReal) :=
    ⟨(f p).toReal, (EReal.coe_toReal (ne_of_lt hpt) (ne_of_gt (hbot p))).symm⟩
  -- upper bound
  have hA : conjugate f (x - p) ≤ ((inner ℝ (x - p) p - c : ℝ) : EReal) := by
    rw [ag7_conj_le_iff]
    intro y
    by_cases hyt : f y = ⊤
    · rw [hyt, EReal.sub_top]; exact bot_le
    have hyb : f y ≠ ⊥ := ne_of_gt (hbot y)
    have hfy : f y = ((f y).toReal : EReal) := (EReal.coe_toReal hyt hyb).symm
    have hg := hglob y
    rw [hfp, hfy, ← EReal.coe_add, EReal.coe_le_coe_iff] at hg
    rw [hfy, ← EReal.coe_sub, EReal.coe_le_coe_iff]
    rw [inner_sub_right] at hg
    linarith
  have hB : ∀ u, ((inner ℝ u p - c : ℝ) : EReal) ≤ conjugate f u := by
    intro u
    have := ag7_le_conj f u p
    rwa [hfp, ← EReal.coe_sub] at this
  rw [prox_mem_iff]
  refine ⟨lt_of_le_of_lt hA (EReal.coe_lt_top _), ?_⟩
  intro u
  calc conjugate f (x - p) + (((2 * 1)⁻¹ * ‖x - p - x‖ ^ 2 : ℝ) : EReal)
      ≤ ((inner ℝ (x - p) p - c : ℝ) : EReal) + (((2 * 1)⁻¹ * ‖x - p - x‖ ^ 2 : ℝ) : EReal) := by
        gcongr
    _ ≤ ((inner ℝ u p - c : ℝ) : EReal) + (((2 * 1)⁻¹ * ‖u - x‖ ^ 2 : ℝ) : EReal) := by
        rw [← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
        have e1 : x - p - x = -p := by abel
        rw [e1, norm_neg]
        have e2 : inner ℝ (x - p) p = inner ℝ x p - ‖p‖ ^ 2 := by
          rw [inner_sub_left, real_inner_self_eq_norm_sq]
        have e3 : inner ℝ u p = inner ℝ (u - x) p + inner ℝ x p := by
          rw [inner_sub_left]; ring
        have e4 : ‖(u - x) + p‖ ^ 2 = ‖u - x‖ ^ 2 + 2 * inner ℝ (u - x) p + ‖p‖ ^ 2 :=
          norm_add_sq_real _ _
        have e5 : 0 ≤ ‖(u - x) + p‖ ^ 2 := sq_nonneg _
        have h2 : ((2:ℝ) * 1)⁻¹ = 1 / 2 := by norm_num
        rw [e2, e3, h2]
        linarith
    _ ≤ conjugate f u + (((2 * 1)⁻¹ * ‖u - x‖ ^ 2 : ℝ) : EReal) := by
        gcongr
        exact hB u

lemma part5 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) : lam = 1 → ConvexEReal f →
    subMap idMap (proximalMapping f lam) = proximalMapping (conjugate f) 1 := by
  intro hlam hconv
  subst hlam
  funext x
  ext z
  simp only [subMap, idMap, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · rintro ⟨u, rfl, p, hp, rfl⟩
    exact ag7_sub_mem f hf_proper.1 hconv _ p hp
  · intro hz
    obtain ⟨p, hp, -⟩ := part4 f 1 hf_proper hf_lsc one_pos hconv x
    have hq := ag7_sub_mem f hf_proper.1 hconv x p hp
    have hne := nonexp_of_convex (conjugate f) 1 (conjugate_bot f hf_proper) (conjugate_convex f)
      one_pos x x z (x - p) hz hq
    rw [sub_self, norm_zero] at hne
    have h0 : x - p - z = 0 := norm_le_zero_iff.mp hne
    refine ⟨x, rfl, p, hp, ?_⟩
    rw [sub_eq_zero] at h0
    exact h0.symm

lemma ag7_part6_core (f : E → EReal) (hf_proper : IsProper f) (hconv : ConvexEReal f)
    (z p q x v : E)
    (hp : p ∈ proximalMapping f 1 z) (hpu : ∀ y, y ∈ proximalMapping f 1 z → y = p)
    (hq : q ∈ proximalMapping (conjugate f) 1 z)
    (hqu : ∀ y, y ∈ proximalMapping (conjugate f) 1 z → y = q) :
    (p, q) = (x, v) ↔ z = x + v ∧ v ∈ subdifferential f x := by
  have hqp : q = z - p := (hqu (z - p) (ag7_sub_mem f hf_proper.1 hconv z p hp)).symm
  subst hqp
  rw [Prod.mk.injEq]
  constructor
  · rintro ⟨h1, h2⟩
    subst h1
    subst h2
    refine ⟨by abel, ?_⟩
    simp only [subdifferential, Set.mem_setOf_eq]
    exact lim_of_reg f _ _ (reg_of_global f _ _ (hf_proper.1 _) hp.1
      (ag7_glob f hf_proper.1 hconv z _ hp))
  · rintro ⟨h1, hv⟩
    subst h1
    have hv' : IsSubgradientAt f x v := hv
    have hglob := lim_global_of_convex f hconv x v hv'
    have hx : x ∈ proximalMapping f 1 (x + v) := by
      apply prox_of_sub f 1 one_pos (x + v) x hv'.1 hv'.2.1
      intro y
      have e : (1:ℝ)⁻¹ • (x + v - x) = v := by simp
      rw [e]
      exact hglob y
    have hxp := hpu x hx
    subst hxp
    exact ⟨rfl, by abel⟩

lemma part6 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    : (lam = 1 →
    ConvexEReal f →
    ∃ (hP : IsSingleValued (proximalMapping f 1)),
    ∃ (hQ : IsSingleValued (proximalMapping (conjugate f) 1)),
      let Pfun : E → E := fun z => Classical.choose (hP z)
      let Qfun : E → E := fun z => Classical.choose (hQ z)
      ∀ z x v,
        (Pfun z, Qfun z) = (x, v) ↔
        z = x + v ∧ v ∈ subdifferential f x) := by
  intro hlam hconv
  have hP : IsSingleValued (proximalMapping f 1) := part4 f 1 hf_proper hf_lsc one_pos hconv
  have hQ : IsSingleValued (proximalMapping (conjugate f) 1) := by
    intro z
    obtain ⟨p, hp, hpu⟩ := hP z
    refine ⟨z - p, ag7_sub_mem f hf_proper.1 hconv z p hp, ?_⟩
    intro q hq
    have hq' : q ∈ subMap idMap (proximalMapping f 1) z := by
      rw [part5 f 1 hf_proper hf_lsc one_pos rfl hconv]; exact hq
    obtain ⟨u, hu, p', hp', rfl⟩ := hq'
    rw [hpu p' hp']
    simp only [idMap, Set.mem_singleton_iff] at hu
    rw [hu]
  refine ⟨hP, hQ, ?_⟩
  intro Pfun Qfun z x v
  exact ag7_part6_core f hf_proper hconv z _ _ x v (Classical.choose_spec (hP z)).1
    (Classical.choose_spec (hP z)).2 (Classical.choose_spec (hQ z)).1 (Classical.choose_spec (hQ z)).2



-- ===== ag8 =====

lemma ag8_mem_iff (f : E → EReal) (lam : ℝ) (x z : E) :
    z ∈ addMap idMap (smulMap lam (subdifferential f)) x ↔
      ∃ v, IsSubgradientAt f x v ∧ z = x + lam • v := by
  constructor
  · rintro ⟨u, hu, w, ⟨v, hv, rfl⟩, rfl⟩
    have hux : u = x := hu
    subst hux
    exact ⟨v, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨x, rfl, lam • v, ⟨v, hv, rfl⟩, rfl⟩

lemma ag8_add_coe_cancel (a : EReal) (r : ℝ) : (a + (r : EReal)) + ((-r : ℝ) : EReal) = a := by
  induction a using EReal.rec with
  | bot => simp
  | top => simp
  | coe x =>
    rw [← EReal.coe_add, ← EReal.coe_add]
    congr 1
    ring

lemma ag8_two_inv (lam : ℝ) (h_lam : 0 < lam) : 2 * (2 * lam)⁻¹ = lam⁻¹ := by
  field_simp

lemma ag8_bot_lt_add (a : EReal) (r : ℝ) (h : ⊥ < a) : ⊥ < a + (r : EReal) := by
  induction a using EReal.rec with
  | bot => exact absurd h (lt_irrefl _)
  | top => rw [EReal.top_add_coe]; exact bot_lt_top
  | coe x => rw [← EReal.coe_add]; exact EReal.bot_lt_coe _

lemma ag8_bot_lt (f : E → EReal) (lam : ℝ) (hbot : ∀ z, ⊥ < f z) (z : E) :
    ⊥ < proxPerturbedFun f lam z :=
  ag8_bot_lt_add _ _ (hbot z)

lemma ag8_lsc (f : E → EReal) (lam : ℝ) (hf_lsc : LowerSemicontinuous f) :
    LowerSemicontinuous (proxPerturbedFun f lam) :=
  lsc_add_cont f hf_lsc (fun z => (2 * lam)⁻¹ * ‖z‖ ^ 2) (by fun_prop)

lemma ag8_g_eq_f (f : E → EReal) (lam : ℝ) :
    (fun z => proxPerturbedFun f lam z + ((-(2 * lam)⁻¹ * ‖z‖ ^ 2 : ℝ) : EReal)) = f := by
  funext z
  unfold proxPerturbedFun
  rw [neg_mul]
  exact ag8_add_coe_cancel _ _

lemma part7 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f) (hf_lsc : LowerSemicontinuous f)
    (h_lam : 0 < lam) : List.TFAE [
    IsMaximalMonotone (proximalMapping f lam),
    ConvexEReal (proxPerturbedFun f lam),
    IsMonotone (addMap idMap (smulMap lam (subdifferential f)))
  ] := by
  tfae_have 1 → 2 := maxmono_convex f lam hf_proper hf_lsc h_lam
  tfae_have 2 → 1 := convex_maxmono f lam hf_proper hf_lsc h_lam
  tfae_have 2 → 3 := by
    intro hg x₀ x₁ z₀ z₁ hz₀ hz₁
    rw [ag8_mem_iff] at hz₀ hz₁
    obtain ⟨v₀, hv₀, rfl⟩ := hz₀
    obtain ⟨v₁, hv₁, rfl⟩ := hz₁
    have h0 : IsSubgradientAt (proxPerturbedFun f lam) x₀ (v₀ + (2 * (2 * lam)⁻¹) • x₀) :=
      lim_add_quad f ((2 * lam)⁻¹) x₀ v₀ hv₀
    have h1 : IsSubgradientAt (proxPerturbedFun f lam) x₁ (v₁ + (2 * (2 * lam)⁻¹) • x₁) :=
      lim_add_quad f ((2 * lam)⁻¹) x₁ v₁ hv₁
    have hm := global_sub_mono (proxPerturbedFun f lam) x₀ x₁ _ _ h0.1 h0.2.1 h1.1 h1.2.1
      (lim_global_of_convex _ hg x₀ _ h0) (lim_global_of_convex _ hg x₁ _ h1)
    rw [ag8_two_inv lam h_lam] at hm
    have hkey : x₁ + lam • v₁ - (x₀ + lam • v₀) = lam • (v₁ + lam⁻¹ • x₁ - (v₀ + lam⁻¹ • x₀)) := by
      simp only [smul_sub, smul_add, smul_smul, mul_inv_cancel₀ h_lam.ne', one_smul]
      abel
    rw [hkey, real_inner_smul_left]
    exact mul_nonneg h_lam.le hm
  tfae_have 3 → 2 := by
    intro hmono
    refine mono_convex (proxPerturbedFun f lam) (ag8_lsc f lam hf_lsc)
      (ag8_bot_lt f lam hf_proper.1) ?_
    intro x₀ x₁ u₀ u₁ hu₀ hu₁
    have k0 := reg_add_quad (proxPerturbedFun f lam) (-(2 * lam)⁻¹) x₀ u₀ hu₀
    have k1 := reg_add_quad (proxPerturbedFun f lam) (-(2 * lam)⁻¹) x₁ u₁ hu₁
    rw [ag8_g_eq_f] at k0 k1
    have m0 := (ag8_mem_iff f lam x₀ _).2 ⟨_, lim_of_reg f x₀ _ k0, rfl⟩
    have m1 := (ag8_mem_iff f lam x₁ _).2 ⟨_, lim_of_reg f x₁ _ k1, rfl⟩
    have hm := hmono x₀ x₁ _ _ m0 m1
    have hc : lam * (2 * -(2 * lam)⁻¹) = -1 := by
      field_simp
    have hkey : x₁ + lam • (u₁ + (2 * -(2 * lam)⁻¹) • x₁) - (x₀ + lam • (u₀ + (2 * -(2 * lam)⁻¹) • x₀))
        = lam • (u₁ - u₀) := by
      rw [smul_add, smul_add, smul_smul, smul_smul, hc, smul_sub]
      simp only [neg_one_smul]
      abel
    rw [hkey, real_inner_smul_left] at hm
    exact (mul_nonneg_iff_of_pos_left h_lam).mp hm
  tfae_finish

lemma part8 (f : E → EReal) (lam : ℝ) (hf_proper : IsProper f)
    (h_lam : 0 < lam) : (ConvexEReal (proxPerturbedFun f lam) →
    proximalMapping f lam =
      invMap (addMap idMap (smulMap lam (subdifferential f)))) := by
  intro hg
  funext x
  ext w
  show w ∈ proximalMapping f lam x ↔ x ∈ addMap idMap (smulMap lam (subdifferential f)) w
  rw [ag8_mem_iff]
  constructor
  · intro hw
    have hreg := prox_reg_sub f lam h_lam hf_proper.1 x w hw
    refine ⟨lam⁻¹ • (x - w), lim_of_reg f w _ hreg, ?_⟩
    rw [smul_smul, mul_inv_cancel₀ h_lam.ne', one_smul]
    abel
  · rintro ⟨v, hv, rfl⟩
    have h1 : IsSubgradientAt (proxPerturbedFun f lam) w (v + (2 * (2 * lam)⁻¹) • w) :=
      lim_add_quad f ((2 * lam)⁻¹) w v hv
    have h2 := lim_global_of_convex (proxPerturbedFun f lam) hg w _ h1
    rw [prox_iff_g f lam h_lam hf_proper.1]
    refine ⟨hv.2.1, ?_⟩
    have heq : v + (2 * (2 * lam)⁻¹) • w = lam⁻¹ • (w + lam • v) := by
      rw [ag8_two_inv lam h_lam, smul_add, smul_smul, inv_mul_cancel₀ h_lam.ne', one_smul, add_comm]
    rw [heq] at h2
    exact h2


theorem RW_chap_12_19
  (f : E → EReal)
  (lam : ℝ)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (h_lam : 0 < lam) :
  IsMonotone (proximalMapping f lam) ∧
  (ConvexEReal f → IsMaximalMonotone (proximalMapping f lam)) ∧
  (ConvexEReal f → IsNonexpansive (proximalMapping f lam)) ∧
  (ConvexEReal f → IsSingleValued (proximalMapping f lam)) ∧
  (lam = 1 →
    ConvexEReal f →
    subMap idMap (proximalMapping f lam) =
      proximalMapping (conjugate f) 1) ∧
  (lam = 1 →
    ConvexEReal f →
    ∃ (hP : IsSingleValued (proximalMapping f 1)),
    ∃ (hQ : IsSingleValued (proximalMapping (conjugate f) 1)),
      let Pfun : E → E := fun z => Classical.choose (hP z)
      let Qfun : E → E := fun z => Classical.choose (hQ z)
      ∀ z x v,
        (Pfun z, Qfun z) = (x, v) ↔
        z = x + v ∧ v ∈ subdifferential f x) ∧
  List.TFAE [
    IsMaximalMonotone (proximalMapping f lam),
    ConvexEReal (proxPerturbedFun f lam),
    IsMonotone (addMap idMap (smulMap lam (subdifferential f)))
  ] ∧
  (ConvexEReal (proxPerturbedFun f lam) →
    proximalMapping f lam =
      invMap (addMap idMap (smulMap lam (subdifferential f)))) ∧
  (ConvexEReal (proxPerturbedFun f lam) →
    ∀ (μ : ℝ), 0 < μ → μ < lam →
      IsSingleValued (proximalMapping f μ) ∧
      ∀ (x y : E), ∀ u ∈ proximalMapping f μ x, ∀ v ∈ proximalMapping f μ y,
        ‖u - v‖ ≤ (lam / (lam - μ)) * ‖x - y‖) := by
  exact ⟨part1 f lam hf_proper h_lam, fun h => convex_maxmono f lam hf_proper hf_lsc h_lam (convex_proxPerturbed f lam h_lam h), fun h => nonexp_of_convex f lam hf_proper.1 h h_lam, part4 f lam hf_proper hf_lsc h_lam, part5 f lam hf_proper hf_lsc h_lam, part6 f lam hf_proper hf_lsc, part7 f lam hf_proper hf_lsc h_lam, part8 f lam hf_proper h_lam, part9 f lam hf_proper hf_lsc h_lam⟩

end RW_chap_12_19
