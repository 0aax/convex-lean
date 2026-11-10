import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_4_5`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_4_5` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_4_5`, so the main result is `FCA_chap_D_4_4_5.FCA_chap_D_4_4_5`.
-/

namespace FCA_chap_D_4_4_5

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ F] in
theorem FCA_chap_D_4_4_5
  (Y : Set F)
  (g : E → F → ℝ)
  (hY_compact : IsCompact Y)
  (hf_usc : ∀ x, ∀ y, y ∈ Y → LowerSemicontinuousAt (fun v => (-1 : ℝ) * g x v) y)
  (hf_convex : ∀ y ∈ Y, ConvexOn ℝ Set.univ (fun x => g x y))
  (hf_differentiable : ∀ y ∈ Y, Differentiable ℝ (fun x => g x y))
  (hf_finite : ∀ x, ⨆ y ∈ Y, (g x y : EReal) < ⊤) :
  let F_fun : E → EReal := fun x => ⨆ y ∈ Y, (g x y : EReal)
  ∀ (x₀ : E) (y₀ : F),
    ((y₀ ∈ Y) ∧
      IsMaxOn (fun (y : F) => g x₀ y) Y y₀ ∧
      (∀ (y : F), y ∈ Y → IsMaxOn (fun (y : F) => g x₀ y) Y y → y = y₀)) →
    (∃ (F_finite : E → ℝ),
      (∀ (x : E), (F_finite x : EReal) = F_fun x) ∧
      DifferentiableAt ℝ F_finite x₀ ∧
      (gradient F_finite x₀ = gradient (fun (x : E) => g x y₀) x₀)) := by
  intro F_fun x₀ y₀ hyp
  obtain ⟨hy₀, hmax, huniq⟩ := hyp
  -- real-valued version of the supremum
  set Fr : E → ℝ := fun x => (F_fun x).toReal with hFr
  have hcoe : ∀ x, ((Fr x : ℝ) : EReal) = F_fun x := by
    intro x
    apply EReal.coe_toReal
    · exact (hf_finite x).ne
    · apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot (g x y₀))
      exact le_iSup₂_of_le (f := fun y (_ : y ∈ Y) => ((g x y : ℝ) : EReal)) y₀ hy₀ le_rfl
  have hle : ∀ x, ∀ y ∈ Y, g x y ≤ Fr x := by
    intro x y hy
    have h : ((g x y : ℝ) : EReal) ≤ F_fun x :=
      le_iSup₂_of_le (f := fun y (_ : y ∈ Y) => ((g x y : ℝ) : EReal)) y hy le_rfl
    rw [← hcoe x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hsup : ∀ x (c : ℝ), (∀ y ∈ Y, g x y ≤ c) → Fr x ≤ c := by
    intro x c hc
    have h : F_fun x ≤ (c : EReal) := iSup₂_le fun y hy => EReal.coe_le_coe_iff.mpr (hc y hy)
    rw [← hcoe x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hFx₀ : Fr x₀ = g x₀ y₀ :=
    le_antisymm (hsup x₀ _ fun y hy => hmax hy) (hle x₀ y₀ hy₀)
  -- derivative of g · y₀
  set L := fderiv ℝ (fun x => g x y₀) x₀ with hL
  have hG : HasFDerivAt (fun x => g x y₀) L x₀ := (hf_differentiable y₀ hy₀ x₀).hasFDerivAt
  have hGo := hasFDerivAt_iff_isLittleO_nhds_zero.mp hG
  -- one-sided directional estimate
  have hdir : ∀ v : E, ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < t → t < δ →
      Fr (x₀ + t • v) ≤ Fr x₀ + t * (L v + ε) := by
    intro v ε hε
    -- step 1: choose s
    obtain ⟨s, hs, hs1⟩ : ∃ s > 0, g (x₀ + s • v) y₀ - g x₀ y₀ ≤ s * (L v + ε / 2) := by
      have hc : (0 : ℝ) < ε / (2 * (‖v‖ + 1)) := by positivity
      have hb := hGo.def hc
      have htend : Filter.Tendsto (fun s : ℝ => s • v) (𝓝[>] 0) (𝓝 0) := by
        have h := ((continuous_id.smul continuous_const : Continuous fun s : ℝ => s • v).tendsto
          (0 : ℝ))
        simp only [id, zero_smul] at h
        exact h.mono_left nhdsWithin_le_nhds
      obtain ⟨s, hs1, hs⟩ := ((htend.eventually hb).and self_mem_nhdsWithin).exists
      refine ⟨s, hs, ?_⟩
      simp only [map_smul, smul_eq_mul, norm_smul, Real.norm_eq_abs] at hs1
      rw [abs_of_pos hs] at hs1
      have h2 := (abs_le.mp hs1).2
      have h3 : ε / (2 * (‖v‖ + 1)) * (s * ‖v‖) ≤ s * (ε / 2) := by
        have h4 : ε / (2 * (‖v‖ + 1)) * ‖v‖ ≤ ε / 2 := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
          nlinarith [norm_nonneg v]
        nlinarith
      nlinarith
    -- step 2: neighbourhood U of y₀
    set x₁ := x₀ + s • v with hx₁
    have hU : ∀ᶠ y in 𝓝 y₀, g x₁ y < g x₁ y₀ + s * ε / 2 := by
      have h := (lowerSemicontinuousAt_iff.mp (hf_usc x₁ y₀ hy₀))
        ((-1) * g x₁ y₀ - s * ε / 2) (by nlinarith)
      filter_upwards [h] with y hy
      linarith
    obtain ⟨U, hUsub, hUopen, hy₀U⟩ := mem_nhds_iff.mp hU
    -- step 3: strict upper bound off U
    obtain ⟨M', hM'lt, hM'⟩ : ∃ M', M' < g x₀ y₀ ∧ ∀ y ∈ Y \ U, g x₀ y ≤ M' := by
      rcases (Y \ U).eq_empty_or_nonempty with hK | hK
      · refine ⟨g x₀ y₀ - 1, by linarith, ?_⟩
        intro y hy
        rw [hK] at hy
        exact absurd hy (Set.notMem_empty y)
      · have husc : UpperSemicontinuousOn (fun y => g x₀ y) (Y \ U) := by
          intro y hy c hc
          have h := (lowerSemicontinuousAt_iff.mp (hf_usc x₀ y hy.1)) (-c) (by simp; linarith)
          apply Filter.Eventually.filter_mono nhdsWithin_le_nhds
          filter_upwards [h] with z hz
          simp at hz
          linarith
        obtain ⟨y', hy'K, hy'max⟩ := husc.exists_isMaxOn hK (hY_compact.diff hUopen)
        refine ⟨g x₀ y', ?_, fun y hy => hy'max hy⟩
        by_contra hcon
        push_neg at hcon
        have hm : IsMaxOn (fun y => g x₀ y) Y y' := fun y hy => le_trans (hmax hy) hcon
        have heq := huniq y' hy'K.1 hm
        exact hy'K.2 (heq ▸ hy₀U)
    -- step 4: conclude
    obtain ⟨δ', hδ', hδ'D⟩ : ∃ δ' > 0, ∀ lam : ℝ, 0 ≤ lam → lam < δ' →
        lam * (Fr x₁ - M' - s * (L v + ε)) ≤ g x₀ y₀ - M' := by
      refine ⟨(g x₀ y₀ - M') / (|Fr x₁ - M' - s * (L v + ε)| + 1),
        div_pos (by linarith) (by positivity), ?_⟩
      intro lam hlam0 hlamlt
      rw [lt_div_iff₀ (by positivity)] at hlamlt
      nlinarith [mul_le_mul_of_nonneg_left (le_abs_self (Fr x₁ - M' - s * (L v + ε))) hlam0]
    refine ⟨s * min 1 δ', by positivity, ?_⟩
    intro t ht htδ
    rw [hFx₀]
    apply hsup
    intro y hy
    set lam := t / s with hlam
    have hlam0 : 0 ≤ lam := by positivity
    have hlamlt : lam < min 1 δ' := by
      rw [hlam, div_lt_iff₀ hs]; linarith
    have hlam1 : lam ≤ 1 := le_trans hlamlt.le (min_le_left _ _)
    have hlamδ : lam < δ' := lt_of_lt_of_le hlamlt (min_le_right _ _)
    have hts : t = lam * s := by rw [hlam, div_mul_cancel₀ t hs.ne']
    have hconv := (hf_convex y hy).2 (Set.mem_univ x₀) (Set.mem_univ x₁)
      (sub_nonneg.mpr hlam1) hlam0 (by ring)
    have hpt : (1 - lam) • x₀ + lam • x₁ = x₀ + t • v := by
      rw [hx₁, smul_add, smul_smul, ← hts, ← add_assoc, ← add_smul, sub_add_cancel, one_smul]
    simp only [smul_eq_mul] at hconv
    rw [hpt] at hconv
    have hgoal : g x₀ y₀ + lam * (s * (L v + ε)) = g x₀ y₀ + t * (L v + ε) := by
      rw [hts]; ring
    rw [← hgoal]
    by_cases hyU : y ∈ U
    · have h1 : g x₀ y ≤ g x₀ y₀ := hmax hy
      have h2 : g x₁ y < g x₁ y₀ + s * ε / 2 := hUsub hyU
      linarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hlam1),
        mul_le_mul_of_nonneg_left h2.le hlam0, mul_le_mul_of_nonneg_left hs1 hlam0]
    · have h1 := hM' y ⟨hy, hyU⟩
      have h2 := hle x₁ y hy
      have h3 := hδ'D lam hlam0 hlamδ
      linarith [mul_le_mul_of_nonneg_left h1 (sub_nonneg.mpr hlam1),
        mul_le_mul_of_nonneg_left h2 hlam0]
  -- two-sided directional estimate
  have hφ0 : ∀ v : E, ∀ ε > 0, ∀ᶠ t in 𝓝 (0:ℝ),
      Fr (x₀ + t • v) - Fr x₀ - L (t • v) ≤ ε * |t| := by
    intro v ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hdir v ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := hdir (-v) ε hε
    rw [Metric.eventually_nhds_iff]
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun t ht => ?_⟩
    rw [Real.dist_eq, sub_zero] at ht
    have ht1 : |t| < δ₁ := lt_of_lt_of_le ht (min_le_left _ _)
    have ht2 : |t| < δ₂ := lt_of_lt_of_le ht (min_le_right _ _)
    rw [map_smul, smul_eq_mul]
    rcases lt_trichotomy t 0 with h | h | h
    · have h' := h₂ (-t) (neg_pos.mpr h) (by rw [abs_of_neg h] at ht2; exact ht2)
      rw [neg_smul_neg, map_neg] at h'
      rw [abs_of_neg h]
      nlinarith
    · subst h; simp
    · have h' := h₁ t h (by rw [abs_of_pos h] at ht1; exact ht1)
      rw [abs_of_pos h]
      nlinarith
  -- convexity of Fr
  have hFconv : ConvexOn ℝ Set.univ Fr := by
    refine ⟨convex_univ, fun a _ c _ α β hα hβ hαβ => ?_⟩
    apply hsup
    intro y hy
    have h := (hf_convex y hy).2 (Set.mem_univ a) (Set.mem_univ c) hα hβ hαβ
    simp only [smul_eq_mul] at h ⊢
    exact le_trans h (add_le_add (mul_le_mul_of_nonneg_left (hle a y hy) hα)
      (mul_le_mul_of_nonneg_left (hle c y hy) hβ))
  have hφconv : ConvexOn ℝ Set.univ (fun h => Fr (x₀ + h) - Fr x₀ - L h) := by
    refine ⟨convex_univ, fun a _ c _ α β hα hβ hαβ => ?_⟩
    have h1 : x₀ + (α • a + β • c) = α • (x₀ + a) + β • (x₀ + c) := by
      rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hαβ, one_smul]
    have h2 := hFconv.2 (Set.mem_univ (x₀ + a)) (Set.mem_univ (x₀ + c)) hα hβ hαβ
    have h3 : α * Fr x₀ + β * Fr x₀ = Fr x₀ := by rw [← add_mul, hαβ, one_mul]
    simp only [smul_eq_mul, map_add, map_smul] at h2 ⊢
    rw [h1]
    linarith
  -- Fréchet upper bound
  have hup : ∀ ε > 0, ∀ᶠ h in 𝓝 (0:E), Fr (x₀ + h) - Fr x₀ - L h ≤ ε * ‖h‖ := by
    intro ε hε
    set n := Module.finrank ℝ E with hn
    set b := stdOrthonormalBasis ℝ E with hb
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · filter_upwards with h
      have h0 : h = 0 := by
        rw [← b.sum_repr' h]
        apply Finset.sum_eq_zero
        intro i _
        exact absurd i.2 (by omega)
      subst h0
      simp
    · have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
      have hev : ∀ i, ∀ᶠ h in 𝓝 (0:E),
          Fr (x₀ + ((n:ℝ) * inner ℝ (b i) h) • b i) - Fr x₀ - L (((n:ℝ) * inner ℝ (b i) h) • b i)
            ≤ (ε / n) * |(n:ℝ) * inner ℝ (b i) h| := by
        intro i
        have hc : Filter.Tendsto (fun h : E => (n:ℝ) * inner ℝ (b i) h) (𝓝 0) (𝓝 0) := by
          have hcont : Continuous (fun h : E => (n:ℝ) * inner ℝ (b i) h) :=
            continuous_const.mul (continuous_const.inner continuous_id)
          simpa using hcont.tendsto 0
        exact hc.eventually (hφ0 (b i) (ε / n) (by positivity))
      filter_upwards [Filter.eventually_all.mpr hev] with h hh
      have hsum : ∑ i, (1/(n:ℝ)) • (((n:ℝ) * inner ℝ (b i) h) • b i) = h := by
        conv_rhs => rw [← b.sum_repr' h]
        apply Finset.sum_congr rfl
        intro i _
        rw [smul_smul]
        congr 1
        field_simp
      have hw : ∑ _i : Fin n, (1/(n:ℝ)) = 1 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        field_simp
      have hJ := hφconv.map_sum_le (t := Finset.univ) (w := fun _ => 1/(n:ℝ))
        (p := fun i => ((n:ℝ) * inner ℝ (b i) h) • b i) (fun i _ => by positivity) hw
        (fun i _ => Set.mem_univ _)
      simp only at hJ
      rw [hsum] at hJ
      refine le_trans hJ ?_
      calc ∑ i, (1/(n:ℝ)) • (Fr (x₀ + ((n:ℝ) * inner ℝ (b i) h) • b i) - Fr x₀
              - L (((n:ℝ) * inner ℝ (b i) h) • b i))
          ≤ ∑ _i : Fin n, (1/(n:ℝ)) * (ε * ‖h‖) := by
            apply Finset.sum_le_sum
            intro i _
            rw [smul_eq_mul]
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            refine le_trans (hh i) ?_
            have hi : |inner ℝ (b i) h| ≤ ‖h‖ := by
              have := abs_real_inner_le_norm (b i) h
              rwa [b.orthonormal.1 i, one_mul] at this
            rw [abs_mul, abs_of_pos hnR]
            have : ε / n * (n * |inner ℝ (b i) h|) = ε * |inner ℝ (b i) h| := by
              field_simp
            rw [this]
            exact mul_le_mul_of_nonneg_left hi hε.le
        _ = ε * ‖h‖ := by
            rw [← Finset.sum_mul, hw, one_mul]
  -- main: HasFDerivAt Fr L x₀
  have key : HasFDerivAt Fr L x₀ := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
    intro ε hε
    filter_upwards [hup ε hε, hGo.def hε] with h h1 h2
    rw [Real.norm_eq_abs, abs_le]
    rw [Real.norm_eq_abs, abs_le] at h2
    have h3 := hle (x₀ + h) y₀ hy₀
    constructor
    · rw [hFx₀]; linarith [h2.1]
    · exact h1
  refine ⟨Fr, hcoe, key.differentiableAt, ?_⟩
  unfold gradient
  rw [key.fderiv]

end FCA_chap_D_4_4_5
