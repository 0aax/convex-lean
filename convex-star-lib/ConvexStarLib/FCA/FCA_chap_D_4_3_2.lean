import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_3_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_3_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_3_2`, so the main result is `FCA_chap_D_4_3_2.FCA_chap_D_4_3_2`.
-/

namespace FCA_chap_D_4_3_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

namespace FCAD432

open Filter Set

/-- Real directional derivative, defined as the infimum of difference quotients. -/
noncomputable def dirD (g : E → ℝ) (x d : E) : ℝ :=
  sInf ((fun t : ℝ => (g (x + t • d) - g x) / t) '' Ioi 0)

lemma convexOn_line {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) :
    ConvexOn ℝ univ (fun t : ℝ => g (x + t • d)) := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  have h := hg.2 (mem_univ (x + a • d)) (mem_univ (x + b • d)) hμ hν hμν
  have e : x + (μ • a + ν • b) • d = μ • (x + a • d) + ν • (x + b • d) := by
    obtain rfl : ν = 1 - μ := by linarith
    simp only [smul_eq_mul]
    module
  show g (x + (μ • a + ν • b) • d) ≤ μ • g (x + a • d) + ν • g (x + b • d)
  rw [e]
  exact h

lemma dq_mono {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) :
    (g (x + s • d) - g x) / s ≤ (g (x + t • d) - g x) / t := by
  have h := (convexOn_line hg x d).secant_mono (a := 0) (x := s) (y := t) (mem_univ _)
    (mem_univ _) (mem_univ _) hs.ne' (by linarith) hst
  simpa using h

lemma dq_lower {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) {t : ℝ} (ht : 0 < t) :
    g x - g (x - d) ≤ (g (x + t • d) - g x) / t := by
  have h := (convexOn_line hg x d).secant_mono (a := 0) (x := -1) (y := t) (mem_univ _)
    (mem_univ _) (mem_univ _) (by norm_num) ht.ne' (by linarith)
  simp only [zero_smul, add_zero, sub_zero, neg_smul, one_smul, ← sub_eq_add_neg] at h
  rw [div_neg, div_one, neg_sub] at h
  exact h

lemma dq_bdd {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) :
    BddBelow ((fun t : ℝ => (g (x + t • d) - g x) / t) '' Ioi 0) :=
  ⟨g x - g (x - d), by rintro _ ⟨t, ht, rfl⟩; exact dq_lower hg x d ht⟩

lemma dirD_tendsto {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) :
    Tendsto (fun t : ℝ => (g (x + t • d) - g x) / t) (𝓝[>] 0) (𝓝 (dirD g x d)) :=
  MonotoneOn.tendsto_nhdsGT (fun _ hs _ _ hst => dq_mono hg x d hs hst) (dq_bdd hg x d)

lemma dirD_le {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) {t : ℝ} (ht : 0 < t) :
    dirD g x d ≤ (g (x + t • d) - g x) / t :=
  csInf_le (dq_bdd hg x d) ⟨t, ht, rfl⟩

lemma tendsto_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

lemma dirD_smul {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) {c : ℝ} (hc : 0 < c) :
    dirD g x (c • d) = c * dirD g x d := by
  have h2 : Tendsto (fun t : ℝ => c * ((g (x + (c * t) • d) - g x) / (c * t))) (𝓝[>] 0)
      (𝓝 (c * dirD g x d)) :=
    ((dirD_tendsto hg x d).comp (tendsto_mul_nhdsGT hc)).const_mul c
  refine tendsto_nhds_unique (dirD_tendsto hg x (c • d)) (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t:ℝ) ≠ 0 := ne_of_gt ht
  rw [smul_smul, mul_comm t c]
  field_simp

lemma dirD_zero (g : E → ℝ) (x : E) : dirD g x 0 = 0 := by
  simp only [dirD, smul_zero, add_zero, sub_self, zero_div]
  rw [Set.Nonempty.image_const nonempty_Ioi, csInf_singleton]

lemma dirD_add {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d₁ d₂ : E) :
    dirD g x (d₁ + d₂) ≤ dirD g x d₁ + dirD g x d₂ := by
  have h2 := tendsto_mul_nhdsGT (c := 2) two_pos
  have h1 := ((dirD_tendsto hg x d₁).comp h2).add ((dirD_tendsto hg x d₂).comp h2)
  refine ge_of_tendsto h1 ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (0:ℝ) < t := ht
  refine (dirD_le hg x (d₁ + d₂) ht').trans ?_
  have hconv := hg.2 (mem_univ (x + (2 * t) • d₁)) (mem_univ (x + (2 * t) • d₂))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have e : (1/2 : ℝ) • (x + (2 * t) • d₁) + (1/2 : ℝ) • (x + (2 * t) • d₂)
      = x + t • (d₁ + d₂) := by
    module
  rw [e] at hconv
  simp only [Function.comp_apply, smul_eq_mul] at hconv ⊢
  rw [← add_div, div_le_div_iff₀ ht' (by positivity)]
  nlinarith

lemma exists_subgrad {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) :
    ∃ s : E, (∀ v, inner ℝ s v ≤ dirD g x v) ∧ inner ℝ s d = dirD g x d := by
  have hneg : ∀ v, -dirD g x v ≤ dirD g x (-v) := by
    intro v
    have := dirD_add hg x v (-v)
    rw [add_neg_cancel, dirD_zero] at this
    linarith
  have hhom : ∀ c : ℝ, 0 < c → ∀ v, dirD g x (c • v) = c * dirD g x v :=
    fun c hc v => dirD_smul hg x v hc
  have hle : ∀ c : ℝ, c * dirD g x d ≤ dirD g x (c • d) := by
    intro c
    rcases lt_trichotomy c 0 with hc | rfl | hc
    · have : c • d = (-c) • (-d) := by rw [smul_neg, neg_smul, neg_neg]
      rw [this, hhom (-c) (by linarith) (-d)]
      nlinarith [hneg d]
    · simp [dirD_zero]
    · rw [hhom c hc d]
  let ψ : E →ₗ.[ℝ] ℝ := LinearPMap.mkSpanSingleton' d (dirD g x d) (by
    intro c hc
    rcases eq_or_ne c 0 with rfl | hc0
    · simp
    · have hd : d = 0 := by
        rcases smul_eq_zero.1 hc with h | h
        · exact absurd h hc0
        · exact h
      subst hd; simp [dirD_zero])
  obtain ⟨ℓ, hℓ1, hℓ2⟩ := exists_extension_of_le_sublinear ψ (dirD g x) hhom (dirD_add hg x) (by
    rintro ⟨v, hv⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    rw [LinearPMap.mkSpanSingleton'_apply]
    simpa [smul_eq_mul] using hle c)
  refine ⟨(InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap ℓ), fun v => ?_, ?_⟩
  · rw [InnerProductSpace.toDual_symm_apply]
    simpa using hℓ2 v
  · rw [InnerProductSpace.toDual_symm_apply]
    have := hℓ1 ⟨d, Submodule.mem_span_singleton_self d⟩
    simp only [LinearMap.coe_toContinuousLinearMap']
    rw [this]
    exact LinearPMap.mkSpanSingleton'_apply_self _ _ _ _

lemma isClosed_sub (D : E → ℝ) : IsClosed {s : E | ∀ d, inner ℝ s d ≤ D d} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun d => isClosed_le (continuous_id.inner continuous_const) continuous_const

lemma convex_sub (D : E → ℝ) : Convex ℝ {s : E | ∀ d, inner ℝ s d ≤ D d} := by
  intro s₁ hs₁ s₂ hs₂ a b ha hb hab d
  have h1 := mul_le_mul_of_nonneg_left (hs₁ d) ha
  have h2 := mul_le_mul_of_nonneg_left (hs₂ d) hb
  rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  calc a * inner ℝ s₁ d + b * inner ℝ s₂ d ≤ a * D d + b * D d := add_le_add h1 h2
    _ = D d := by rw [← add_mul, hab, one_mul]

lemma bdd_sub {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x : E) :
    Bornology.IsBounded {s : E | ∀ d, inner ℝ s d ≤ dirD g x d} := by
  have hc : Continuous g := hg.locallyLipschitz.continuous
  obtain ⟨M, hM⟩ := (isCompact_closedBall x 1).exists_bound_of_continuousOn hc.continuousOn
  have hx := hM x (Metric.mem_closedBall_self zero_le_one)
  rw [isBounded_iff_forall_norm_le]
  refine ⟨2 * M, fun s hs => ?_⟩
  rcases eq_or_ne s 0 with rfl | hs0
  · simp only [norm_zero]; linarith [norm_nonneg (g x)]
  · have hns : ‖s‖ ≠ 0 := norm_ne_zero_iff.2 hs0
    set v : E := ‖s‖⁻¹ • s with hv_def
    have hv : ‖v‖ = 1 := by
      rw [hv_def, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hns]
    have h1 : inner ℝ s v = ‖s‖ := by
      rw [hv_def, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have h2 := hs v
    have h3 := dirD_le hg x v one_pos
    have h4 := hM (x + v) (by rw [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left, hv])
    rw [one_smul, div_one] at h3
    rw [Real.norm_eq_abs] at h4 hx
    have := abs_le.1 h4
    have := abs_le.1 hx
    linarith

lemma isCompact_convexHull_iUnion {ι : Type*} [Finite ι] (K : ι → Set E)
    (hK : ∀ i, IsCompact (K i)) (hKc : ∀ i, Convex ℝ (K i)) (hKn : ∀ i, (K i).Nonempty) :
    IsCompact (convexHull ℝ (⋃ i, K i)) := by
  classical
  have := Fintype.ofFinite ι
  have hSc : IsCompact ((fun p : (ι → ℝ) × (ι → E) => ∑ i, p.1 i • p.2 i) ''
      (stdSimplex ℝ ι ×ˢ Set.univ.pi K)) := by
    apply IsCompact.image ((isCompact_stdSimplex ι).prod (isCompact_univ_pi hK))
    fun_prop
  have hsub : (fun p : (ι → ℝ) × (ι → E) => ∑ i, p.1 i • p.2 i) ''
      (stdSimplex ℝ ι ×ˢ Set.univ.pi K) ⊆ convexHull ℝ (⋃ i, K i) := by
    rintro _ ⟨⟨w, c⟩, ⟨hw, hc⟩, rfl⟩
    exact (convex_convexHull ℝ _).sum_mem (fun i _ => hw.1 i) hw.2
      (fun i _ => subset_convexHull ℝ _ (mem_iUnion_of_mem i (hc i (mem_univ i))))
  have hsup : convexHull ℝ (⋃ i, K i) ⊆ (fun p : (ι → ℝ) × (ι → E) => ∑ i, p.1 i • p.2 i) ''
      (stdSimplex ℝ ι ×ˢ Set.univ.pi K) := by
    refine convexHull_min ?_ ?_
    · rintro y hy
      obtain ⟨j, hj⟩ := mem_iUnion.1 hy
      choose c₀ hc₀ using hKn
      refine ⟨⟨Pi.single j 1, Function.update c₀ j y⟩, ⟨single_mem_stdSimplex ℝ j, ?_⟩, ?_⟩
      · intro i _
        rcases eq_or_ne i j with rfl | hij
        · simp [hj]
        · simp [hij, hc₀ i]
      · simp [Pi.single_apply]
    · rintro _ ⟨⟨w, c⟩, ⟨hw, hc⟩, rfl⟩ _ ⟨⟨w', c'⟩, ⟨hw', hc'⟩, rfl⟩ a b ha hb hab
      refine ⟨⟨a • w + b • w', fun i => if a * w i + b * w' i = 0 then c i else
          ((a * w i) / (a * w i + b * w' i)) • c i + ((b * w' i) / (a * w i + b * w' i)) • c' i⟩,
        ⟨convex_stdSimplex ℝ ι hw hw' ha hb hab, ?_⟩, ?_⟩
      · intro i _
        dsimp only
        split_ifs with h
        · exact hc i (mem_univ i)
        · have h0 : 0 ≤ a * w i + b * w' i :=
            add_nonneg (mul_nonneg ha (hw.1 i)) (mul_nonneg hb (hw'.1 i))
          have hpos : 0 < a * w i + b * w' i := lt_of_le_of_ne h0 (Ne.symm h)
          exact hKc i (hc i (mem_univ i)) (hc' i (mem_univ i))
            (div_nonneg (mul_nonneg ha (hw.1 i)) hpos.le)
            (div_nonneg (mul_nonneg hb (hw'.1 i)) hpos.le) (by rw [← add_div, div_self h])
      · dsimp only
        rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        split_ifs with h
        · have p1 := mul_nonneg ha (hw.1 i)
          have p2 := mul_nonneg hb (hw'.1 i)
          have h1 : a * w i = 0 := by linarith
          have h2 : b * w' i = 0 := by linarith
          rw [h, zero_smul, smul_smul, smul_smul, h1, h2, zero_smul, zero_smul, add_zero]
        · rw [smul_add, smul_smul, smul_smul, smul_smul, smul_smul, mul_div_cancel₀ _ h,
            mul_div_cancel₀ _ h]
  rw [Set.Subset.antisymm hsup hsub]
  exact hSc

lemma dq_coe (g : E → ℝ) (x d : E) (t : ℝ) :
    differenceQuotient (liftRealtoEReal g) x d t = (((g (x + t • d) - g x) / t : ℝ) : EReal) := by
  simp only [differenceQuotient, liftRealtoEReal, EReal.coe_div, EReal.coe_sub]

lemma dd_eq {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x d : E) :
    directionalDeriv (liftRealtoEReal g) x d = ((dirD g x d : ℝ) : EReal) := by
  unfold directionalDeriv
  simp only [dq_coe]
  exact Tendsto.limUnder_eq (EReal.tendsto_coe.2 (dirD_tendsto hg x d))

lemma dsub_eq {g : E → ℝ} (hg : ConvexOn ℝ univ g) (x : E) :
    directionalSubdifferential (liftRealtoEReal g) x = {s | ∀ d, inner ℝ s d ≤ dirD g x d} := by
  ext s
  simp only [directionalSubdifferential, Set.mem_setOf_eq, dd_eq hg, EReal.coe_le_coe_iff]

end FCAD432

set_option linter.unusedVariables false in
theorem FCA_chap_D_4_3_2 {n m : ℕ}
  (f : Fin m → (E → ℝ))
  (x : E)
  (hm : m > 0)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i)) :
  let F_fun : E → ℝ := fun x => ⨆ i, (f i) x
  let I := {i | (f i) x = F_fun x}
  directionalSubdifferential (liftRealtoEReal F_fun) x =
  convexHull ℝ (⋃ i ∈ I, directionalSubdifferential (liftRealtoEReal (f i)) x) := by

  open FCAD432 Filter Set in
  intro F_fun I
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hle : ∀ i y, f i y ≤ F_fun y := fun i y =>
    le_ciSup (Finite.bddAbove_range (fun j => f j y)) i
  have hF : ConvexOn ℝ univ F_fun := by
    refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
    apply ciSup_le
    intro i
    calc f i (a • y + b • z) ≤ a • f i y + b • f i z :=
          (hf_convex i).2 (mem_univ _) (mem_univ _) ha hb hab
      _ ≤ a • F_fun y + b • F_fun z := by
        simp only [smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hle i y) ha)
          (mul_le_mul_of_nonneg_left (hle i z) hb)
  have hK : ∀ i, directionalSubdifferential (liftRealtoEReal (f i)) x =
      {s | ∀ d, inner ℝ s d ≤ dirD (f i) x d} := fun i => dsub_eq (hf_convex i) x
  rw [dsub_eq hF]
  simp only [hK]
  -- active functions have smaller directional derivatives
  have ha : ∀ i ∈ I, ∀ d, dirD (f i) x d ≤ dirD F_fun x d := by
    intro i hi d
    refine le_of_tendsto_of_tendsto (dirD_tendsto (hf_convex i) x d) (dirD_tendsto hF x d) ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hi' : f i x = F_fun x := hi
    rw [hi']
    exact div_le_div_of_nonneg_right (by linarith [hle i (x + t • d)]) (le_of_lt ht)
  -- the directional derivative of the max is attained by an active function
  have hb : ∀ d, ∃ i ∈ I, dirD F_fun x d ≤ dirD (f i) x d := by
    intro d
    by_contra hcon
    push_neg at hcon
    have hcont : ∀ g : E → ℝ, ConvexOn ℝ univ g →
        Tendsto (fun t : ℝ => g (x + t • d)) (𝓝[>] 0) (𝓝 (g x)) := by
      intro g hg
      have hc : Continuous g := hg.locallyLipschitz.continuous
      have : Tendsto (fun t : ℝ => g (x + t • d)) (𝓝 0) (𝓝 (g (x + (0:ℝ) • d))) :=
        (hc.comp (continuous_const.add (continuous_id.smul continuous_const))).tendsto 0
      rw [zero_smul, add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < t ∧ ∀ i, f i (x + t • d) = F_fun (x + t • d) →
        (f i (x + t • d) - F_fun x) / t < dirD F_fun x d := by
      refine (eventually_mem_nhdsWithin).and (eventually_all.2 fun i => ?_)
      by_cases hi : i ∈ I
      · have hi' : f i x = F_fun x := hi
        filter_upwards [(dirD_tendsto (hf_convex i) x d).eventually_lt_const (hcon i hi)]
          with t ht _
        rw [← hi']
        exact ht
      · have hlt : f i x < F_fun x := lt_of_le_of_ne (hle i x) hi
        filter_upwards [(hcont _ (hf_convex i)).eventually_lt (hcont _ hF) hlt] with t ht heq
        exact absurd heq (ne_of_lt ht)
    obtain ⟨t, ht0, ht⟩ := hev.exists
    obtain ⟨j, hj⟩ := exists_eq_ciSup_of_finite (f := fun i => f i (x + t • d))
    have hj' : f j (x + t • d) = F_fun (x + t • d) := hj
    have h1 := ht j hj'
    have h2 := dirD_le hF x d ht0
    rw [hj'] at h1
    linarith
  apply Set.Subset.antisymm
  · intro s hs
    by_contra hsC
    have hC : IsClosed (convexHull ℝ (⋃ i ∈ I, {s : E | ∀ d, inner ℝ s d ≤ dirD (f i) x d})) := by
      rw [Set.biUnion_eq_iUnion]
      refine (isCompact_convexHull_iUnion _ (fun i => ?_) (fun i => convex_sub _)
        (fun i => ?_)).isClosed
      · exact Metric.isCompact_of_isClosed_isBounded (isClosed_sub _) (bdd_sub (hf_convex _) x)
      · obtain ⟨c, hc, _⟩ := exists_subgrad (hf_convex i) x 0
        exact ⟨c, hc⟩
    obtain ⟨ψ, u, hψ1, hψ2⟩ := geometric_hahn_banach_closed_point (convex_convexHull ℝ _) hC hsC
    have hψ : ∀ v, ψ v = inner ℝ ((InnerProductSpace.toDual ℝ E).symm ψ) v :=
      fun v => (InnerProductSpace.toDual_symm_apply).symm
    obtain ⟨j, hjI, hj⟩ := hb ((InnerProductSpace.toDual ℝ E).symm ψ)
    obtain ⟨c, hc1, hc2⟩ := exists_subgrad (hf_convex j) x ((InnerProductSpace.toDual ℝ E).symm ψ)
    have hcC : c ∈ convexHull ℝ (⋃ i ∈ I, {s : E | ∀ d, inner ℝ s d ≤ dirD (f i) x d}) :=
      subset_convexHull ℝ _ (mem_biUnion hjI hc1)
    have h1 := hψ1 c hcC
    rw [hψ, real_inner_comm, hc2] at h1
    rw [hψ, real_inner_comm] at hψ2
    have h2 := hs ((InnerProductSpace.toDual ℝ E).symm ψ)
    linarith
  · refine convexHull_min ?_ (convex_sub _)
    intro s hs
    obtain ⟨i, hi, hs'⟩ := mem_iUnion₂.1 hs
    intro d
    exact (hs' d).trans (ha i hi d)

end FCA_chap_D_4_3_2
