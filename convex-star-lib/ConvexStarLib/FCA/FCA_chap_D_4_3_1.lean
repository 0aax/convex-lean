import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_3_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_3_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_3_1`, so the main result is `FCA_chap_D_4_3_1.FCA_chap_D_4_3_1`.
-/

namespace FCA_chap_D_4_3_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

namespace FCAAux

open Filter Set

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- real difference quotient -/
noncomputable def dq (h : V → ℝ) (x d : V) (t : ℝ) : ℝ := (h (x + t • d) - h x) / t

lemma convex_line {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) {a b s t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    h (x + (a * s + b * t) • d) ≤ a * h (x + s • d) + b * h (x + t • d) := by
  have := hh.2 (Set.mem_univ (x + s • d)) (Set.mem_univ (x + t • d)) ha hb hab
  simp only [smul_eq_mul] at this
  convert this using 2
  rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hab, one_smul, smul_smul, smul_smul,
    ← add_smul]

lemma dq_mono {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) {s t : ℝ} (hs : 0 < s)
    (hst : s ≤ t) : dq h x d s ≤ dq h x d t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have key := convex_line hh x d (a := 1 - s / t) (b := s / t) (s := 0) (t := t)
    (by rw [sub_nonneg, div_le_one ht]; exact hst) (by positivity) (by ring)
  have e : (1 - s / t) * 0 + s / t * t = s := by rw [mul_zero, zero_add]; field_simp
  rw [e, zero_smul, add_zero] at key
  unfold dq
  rw [div_le_div_iff₀ hs ht]
  have := mul_le_mul_of_nonneg_left key ht.le
  have e2 : t * ((1 - s / t) * h x + s / t * h (x + t • d)) = (t - s) * h x + s * h (x + t • d) := by
    field_simp
  rw [e2] at this
  nlinarith

lemma dq_lower {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) {t : ℝ} (ht : 0 < t) :
    h x - h (x + (-1 : ℝ) • d) ≤ dq h x d t := by
  have key := convex_line hh x d (a := 1 / (1 + t)) (b := t / (1 + t)) (s := t) (t := -1)
    (by positivity) (by positivity) (by field_simp)
  have e : 1 / (1 + t) * t + t / (1 + t) * (-1) = 0 := by field_simp; ring
  rw [e, zero_smul, add_zero] at key
  unfold dq
  rw [le_div_iff₀ ht]
  have := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ 1 + t)
  have e2 : (1 + t) * (1 / (1 + t) * h (x + t • d) + t / (1 + t) * h (x + (-1:ℝ) • d))
      = h (x + t • d) + t * h (x + (-1:ℝ) • d) := by
    field_simp
  rw [e2] at this
  nlinarith

lemma dq_tendsto {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) :
    ∃ L, Tendsto (dq h x d) (𝓝[>] 0) (𝓝 L) :=
  ⟨_, MonotoneOn.tendsto_nhdsGT (fun s hs t _ hst => dq_mono hh x d hs hst)
    ⟨h x - h (x + (-1 : ℝ) • d), by rintro _ ⟨t, ht, rfl⟩; exact dq_lower hh x d ht⟩⟩

/-- real directional derivative -/
noncomputable def D (h : V → ℝ) (x d : V) : ℝ := limUnder (𝓝[>] (0:ℝ)) (dq h x d)

lemma D_tendsto {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) :
    Tendsto (dq h x d) (𝓝[>] 0) (𝓝 (D h x d)) :=
  tendsto_nhds_limUnder (dq_tendsto hh x d)

lemma D_le_dq {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) {t : ℝ} (ht : 0 < t) :
    D h x d ≤ dq h x d t := by
  apply le_of_tendsto (D_tendsto hh x d)
  filter_upwards [Ioo_mem_nhdsGT ht] with s hs
  exact dq_mono hh x d hs.1 hs.2.le

lemma D_zero {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x : V) : D h x 0 = 0 := by
  have : dq h x 0 = fun _ => 0 := by funext t; simp [dq]
  have h1 := D_tendsto hh x 0
  rw [this] at h1
  exact tendsto_nhds_unique h1 tendsto_const_nhds

lemma tendsto_mul_nhdsGT {c : ℝ} (hc : 0 < c) :
    Tendsto (fun t : ℝ => c * t) (𝓝[>] 0) (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · have : Tendsto (fun t : ℝ => c * t) (𝓝 0) (𝓝 (c * 0)) := tendsto_const_nhds.mul tendsto_id
    rw [mul_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact mul_pos hc ht

lemma D_smul {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : V) {c : ℝ} (hc : 0 < c) :
    D h x (c • d) = c * D h x d := by
  have h1 := D_tendsto hh x (c • d)
  have h2 : Tendsto (fun t => c * dq h x d (c * t)) (𝓝[>] 0) (𝓝 (c * D h x d)) :=
    ((D_tendsto hh x d).comp (tendsto_mul_nhdsGT hc)).const_mul c
  refine tendsto_nhds_unique h1 (h2.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : (t:ℝ) ≠ 0 := ne_of_gt ht
  simp only [dq, mul_smul]
  rw [smul_comm c t d]
  field_simp

lemma D_add {h : V → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d₁ d₂ : V) :
    D h x (d₁ + d₂) ≤ D h x d₁ + D h x d₂ := by
  have h2 : Tendsto (fun t => dq h x d₁ (2 * t) + dq h x d₂ (2 * t)) (𝓝[>] 0)
      (𝓝 (D h x d₁ + D h x d₂)) :=
    ((D_tendsto hh x d₁).comp (tendsto_mul_nhdsGT two_pos)).add
      ((D_tendsto hh x d₂).comp (tendsto_mul_nhdsGT two_pos))
  apply le_of_tendsto_of_tendsto (D_tendsto hh x (d₁ + d₂)) h2
  filter_upwards [self_mem_nhdsWithin] with t ht
  have key := hh.2 (Set.mem_univ (x + (2*t) • d₁)) (Set.mem_univ (x + (2*t) • d₂))
    (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1/2:ℝ) + 1/2 = 1)
  have e : (1/2 : ℝ) • (x + (2*t) • d₁) + (1/2 : ℝ) • (x + (2*t) • d₂) = x + t • (d₁ + d₂) := by
    module
  rw [e] at key
  have ht' : 0 < t := ht
  simp only [dq, smul_eq_mul] at key ⊢
  rw [← add_div, div_le_div_iff₀ ht' (by positivity)]
  have := mul_le_mul_of_nonneg_left key ht'.le
  nlinarith


section Bridge

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]

lemma differenceQuotient_lift (h : W → ℝ) (x d : W) (t : ℝ) :
    differenceQuotient (liftRealtoEReal h) x d t = ((dq h x d t : ℝ) : EReal) := by
  simp only [differenceQuotient, liftRealtoEReal, dq, EReal.coe_div, EReal.coe_sub]

lemma directionalDeriv_lift {h : W → ℝ} (hh : ConvexOn ℝ Set.univ h) (x d : W) :
    directionalDeriv (liftRealtoEReal h) x d = ((D h x d : ℝ) : EReal) := by
  unfold directionalDeriv
  apply Tendsto.limUnder_eq
  simp_rw [differenceQuotient_lift]
  exact EReal.tendsto_coe.2 (D_tendsto hh x d)

lemma mem_dsub_iff {h : W → ℝ} (hh : ConvexOn ℝ Set.univ h) (x s : W) :
    s ∈ directionalSubdifferential (liftRealtoEReal h) x ↔ ∀ d, inner ℝ s d ≤ D h x d := by
  simp only [directionalSubdifferential, Set.mem_setOf_eq, directionalDeriv_lift hh,
    EReal.coe_le_coe_iff]

lemma exists_le_sublinear [FiniteDimensional ℝ W]
    (N : W → ℝ) (N_hom : ∀ c : ℝ, 0 < c → ∀ x, N (c • x) = c * N x)
    (N_add : ∀ x y, N (x + y) ≤ N x + N y) :
    ∃ s : W, ∀ d, inner ℝ s d ≤ N d := by
  have hN0 : N 0 = 0 := by
    have := N_hom 2 (by norm_num) 0
    rw [smul_zero] at this
    linarith
  obtain ⟨g, -, hg⟩ := exists_extension_of_le_sublinear ⟨⊥, 0⟩ N N_hom N_add (by
    rintro ⟨x, hx⟩
    rw [Submodule.mem_bot] at hx
    subst hx
    simp [hN0])
  refine ⟨(InnerProductSpace.toDual ℝ W).symm (LinearMap.toContinuousLinearMap g), fun d => ?_⟩
  rw [InnerProductSpace.toDual_symm_apply]
  simpa using hg d

end Bridge

section Chain

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable {κ : Type*} [Fintype κ]

lemma D_mono_dir {g : EuclideanSpace ℝ κ → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (y w w' : EuclideanSpace ℝ κ) (hw : ∀ i, w i ≤ w' i) : D g y w ≤ D g y w' := by
  apply le_of_tendsto_of_tendsto (D_tendsto hg y w) (D_tendsto hg y w')
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  unfold dq
  apply div_le_div_of_nonneg_right _ ht'.le
  apply sub_le_sub_right
  apply hmono
  intro i
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul]
  nlinarith [hw i]

lemma rho_nonneg {g : EuclideanSpace ℝ κ → ℝ} (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (y ρ : EuclideanSpace ℝ κ) (hρ : ∀ w, inner ℝ ρ w ≤ D g y w) (i : κ) : 0 ≤ ρ i := by
  classical
  have h1 := hρ (EuclideanSpace.single i (-1))
  rw [EuclideanSpace.inner_single_right] at h1
  have h2 : D g y (EuclideanSpace.single i (-1)) ≤ D g y 0 := D_mono_dir hg hmono y _ _ (by
    intro j
    simp only [EuclideanSpace.single_apply, PiLp.zero_apply]
    split_ifs <;> norm_num)
  rw [D_zero hg] at h2
  simp only [conj_trivial] at h1
  linarith

lemma chain_lower (f : κ → W → ℝ) (g : EuclideanSpace ℝ κ → ℝ) (F : W → EuclideanSpace ℝ κ)
    (hF : ∀ x i, F x i = f i x)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (hG : ConvexOn ℝ Set.univ (g ∘ F)) (x d : W) (v : EuclideanSpace ℝ κ)
    (hv : ∀ i, v i = D (f i) x d) :
    D g (F x) v ≤ D (g ∘ F) x d := by
  apply ge_of_tendsto (D_tendsto hG x d)
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht' : 0 < t := ht
  refine (D_le_dq hg (F x) v ht').trans ?_
  unfold dq
  apply div_le_div_of_nonneg_right _ ht'.le
  apply sub_le_sub_right
  apply hmono
  intro i
  have := D_le_dq (hf i) x d ht'
  unfold dq at this
  rw [le_div_iff₀ ht'] at this
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hF, hv]
  linarith

lemma chain_upper (f : κ → W → ℝ) (g : EuclideanSpace ℝ κ → ℝ) (F : W → EuclideanSpace ℝ κ)
    (hF : ∀ x i, F x i = f i x)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (hG : ConvexOn ℝ Set.univ (g ∘ F)) (x d : W) (v : EuclideanSpace ℝ κ)
    (hv : ∀ i, v i = D (f i) x d) :
    D (g ∘ F) x d ≤ D g (F x) v := by
  set one : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun _ => 1) with hone
  have key : ∀ ε > 0, D (g ∘ F) x d ≤ D g (F x) v + ε * D g (F x) one := by
    intro ε hε
    have h1 : D (g ∘ F) x d ≤ D g (F x) (v + ε • one) := by
      apply le_of_tendsto_of_tendsto (D_tendsto hG x d) (D_tendsto hg (F x) (v + ε • one))
      have hev : ∀ᶠ t in 𝓝[>] (0:ℝ), ∀ i, dq (f i) x d t < D (f i) x d + ε := by
        rw [Filter.eventually_all]
        intro i
        exact (D_tendsto (hf i) x d).eventually_lt_const (by linarith)
      filter_upwards [hev, self_mem_nhdsWithin] with t ht ht0
      have ht0' : 0 < t := ht0
      unfold dq
      apply div_le_div_of_nonneg_right _ ht0'.le
      apply sub_le_sub_right
      apply hmono
      intro i
      have := ht i
      unfold dq at this
      rw [div_lt_iff₀ ht0'] at this
      simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hF, hv, hone]
      nlinarith
    calc D (g ∘ F) x d ≤ D g (F x) (v + ε • one) := h1
      _ ≤ D g (F x) v + D g (F x) (ε • one) := D_add hg _ _ _
      _ = D g (F x) v + ε * D g (F x) one := by rw [D_smul hg _ _ hε]
  apply _root_.le_of_forall_pos_le_add
  intro δ hδ
  set C := D g (F x) one
  have hC : 0 < |C| + 1 := by positivity
  have h1 := key (δ / (|C| + 1)) (by positivity)
  have h2 : δ / (|C| + 1) * C ≤ δ := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hC]
    nlinarith [le_abs_self C]
  linarith

end Chain


section Incl

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
variable {κ : Type*} [Fintype κ]

lemma supset_dir (f : κ → W → ℝ) (g : EuclideanSpace ℝ κ → ℝ) (F : W → EuclideanSpace ℝ κ)
    (hF : ∀ x i, F x i = f i x)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (hG : ConvexOn ℝ Set.univ (g ∘ F)) (x : W)
    (ρ : EuclideanSpace ℝ κ) (hρ : ∀ w, inner ℝ ρ w ≤ D g (F x) w)
    (s : κ → W) (hs : ∀ i d, inner ℝ (s i) d ≤ D (f i) x d) (d : W) :
    inner ℝ (∑ i, ρ i • s i) d ≤ D (g ∘ F) x d := by
  set v : EuclideanSpace ℝ κ := WithLp.toLp 2 (fun i => D (f i) x d) with hv
  calc inner ℝ (∑ i, ρ i • s i) d = ∑ i, ρ i * inner ℝ (s i) d := by
        rw [sum_inner]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [real_inner_smul_left]
    _ ≤ ∑ i, ρ i * D (f i) x d := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left (hs i d) (rho_nonneg hg hmono _ ρ hρ i)
    _ = inner ℝ ρ v := by
        rw [PiLp.inner_apply]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        simp [hv, mul_comm]
    _ ≤ D g (F x) v := hρ v
    _ ≤ D (g ∘ F) x d := chain_lower f g F hF hf hg hmono hG x d v (fun i => by simp [hv])

lemma subset_dir [FiniteDimensional ℝ W] (f : κ → W → ℝ) (g : EuclideanSpace ℝ κ → ℝ)
    (F : W → EuclideanSpace ℝ κ)
    (hF : ∀ x i, F x i = f i x)
    (hf : ∀ i, ConvexOn ℝ Set.univ (f i)) (hg : ConvexOn ℝ Set.univ g)
    (hmono : ∀ y z : EuclideanSpace ℝ κ, (∀ i, y i ≥ z i) → g y ≥ g z)
    (hG : ConvexOn ℝ Set.univ (g ∘ F)) (x : W)
    (s : W) (hs : ∀ d, inner ℝ s d ≤ D (g ∘ F) x d) :
    ∃ ρ : EuclideanSpace ℝ κ, (∀ w, inner ℝ ρ w ≤ D g (F x) w) ∧
      ∃ σ : κ → W, (∀ i d, inner ℝ (σ i) d ≤ D (f i) x d) ∧ s = ∑ i, ρ i • σ i := by
  classical
  let q : (κ → W) → EuclideanSpace ℝ κ := fun d => WithLp.toLp 2 (fun i => D (f i) x (d i))
  let M : EuclideanSpace ℝ κ × (κ → W) → ℝ := fun z => D g (F x) (z.1 + q z.2)
  have hM_hom : ∀ c : ℝ, 0 < c → ∀ z, M (c • z) = c * M z := by
    intro c hc z
    simp only [M]
    rw [← D_smul hg _ _ hc]
    congr 1
    ext i
    simp [q, D_smul (hf i) _ _ hc]
  have hM_add : ∀ z z', M (z + z') ≤ M z + M z' := by
    intro z z'
    simp only [M]
    calc D g (F x) ((z + z').1 + q (z + z').2)
        ≤ D g (F x) ((z.1 + q z.2) + (z'.1 + q z'.2)) := by
          apply D_mono_dir hg hmono
          intro i
          simp only [q, Prod.fst_add, Prod.snd_add, PiLp.add_apply, Pi.add_apply]
          have := D_add (hf i) x (z.2 i) (z'.2 i)
          linarith
      _ ≤ _ := D_add hg _ _ _
  have hM0 : ∀ w, M (w, 0) = D g (F x) w := by
    intro w
    simp only [M]
    congr 1
    ext i
    simp [q, D_zero (hf i)]
  have hsM : ∀ d, inner ℝ s d ≤ M (0, fun _ => d) := by
    intro d
    refine (hs d).trans ?_
    simp only [M, zero_add]
    exact chain_upper f g F hF hf hg hmono hG x d (q fun _ => d) (fun i => rfl)
  rcases isEmpty_or_nonempty κ with hκ | ⟨⟨i0⟩⟩
  · -- empty index type
    have hs0 : s = 0 := by
      have := hsM s
      have hM : M (0, fun _ => s) = 0 := by
        simp only [M]
        rw [Subsingleton.elim (0 + q fun _ => s) 0, D_zero hg]
      rw [hM, real_inner_self_nonpos] at this
      exact this
    obtain ⟨ρ, hρ⟩ := exists_le_sublinear (D g (F x)) (fun c hc w => D_smul hg _ _ hc)
      (fun w w' => D_add hg _ _ _)
    exact ⟨ρ, hρ, fun i => isEmptyElim i, fun i => isEmptyElim i, by simp [hs0]⟩
  · -- nonempty index type
    let Δ : W →ₗ[ℝ] EuclideanSpace ℝ κ × (κ → W) :=
      LinearMap.prod 0 (LinearMap.pi fun _ => LinearMap.id)
    let phi : EuclideanSpace ℝ κ × (κ → W) →ₗ[ℝ] ℝ :=
      (innerₛₗ ℝ s) ∘ₗ (LinearMap.proj i0) ∘ₗ (LinearMap.snd ℝ _ _)
    obtain ⟨Λ, hΛphi, hΛM⟩ := exists_extension_of_le_sublinear (phi.toPMap (LinearMap.range Δ)) M
      hM_hom hM_add (by
        rintro ⟨z, ⟨d, rfl⟩⟩
        simpa [phi, Δ] using hsM d)
    have hΛΔ : ∀ d, Λ (0, fun _ => d) = inner ℝ s d := by
      intro d
      have := hΛphi ⟨Δ d, ⟨d, rfl⟩⟩
      simpa [phi, Δ] using this
    let ρ : EuclideanSpace ℝ κ := (InnerProductSpace.toDual ℝ _).symm
      (LinearMap.toContinuousLinearMap (Λ ∘ₗ LinearMap.inl ℝ _ _))
    let t : κ → W := fun i => (InnerProductSpace.toDual ℝ W).symm
      (LinearMap.toContinuousLinearMap (Λ ∘ₗ LinearMap.inr ℝ _ _ ∘ₗ LinearMap.single ℝ (fun _ => W) i))
    have hρ_inner : ∀ w, inner ℝ ρ w = Λ (w, 0) := by
      intro w
      simp [ρ, InnerProductSpace.toDual_symm_apply]
    have ht_inner : ∀ i d, inner ℝ (t i) d = Λ (0, Pi.single i d) := by
      intro i d
      simp [t, InnerProductSpace.toDual_symm_apply]
    have hρ : ∀ w, inner ℝ ρ w ≤ D g (F x) w := by
      intro w
      rw [hρ_inner, ← hM0]
      exact hΛM _
    have hρ_nn : ∀ i, 0 ≤ ρ i := rho_nonneg hg hmono _ ρ hρ
    have hρ_i : ∀ i, ρ i = Λ (EuclideanSpace.single i 1, 0) := by
      intro i
      rw [← hρ_inner, EuclideanSpace.inner_single_right]
      simp
    have ht_le : ∀ i d, inner ℝ (t i) d ≤ ρ i * D (f i) x d := by
      intro i d
      have h1 := hΛM (-(D (f i) x d) • EuclideanSpace.single i 1, Pi.single i d)
      have h2 : M (-(D (f i) x d) • EuclideanSpace.single i 1, Pi.single i d) = 0 := by
        simp only [M]
        convert D_zero hg (F x) using 2
        ext j
        by_cases hj : j = i
        · subst hj
          simp [q]
        · simp [q, hj, D_zero (hf j)]
      have h3 : Λ (-(D (f i) x d) • EuclideanSpace.single i 1, Pi.single i d)
          = -(D (f i) x d) * ρ i + inner ℝ (t i) d := by
        rw [ht_inner, hρ_i, ← smul_eq_mul, ← map_smul, ← map_add]
        congr 1
        ext <;> simp
      linarith
    have hs_sum : s = ∑ i, t i := by
      apply ext_inner_right ℝ
      intro d
      rw [sum_inner, ← hΛΔ]
      simp only [ht_inner]
      rw [← map_sum]
      congr 1
      ext j
      · simp [Prod.fst_sum]
      · simp [Prod.snd_sum, Finset.sum_apply, Finset.sum_pi_single]
    choose s0 hs0 using fun i => exists_le_sublinear (D (f i) x)
      (fun c hc d => D_smul (hf i) _ _ hc) (fun d d' => D_add (hf i) _ _ _)
    let σ : κ → W := fun i => if ρ i = 0 then s0 i else (ρ i)⁻¹ • t i
    refine ⟨ρ, hρ, σ, ?_, ?_⟩
    · intro i d
      simp only [σ]
      split_ifs with h
      · exact hs0 i d
      · have hpos : 0 < ρ i := lt_of_le_of_ne (hρ_nn i) (Ne.symm h)
        rw [real_inner_smul_left]
        calc (ρ i)⁻¹ * inner ℝ (t i) d ≤ (ρ i)⁻¹ * (ρ i * D (f i) x d) :=
              mul_le_mul_of_nonneg_left (ht_le i d) (inv_nonneg.2 hpos.le)
          _ = D (f i) x d := by field_simp
    · rw [hs_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      simp only [σ]
      split_ifs with h
      · rw [h, zero_smul]
        have := ht_le i (t i)
        rw [h, zero_mul, real_inner_self_nonpos] at this
        exact this
      · rw [smul_smul, mul_inv_cancel₀ h, one_smul]

end Incl

end FCAAux

theorem FCA_chap_D_4_3_1
    (f : ι → E → ℝ)
    (g : EuclideanSpace ℝ ι → ℝ)
    (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hg_convex : ConvexOn ℝ Set.univ g)
    (hg_increasing : ∀ y z : EuclideanSpace ℝ ι, (∀ i, y i ≥ z i) → g y ≥ g z) :
    let F_fun : E → EuclideanSpace ℝ ι := fun x => (WithLp.equiv 2 _).symm (fun i => f i x)
    ∀ (x : E),
      directionalSubdifferential (liftRealtoEReal (g ∘ F_fun)) x =
      {v | ∃ ρ ∈ directionalSubdifferential (liftRealtoEReal g) (F_fun x),
          ∃ s : ι → E,
            (∀ i, s i ∈ directionalSubdifferential (liftRealtoEReal (f i)) x) ∧
            v = ∑ i, (ρ i) • s i} := by
  intro F_fun x
  have hF : ∀ x i, F_fun x i = f i x := fun x i => rfl
  have hG : ConvexOn ℝ Set.univ (g ∘ F_fun) := by
    refine ⟨convex_univ, fun y _ z _ a b ha hb hab => ?_⟩
    simp only [Function.comp_apply, smul_eq_mul]
    calc g (F_fun (a • y + b • z)) ≤ g (a • F_fun y + b • F_fun z) := by
          apply hg_increasing
          intro i
          simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hF]
          exact (hf_convex i).2 trivial trivial ha hb hab
      _ ≤ a * g (F_fun y) + b * g (F_fun z) := hg_convex.2 trivial trivial ha hb hab
  ext v
  simp only [Set.mem_setOf_eq]
  rw [FCAAux.mem_dsub_iff hG]
  constructor
  · intro hv
    obtain ⟨ρ, hρ, σ, hσ, rfl⟩ :=
      FCAAux.subset_dir f g F_fun hF hf_convex hg_convex hg_increasing hG x v hv
    exact ⟨ρ, (FCAAux.mem_dsub_iff hg_convex _ _).2 hρ, σ,
      fun i => (FCAAux.mem_dsub_iff (hf_convex i) _ _).2 (hσ i), rfl⟩
  · rintro ⟨ρ, hρ, σ, hσ, rfl⟩
    exact FCAAux.supset_dir f g F_fun hF hf_convex hg_convex hg_increasing hG x ρ
      ((FCAAux.mem_dsub_iff hg_convex _ _).1 hρ) σ
      (fun i => (FCAAux.mem_dsub_iff (hf_convex i) _ _).1 (hσ i))

end FCA_chap_D_4_3_1
