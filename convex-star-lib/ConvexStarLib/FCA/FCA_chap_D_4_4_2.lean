import ConvexStarLib.Defs

/-!
# `FCA_chap_D_4_4_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_4_4_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_4_4_2`, so the main result is `FCA_chap_D_4_4_2.FCA_chap_D_4_4_2`.
-/

namespace FCA_chap_D_4_4_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_cvx {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x y : E) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) : f (a • x + b • y) ≤ a * f x + b * f y :=
  hf.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_dq_mono {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) {s t : ℝ}
    (hs : 0 < s) (hst : s ≤ t) :
    (f (x + s • d) - f x) / s ≤ (f (x + t • d) - f x) / t := by
  have ht : 0 < t := lt_of_lt_of_le hs hst
  have h := FCA_aux_cvx hf x (x + t • d) (a := (t - s) / t) (b := s / t)
    (div_nonneg (by linarith) ht.le) (div_nonneg hs.le ht.le)
    (by rw [← add_div, sub_add_cancel, div_self ht.ne'])
  have heq : ((t - s) / t) • x + (s / t) • (x + t • d) = x + s • d := by
    rw [smul_add, smul_smul, div_mul_cancel₀ s ht.ne', ← add_assoc, ← add_smul,
      ← add_div, sub_add_cancel, div_self ht.ne', one_smul]
  rw [heq] at h
  rw [div_le_div_iff₀ hs ht]
  have h2 : t * ((t - s) / t * f x + s / t * f (x + t • d))
      = (t - s) * f x + s * f (x + t • d) := by
    field_simp
  have h3 := mul_le_mul_of_nonneg_left h ht.le
  rw [h2] at h3
  linarith

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_dq_lb {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) {t : ℝ} (ht : 0 < t) :
    f x - f (x - d) ≤ (f (x + t • d) - f x) / t := by
  have h1t : 0 < 1 + t := by linarith
  have h := FCA_aux_cvx hf (x - d) (x + t • d) (a := t / (1 + t)) (b := 1 / (1 + t))
    (by positivity) (by positivity) (by field_simp; ring)
  have e1 : t / (1 + t) + 1 / (1 + t) = 1 := by field_simp; ring
  have e2 : 1 / (1 + t) * t = t / (1 + t) := by ring
  have heq : (t / (1 + t)) • (x - d) + (1 / (1 + t)) • (x + t • d) = x := by
    calc (t / (1 + t)) • (x - d) + (1 / (1 + t)) • (x + t • d)
        = (t / (1 + t) + 1 / (1 + t)) • x + (1 / (1 + t) * t - t / (1 + t)) • d := by module
      _ = x := by rw [e1, e2, sub_self, one_smul, zero_smul, add_zero]
  rw [heq] at h
  rw [le_div_iff₀ ht]
  have h3 := mul_le_mul_of_nonneg_left h h1t.le
  have h2 : (1 + t) * (t / (1 + t) * f (x - d) + 1 / (1 + t) * f (x + t • d))
      = t * f (x - d) + f (x + t • d) := by
    field_simp
  rw [h2] at h3
  nlinarith

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_bdd {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    BddBelow (Set.range fun t : Set.Ioi (0:ℝ) => (f (x + (t:ℝ) • d) - f x) / t) := by
  refine ⟨f x - f (x - d), ?_⟩
  rintro _ ⟨t, rfl⟩
  exact FCA_aux_dq_lb hf x d t.2

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_inf_le {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) {t : ℝ} (ht : 0 < t) :
    (⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • d) - f x) / t) ≤ (f (x + t • d) - f x) / t :=
  ciInf_le (FCA_aux_bdd hf x d) (⟨t, ht⟩ : Set.Ioi (0:ℝ))

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_le_inf {f : E → ℝ} (x d : E) {c : ℝ}
    (h : ∀ t : ℝ, 0 < t → c ≤ (f (x + t • d) - f x) / t) :
    c ≤ ⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • d) - f x) / t :=
  le_ciInf fun t => h t t.2

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_tendsto {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    Filter.Tendsto (fun t : ℝ => (f (x + t • d) - f x) / t) (𝓝[>] 0)
      (𝓝 (⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • d) - f x) / t)) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    exact lt_of_lt_of_le ha (FCA_aux_inf_le hf x d ht)
  · obtain ⟨t0, ht0⟩ := exists_lt_of_ciInf_lt hb
    filter_upwards [Ioo_mem_nhdsGT t0.2] with t ht
    exact lt_of_le_of_lt (FCA_aux_dq_mono hf x d ht.1 ht.2.le) ht0

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_dd_eq {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    directionalDeriv (liftRealtoEReal f) x d =
      ((⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • d) - f x) / t : ℝ) : EReal) := by
  unfold directionalDeriv
  apply Filter.Tendsto.limUnder_eq
  have h1 : (fun t : ℝ => differenceQuotient (liftRealtoEReal f) x d t)
      = fun t : ℝ => (((f (x + t • d) - f x) / t : ℝ) : EReal) := by
    funext t
    simp only [differenceQuotient, liftRealtoEReal]
    rw [EReal.coe_div, EReal.coe_sub]
  rw [h1]
  exact (continuous_coe_real_ereal.tendsto _).comp (FCA_aux_tendsto hf x d)

omit [FiniteDimensional ℝ E] in
lemma FCA_aux_mem_iff {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x s : E) :
    s ∈ directionalSubdifferential (liftRealtoEReal f) x ↔ ∀ y, f x + inner ℝ s (y - x) ≤ f y := by
  simp only [directionalSubdifferential, Set.mem_setOf_eq, FCA_aux_dd_eq hf, EReal.coe_le_coe_iff]
  constructor
  · intro h y
    have h1 := (h (y - x)).trans (FCA_aux_inf_le hf x (y - x) one_pos)
    simp only [one_smul, add_sub_cancel, div_one] at h1
    linarith
  · intro h d
    apply FCA_aux_le_inf
    intro t ht
    rw [le_div_iff₀ ht]
    have := h (x + t • d)
    rw [add_sub_cancel_left, inner_smul_right] at this
    linarith


lemma FCA_aux_hb {f : E → ℝ} (hf : ConvexOn ℝ Set.univ f) (x d : E) :
    ∃ c : E, (∀ y, f x + inner ℝ c (y - x) ≤ f y) ∧
      (⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • d) - f x) / t) ≤ inner ℝ c d := by
  let N : E → ℝ := fun v => ⨅ t : Set.Ioi (0:ℝ), (f (x + (t:ℝ) • v) - f x) / t
  have hN_le : ∀ v {t : ℝ}, 0 < t → N v ≤ (f (x + t • v) - f x) / t :=
    fun v t ht => FCA_aux_inf_le hf x v ht
  have hN_ge : ∀ v c, (∀ t : ℝ, 0 < t → c ≤ (f (x + t • v) - f x) / t) → c ≤ N v :=
    fun v c h => FCA_aux_le_inf x v h
  have hN0 : N 0 = 0 := by
    apply le_antisymm
    · have := hN_le 0 one_pos
      simpa using this
    · apply hN_ge
      intro t ht
      simp
  have N_hom : ∀ c : ℝ, 0 < c → ∀ v, N (c • v) = c * N v := by
    intro c hc v
    apply le_antisymm
    · have : N (c • v) / c ≤ N v := by
        apply hN_ge
        intro t ht
        have h1 := hN_le (c • v) (div_pos ht hc)
        rw [smul_smul, div_mul_cancel₀ t hc.ne'] at h1
        rw [div_le_iff₀ hc]
        calc N (c • v) ≤ (f (x + t • v) - f x) / (t / c) := h1
          _ = (f (x + t • v) - f x) / t * c := by field_simp
      rwa [div_le_iff₀ hc, mul_comm] at this
    · apply hN_ge
      intro t ht
      have h1 := hN_le v (mul_pos ht hc)
      rw [smul_smul]
      calc c * N v ≤ c * ((f (x + (t * c) • v) - f x) / (t * c)) :=
            mul_le_mul_of_nonneg_left h1 hc.le
        _ = (f (x + (t * c) • v) - f x) / t := by field_simp
  have N_add : ∀ u v, N (u + v) ≤ N u + N v := by
    intro u v
    have key : ∀ t t' : ℝ, 0 < t → 0 < t' →
        N (u + v) ≤ (f (x + t • u) - f x) / t + (f (x + t' • v) - f x) / t' := by
      intro t t' ht ht'
      have hm : 0 < min t t' := lt_min ht ht'
      have h1 := hN_le (u + v) (half_pos hm)
      have h2 : (f (x + (min t t' / 2) • (u + v)) - f x) / (min t t' / 2) ≤
          (f (x + (min t t') • u) - f x) / (min t t') +
            (f (x + (min t t') • v) - f x) / (min t t') := by
        have hc := FCA_aux_cvx hf (x + (min t t') • u) (x + (min t t') • v) (a := 1/2) (b := 1/2)
          (by norm_num) (by norm_num) (by norm_num)
        have heq : (1/2:ℝ) • (x + (min t t') • u) + (1/2:ℝ) • (x + (min t t') • v)
            = x + (min t t' / 2) • (u + v) := by module
        rw [heq] at hc
        rw [← add_div, div_le_div_iff₀ (half_pos hm) hm]
        nlinarith
      have h3 := FCA_aux_dq_mono hf x u hm (min_le_left t t')
      have h4 := FCA_aux_dq_mono hf x v hm (min_le_right t t')
      linarith
    have k1 : ∀ t' : ℝ, 0 < t' → N (u + v) - (f (x + t' • v) - f x) / t' ≤ N u := by
      intro t' ht'
      apply hN_ge
      intro t ht
      have := key t t' ht ht'
      linarith
    have k2 : N (u + v) - N u ≤ N v := by
      apply hN_ge
      intro t' ht'
      have := k1 t' ht'
      linarith
    linarith
  have H : ∀ c : ℝ, c • d = 0 → c • N d = 0 := by
    intro c hc
    rcases smul_eq_zero.1 hc with h | h
    · simp [h]
    · simp [h, hN0]
  let g0 := LinearPMap.mkSpanSingleton' d (N d) H
  have hg0 : ∀ z : g0.domain, g0 z ≤ N z := by
    rintro ⟨z, hz⟩
    have hz' : z ∈ (ℝ ∙ d) := hz
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz'
    simp only [g0]
    rw [LinearPMap.mkSpanSingleton'_apply]
    rcases lt_trichotomy c 0 with hc | hc | hc
    · have e : c • d = (-c) • (-d) := by rw [smul_neg, neg_smul, neg_neg]
      rw [e, N_hom (-c) (by linarith) (-d), smul_eq_mul]
      have h0 := N_add d (-d)
      rw [add_neg_cancel, hN0] at h0
      nlinarith
    · subst hc
      simp [hN0]
    · rw [N_hom c hc d, smul_eq_mul]
  obtain ⟨g, hg_ext, hg_le⟩ := exists_extension_of_le_sublinear g0 N N_hom N_add hg0
  let c := (InnerProductSpace.toDual ℝ E).symm (LinearMap.toContinuousLinearMap g)
  have hc : ∀ v, inner ℝ c v = g v := by
    intro v
    rw [InnerProductSpace.toDual_symm_apply]
    rfl
  refine ⟨c, ?_, ?_⟩
  · intro y
    rw [hc]
    have := (hg_le (y - x)).trans (hN_le (y - x) one_pos)
    simp only [one_smul, div_one, add_sub_cancel] at this
    linarith
  · rw [hc]
    have hd : d ∈ g0.domain := Submodule.mem_span_singleton_self d
    have := hg_ext ⟨d, hd⟩
    simp only at this
    rw [this]
    simp only [g0]
    rw [LinearPMap.mkSpanSingleton'_apply_self]

lemma FCA_aux_isCompact_convexHull {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  let n := Module.finrank ℝ E
  let Φ : (k : ℕ) → (Fin k → E) × (Fin k → ℝ) → E := fun k p => ∑ i, p.2 i • p.1 i
  let K : (k : ℕ) → Set ((Fin k → E) × (Fin k → ℝ)) :=
    fun k => (Set.univ.pi fun _ => S) ×ˢ stdSimplex ℝ (Fin k)
  have hK : ∀ k, IsCompact (Φ k '' K k) := by
    intro k
    apply IsCompact.image ((isCompact_univ_pi fun _ => hS).prod (isCompact_stdSimplex (Fin k)))
    apply continuous_finset_sum
    intro i _
    exact ((continuous_apply i).comp continuous_snd).smul ((continuous_apply i).comp continuous_fst)
  have heq : convexHull ℝ S = ⋃ k : Fin (n + 2), Φ k '' K k := by
    apply Set.Subset.antisymm
    · intro x hx
      obtain ⟨ι, _, z, w, hzS, hai, hw0, hw1, hx⟩ := eq_pos_convex_span_of_mem_convexHull hx
      have hcard : Fintype.card ι ≤ n + 1 :=
        hai.card_le_finrank_succ.trans (Nat.succ_le_succ (Submodule.finrank_le _))
      let e := Fintype.equivFin ι
      refine Set.mem_iUnion.2 ⟨⟨Fintype.card ι, by omega⟩, ⟨z ∘ e.symm, w ∘ e.symm⟩, ⟨?_, ?_⟩, ?_⟩
      · intro i _
        exact hzS ⟨_, rfl⟩
      · refine ⟨fun i => (hw0 _).le, ?_⟩
        rw [← hw1]
        exact Equiv.sum_comp e.symm w
      · rw [← hx]
        exact Equiv.sum_comp e.symm (fun i => w i • z i)
    · apply Set.iUnion_subset
      intro k
      rintro _ ⟨⟨p, w⟩, ⟨hp, hw⟩, rfl⟩
      exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
        (fun i _ => subset_convexHull ℝ S (hp i (Set.mem_univ i)))
  rw [heq]
  exact isCompact_iUnion fun k => hK k

theorem FCA_chap_D_4_4_2
  {J : Type*}
  [TopologicalSpace J]
  [CompactSpace J]
  [Nonempty J]
  [FirstCountableTopology J]
  (f : J → E → ℝ)
  (x : E)
  (hf_convex : ∀ i, ConvexOn ℝ Set.univ (f i))
  (hf_finite : ∀ z, ⨆ j, (f j z : EReal) < ⊤)
  (hf_usc : ∀ z j', UpperSemicontinuousAt (fun (j : J) => f j z) j') :
  let F : E → EReal := fun z => ⨆ j, (f j z : EReal)
  let active := {j | f j x = F x}
  convexHull ℝ (⋃ j ∈ active, directionalSubdifferential (liftRealtoEReal (f j)) x) =
    directionalSubdifferential F x := by
  intro F active
  classical
  have hF_ge : ∀ j z, (f j z : EReal) ≤ F z := fun j z => le_iSup (fun j => (f j z : EReal)) j
  have hF_ne_top : ∀ z, F z ≠ ⊤ := fun z => (hf_finite z).ne
  have hF_ne_bot : ∀ z, F z ≠ ⊥ := by
    intro z h
    have := hF_ge (Classical.arbitrary J) z
    rw [h] at this
    exact EReal.coe_ne_bot _ (le_bot_iff.1 this)
  obtain ⟨G, hFG⟩ : ∃ G : E → ℝ, ∀ z, F z = (G z : EReal) :=
    ⟨fun z => (F z).toReal, fun z => (EReal.coe_toReal (hF_ne_top z) (hF_ne_bot z)).symm⟩
  have hle : ∀ j z, f j z ≤ G z := by
    intro j z
    have := hF_ge j z
    rw [hFG z] at this
    exact EReal.coe_le_coe_iff.1 this
  have husc : ∀ z, UpperSemicontinuous (fun j => f j z) := fun z j => hf_usc z j
  have hattain : ∀ z, ∃ j, f j z = G z := by
    intro z
    obtain ⟨j, -, hj⟩ := ((husc z).upperSemicontinuousOn Set.univ).exists_isMaxOn
      Set.univ_nonempty isCompact_univ
    refine ⟨j, le_antisymm (hle j z) ?_⟩
    have : F z ≤ (f j z : EReal) :=
      iSup_le fun i => EReal.coe_le_coe_iff.2 (hj (Set.mem_univ i))
    rw [hFG z] at this
    exact EReal.coe_le_coe_iff.1 this
  have hGconv : ConvexOn ℝ Set.univ G := by
    refine ⟨convex_univ, ?_⟩
    intro y _ z _ a b ha hb hab
    obtain ⟨j, hj⟩ := hattain (a • y + b • z)
    rw [← hj]
    calc f j (a • y + b • z) ≤ a • f j y + b • f j z :=
          (hf_convex j).2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
      _ ≤ a • G y + b • G z := by
        simp only [smul_eq_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hle j y) ha)
          (mul_le_mul_of_nonneg_left (hle j z) hb)
  have hF_lift : F = liftRealtoEReal G := funext hFG
  have hA : active = {j | f j x = G x} := by
    ext j
    simp only [active, Set.mem_setOf_eq, hFG x, EReal.coe_eq_coe_iff]
  rw [hA, hF_lift]
  have hSG : ∀ j, directionalSubdifferential (liftRealtoEReal (f j)) x =
      {s | ∀ y, f j x + inner ℝ s (y - x) ≤ f j y} :=
    fun j => Set.ext fun s => FCA_aux_mem_iff (hf_convex j) x s
  have hSGG : directionalSubdifferential (liftRealtoEReal G) x =
      {s | ∀ y, G x + inner ℝ s (y - x) ≤ G y} :=
    Set.ext fun s => FCA_aux_mem_iff hGconv x s
  simp only [hSG, hSGG]
  set S := ⋃ j ∈ {j | f j x = G x}, {s : E | ∀ y, f j x + inner ℝ s (y - x) ≤ f j y}
    with hS_def
  have hS_sub : S ⊆ {s | ∀ y, G x + inner ℝ s (y - x) ≤ G y} := by
    intro s hs
    simp only [hS_def, Set.mem_iUnion, Set.mem_setOf_eq] at hs
    obtain ⟨j, hj, hs⟩ := hs
    intro y
    rw [← hj]
    exact (hs y).trans (hle j y)
  have hSGG_conv : Convex ℝ {s : E | ∀ y, G x + inner ℝ s (y - x) ≤ G y} := by
    intro s hs s' hs' a b ha hb hab y
    have h1 := hs y
    have h2 := hs' y
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    obtain rfl : b = 1 - a := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
  apply Set.Subset.antisymm
  · exact convexHull_min hS_sub hSGG_conv
  · intro s hs
    by_contra hns
    have hS_compact : IsCompact S := by
      apply Metric.isCompact_of_isClosed_isBounded
      · let K : Set (J × E) := {p | G x ≤ f p.1 x} ∩
          ⋂ y, {p : J × E | G x + inner ℝ p.2 (y - x) ≤ f p.1 y}
        have hK : IsClosed K := by
          apply IsClosed.inter
          · exact ((husc x).isClosed_preimage (G x)).preimage continuous_fst
          · apply isClosed_iInter
            intro y
            rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
            intro p hp
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hp
            obtain ⟨r, hr1, hr2⟩ := exists_between hp
            have e1 : ∀ᶠ q in 𝓝 p, f q.1 y < r :=
              (continuous_fst.tendsto p).eventually (hf_usc y p.1 r hr1)
            have e2 : ∀ᶠ q in 𝓝 p, r < G x + inner ℝ q.2 (y - x) := by
              have hc : Continuous fun q : J × E => G x + inner ℝ q.2 (y - x) :=
                continuous_const.add (continuous_snd.inner continuous_const)
              exact hc.continuousAt.eventually (lt_mem_nhds hr2)
            filter_upwards [e1, e2] with q hq1 hq2
            simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le]
            linarith
        have hSK : S = Prod.snd '' K := by
          ext s
          simp only [hS_def, Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_image, Prod.exists,
            exists_eq_right, K, exists_prop, Set.mem_inter_iff,
            Set.mem_iInter]
          constructor
          · rintro ⟨j, hj, hs⟩
            refine ⟨j, hj.ge, fun y => ?_⟩
            rw [← hj]
            exact hs y
          · rintro ⟨j, hj, hs⟩
            have hj' : f j x = G x := le_antisymm (hle j x) hj
            refine ⟨j, hj', fun y => ?_⟩
            rw [hj']
            exact hs y
        rw [hSK]
        exact isClosedMap_snd_of_compactSpace K hK
      · have hcont : ContinuousAt G x := hGconv.locallyLipschitz.continuous.continuousAt
        obtain ⟨δ, hδ, hδG⟩ := Metric.continuousAt_iff.1 hcont 1 one_pos
        rw [Metric.isBounded_iff_subset_closedBall 0]
        refine ⟨2 / δ, fun s hs => ?_⟩
        have hs' := hS_sub hs
        rw [Metric.mem_closedBall, _root_.dist_zero_right]
        by_contra hlt
        push_neg at hlt
        have hspos : 0 < ‖s‖ := lt_trans (by positivity) hlt
        have hy : dist (x + (δ / 2 / ‖s‖) • s) x < δ := by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
          field_simp
          linarith
        have h1 := hδG hy
        have h2 := hs' (x + (δ / 2 / ‖s‖) • s)
        rw [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at h2
        rw [Real.dist_eq] at h1
        have h3 : δ / 2 / ‖s‖ * ‖s‖ ^ 2 = δ / 2 * ‖s‖ := by
          field_simp
        rw [h3] at h2
        have h4 := (abs_lt.1 h1).2
        have h5 : 1 < δ / 2 * ‖s‖ := by
          rw [div_lt_iff₀ hδ] at hlt
          linarith
        linarith
    have hcc := FCA_aux_isCompact_convexHull hS_compact
    obtain ⟨ℓ, u, hℓa, hℓs⟩ :=
      geometric_hahn_banach_closed_point (convex_convexHull ℝ S) hcc.isClosed hns
    let d := (InnerProductSpace.toDual ℝ E).symm ℓ
    have hd : ∀ v, ℓ v = inner ℝ d v := fun v => (InnerProductSpace.toDual_symm_apply).symm
    obtain ⟨D, hD⟩ : ∃ D : ℝ, D = ⨅ t : Set.Ioi (0:ℝ), (G (x + (t:ℝ) • d) - G x) / t :=
      ⟨_, rfl⟩
    obtain ⟨j, hjA, hj⟩ : ∃ j, f j x = G x ∧ ∀ t : ℝ, 0 < t → G x + t * D ≤ f j (x + t • d) := by
      let L : Set.Ioi (0:ℝ) → Set J := fun t => {j | G x + (t:ℝ) * D ≤ f j (x + (t:ℝ) • d)}
      have hL_closed : ∀ t, IsClosed (L t) :=
        fun t => (husc (x + (t:ℝ) • d)).isClosed_preimage (G x + t * D)
      have hL_ne : ∀ t, (L t).Nonempty := by
        intro t
        obtain ⟨j, hj⟩ := hattain (x + (t:ℝ) • d)
        refine ⟨j, ?_⟩
        show G x + (t:ℝ) * D ≤ f j (x + (t:ℝ) • d)
        rw [hj]
        have := FCA_aux_inf_le hGconv x d t.2
        rw [← hD, le_div_iff₀ t.2] at this
        linarith
      have hL_mono : ∀ t t' : Set.Ioi (0:ℝ), (t:ℝ) ≤ t' → L t ⊆ L t' := by
        intro t t' htt' j hj
        show G x + (t':ℝ) * D ≤ f j (x + (t':ℝ) • d)
        have hj' : G x + (t:ℝ) * D ≤ f j (x + (t:ℝ) • d) := hj
        have ht'pos : (0:ℝ) < t' := lt_of_lt_of_le t.2 htt'
        have hmono := FCA_aux_dq_mono (hf_convex j) x d t.2 htt'
        rw [div_le_div_iff₀ t.2 ht'pos] at hmono
        have hjx := hle j x
        have k1 : (G x - f j x) * t ≤ (G x - f j x) * t' :=
          mul_le_mul_of_nonneg_left htt' (by linarith)
        have k2 : (G x + t * D - f j x) * t' ≤ (f j (x + (t:ℝ) • d) - f j x) * t' :=
          mul_le_mul_of_nonneg_right (by linarith) ht'pos.le
        have k3 : (t:ℝ) * (G x + t' * D) ≤ t * f j (x + (t':ℝ) • d) := by
          nlinarith
        exact le_of_mul_le_mul_left k3 t.2
      have hdir : Directed (· ⊇ ·) L := by
        intro t t'
        exact ⟨⟨min t t', Set.mem_Ioi.2 (lt_min t.2 t'.2)⟩, hL_mono _ _ (min_le_left _ _),
          hL_mono _ _ (min_le_right _ _)⟩
      obtain ⟨j, hj⟩ := IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed L hdir
        hL_ne (fun t => (hL_closed t).isCompact) hL_closed
      simp only [Set.mem_iInter] at hj
      have hj' : ∀ t : ℝ, 0 < t → G x + t * D ≤ f j (x + t • d) := fun t ht => hj ⟨t, ht⟩
      refine ⟨j, le_antisymm (hle j x) ?_, hj'⟩
      have h_ev : ∀ᶠ t in 𝓝[>] (0:ℝ), G x - f j x ≤ t * (f j (x + d) - f j x - D) := by
        filter_upwards [Ioo_mem_nhdsGT one_pos] with t ht
        have h1 := hj' t ht.1
        have h2 := FCA_aux_cvx (hf_convex j) x (x + d) (a := 1 - t) (b := t)
          (by linarith [ht.2]) ht.1.le (by ring)
        have heq : (1 - t) • x + t • (x + d) = x + t • d := by module
        rw [heq] at h2
        nlinarith
      have h_tend : Filter.Tendsto (fun t : ℝ => t * (f j (x + d) - f j x - D)) (𝓝[>] (0:ℝ))
          (𝓝 0) := by
        have : Filter.Tendsto (fun t : ℝ => t * (f j (x + d) - f j x - D)) (𝓝 (0:ℝ))
            (𝓝 (0 * (f j (x + d) - f j x - D))) :=
          (continuous_mul_right _).tendsto 0
        rw [zero_mul] at this
        exact tendsto_nhdsWithin_of_tendsto_nhds this
      have := ge_of_tendsto h_tend h_ev
      linarith
    obtain ⟨c, hc_sub, hc_d⟩ := FCA_aux_hb (hf_convex j) x d
    have hcS : c ∈ S := by
      simp only [hS_def, Set.mem_iUnion, Set.mem_setOf_eq]
      exact ⟨j, hjA, hc_sub⟩
    have h1 : ℓ c < u := hℓa c (subset_convexHull ℝ S hcS)
    have h2 : inner ℝ s d ≤ D := by
      rw [hD]
      apply FCA_aux_le_inf
      intro t ht
      rw [le_div_iff₀ ht]
      have := hs (x + t • d)
      rw [add_sub_cancel_left, real_inner_smul_right] at this
      linarith
    have h3 : D ≤ ⨅ t : Set.Ioi (0:ℝ), (f j (x + (t:ℝ) • d) - f j x) / t := by
      apply FCA_aux_le_inf
      intro t ht
      rw [le_div_iff₀ ht]
      have := hj t ht
      rw [hjA]
      linarith
    rw [hd] at h1 hℓs
    have e1 := real_inner_comm d c
    have e2 := real_inner_comm d s
    linarith

end FCA_chap_D_4_4_2
