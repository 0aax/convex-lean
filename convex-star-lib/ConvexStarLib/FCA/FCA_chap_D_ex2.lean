import ConvexStarLib.Defs

/-!
# `FCA_chap_D_ex2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_D_ex2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_D_ex2`, so the main result is `FCA_chap_D_ex2.FCA_chap_D_ex2`.
-/

namespace FCA_chap_D_ex2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
lemma aux_convexOn {f : E → ℝ} (hf : InConvRn (liftRealtoEReal f)) :
    ConvexOn ℝ Set.univ f := by
  refine ⟨convex_univ, fun a _ b _ μ ν hμ hν hμν => ?_⟩
  have h := hf.2.2 (x := (a, f a)) (y := (b, f b))
    (by simp [epigraph, liftRealtoEReal]) (by simp [epigraph, liftRealtoEReal]) hμ hν hμν
  simpa [epigraph, liftRealtoEReal] using h

omit [FiniteDimensional ℝ E] in
lemma aux_dir {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (z d : E) :
    directionalDeriv (liftRealtoEReal f) z d =
      ((sInf ((fun t : ℝ => (f (z + t • d) - f z) / t) '' Set.Ioo 0 2) : ℝ) : EReal) ∧
    BddBelow ((fun t : ℝ => (f (z + t • d) - f z) / t) '' Set.Ioo 0 2) := by
  set q : ℝ → ℝ := fun t => (f (z + t • d) - f z) / t with hq
  have hg : ConvexOn ℝ Set.univ (fun t : ℝ => f (z + t • d)) := by
    refine ⟨convex_univ, fun s _ t _ a b ha hb hab => ?_⟩
    have : z + (a • s + b • t) • d = a • (z + s • d) + b • (z + t • d) := by
      calc z + (a • s + b • t) • d = (a + b) • z + (a • s + b • t) • d := by rw [hab, one_smul]
        _ = a • (z + s • d) + b • (z + t • d) := by
          simp only [add_smul, smul_add, smul_smul, smul_eq_mul]; abel
    simp only [this]
    exact hconv.2 (Set.mem_univ _) (Set.mem_univ _) ha hb hab
  have hsec : ∀ s t : ℝ, s ≠ 0 → t ≠ 0 → s ≤ t → q s ≤ q t := by
    intro s t hs ht hst
    have := hg.secant_mono (a := 0) (Set.mem_univ _) (Set.mem_univ s) (Set.mem_univ t) hs ht hst
    simpa [q] using this
  have hmono : MonotoneOn q (Set.Ioo 0 2) := fun s hs t ht hst => hsec s t hs.1.ne' ht.1.ne' hst
  have hbdd : BddBelow (q '' Set.Ioo 0 2) := by
    refine ⟨q (-1), ?_⟩
    rintro _ ⟨t, ht, rfl⟩
    exact hsec (-1) t (by norm_num) ht.1.ne' (by linarith [ht.1])
  refine ⟨?_, hbdd⟩
  have htend := hmono.tendsto_nhdsWithin_Ioo_right ⟨1, by norm_num, by norm_num⟩ hbdd
  have htend' : Filter.Tendsto (fun t => differenceQuotient (liftRealtoEReal f) z d t) (𝓝[>] 0)
      (𝓝 ((sInf (q '' Set.Ioo 0 2) : ℝ) : EReal)) := by
    have := (continuous_coe_real_ereal.tendsto _).comp htend
    convert this using 1
  exact htend'.limUnder_eq

omit [FiniteDimensional ℝ E] in
lemma aux_sub {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (z v : E) :
    v ∈ directionalSubdifferential (liftRealtoEReal f) z ↔ ∀ y, f z + inner ℝ v (y - z) ≤ f y := by
  simp only [directionalSubdifferential, Set.mem_setOf_eq]
  constructor
  · intro h y
    have h1 := h (y - z)
    obtain ⟨hD, hbdd⟩ := aux_dir hconv z (y - z)
    rw [hD, EReal.coe_le_coe_iff] at h1
    have h2 := csInf_le hbdd ⟨1, ⟨by norm_num, by norm_num⟩, rfl⟩
    simp only [one_smul, add_sub_cancel, div_one] at h2
    linarith
  · intro h d
    obtain ⟨hD, hbdd⟩ := aux_dir hconv z d
    rw [hD, EReal.coe_le_coe_iff]
    apply le_csInf ((Set.nonempty_Ioo.2 (by norm_num : (0:ℝ) < 2)).image _)
    rintro _ ⟨t, ht, rfl⟩
    simp only
    rw [le_div_iff₀ ht.1]
    have := h (z + t • d)
    simp only [add_sub_cancel_left, real_inner_smul_right] at this
    linarith

lemma aux_hb {f : E → ℝ} (hconv : ConvexOn ℝ Set.univ f) (hcont : Continuous f) (x : E)
    (B : Set (E × ℝ)) (hB : Convex ℝ B) (hxB : (x, f x) ∈ B)
    (hdisj : ∀ p ∈ B, p.2 ≤ f p.1) :
    ∃ v : E, (∀ y, f x + inner ℝ v (y - x) ≤ f y) ∧
      ∀ p ∈ B, p.2 ≤ f x + inner ℝ v (p.1 - x) := by
  set A : Set (E × ℝ) := {p | f p.1 < p.2} with hA_def
  have hAo : IsOpen A := isOpen_lt (hcont.comp continuous_fst) continuous_snd
  have hAc : Convex ℝ A := by
    intro p hp q hq a b ha hb hab
    simp only [A, Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
      smul_eq_mul] at *
    have h1 := hconv.2 (Set.mem_univ p.1) (Set.mem_univ q.1) ha hb hab
    simp only [smul_eq_mul] at h1
    rcases eq_or_lt_of_le ha with h | h
    · subst h
      have hb1 : b = 1 := by linarith
      subst hb1
      simp only [zero_smul, one_smul, zero_add, zero_mul, one_mul]
      exact hq
    · calc f (a • p.1 + b • q.1) ≤ a * f p.1 + b * f q.1 := h1
        _ < a * p.2 + b * q.2 := by
          have := mul_lt_mul_of_pos_left hp h
          have := mul_le_mul_of_nonneg_left hq.le hb
          linarith
  have hdisj' : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    exact absurd (hdisj p hpB) (not_le.2 hpA)
  obtain ⟨ℓ, u, hAu, hBu⟩ := geometric_hahn_banach_open hAc hAo hB hdisj'
  have hℓ : ∀ (y : E) (t : ℝ), ℓ (y, t) = ℓ (y, 0) + t * ℓ (0, 1) := by
    intro y t
    have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by simp
    rw [this, map_add, map_smul, smul_eq_mul]
  set α := ℓ (0, 1) with hα_def
  have h1 := hBu _ hxB
  have h2 := hAu (x, f x + 1) (by simp [A])
  rw [hℓ] at h1 h2
  have hα : α < 0 := by linarith
  have hα0 : α ≠ 0 := hα.ne
  have h3 : ∀ y, ℓ (y, 0) + f y * α ≤ u := by
    intro y
    apply le_of_forall_pos_lt_add
    intro ε hε
    have hpos : 0 < ε / (-α) := _root_.div_pos hε (by linarith)
    have h4 := hAu (y, f y + ε / (-α)) (by show f y < f y + ε / (-α); linarith)
    rw [hℓ] at h4
    have h5 : ε / (-α) * α = -ε := by field_simp
    nlinarith
  set ψ : StrongDual ℝ E := ℓ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hψ_def
  have hψ : ∀ y, ψ y = ℓ (y, 0) := fun y => rfl
  set w := (InnerProductSpace.toDual ℝ E).symm ψ with hw_def
  have hw : ∀ y, inner ℝ w y = ψ y := fun y => InnerProductSpace.toDual_symm_apply
  have hx3 := h3 x
  refine ⟨(-α)⁻¹ • w, ?_, ?_⟩
  · intro y
    have hy3 := h3 y
    rw [real_inner_smul_left, hw, map_sub, hψ, hψ]
    have hna : 0 < -α := by linarith
    have key : ℓ (y, 0) - ℓ (x, 0) ≤ (f y - f x) * (-α) := by nlinarith
    have : (-α)⁻¹ * (ℓ (y, 0) - ℓ (x, 0)) ≤ f y - f x := by
      rw [inv_mul_le_iff₀ hna]; linarith
    linarith
  · rintro ⟨y, t⟩ hp
    have hp3 := hBu _ hp
    rw [hℓ] at hp3
    simp only
    rw [real_inner_smul_left, hw, map_sub, hψ, hψ]
    have hna : 0 < -α := by linarith
    have key : (t - f x) * (-α) ≤ ℓ (y, 0) - ℓ (x, 0) := by nlinarith
    have : t - f x ≤ (-α)⁻¹ * (ℓ (y, 0) - ℓ (x, 0)) := by
      rw [le_inv_mul_iff₀ hna]; linarith
    linarith

theorem FCA_chap_D_ex2
  (f : E → ℝ)
  (x : E)
  (hf : InConvRn (liftRealtoEReal f)) :
  (sInf {c : ℝ | (c ≥ 0) ∧ (∀ d, f (x + d) ≥ (f x) - c * ‖d‖)}
  = sInf (Set.image (fun v => ‖v‖) (directionalSubdifferential (liftRealtoEReal f) x))) ∧
  (∀ (ε : ℝ), (ε > 0) →
  (ε⁻¹ * (sSup (Set.image (fun d => f (x + d) - (f x)) {d | ‖d‖ ≤ ε})) ≥
  sSup (Set.image (fun v => ‖v‖) (directionalSubdifferential (liftRealtoEReal f) x)))) ∧
  ((directionalSubdifferential (liftRealtoEReal f) x) =
  ⋂ ε > 0, closure (convexHull ℝ {v | ∃ d,
                                      (‖d‖ < ε) ∧
                                      (v ∈ (directionalSubdifferential (liftRealtoEReal f) (x + d)))})) := by
  have hconv : ConvexOn ℝ Set.univ f := aux_convexOn hf
  have hcont : Continuous f := hconv.locallyLipschitz.continuous
  have hsub := aux_sub hconv
  have hC_sub : ∀ v ∈ directionalSubdifferential (liftRealtoEReal f) x,
      ‖v‖ ≥ 0 ∧ ∀ d, f (x + d) ≥ f x - ‖v‖ * ‖d‖ := by
    intro v hv
    have hv' := (hsub x v).1 hv
    refine ⟨norm_nonneg _, fun d => ?_⟩
    have h1 := hv' (x + d)
    simp only [add_sub_cancel_left] at h1
    have h2 := abs_real_inner_le_norm v d
    have h3 := neg_abs_le (inner ℝ v d)
    linarith
  have hC_to_N : ∀ c : ℝ, c ≥ 0 → (∀ d, f (x + d) ≥ f x - c * ‖d‖) →
      ∃ v ∈ directionalSubdifferential (liftRealtoEReal f) x, ‖v‖ ≤ c := by
    intro c hc0 hc
    have hBconv : Convex ℝ {p : E × ℝ | p.2 ≤ f x - c * ‖p.1 - x‖} := by
      intro p hp q hq a b ha hb hab
      simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
        smul_eq_mul] at *
      have e1 : a • p.1 + b • q.1 - x = a • (p.1 - x) + b • (q.1 - x) := by
        calc a • p.1 + b • q.1 - x = a • p.1 + b • q.1 - (a + b) • x := by rw [hab, one_smul]
          _ = a • (p.1 - x) + b • (q.1 - x) := by
            simp only [smul_sub, add_smul]; abel
      have e2 : ‖a • p.1 + b • q.1 - x‖ ≤ a * ‖p.1 - x‖ + b * ‖q.1 - x‖ := by
        rw [e1]
        calc _ ≤ ‖a • (p.1 - x)‖ + ‖b • (q.1 - x)‖ := norm_add_le _ _
          _ = _ := by rw [norm_smul, norm_smul, Real.norm_of_nonneg ha, Real.norm_of_nonneg hb]
      have e3 := mul_le_mul_of_nonneg_left e2 hc0
      have e4 := mul_le_mul_of_nonneg_left hp ha
      have e5 := mul_le_mul_of_nonneg_left hq hb
      have e6 : a * f x + b * f x = f x := by rw [← add_mul, hab, one_mul]
      nlinarith
    obtain ⟨v, hv1, hv2⟩ := aux_hb hconv hcont x _ hBconv (by simp) (by
      rintro ⟨y, t⟩ hp
      simp only [Set.mem_setOf_eq] at hp ⊢
      have := hc (y - x)
      simp only [add_sub_cancel] at this
      linarith)
    refine ⟨v, (hsub x v).2 hv1, ?_⟩
    have h1 := hv2 (x - v, f x - c * ‖v‖) (by simp)
    simp only [sub_sub_cancel_left, inner_neg_right, real_inner_self_eq_norm_sq] at h1
    rcases eq_or_lt_of_le (norm_nonneg v) with h | h
    · rw [← h]; exact hc0
    · nlinarith
  have hD_ne : (directionalSubdifferential (liftRealtoEReal f) x).Nonempty := by
    obtain ⟨v, hv1, -⟩ := aux_hb hconv hcont x {(x, f x)} (convex_singleton _) rfl (by simp)
    exact ⟨v, (hsub x v).2 hv1⟩
  refine ⟨?_, ?_, ?_⟩
  · -- claim 1
    have hCbdd : BddBelow {c : ℝ | (c ≥ 0) ∧ (∀ d, f (x + d) ≥ (f x) - c * ‖d‖)} :=
      ⟨0, fun c hc => hc.1⟩
    have hNbdd : BddBelow ((fun v => ‖v‖) '' directionalSubdifferential (liftRealtoEReal f) x) :=
      ⟨0, by rintro _ ⟨v, -, rfl⟩; exact norm_nonneg v⟩
    have hNne : ((fun v => ‖v‖) '' directionalSubdifferential (liftRealtoEReal f) x).Nonempty :=
      hD_ne.image _
    apply le_antisymm
    · apply le_csInf hNne
      rintro _ ⟨v, hv, rfl⟩
      exact csInf_le hCbdd (hC_sub v hv)
    · have hCne : {c : ℝ | (c ≥ 0) ∧ (∀ d, f (x + d) ≥ (f x) - c * ‖d‖)}.Nonempty :=
        let ⟨v, hv⟩ := hD_ne; ⟨‖v‖, hC_sub v hv⟩
      apply le_csInf hCne
      rintro c ⟨hc0, hc⟩
      obtain ⟨v, hv, hvc⟩ := hC_to_N c hc0 hc
      exact (csInf_le hNbdd ⟨v, hv, rfl⟩).trans hvc
  · -- claim 2
    intro ε hε
    have hSbdd : BddAbove ((fun d => f (x + d) - f x) '' {d : E | ‖d‖ ≤ ε}) := by
      have hK : IsCompact {d : E | ‖d‖ ≤ ε} := by
        have := isCompact_closedBall (0:E) ε
        convert this using 1
        ext d; simp
      exact (hK.image (by fun_prop)).bddAbove
    have h0S : (0:ℝ) ∈ (fun d => f (x + d) - f x) '' {d : E | ‖d‖ ≤ ε} :=
      ⟨0, by simp [hε.le], by simp⟩
    have hS0 : 0 ≤ sSup ((fun d => f (x + d) - f x) '' {d : E | ‖d‖ ≤ ε}) := le_csSup hSbdd h0S
    apply Real.sSup_le
    · rintro _ ⟨v, hv, rfl⟩
      have hv' := (hsub x v).1 hv
      rw [le_inv_mul_iff₀ hε]
      show ε * ‖v‖ ≤ _
      rcases eq_or_lt_of_le (norm_nonneg v) with h | h
      · rw [← h, mul_zero]; exact hS0
      · have hd : ‖(ε / ‖v‖) • v‖ ≤ ε := by
          rw [norm_smul, Real.norm_of_nonneg (by positivity), div_mul_cancel₀ _ h.ne']
        have hmem : f (x + (ε / ‖v‖) • v) - f x ∈
            (fun d => f (x + d) - f x) '' {d : E | ‖d‖ ≤ ε} := ⟨_, hd, rfl⟩
        have h1 := le_csSup hSbdd hmem
        have h2 := hv' (x + (ε / ‖v‖) • v)
        simp only [add_sub_cancel_left, real_inner_smul_right, real_inner_self_eq_norm_sq] at h2
        have h3 : ε / ‖v‖ * ‖v‖ ^ 2 = ε * ‖v‖ := by field_simp
        linarith
    · positivity
  · -- claim 3
    ext v
    constructor
    · intro hv
      simp only [Set.mem_iInter]
      intro ε hε
      apply subset_closure
      apply subset_convexHull
      exact ⟨0, by simp [hε], by simpa using hv⟩
    · intro hv
      simp only [Set.mem_iInter] at hv
      apply (hsub x v).2
      intro y
      apply le_of_forall_pos_lt_add
      intro δ hδ
      obtain ⟨η, hη, hηf⟩ := Metric.continuous_iff.1 hcont x (δ / 4) (by positivity)
      have hv' := hv (η / 2) (by positivity)
      have hHc : IsClosed {w : E | f x + inner ℝ w (y - x) ≤ f y + 3 * δ / 4} :=
        isClosed_le (by fun_prop) continuous_const
      have hHconv : Convex ℝ {w : E | f x + inner ℝ w (y - x) ≤ f y + 3 * δ / 4} := by
        intro w1 hw1 w2 hw2 a b ha hb hab
        simp only [Set.mem_setOf_eq] at *
        rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
        have e1 := mul_le_mul_of_nonneg_left hw1 ha
        have e2 := mul_le_mul_of_nonneg_left hw2 hb
        have e3 : a * f x + b * f x = f x := by rw [← add_mul, hab, one_mul]
        have e4 : a * (f y + 3 * δ / 4) + b * (f y + 3 * δ / 4) = f y + 3 * δ / 4 := by
          rw [← add_mul, hab, one_mul]
        nlinarith
      have hsubH : {w | ∃ d, ‖d‖ < η / 2 ∧
          w ∈ directionalSubdifferential (liftRealtoEReal f) (x + d)} ⊆
          {w : E | f x + inner ℝ w (y - x) ≤ f y + 3 * δ / 4} := by
        rintro w ⟨d, hd, hw⟩
        have hw' := (hsub (x + d) w).1 hw
        have e1 := hw' y
        have e2 := hw' (x + (2:ℝ) • d)
        have e3 := hηf (x + d) (by rw [dist_eq_norm, add_sub_cancel_left]; linarith)
        have e4 := hηf (x + (2:ℝ) • d) (by
          rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg (by norm_num)]
          linarith)
        rw [Real.dist_eq, abs_lt] at e3 e4
        have e5 : x + (2:ℝ) • d - (x + d) = d := by rw [two_smul]; abel
        have e6 : inner ℝ w (y - (x + d)) = inner ℝ w (y - x) - inner ℝ w d := by
          rw [← inner_sub_right]; congr 1; abel
        rw [e5] at e2
        rw [e6] at e1
        simp only [Set.mem_setOf_eq]
        linarith [e3.1, e3.2, e4.1, e4.2]
      have := closure_minimal (convexHull_min hsubH hHconv) hHc hv'
      simp only [Set.mem_setOf_eq] at this
      linarith

end FCA_chap_D_ex2
