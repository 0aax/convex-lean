import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_3_6`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_3_6` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_3_6`, so the main result is `FCA_chap_E_1_3_6.FCA_chap_E_1_3_6`.
-/

namespace FCA_chap_E_1_3_6

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_1_3_6
  (f : E → EReal)
  (g : E → EReal)
  (hf_nondegenerate : IsNondegenerate f)
  (g_ne_bot : ∀ x, ⊥ < g x) :
  (((Minorizes (biconjugate f) g) ∧ (Minorizes g f)) → (∀ s, conjugate g s = conjugate f s)) ∧
  ((biconjugate f = f) ↔ (InClosedConvRn f)) := by
  have le_conj : ∀ (h : E → EReal) (v x : E),
      ((inner ℝ v x : ℝ) : EReal) - h x ≤ conjugate h v :=
    fun h v x => le_sSup ⟨x, Set.mem_univ _, rfl⟩
  have conj_anti : ∀ (g h : E → EReal), (∀ x, g x ≤ h x) →
      ∀ s, conjugate h s ≤ conjugate g s := by
    intro g h hgh s
    unfold conjugate
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    exact le_sSup_of_le ⟨x, Set.mem_univ _, rfl⟩ (EReal.sub_le_sub le_rfl (hgh x))
  have biconj_le : ∀ (h : E → EReal) (x : E), biconjugate h x ≤ h x := by
    intro h x
    unfold biconjugate
    apply sSup_le
    rintro _ ⟨v, -, rfl⟩
    have h1 := le_conj h v x
    rw [real_inner_comm] at h1
    dsimp only
    generalize h x = c at h1 ⊢
    generalize conjugate h v = d at h1 ⊢
    generalize (inner ℝ x v : ℝ) = a at h1 ⊢
    induction c using EReal.rec with
    | bot =>
      rw [EReal.coe_sub_bot, top_le_iff] at h1
      rw [h1, EReal.sub_top]
    | coe c =>
      induction d using EReal.rec with
      | bot =>
        exfalso
        rw [le_bot_iff] at h1
        exact EReal.coe_ne_bot _ (by exact_mod_cast h1)
      | coe d =>
        norm_cast at h1 ⊢
        linarith
      | top => rw [EReal.sub_top]; exact bot_le
    | top => exact le_top
  have conj_lsc : ∀ (h : E → EReal), LowerSemicontinuous (conjugate h) := by
    intro h
    have : conjugate h = fun v => ⨆ x, ((inner ℝ v x : ℝ) : EReal) - h x := by
      funext v; unfold conjugate; rw [Set.image_univ, sSup_range]
    rw [this]
    apply lowerSemicontinuous_iSup
    intro x
    apply Continuous.lowerSemicontinuous
    generalize h x = c
    induction c using EReal.rec with
    | bot => simp only [EReal.coe_sub_bot]; exact continuous_const
    | coe c =>
      have : (fun v => ((inner ℝ v x : ℝ) : EReal) - (c : EReal)) =
          fun v => (((inner ℝ v x - c : ℝ)) : EReal) := by
        funext v; norm_cast
      rw [this]; exact continuous_coe_real_ereal.comp (by fun_prop)
    | top => simp only [EReal.sub_top]; exact continuous_const
  have conj_convex : ∀ (h : E → EReal), ConvexEReal (conjugate h) := by
    intro h
    unfold ConvexEReal epigraph
    intro p hp q hq a b ha hb hab
    simp only [Set.mem_setOf_eq] at hp hq ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    unfold conjugate at *
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    have h1 := (sSup_le_iff.mp hp) _ ⟨x, Set.mem_univ _, rfl⟩
    have h2 := (sSup_le_iff.mp hq) _ ⟨x, Set.mem_univ _, rfl⟩
    simp only at h1 h2 ⊢
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
    generalize h x = c at h1 h2 ⊢
    induction c using EReal.rec with
    | bot =>
      exfalso
      rw [EReal.coe_sub_bot, top_le_iff] at h1
      exact EReal.coe_ne_top _ h1
    | coe c =>
      norm_cast at h1 h2 ⊢
      have hc : c = a * c + b * c := by rw [← add_mul, hab, one_mul]
      nlinarith [mul_le_mul_of_nonneg_left h1 ha, mul_le_mul_of_nonneg_left h2 hb]
    | top => rw [EReal.sub_top]; exact bot_le
  have affine_le_biconj : ∀ (h : E → EReal) (s : E) (b : ℝ),
      (∀ y, ((inner ℝ s y : ℝ) : EReal) - b ≤ h y) →
      ∀ x, ((inner ℝ s x : ℝ) : EReal) - b ≤ biconjugate h x := by
    intro h s b hs x
    have hconj : conjugate h s ≤ b := by
      unfold conjugate
      apply sSup_le
      rintro _ ⟨y, -, rfl⟩
      have := hs y
      dsimp only
      generalize h y = c at this ⊢
      induction c using EReal.rec with
      | bot =>
        exfalso
        rw [le_bot_iff] at this
        exact EReal.coe_ne_bot _ (by exact_mod_cast this)
      | coe c => norm_cast at this ⊢; linarith
      | top => rw [EReal.sub_top]; exact bot_le
    calc ((inner ℝ s x : ℝ) : EReal) - b ≤ ((inner ℝ x s : ℝ) : EReal) - conjugate h s := by
          rw [real_inner_comm x s]; exact EReal.sub_le_sub le_rfl hconj
      _ ≤ biconjugate h x := le_conj (conjugate h) x s
  obtain ⟨⟨x₀, hx₀⟩, s₀, b₀, h0⟩ := hf_nondegenerate
  have le_biconj : InClosedConvRn f → ∀ x, f x ≤ biconjugate f x := by
    intro hf x
    by_contra hlt
    push_neg at hlt
    obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
    have hconv : Convex ℝ (epigraph f) := hf.1.2.2
    have hclosed : IsClosed (epigraph f) := by
      have := hf.2.isClosed_epigraph
      exact this.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
    have hnot : (x, r) ∉ epigraph f := by
      simp only [epigraph, Set.mem_setOf_eq, not_le]; exact hr2
    obtain ⟨L, u, hL1, hL2⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
    set α := L (0, 1) with hα_def
    set ℓ : E →L[ℝ] ℝ := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hℓ_def
    have hL : ∀ y t, L (y, t) = ℓ y + t * α := by
      intro y t
      have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]; rfl
    have hS : ∀ y (t : ℝ), f y ≤ t → ℓ y + t * α < u := by
      intro y t hyt; rw [← hL]; exact hL1 _ hyt
    have hX : u < ℓ x + r * α := by rw [← hL]; exact hL2
    obtain ⟨y₁, hy₁⟩ := hf.1.2.1
    have hy₁' : f y₁ ≠ ⊥ := (hf.1.1 y₁).ne'
    set t₁ := (f y₁).toReal
    have ht₁ : f y₁ = t₁ := (EReal.coe_toReal hy₁.ne hy₁').symm
    have hα : α ≤ 0 := by
      by_contra hpos; push_neg at hpos
      set t := max t₁ ((u - ℓ y₁) / α)
      have h1 := hS y₁ t (by rw [ht₁]; exact_mod_cast le_max_left _ _)
      have h2 : (u - ℓ y₁) / α ≤ t := le_max_right _ _
      rw [div_le_iff₀ hpos] at h2
      linarith
    set δ := ℓ x + r * α - u with hδ_def
    have hδ : 0 < δ := by linarith
    set D := inner ℝ s₀ x - b₀ - r with hD_def
    obtain ⟨ε, hε, hεD⟩ : ∃ ε : ℝ, 0 < ε ∧ 0 < δ + ε * D := by
      by_cases hD : 0 ≤ D
      · exact ⟨1, one_pos, by nlinarith⟩
      · push_neg at hD
        refine ⟨δ / (-2 * D), div_pos hδ (by linarith), ?_⟩
        have hD0 : D ≠ 0 := hD.ne
        have : δ / (-2 * D) * D = - δ / 2 := by field_simp
        rw [this]; linarith
    set w := (InnerProductSpace.toDual ℝ E).symm ℓ
    have hw : ∀ y, inner ℝ w y = ℓ y := fun y => InnerProductSpace.toDual_symm_apply
    set μ := ε - α with hμ_def
    have hμ : 0 < μ := by linarith
    set s := μ⁻¹ • (w + ε • s₀)
    set b := μ⁻¹ * (u + ε * b₀)
    have hsy : ∀ y, inner ℝ s y - b = μ⁻¹ * (ℓ y + ε * inner ℝ s₀ y - u - ε * b₀) := by
      intro y
      simp only [s, b, real_inner_smul_left, inner_add_left, hw]
      ring
    have hmin : ∀ y, ((inner ℝ s y : ℝ) : EReal) - b ≤ f y := by
      intro y
      have h0y := h0 y
      have hSy := hS y
      have hbot := (hf.1.1 y).ne'
      generalize f y = c at h0y hSy hbot ⊢
      induction c using EReal.rec with
      | bot => exact absurd rfl hbot
      | coe c =>
        have h1 := hSy c le_rfl
        norm_cast at h0y ⊢
        rw [hsy, inv_mul_le_iff₀ hμ, hμ_def]
        nlinarith [mul_le_mul_of_nonneg_left h0y hε.le]
      | top => exact le_top
    have hxval : (r : EReal) < ((inner ℝ s x : ℝ) : EReal) - b := by
      norm_cast
      rw [hsy, lt_inv_mul_iff₀ hμ, hμ_def]
      nlinarith
    have := affine_le_biconj f s b hmin x
    exact absurd (hr1.trans (hxval.trans_le this)) (lt_irrefl _)
  refine ⟨?_, ?_⟩
  · rintro ⟨h1, h2⟩ s
    apply le_antisymm
    · calc conjugate g s ≤ conjugate (biconjugate f) s := conj_anti _ _ h1 s
        _ = biconjugate (conjugate f) s := rfl
        _ ≤ conjugate f s := biconj_le _ s
    · exact conj_anti _ _ h2 s
  · constructor
    · intro hbi
      refine ⟨⟨fun x => ?_, ⟨x₀, lt_top_iff_ne_top.mpr hx₀⟩, ?_⟩, ?_⟩
      · refine lt_of_lt_of_le ?_ (h0 x)
        rw [← EReal.coe_sub]
        exact EReal.bot_lt_coe _
      · rw [← hbi]; exact conj_convex _
      · rw [← hbi]; exact conj_lsc _
    · intro hf
      funext x
      exact le_antisymm (biconj_le f x) (le_biconj hf x)

end FCA_chap_E_1_3_6
