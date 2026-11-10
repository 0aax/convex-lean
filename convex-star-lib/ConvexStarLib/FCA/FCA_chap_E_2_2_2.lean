import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_2_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_2_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_2_2`, so the main result is `FCA_chap_E_2_2_2.FCA_chap_E_2_2_2`.
-/

namespace FCA_chap_E_2_2_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

lemma ri_extend {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] {D : Set X} {y₀ y₁ : X}
    (h₀ : y₀ ∈ intrinsicInterior ℝ D) (h₁ : y₁ ∈ D) :
    ∃ ε : ℝ, 0 < ε ∧ y₀ + ε • (y₀ - y₁) ∈ D := by
  obtain ⟨z, hz, rfl⟩ := h₀
  have h1 : y₁ ∈ affineSpan ℝ D := subset_affineSpan ℝ D h₁
  have hmem : ∀ t : ℝ, (z : X) + t • ((z : X) - y₁) ∈ affineSpan ℝ D := by
    intro t
    have hd : (z : X) -ᵥ y₁ ∈ (affineSpan ℝ D).direction :=
      AffineSubspace.vsub_mem_direction z.2 h1
    have := AffineSubspace.vadd_mem_of_mem_direction (Submodule.smul_mem _ t hd) z.2
    simpa [vadd_eq_add, vsub_eq_sub, add_comm] using this
  let γ : ℝ → affineSpan ℝ D := fun t => ⟨(z : X) + t • ((z : X) - y₁), hmem t⟩
  have hγ : Continuous γ := by
    apply Continuous.subtype_mk
    fun_prop
  have hγ0 : γ 0 = z := by ext; simp [γ]
  have hnhds : γ ⁻¹' interior (((↑) : affineSpan ℝ D → X) ⁻¹' D) ∈ 𝓝 (0 : ℝ) := by
    apply hγ.continuousAt.preimage_mem_nhds
    rw [hγ0]
    exact isOpen_interior.mem_nhds hz
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.1 hnhds
  refine ⟨δ / 2, by positivity, ?_⟩
  have hmemball : δ / 2 ∈ Metric.ball (0:ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (by positivity)]
    linarith
  have h3 : γ (δ / 2) ∈ ((↑) : affineSpan ℝ D → X) ⁻¹' D := interior_subset (hball hmemball)
  exact h3

lemma proper_sep {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    (C : Set X) (hC : Convex ℝ C) (hne : C.Nonempty) (h0 : (0 : X) ∉ C) :
    ∃ f : X →L[ℝ] ℝ, (∀ c ∈ C, 0 ≤ f c) ∧ (∃ c ∈ C, 0 < f c) := by
  by_cases hA : (0 : X) ∈ affineSpan ℝ C
  · set M := (affineSpan ℝ C).direction with hM
    obtain ⟨N, hMN⟩ := Submodule.exists_isCompl M
    have hCM : ∀ c ∈ C, c ∈ M := by
      intro c hc
      have := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ C hc) hA
      simpa using this
    set C' : Set X := C + (N : Set X) with hC'
    have hC'conv : Convex ℝ C' := hC.add N.convex
    have hCC' : C ⊆ C' := fun c hc => ⟨c, hc, 0, N.zero_mem, add_zero c⟩
    have h0' : (0 : X) ∉ C' := by
      rintro ⟨c, hc, n, hn, hcn⟩
      have hcN : c ∈ N := by
        have : c = -n := eq_neg_of_add_eq_zero_left hcn
        rw [this]; exact N.neg_mem hn
      have : c ∈ M ⊓ N := ⟨hCM c hc, hcN⟩
      rw [hMN.inf_eq_bot, Submodule.mem_bot] at this
      exact h0 (this ▸ hc)
    have hspan : affineSpan ℝ C' = ⊤ := by
      obtain ⟨c₀, hc₀⟩ := hne
      have hne' : (affineSpan ℝ C' : Set X).Nonempty :=
        ⟨c₀, subset_affineSpan ℝ C' (hCC' hc₀)⟩
      rw [← AffineSubspace.direction_eq_top_iff_of_nonempty hne', eq_top_iff, ← hMN.sup_eq_top]
      apply sup_le
      · exact AffineSubspace.direction_le (affineSpan_mono ℝ hCC')
      · intro n hn
        have h1 : c₀ + n ∈ affineSpan ℝ C' := subset_affineSpan ℝ C' ⟨c₀, hc₀, n, hn, rfl⟩
        have h2 : c₀ ∈ affineSpan ℝ C' := subset_affineSpan ℝ C' (hCC' hc₀)
        have := AffineSubspace.vsub_mem_direction h1 h2
        simpa using this
    have hint : (interior C').Nonempty :=
      (hC'conv.interior_nonempty_iff_affineSpan_eq_top).2 hspan
    obtain ⟨f, hf⟩ := geometric_hahn_banach_point_open hC'conv.interior isOpen_interior
      (fun h => h0' (interior_subset h))
    simp only [map_zero] at hf
    have hcl : ∀ x ∈ C', 0 ≤ f x := by
      intro x hx
      have hx' : x ∈ closure (interior C') := by
        rw [hC'conv.closure_interior_eq_closure_of_nonempty_interior hint]
        exact subset_closure hx
      have : closure (interior C') ⊆ {x | 0 ≤ f x} :=
        closure_minimal (fun y hy => le_of_lt (hf y hy)) (isClosed_le continuous_const f.continuous)
      exact this hx'
    have hN : ∀ n ∈ N, f n = 0 := by
      obtain ⟨c₀, hc₀⟩ := hne
      intro n hn
      have key : ∀ t : ℝ, 0 ≤ f c₀ + t * f n := by
        intro t
        have := hcl (c₀ + t • n) ⟨c₀, hc₀, t • n, N.smul_mem t hn, rfl⟩
        simpa using this
      by_contra hne
      have h1 := key (-(f c₀ + 1) / f n)
      rw [div_mul_cancel₀ _ hne] at h1
      linarith
    refine ⟨f, fun c hc => hcl c (hCC' hc), ?_⟩
    obtain ⟨a, ha⟩ := hint
    obtain ⟨c, hc, n, hn, rfl⟩ := interior_subset ha
    refine ⟨c, hc, ?_⟩
    have := hf _ ha
    rw [map_add, hN n hn, add_zero] at this
    exact this
  · obtain ⟨f, u, hf0, hfu⟩ := geometric_hahn_banach_point_closed (affineSpan ℝ C).convex
      (AffineSubspace.closed_of_finiteDimensional _) hA
    rw [map_zero] at hf0
    obtain ⟨c₀, hc₀⟩ := hne
    refine ⟨f, fun c hc => ?_, c₀, hc₀, ?_⟩
    · exact le_of_lt (lt_trans hf0 (hfu c (subset_affineSpan ℝ C hc)))
    · exact lt_trans hf0 (hfu c₀ (subset_affineSpan ℝ C hc₀))

lemma core_lemma (g : F → EReal) (A : E →ₗ[ℝ] F)
    (hconv : Convex ℝ (epigraph g)) (hbot : ∀ x, ⊥ < g x)
    (h0 : g 0 < ⊤)
    (x₀ : E) (hx₀ : A x₀ ∈ intrinsicInterior ℝ (effDom g))
    (s : E) (α : ℝ) (hα : ∀ x, ((inner ℝ s x : ℝ) : EReal) - g (A x) ≤ α) :
    ∃ p : F, A.adjoint p = s ∧ ∀ y, ((inner ℝ p y : ℝ) : EReal) - g y ≤ α := by
  set gr : F → ℝ := fun y => (g y).toReal with hgr
  have hgr_eq : ∀ y, g y < ⊤ → g y = (gr y : EReal) := fun y hy =>
    (EReal.coe_toReal hy.ne (hbot y).ne').symm
  set g0 := gr 0 with hg0def
  have hg0 : g 0 = (g0 : EReal) := hgr_eq 0 h0
  set C₀ : Set (F × ℝ) := {z | ∃ (y : F) (r : ℝ) (x : E) (t : ℝ), g y ≤ (r : EReal) ∧ 0 < t ∧
      z = (y - A x, r - inner ℝ s x + α + t)} with hC₀
  have hC : Convex ℝ C₀ := by
    rintro z₁ ⟨y₁, r₁, x₁, t₁, hg₁, ht₁, rfl⟩ z₂ ⟨y₂, r₂, x₂, t₂, hg₂, ht₂, rfl⟩ a b ha hb hab
    have hep : (a • y₁ + b • y₂, a * r₁ + b * r₂) ∈ epigraph g := by
      have := hconv (show (y₁, r₁) ∈ epigraph g from hg₁) (show (y₂, r₂) ∈ epigraph g from hg₂)
        ha hb hab
      simpa using this
    refine ⟨a • y₁ + b • y₂, a * r₁ + b * r₂, a • x₁ + b • x₂, a * t₁ + b * t₂, hep, ?_, ?_⟩
    · rcases ha.eq_or_lt with rfl | ha'
      · simp only [zero_add] at hab
        subst hab
        simpa using ht₂
      · have := mul_pos ha' ht₁
        have := mul_nonneg hb ht₂.le
        linarith
    · ext
      · simp only [Prod.smul_mk, Prod.mk_add_mk, map_add, map_smul, smul_sub]
        abel
      · simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul, inner_add_right,
          real_inner_smul_right]
        linear_combination α * hab
  have h0C : (0 : F × ℝ) ∉ C₀ := by
    rintro ⟨y, r, x, t, hg, ht, hz⟩
    have h1 : y = A x := by
      have := congrArg Prod.fst hz
      simp only [Prod.fst_zero] at this
      exact (sub_eq_zero.1 this.symm)
    have h2 : r - inner ℝ s x + α + t = 0 := by
      have := congrArg Prod.snd hz
      simp only [Prod.snd_zero] at this
      linarith
    subst h1
    have h3 : ((inner ℝ s x : ℝ) : EReal) - (r : EReal) ≤ α :=
      le_trans (EReal.sub_le_sub le_rfl hg) (hα x)
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff] at h3
    linarith
  have hne : C₀.Nonempty := ⟨_, 0, g0, 0, 1, le_of_eq hg0, one_pos, rfl⟩
  obtain ⟨f, hf1, hf2⟩ := proper_sep C₀ hC hne h0C
  set β := f ((0 : F), (1 : ℝ)) with hβ
  set b : F →L[ℝ] ℝ := f.comp (ContinuousLinearMap.inl ℝ F ℝ) with hb
  have hfd : ∀ (y : F) (ρ : ℝ), f (y, ρ) = b y + ρ * β := by
    intro y ρ
    have : ((y, ρ) : F × ℝ) = (y, (0:ℝ)) + ρ • ((0 : F), (1 : ℝ)) := by ext <;> simp
    rw [this, map_add, map_smul, smul_eq_mul]
    rfl
  have hkey : ∀ (y : F) (r : ℝ) (x : E) (t : ℝ), g y ≤ (r : EReal) → 0 < t →
      0 ≤ b y - b (A x) + (r - inner ℝ s x + α + t) * β := by
    intro y r x t hy ht
    have := hf1 _ ⟨y, r, x, t, hy, ht, rfl⟩
    rw [hfd, map_sub] at this
    exact this
  have hβnn : 0 ≤ β := by
    by_contra hneg
    push_neg at hneg
    have := hkey 0 g0 0 (|g0 + α| + 1) (le_of_eq hg0) (by positivity)
    simp only [map_zero, sub_zero, inner_zero_right] at this
    have h4 : 0 < g0 - 0 + α + (|g0 + α| + 1) := by
      have := neg_abs_le (g0 + α)
      linarith
    nlinarith
  have hL : ∀ x, b (A x) + inner ℝ s x * β ≤ (g0 + α + 1) * β := by
    intro x
    have := hkey 0 g0 x 1 (le_of_eq hg0) one_pos
    simp only [map_zero, zero_sub] at this
    nlinarith
  have hL0 : ∀ x, b (A x) + inner ℝ s x * β = 0 := by
    intro x
    by_contra hne
    set c := ((g0 + α + 1) * β + 1) / (b (A x) + inner ℝ s x * β) with hc
    have h5 := hL (c • x)
    rw [map_smul, map_smul, real_inner_smul_right, smul_eq_mul] at h5
    have h6 : c * (b (A x) + inner ℝ s x * β) = (g0 + α + 1) * β + 1 := div_mul_cancel₀ _ hne
    nlinarith
  rcases hβnn.eq_or_lt with hβ0 | hβpos
  · -- vertical case: contradiction with the qualification condition
    exfalso
    obtain ⟨z, ⟨y₁, r₁, x₁, t₁, hg₁, ht₁, rfl⟩, hz⟩ := hf2
    rw [hfd, ← hβ0, mul_zero, add_zero, map_sub] at hz
    have hbA : ∀ x, b (A x) = 0 := by
      intro x
      have := hL0 x
      rw [← hβ0, mul_zero, add_zero] at this
      exact this
    rw [hbA, sub_zero] at hz
    have hy₁ : y₁ ∈ effDom g := lt_of_le_of_lt hg₁ (EReal.coe_lt_top r₁)
    obtain ⟨ε, hε, hmem⟩ := ri_extend hx₀ hy₁
    have hpos : ∀ y ∈ effDom g, 0 ≤ b y := by
      intro y hy
      have := hkey y (gr y) 0 1 (le_of_eq (hgr_eq y hy)) one_pos
      rw [← hβ0, mul_zero, add_zero, map_zero, map_zero, sub_zero] at this
      exact this
    have := hpos _ hmem
    rw [map_add, map_smul, map_sub, hbA, smul_eq_mul] at this
    nlinarith
  · -- non-vertical case
    refine ⟨(InnerProductSpace.toDual ℝ F).symm ((-(1/β)) • b), ?_, ?_⟩
    · apply ext_inner_right ℝ
      intro x
      rw [LinearMap.adjoint_inner_left, InnerProductSpace.toDual_symm_apply]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have := hL0 x
      field_simp
      linarith
    · intro y
      rw [InnerProductSpace.toDual_symm_apply]
      simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
      by_cases hy : g y < ⊤
      · rw [hgr_eq y hy, ← EReal.coe_sub, EReal.coe_le_coe_iff]
        have key : ∀ t : ℝ, 0 < t → 0 ≤ b y + (gr y + α) * β + t * β := by
          intro t ht
          have := hkey y (gr y) 0 t (le_of_eq (hgr_eq y hy)) ht
          simp only [map_zero, sub_zero, inner_zero_right] at this
          linarith
        have h7 : 0 ≤ b y + (gr y + α) * β := by
          by_contra hneg
          push_neg at hneg
          have := key (-(b y + (gr y + α) * β) / (2 * β)) (by
            apply _root_.div_pos <;> linarith)
          have h8 : (-(b y + (gr y + α) * β) / (2 * β)) * β = -(b y + (gr y + α) * β) / 2 := by
            field_simp
          linarith
        have h9 : -(1 / β) * b y = -(b y / β) := by ring
        rw [h9]
        have h10 : b y / β ≥ -(gr y + α) := by
          rw [ge_iff_le, le_div_iff₀ hβpos]
          linarith
        linarith
      · rw [not_lt, top_le_iff] at hy
        rw [hy, EReal.sub_top]
        exact bot_le

set_option linter.unusedVariables false in
theorem FCA_chap_E_2_2_2
  (g : F → EReal)
  (A₀ : E →ₗ[ℝ] F)
  (hg_closed_convex : InClosedConvRn g)
  (hg_nondegenerate : IsNondegenerate g)
  (h_zero : 0 ∈ effDom g)
  (h_dom_nonempty : Set.Nonempty
    (linearRange A₀ ∩ intrinsicInterior ℝ (effDom g))) :
  let gA₀ := fun x => g (A₀ x)
  let A_star_g_star := imageFun A₀.adjoint (conjugate g)
  (∀ s, conjugate gA₀ s = A_star_g_star s) ∧
  (∀ s ∈ effDom ((conjugate gA₀)), ∃ p',
    (A₀.adjoint p' = s) ∧
    ((conjugate g p') =
      sInf (Set.image (conjugate g) {p | A₀.adjoint p = s})) ∧
    ((conjugate gA₀ s) = (A_star_g_star s)) ∧
    ((A_star_g_star s) = (conjugate g p'))) := by

  intro gA₀ A_star_g_star
  obtain ⟨⟨hbot, _, hconv⟩, _⟩ := hg_closed_convex
  obtain ⟨y₀, ⟨x₀, rfl⟩, hy₀⟩ := h_dom_nonempty
  have easy : ∀ s p, A₀.adjoint p = s → conjugate gA₀ s ≤ conjugate g p := by
    intro s p hp
    apply sSup_le
    rintro _ ⟨x, -, rfl⟩
    apply le_sSup
    refine ⟨A₀ x, Set.mem_univ _, ?_⟩
    simp only [gA₀]
    rw [← hp, LinearMap.adjoint_inner_left]
  have easy' : ∀ s, conjugate gA₀ s ≤ A_star_g_star s := by
    intro s
    apply le_sInf
    rintro _ ⟨p, hp, rfl⟩
    exact easy s p hp
  have hard : ∀ s, conjugate gA₀ s < ⊤ →
      ∃ p, A₀.adjoint p = s ∧ conjugate g p ≤ conjugate gA₀ s := by
    intro s hs
    have hne_bot : conjugate gA₀ s ≠ ⊥ := by
      have h1 : ((inner ℝ s (0:E) : ℝ) : EReal) - gA₀ 0 ≤ conjugate gA₀ s :=
        le_sSup ⟨0, Set.mem_univ _, rfl⟩
      have h2 : gA₀ 0 = g 0 := by simp [gA₀]
      rw [h2, inner_zero_right, EReal.coe_zero, zero_sub] at h1
      intro hbot'
      rw [hbot', le_bot_iff, EReal.neg_eq_bot_iff] at h1
      exact h_zero.ne h1
    set α := (conjugate gA₀ s).toReal with hαdef
    have hα : conjugate gA₀ s = α := (EReal.coe_toReal hs.ne hne_bot).symm
    obtain ⟨p, hp1, hp2⟩ := core_lemma g A₀ hconv hbot h_zero x₀ hy₀ s α (fun x => by
      rw [← hα]; exact le_sSup ⟨x, Set.mem_univ _, rfl⟩)
    refine ⟨p, hp1, ?_⟩
    rw [hα]
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    exact hp2 y
  have main : ∀ s, conjugate gA₀ s = A_star_g_star s := by
    intro s
    rcases lt_or_eq_of_le (le_top : conjugate gA₀ s ≤ ⊤) with hs | hs
    · obtain ⟨p, hp1, hp2⟩ := hard s hs
      apply le_antisymm (easy' s)
      calc A_star_g_star s ≤ conjugate g p := sInf_le ⟨p, hp1, rfl⟩
        _ ≤ conjugate gA₀ s := hp2
    · have := easy' s
      rw [hs, top_le_iff] at this
      rw [hs, this]
  refine ⟨main, ?_⟩
  intro s hs
  obtain ⟨p, hp1, hp2⟩ := hard s hs
  have hle : A_star_g_star s ≤ conjugate g p := sInf_le ⟨p, hp1, rfl⟩
  have heq : conjugate g p = A_star_g_star s := le_antisymm (hp2.trans (easy' s)) hle
  exact ⟨p, hp1, heq, main s, heq.symm⟩

end FCA_chap_E_2_2_2
