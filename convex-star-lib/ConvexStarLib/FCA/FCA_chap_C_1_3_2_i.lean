import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_3_2_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_3_2_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_3_2_i`, so the main result is `FCA_chap_C_1_3_2_i.FCA_chap_C_1_3_2_i`.
-/

namespace FCA_chap_C_1_3_2_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_3_2_i
  {ι : Type*}
  (σ : ι → (E → EReal))
  (J : Set ι)
  (hσ_sublinear : ∀ j ∈ J, IsSublinear ((σ j)))
  (hσ_minorized : ∃ (s : E), ∃ (b : ℝ),
    ∀ j ∈ J, ∀ (x : E),
    (σ j) x ≥ (inner ℝ s x) + b)
  (hJ : J.Nonempty) :
  let σ_inf := fun x => sInf (⋃ j ∈ J, {(σ j) x})
  let σ' := convexHullFun σ_inf
  IsSublinear σ' := by
  intro σ_inf σ'
  obtain ⟨s, b, hsb⟩ := hσ_minorized
  -- each `σ j x` is either `⊤` or a real number
  have hσ_real : ∀ j ∈ J, ∀ x, σ j x ≠ ⊤ → σ j x = ((σ j x).toReal : EReal) := by
    intro j hj x hx
    exact (EReal.coe_toReal hx ((hσ_sublinear j hj).1.1 x).ne').symm
  -- lower bound `⟪s, x⟫ ≤ σ j x`
  have hlow : ∀ j ∈ J, ∀ x, ((inner ℝ s x : ℝ) : EReal) ≤ σ j x := by
    intro j hj x
    by_cases htop : σ j x = ⊤
    · rw [htop]; exact le_top
    · obtain ⟨m, hm⟩ : ∃ m : ℝ, σ j x = m := ⟨_, hσ_real j hj x htop⟩
      rw [hm, EReal.coe_le_coe_iff]
      by_contra hlt
      push_neg at hlt
      have hdpos : 0 < inner ℝ s x - m := by linarith
      have htpos : 0 < (|b| + 1) / (inner ℝ s x - m) := by positivity
      have h1 := hsb j hj (((|b| + 1) / (inner ℝ s x - m)) • x)
      rw [(hσ_sublinear j hj).2 x _ htpos, hm, real_inner_smul_right] at h1
      rw [← EReal.coe_mul, ← EReal.coe_add, ge_iff_le, EReal.coe_le_coe_iff] at h1
      have h2 : (|b| + 1) / (inner ℝ s x - m) * (inner ℝ s x - m) = |b| + 1 := by field_simp
      have h3 := neg_abs_le b
      nlinarith
  have hinf_low : ∀ x, ((inner ℝ s x : ℝ) : EReal) ≤ σ_inf x := by
    intro x
    apply le_sInf
    intro y hy
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    exact hlow j hj x
  have hinf_le : ∀ j ∈ J, ∀ x, σ_inf x ≤ σ j x := by
    intro j hj x
    apply sInf_le
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨j, hj, rfl⟩
  have hinf_smul : ∀ x (r t : ℝ), 0 < t → σ_inf x ≤ r → σ_inf (t • x) ≤ ((t * r : ℝ) : EReal) := by
    intro x r t ht hxr
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    have h1 : σ_inf x < ((z / t : ℝ) : EReal) := by
      refine lt_of_le_of_lt hxr ?_
      rw [EReal.coe_lt_coe_iff, lt_div_iff₀ ht]; linarith
    rw [sInf_lt_iff] at h1
    obtain ⟨y, hy, hyz⟩ := h1
    simp only [Set.mem_iUnion, Set.mem_singleton_iff] at hy
    obtain ⟨j, hj, rfl⟩ := hy
    have hne : σ j x ≠ ⊤ := ne_top_of_lt hyz
    have hmx := hσ_real j hj x hne
    refine le_trans (hinf_le j hj (t • x)) ?_
    rw [(hσ_sublinear j hj).2 x t ht, hmx, ← EReal.coe_mul, EReal.coe_le_coe_iff]
    rw [hmx, EReal.coe_lt_coe_iff, lt_div_iff₀ ht] at hyz
    linarith
  -- the convex hull of the epigraph
  obtain ⟨C, hC⟩ : ∃ C, C = convexHull ℝ (epigraph σ_inf) := ⟨_, rfl⟩
  have hσ'_def : ∀ x, σ' x = sInf ((fun r : ℝ => (r : EReal)) '' {r : ℝ | (x, r) ∈ C}) := by
    intro x; subst hC; rfl
  have hCconv : Convex ℝ C := hC ▸ convex_convexHull ℝ _
  have hepiC : epigraph σ_inf ⊆ C := hC ▸ subset_convexHull ℝ _
  have hA : ∀ x (r : ℝ), (x, r) ∈ C → σ' x ≤ r := by
    intro x r h
    rw [hσ'_def]
    apply sInf_le
    exact ⟨r, h, rfl⟩
  have hCup : ∀ x (r r' : ℝ), (x, r) ∈ C → r ≤ r' → (x, r') ∈ C := by
    intro x r r' h hrr'
    have key : C ⊆ {p : E × ℝ | p + (0, r' - r) ∈ C} := by
      rw [hC]
      apply convexHull_min
      · intro p hp
        rw [← hC]
        apply hepiC
        show σ_inf (p + (0, r' - r)).1 ≤ ((p + (0, r' - r)).2 : EReal)
        simp only [Prod.fst_add, Prod.snd_add, add_zero]
        refine le_trans hp ?_
        rw [EReal.coe_le_coe_iff]; linarith
      · rw [← hC]
        intro p hp q hq a c ha hc hac
        simp only [Set.mem_setOf_eq] at hp hq ⊢
        have := hCconv hp hq ha hc hac
        convert this using 1
        rw [smul_add, smul_add, add_add_add_comm, ← add_smul, hac, one_smul]
    have := key h
    simp only [Set.mem_setOf_eq, Prod.mk_add_mk, add_zero] at this
    convert this using 2; ring
  have hCsmul : ∀ (t : ℝ), 0 < t → ∀ p ∈ C, t • p ∈ C := by
    intro t ht
    have key : C ⊆ {p : E × ℝ | t • p ∈ C} := by
      rw [hC]
      apply convexHull_min
      · intro p hp
        rw [← hC]
        apply hepiC
        show σ_inf (t • p).1 ≤ ((t • p).2 : EReal)
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
        exact hinf_smul p.1 p.2 t ht hp
      · rw [← hC]
        exact hCconv.smul_preimage t
    exact fun p hp => key hp
  have hClow : ∀ p ∈ C, inner ℝ s p.1 ≤ p.2 := by
    have key : C ⊆ {p : E × ℝ | inner ℝ s p.1 ≤ p.2} := by
      rw [hC]
      apply convexHull_min
      · intro p hp
        have h1 := le_trans (hinf_low p.1) hp
        exact EReal.coe_le_coe_iff.mp h1
      · intro p hp q hq a c ha hc hac
        simp only [Set.mem_setOf_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
          smul_eq_mul, inner_add_right, real_inner_smul_right] at hp hq ⊢
        have := mul_le_mul_of_nonneg_left hp ha
        have := mul_le_mul_of_nonneg_left hq hc
        linarith
    exact fun p hp => key hp
  have hB : ∀ x (r : ℝ), σ' x < r → (x, r) ∈ C := by
    intro x r h
    rw [hσ'_def, sInf_lt_iff] at h
    obtain ⟨y, ⟨r', hr', rfl⟩, hlt⟩ := h
    exact hCup x r' r hr' (EReal.coe_lt_coe_iff.mp hlt).le
  have hσ'_low : ∀ x, ((inner ℝ s x : ℝ) : EReal) ≤ σ' x := by
    intro x
    rw [hσ'_def]
    apply le_sInf
    rintro y ⟨r, hr, rfl⟩
    exact EReal.coe_le_coe_iff.mpr (hClow (x, r) hr)
  have hbot : ∀ x, ⊥ < σ' x := fun x => lt_of_lt_of_le (EReal.bot_lt_coe _) (hσ'_low x)
  -- finiteness somewhere
  obtain ⟨j₀, hj₀⟩ := hJ
  obtain ⟨x₀, hx₀⟩ := (hσ_sublinear j₀ hj₀).1.2.1
  have htop : σ' x₀ < ⊤ := by
    have hmx := hσ_real j₀ hj₀ x₀ hx₀.ne
    have hmem : (x₀, (σ j₀ x₀).toReal) ∈ C := by
      apply hepiC
      show σ_inf x₀ ≤ (((σ j₀ x₀).toReal : ℝ) : EReal)
      rw [← hmx]; exact hinf_le j₀ hj₀ x₀
    exact lt_of_le_of_lt (hA _ _ hmem) (EReal.coe_lt_top _)
  -- convexity
  have hconv : ConvexEReal σ' := by
    intro p hp q hq a c ha hc hac
    show σ' (a • p + c • q).1 ≤ ((a • p + c • q).2 : EReal)
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hz ⊢
    have hεpos : 0 < z - (a * p.2 + c * q.2) := by linarith
    have h1 : (p.1, p.2 + (z - (a * p.2 + c * q.2))) ∈ C :=
      hB p.1 _ (lt_of_le_of_lt hp (by rw [EReal.coe_lt_coe_iff]; linarith))
    have h2 : (q.1, q.2 + (z - (a * p.2 + c * q.2))) ∈ C :=
      hB q.1 _ (lt_of_le_of_lt hq (by rw [EReal.coe_lt_coe_iff]; linarith))
    have h3 := hCconv h1 h2 ha hc hac
    have h4 : a • (p.1, p.2 + (z - (a * p.2 + c * q.2))) + c • (q.1, q.2 + (z - (a * p.2 + c * q.2)))
        = (a • p.1 + c • q.1, z) := by
      ext
      · simp
      · simp only [Prod.snd_add, Prod.smul_snd, smul_eq_mul]
        linear_combination (z - (a * p.2 + c * q.2)) * hac
    rw [h4] at h3
    exact hA _ _ h3
  -- positive homogeneity
  have hscale : ∀ x (m t : ℝ), 0 < t → σ' x ≤ m → σ' (t • x) ≤ ((t * m : ℝ) : EReal) := by
    intro x m t ht hxm
    rw [← EReal.le_of_forall_lt_iff_le]
    intro z hz
    rw [EReal.coe_lt_coe_iff] at hz
    have h1 : (x, z / t) ∈ C :=
      hB x (z / t) (lt_of_le_of_lt hxm (by rw [EReal.coe_lt_coe_iff, lt_div_iff₀ ht]; linarith))
    have h2 := hCsmul t ht _ h1
    have h3 : t • (x, z / t) = (t • x, z) := by
      ext
      · simp
      · simp only [Prod.smul_snd, smul_eq_mul]; field_simp
    rw [h3] at h2
    exact hA _ _ h2
  have hhom : IsERealPosHomogeneous σ' := by
    intro x t ht
    apply le_antisymm
    · by_cases htop' : σ' x = ⊤
      · rw [htop', EReal.coe_mul_top_of_pos ht]; exact le_top
      · have hmx : σ' x = ((σ' x).toReal : EReal) := (EReal.coe_toReal htop' (hbot x).ne').symm
        rw [hmx, ← EReal.coe_mul]
        exact hscale x _ t ht hmx.le
    · by_cases htop' : σ' (t • x) = ⊤
      · rw [htop']; exact le_top
      · have hmx : σ' (t • x) = ((σ' (t • x)).toReal : EReal) :=
          (EReal.coe_toReal htop' (hbot _).ne').symm
        have h1 := hscale (t • x) _ t⁻¹ (inv_pos.mpr ht) hmx.le
        rw [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] at h1
        have hne : σ' x ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top _) h1
        have hmx' : σ' x = ((σ' x).toReal : EReal) := (EReal.coe_toReal hne (hbot x).ne').symm
        rw [hmx', ← EReal.coe_mul, hmx, EReal.coe_le_coe_iff]
        rw [hmx', EReal.coe_le_coe_iff] at h1
        calc t * (σ' x).toReal ≤ t * (t⁻¹ * (σ' (t • x)).toReal) :=
              mul_le_mul_of_nonneg_left h1 ht.le
          _ = (σ' (t • x)).toReal := by field_simp
  exact ⟨⟨hbot, ⟨x₀, htop⟩, hconv⟩, hhom⟩

end FCA_chap_C_1_3_2_i
