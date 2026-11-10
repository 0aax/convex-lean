import ConvexStarLib.Defs

/-!
# `FCA_chap_E_1_4_4`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_1_4_4` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_1_4_4`, so the main result is `FCA_chap_E_1_4_4.FCA_chap_E_1_4_4`.
-/

namespace FCA_chap_E_1_4_4

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_E_1_4_4
  (f : E → EReal)
  (x s : E)
  (hf_closed_convex : InClosedConvRn f)
  (hf_nondegenerate : IsNondegenerate f) :
  List.TFAE [
    f x + conjugate f s - inner ℝ s x = 0,
    s ∈ convexSubdifferential f x,
    x ∈ convexSubdifferential (conjugate f) s
  ] := by
  obtain ⟨⟨hbot, ⟨x0, hx0⟩, hconv⟩, hlsc⟩ := hf_closed_convex
  obtain ⟨_, s0, b, hs0⟩ := hf_nondegenerate
  have hkey : ∀ c : ℝ, ¬ f x ≤ (c : EReal) →
      ∃ (a : E) (β : ℝ), (∀ z, ((inner ℝ a z - β : ℝ) : EReal) ≤ f z) ∧
        c < inner ℝ a x - β := by
    intro c hc
    have hclosed : IsClosed (epigraph f) := by
      have h1 := hlsc.isClosed_epigraph
      have h2 : epigraph f =
          (fun p : E × ℝ => (p.1, (p.2 : EReal))) ⁻¹' {p : E × EReal | f p.1 ≤ p.2} := rfl
      rw [h2]
      exact h1.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
    have hnot : (x, c) ∉ epigraph f := hc
    obtain ⟨L, u, hL, hu⟩ := geometric_hahn_banach_closed_point hconv hclosed hnot
    set ℓ : StrongDual ℝ E := L.comp (ContinuousLinearMap.inl ℝ E ℝ) with hℓ
    set α : ℝ := L ((0 : E), (1 : ℝ)) with hα
    have hLeq : ∀ (z : E) (t : ℝ), L (z, t) = ℓ z + t * α := by
      intro z t
      have : ((z, t) : E × ℝ) = (z, 0) + t • ((0 : E), (1 : ℝ)) := by
        ext <;> simp
      rw [this, map_add, map_smul, smul_eq_mul]
      rfl
    have hx0r : f x0 = ((f x0).toReal : EReal) := (EReal.coe_toReal hx0.ne (hbot x0).ne').symm
    set r0 := (f x0).toReal with hr0
    have hαle : α ≤ 0 := by
      by_contra hpos
      push_neg at hpos
      set k := |u - ℓ x0 - r0 * α| / α with hk
      have hk0 : 0 ≤ k := div_nonneg (abs_nonneg _) hpos.le
      have hmem : (x0, r0 + k) ∈ epigraph f := by
        show f x0 ≤ ((r0 + k : ℝ) : EReal)
        rw [hx0r]
        exact EReal.coe_le_coe_iff.mpr (by linarith)
      have h1 := hL _ hmem
      rw [hLeq] at h1
      have hkα : k * α = |u - ℓ x0 - r0 * α| := div_mul_cancel₀ _ hpos.ne'
      have h2 := le_abs_self (u - ℓ x0 - r0 * α)
      nlinarith
    haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
    set a0 : E := (InnerProductSpace.toDual ℝ E).symm ℓ with ha0def
    have ha0 : ∀ z, inner ℝ a0 z = ℓ z := fun z => InnerProductSpace.toDual_symm_apply
    set D := ℓ x + c * α - u with hDdef
    have hD : 0 < D := by
      have := hu
      rw [hLeq] at this
      rw [hDdef]
      linarith
    set K := b - inner ℝ s0 x + c with hKdef
    set μ := D / (|K| + 1) with hμdef
    have hK1 : 0 < |K| + 1 := by positivity
    have hμ : 0 < μ := div_pos hD hK1
    have hμK : μ * K < D := by
      have h1 : μ * (|K| + 1) = D := div_mul_cancel₀ _ hK1.ne'
      have h2 : K ≤ |K| := le_abs_self K
      nlinarith
    set γ := μ - α with hγdef
    have hγ : 0 < γ := by rw [hγdef]; linarith
    have hinner : ∀ z, inner ℝ (γ⁻¹ • (a0 + μ • s0)) z - (u + μ * b) / γ
        = (ℓ z + μ * inner ℝ s0 z - (u + μ * b)) / γ := by
      intro z
      rw [real_inner_smul_left, inner_add_left, real_inner_smul_left, ha0]
      field_simp
    refine ⟨γ⁻¹ • (a0 + μ • s0), (u + μ * b) / γ, ?_, ?_⟩
    · intro z
      cases hfz : f z with
      | bot => exact absurd hfz (hbot z).ne'
      | top => exact le_top
      | coe r =>
        have hmem : (z, r) ∈ epigraph f := by
          show f z ≤ (r : EReal)
          rw [hfz]
        have h1 := hL _ hmem
        rw [hLeq] at h1
        have h2 := hs0 z
        rw [hfz] at h2
        have h3 : inner ℝ s0 z - b ≤ r := by
          have : ((inner ℝ s0 z : ℝ) : EReal) - (b : EReal) = ((inner ℝ s0 z - b : ℝ) : EReal) := by
            norm_cast
          rw [this] at h2
          exact EReal.coe_le_coe_iff.mp h2
        rw [EReal.coe_le_coe_iff, hinner, div_le_iff₀ hγ]
        have h4 := mul_le_mul_of_nonneg_left h3 hμ.le
        rw [hγdef]
        nlinarith
    · rw [hinner, lt_div_iff₀ hγ]
      rw [hγdef]
      have := hμK
      rw [hKdef] at this
      rw [hDdef] at this
      nlinarith
  have hcases : ∀ y, f y = ⊤ ∨ ∃ r : ℝ, f y = r := by
    intro y
    cases h : f y with
    | bot => exact absurd h (hbot y).ne'
    | coe r => exact Or.inr ⟨r, rfl⟩
    | top => exact Or.inl rfl
  have hle : ∀ t y : E, ((inner ℝ t y : ℝ) : EReal) - f y ≤ conjugate f t := fun t y =>
    le_sSup ⟨y, Set.mem_univ _, rfl⟩
  have hx0r : f x0 = ((f x0).toReal : EReal) := (EReal.coe_toReal hx0.ne (hbot x0).ne').symm
  have hconj_bot : ∀ t, conjugate f t ≠ ⊥ := by
    intro t h
    have h1 := hle t x0
    rw [h, hx0r, ← EReal.coe_sub] at h1
    exact absurd h1 (not_le.mpr (EReal.bot_lt_coe _))
  have hconj_le : ∀ (a : E) (β : ℝ), (∀ z, ((inner ℝ a z - β : ℝ) : EReal) ≤ f z) →
      conjugate f a ≤ β := by
    intro a β h
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    rcases hcases y with hy | ⟨r, hy⟩
    · simp only [hy, EReal.sub_top]; exact bot_le
    · have := h y
      rw [hy, EReal.coe_le_coe_iff] at this
      simp only [hy]
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
  tfae_have 1 → 2 := by
    intro h
    have hfx_top : f x ≠ ⊤ := by
      intro htop
      rw [htop, EReal.top_add_of_ne_bot (hconj_bot s), EReal.top_sub_coe] at h
      exact EReal.top_ne_zero h
    have hconj_top : conjugate f s ≠ ⊤ := by
      intro htop
      rw [htop, EReal.add_top_of_ne_bot (hbot x).ne', EReal.top_sub_coe] at h
      exact EReal.top_ne_zero h
    obtain ⟨p, hp⟩ : ∃ p : ℝ, f x = p := ⟨_, (EReal.coe_toReal hfx_top (hbot x).ne').symm⟩
    obtain ⟨q, hq⟩ : ∃ q : ℝ, conjugate f s = q :=
      ⟨_, (EReal.coe_toReal hconj_top (hconj_bot s)).symm⟩
    rw [hp, hq, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_zero] at h
    intro y
    rw [hp]
    rcases hcases y with hy | ⟨r, hy⟩
    · rw [hy]; exact le_top
    · have h1 := hle s y
      rw [hy, hq, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
      rw [hy, ge_iff_le, ← EReal.coe_add, EReal.coe_le_coe_iff, inner_sub_right]
      linarith
  tfae_have 2 → 3 := by
    intro h
    have hfx_top : f x ≠ ⊤ := by
      intro htop
      have h1 := h x0
      rw [htop, EReal.top_add_coe] at h1
      exact absurd hx0 (not_lt.mpr h1)
    obtain ⟨p, hp⟩ : ∃ p : ℝ, f x = p := ⟨_, (EReal.coe_toReal hfx_top (hbot x).ne').symm⟩
    have hq : conjugate f s = ((inner ℝ s x - p : ℝ) : EReal) := by
      apply le_antisymm
      · apply hconj_le
        intro z
        have h1 := h z
        rw [hp, ← EReal.coe_add, inner_sub_right] at h1
        refine le_trans (le_of_eq ?_) h1
        congr 1
        ring
      · have := hle s x
        rw [hp, ← EReal.coe_sub] at this
        exact this
    intro t
    have h1 := hle t x
    rw [hp, ← EReal.coe_sub] at h1
    rw [hq, ← EReal.coe_add, inner_sub_right]
    refine le_trans (le_of_eq ?_) h1
    congr 1
    rw [real_inner_comm x t, real_inner_comm x s]
    ring
  tfae_have 3 → 1 := by
    intro h
    have hconj_s0 : conjugate f s0 ≤ b := by
      apply hconj_le
      intro z
      have := hs0 z
      rw [EReal.coe_sub]
      exact this
    have hconj_top : conjugate f s ≠ ⊤ := by
      intro htop
      have h1 := h s0
      rw [htop, EReal.top_add_coe] at h1
      exact absurd (le_trans h1 hconj_s0) (not_le.mpr (EReal.coe_lt_top b))
    obtain ⟨q, hq⟩ : ∃ q : ℝ, conjugate f s = q :=
      ⟨_, (EReal.coe_toReal hconj_top (hconj_bot s)).symm⟩
    have hfx_le : f x ≤ ((inner ℝ x s - q : ℝ) : EReal) := by
      by_contra hc
      obtain ⟨a, β, hab, hlt⟩ := hkey _ hc
      have h1 := hconj_le a β hab
      have h2 := h a
      rw [hq, ← EReal.coe_add] at h2
      have h3 := le_trans h2 h1
      rw [EReal.coe_le_coe_iff, inner_sub_right, real_inner_comm a x] at h3
      linarith
    rcases hcases x with hx | ⟨r, hx⟩
    · rw [hx] at hfx_le; exact absurd hfx_le (not_le.mpr (EReal.coe_lt_top _))
    · rw [hx, EReal.coe_le_coe_iff] at hfx_le
      have h1 := hle s x
      rw [hx, hq, ← EReal.coe_sub, EReal.coe_le_coe_iff] at h1
      rw [hx, hq, ← EReal.coe_add, ← EReal.coe_sub, EReal.coe_eq_zero]
      rw [real_inner_comm s x] at hfx_le
      linarith
  tfae_finish

end FCA_chap_E_1_4_4
