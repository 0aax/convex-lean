import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_1_2`, so the main result is `FCA_chap_C_3_1_2.FCA_chap_C_3_1_2`.
-/

namespace FCA_chap_C_3_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_3_1_2
  (S : Set E)
  (σ : E → EReal)
  (hS_nonempty : Set.Nonempty S)
  (hS_closed : IsClosed S)
  (hS_convex : Convex ℝ S)
  (hσ_closed : LowerSemicontinuous σ)
  (hσ_sublinear : IsSublinear σ) :
  let support_fun := supportFunction S
  let S' := supportSublevelSet σ
  List.TFAE [
    ∀ (x : E), support_fun x = σ x,
    S = S'
  ] := by
  intro support_fun S'
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  obtain ⟨⟨hσ_bot, ⟨x₀, hx₀⟩, hσ_conv⟩, hσ_hom⟩ := hσ_sublinear
  tfae_have 1 → 2 := by
    intro h
    ext v
    constructor
    · intro hv w
      rw [← h w]
      exact le_sSup ⟨v, hv, rfl⟩
    · intro hv
      by_contra hvS
      obtain ⟨f, u, hfS, hfv⟩ := geometric_hahn_banach_closed_point hS_convex hS_closed hvS
      set w := (InnerProductSpace.toDual ℝ E).symm f with hw_def
      have hw : ∀ y, inner ℝ y w = f y := by
        intro y
        rw [real_inner_comm, hw_def]
        exact InnerProductSpace.toDual_symm_apply
      have h1 : support_fun w ≤ (u : EReal) := by
        apply sSup_le
        rintro _ ⟨s, hs, rfl⟩
        dsimp only
        rw [hw]
        exact EReal.coe_le_coe_iff.mpr (hfS s hs).le
      have h2 : ((inner ℝ v w : ℝ) : EReal) ≤ support_fun w := by
        rw [h w]
        exact hv w
      rw [hw] at h2
      have h3 := h2.trans h1
      rw [EReal.coe_le_coe_iff] at h3
      linarith
  tfae_have 2 → 1 := by
    intro hSS x
    have hfin : ∀ y, σ y ≠ ⊤ → ∃ a : ℝ, σ y = a := by
      intro y hy
      exact ⟨(σ y).toReal, (EReal.coe_toReal hy (hσ_bot y).ne').symm⟩
    have key : ∀ r : ℝ, (r : EReal) < σ x → ∃ v ∈ S', r < inner ℝ v x := by
      intro r hr
      obtain ⟨v₀, hv₀⟩ : S'.Nonempty := hSS ▸ hS_nonempty
      have hK_conv : Convex ℝ (epigraph σ) := hσ_conv
      have hK_closed : IsClosed (epigraph σ) := by
        have h1 := hσ_closed.isClosed_epigraph
        exact h1.preimage (continuous_fst.prodMk (continuous_coe_real_ereal.comp continuous_snd))
      have hxr : (x, r) ∉ epigraph σ := by
        intro h
        exact absurd h (not_le.mpr hr)
      obtain ⟨f, u, hfxr, hfK⟩ := geometric_hahn_banach_point_closed hK_conv hK_closed hxr
      set w := (InnerProductSpace.toDual ℝ E).symm (f.comp (ContinuousLinearMap.inl ℝ E ℝ))
        with hw_def
      set α := f (0, 1) with hα_def
      have hf : ∀ (y : E) (s : ℝ), f (y, s) = inner ℝ w y + s * α := by
        intro y s
        have : ((y, s) : E × ℝ) = (y, (0:ℝ)) + s • ((0:E), (1:ℝ)) := by simp
        rw [this, map_add, map_smul, smul_eq_mul]
        rw [hw_def, InnerProductSpace.toDual_symm_apply]
        rfl
      -- cone property
      have hcone : ∀ (y : E) (s : ℝ), σ y ≤ (s : EReal) → ∀ t : ℝ, 0 < t →
          σ (t • y) ≤ ((t * s : ℝ) : EReal) := by
        intro y s hys t ht
        rw [hσ_hom y t ht]
        obtain ⟨a, ha⟩ := hfin y (ne_top_of_le_ne_top (EReal.coe_ne_top s) hys)
        rw [ha] at hys ⊢
        rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
        rw [EReal.coe_le_coe_iff] at hys
        exact mul_le_mul_of_nonneg_left hys ht.le
      -- f nonneg on the epigraph
      have hpos : ∀ (y : E) (s : ℝ), σ y ≤ (s : EReal) → 0 ≤ inner ℝ w y + s * α := by
        intro y s hys
        by_contra hneg
        push_neg at hneg
        set c := inner ℝ w y + s * α with hc_def
        set t := (|u| + 1) / (-c) with ht_def
        have hc : 0 < -c := by linarith
        have ht : 0 < t := div_pos (by positivity) hc
        have h1 := hfK (t • y, t * s) (hcone y s hys t ht)
        rw [hf, real_inner_smul_right] at h1
        have h2 : t * (inner ℝ w y) + t * s * α = t * c := by rw [hc_def]; ring
        have h3 : t * c = -(|u| + 1) := by
          rw [ht_def, div_mul_eq_mul_div, div_eq_iff hc.ne']; ring
        linarith [neg_abs_le u]
      obtain ⟨a, ha⟩ := hfin x₀ hx₀.ne
      have hu0 : u ≤ 0 := by
        by_contra hu
        push_neg at hu
        set c := inner ℝ w x₀ + a * α with hc_def
        set t := u / (|c| + 1) with ht_def
        have ht : 0 < t := div_pos hu (by positivity)
        have h1 := hfK (t • x₀, t * a) (hcone x₀ a ha.le t ht)
        rw [hf, real_inner_smul_right] at h1
        have h2 : t * (inner ℝ w x₀) + t * a * α = t * c := by rw [hc_def]; ring
        have h3 : t * c ≤ t * |c| := mul_le_mul_of_nonneg_left (le_abs_self c) ht.le
        have h4 : t * |c| < u := by
          rw [ht_def, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith [abs_nonneg c]
        linarith
      have hα0 : 0 ≤ α := by
        by_contra hα
        push_neg at hα
        set c := inner ℝ w x₀ + a * α with hc_def
        set c' := (|c| + 1) / (-α) with hc'_def
        have hc' : 0 ≤ c' := div_nonneg (by positivity) (by linarith)
        have h1 := hpos x₀ (a + c') (by rw [ha]; exact EReal.coe_le_coe_iff.mpr (by linarith))
        have h2 : c' * α = -(|c| + 1) := by
          rw [hc'_def, div_mul_eq_mul_div, div_eq_iff (by linarith : (0:ℝ) < -α).ne']; ring
        have h3 : inner ℝ w x₀ + (a + c') * α = c + c' * α := by rw [hc_def]; ring
        linarith [le_abs_self c]
      rw [hf] at hfxr
      rcases hα0.lt_or_eq with hα | hα
      · refine ⟨(-α⁻¹) • w, ?_, ?_⟩
        · intro y
          by_cases hy : σ y = ⊤
          · rw [hy]; exact le_top
          obtain ⟨s, hs⟩ := hfin y hy
          rw [hs, EReal.coe_le_coe_iff, real_inner_smul_left]
          have h0 := hpos y s hs.le
          have h1 : 0 ≤ α⁻¹ * (inner ℝ w y + s * α) := mul_nonneg (inv_nonneg.mpr hα.le) h0
          have h2 : α⁻¹ * (inner ℝ w y + s * α) = α⁻¹ * inner ℝ w y + s := by
            field_simp
          linarith
        · rw [real_inner_smul_left]
          have h1 : α⁻¹ * (inner ℝ w x + r * α) < 0 :=
            mul_neg_of_pos_of_neg (inv_pos.mpr hα) (by linarith)
          have h2 : α⁻¹ * (inner ℝ w x + r * α) = α⁻¹ * inner ℝ w x + r := by
            field_simp
          linarith
      · -- α = 0
        rw [← hα, mul_zero, add_zero] at hfxr
        have hwx : inner ℝ w x < 0 := by linarith
        set t := (|r - inner ℝ v₀ x| + 1) / (-inner ℝ w x) with ht_def
        have ht : 0 ≤ t := div_nonneg (by positivity) (by linarith)
        refine ⟨v₀ - t • w, ?_, ?_⟩
        · intro y
          by_cases hy : σ y = ⊤
          · rw [hy]; exact le_top
          obtain ⟨s, hs⟩ := hfin y hy
          have h1 := hpos y s hs.le
          rw [← hα, mul_zero, add_zero] at h1
          have h2 := hv₀ y
          rw [hs, EReal.coe_le_coe_iff] at h2 ⊢
          rw [inner_sub_left, real_inner_smul_left]
          nlinarith
        · rw [inner_sub_left, real_inner_smul_left]
          have h3 : t * inner ℝ w x = -(|r - inner ℝ v₀ x| + 1) := by
            rw [ht_def, div_mul_eq_mul_div, div_eq_iff (by linarith : (0:ℝ) < -inner ℝ w x).ne']
            ring
          linarith [le_abs_self (r - inner ℝ v₀ x)]
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨v, hv, rfl⟩
      rw [hSS] at hv
      exact hv x
    · by_contra hlt
      push_neg at hlt
      obtain ⟨r, hr1, hr2⟩ := EReal.lt_iff_exists_real_btwn.mp hlt
      obtain ⟨v, hv, hrv⟩ := key r hr2
      have h3 : ((inner ℝ v x : ℝ) : EReal) ≤ support_fun x := le_sSup ⟨v, hSS ▸ hv, rfl⟩
      have h4 := h3.trans_lt hr1
      rw [EReal.coe_lt_coe_iff] at h4
      linarith
  tfae_finish

end FCA_chap_C_3_1_2
