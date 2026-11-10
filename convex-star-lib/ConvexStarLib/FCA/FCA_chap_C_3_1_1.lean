import ConvexStarLib.Defs

/-!
# `FCA_chap_C_3_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_3_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_3_1_1`, so the main result is `FCA_chap_C_3_1_1.FCA_chap_C_3_1_1`.
-/

namespace FCA_chap_C_3_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_3_1_1
  (σ : E → EReal)
  (hσ_closed : LowerSemicontinuous σ)
  (hσ_sublinear : IsSublinear σ) :
  let Sσ := supportSublevelSet σ
  Sσ.Nonempty ∧
  (∀ x, σ x = supportFunction Sσ x) := by
  intro Sσ
  obtain ⟨⟨hbot, ⟨x₀, hx₀⟩, hconv⟩, hhom⟩ := hσ_sublinear
  -- real-valuedness away from ⊤
  have hreal : ∀ y, σ y ≠ ⊤ → σ y = ((σ y).toReal : EReal) := fun y hy =>
    (EReal.coe_toReal hy (hbot y).ne').symm
  -- closedness of the epigraph
  have hclosed : IsClosed (epigraph σ) := by
    have h1 := hσ_closed.isClosed_epigraph
    have : epigraph σ = (Prod.map id ((↑) : ℝ → EReal)) ⁻¹' {p : E × EReal | σ p.1 ≤ p.2} := by
      ext p; simp [epigraph]
    rw [this]
    exact h1.preimage (continuous_id.prodMap continuous_coe_real_ereal)
  -- cone property
  have hcone : ∀ y : E, ∀ ρ : ℝ, σ y ≤ (ρ : EReal) → ∀ t : ℝ, 0 < t →
      σ (t • y) ≤ ((t * ρ : ℝ) : EReal) := by
    intro y ρ hyρ t ht
    rw [hhom y t ht]
    have hy : σ y ≠ ⊤ := ne_top_of_le_ne_top (EReal.coe_ne_top ρ) hyρ
    rw [hreal y hy] at hyρ ⊢
    rw [← EReal.coe_mul, EReal.coe_le_coe_iff]
    rw [EReal.coe_le_coe_iff] at hyρ
    exact mul_le_mul_of_nonneg_left hyρ ht.le
  -- base point
  set ρ₀ := (σ x₀).toReal with hρ₀
  have hb₀ : σ x₀ ≤ (ρ₀ : EReal) := (hreal x₀ hx₀.ne).le
  -- separation
  have hsep : ∀ x : E, ∀ r : ℝ, ¬ (σ x ≤ (r : EReal)) → ∃ s : E, ∃ β : ℝ, 0 ≤ β ∧
      (∀ y : E, ∀ ρ : ℝ, σ y ≤ (ρ : EReal) → 0 ≤ inner ℝ s y + β * ρ) ∧
      inner ℝ s x + β * r < 0 := by
    intro x r hxr
    obtain ⟨f, u, hfu, hfb⟩ := geometric_hahn_banach_point_closed hconv hclosed
      (show (x, r) ∉ epigraph σ from hxr)
    obtain ⟨s, hs⟩ : ∃ s : E, ∀ y, inner ℝ s y = f (y, 0) :=
      ⟨(InnerProductSpace.toDual ℝ E).symm (f.comp (ContinuousLinearMap.inl ℝ E ℝ)),
        fun y => by simp⟩
    have hf : ∀ y : E, ∀ ρ : ℝ, f (y, ρ) = inner ℝ s y + f (0, 1) * ρ := by
      intro y ρ
      have h1 : ((y, ρ) : E × ℝ) = (y, (0:ℝ)) + ρ • ((0:E), (1:ℝ)) := by
        ext <;> simp
      rw [h1, map_add, map_smul, hs, smul_eq_mul, mul_comm]
    have hfb' : ∀ y : E, ∀ ρ : ℝ, σ y ≤ (ρ : EReal) → u < f (y, ρ) := fun y ρ h => hfb (y, ρ) h
    have hsmul : ∀ y : E, ∀ ρ t : ℝ, f (t • y, t * ρ) = t * f (y, ρ) := by
      intro y ρ t
      have : ((t • y, t * ρ) : E × ℝ) = t • (y, ρ) := by simp [smul_eq_mul]
      rw [this, map_smul, smul_eq_mul]
    -- f ≥ 0 on epi
    have hpos : ∀ y : E, ∀ ρ : ℝ, σ y ≤ (ρ : EReal) → 0 ≤ f (y, ρ) := by
      intro y ρ hyρ
      by_contra hneg
      push_neg at hneg
      have hd : 0 < - f (y, ρ) := by linarith
      set t := (|u| + 1) / (- f (y, ρ)) with ht
      have htpos : 0 < t := by positivity
      have h1 := hfb' _ _ (hcone y ρ hyρ t htpos)
      rw [hsmul] at h1
      have h2 : t * f (y, ρ) = -(|u| + 1) := by
        have : f (y, ρ) ≠ 0 := hneg.ne
        rw [ht]; field_simp
      linarith [le_abs_self u, neg_abs_le u]
    have hu : u ≤ 0 := by
      by_contra hu
      push_neg at hu
      have h1 := hpos x₀ ρ₀ hb₀
      rcases eq_or_lt_of_le h1 with h | h
      · linarith [hfb' x₀ ρ₀ hb₀]
      · set t := u / (2 * f (x₀, ρ₀)) with ht
        have htpos : 0 < t := by positivity
        have h2 := hfb' _ _ (hcone x₀ ρ₀ hb₀ t htpos)
        rw [hsmul] at h2
        have h3 : t * f (x₀, ρ₀) = u / 2 := by
          rw [ht]; field_simp
        linarith
    have hβ : 0 ≤ f (0, 1) := by
      by_contra hβ
      push_neg at hβ
      have h1 := hpos x₀ ρ₀ hb₀
      rw [hf] at h1
      set t := (inner ℝ s x₀ + f (0, 1) * ρ₀) / (- f (0, 1)) + 1 with ht
      have htnn : 0 ≤ t := by
        have : 0 < - f (0, 1) := by linarith
        positivity
      have h2 := hpos x₀ (ρ₀ + t) (le_trans hb₀ (EReal.coe_le_coe_iff.mpr (by linarith)))
      rw [hf] at h2
      have h3 : inner ℝ s x₀ + f (0, 1) * (ρ₀ + t) = f (0, 1) := by
        rw [ht]
        have : f (0, 1) ≠ 0 := hβ.ne
        field_simp
        ring
      linarith
    refine ⟨s, f (0, 1), hβ, fun y ρ h => ?_, ?_⟩
    · rw [← hf]; exact hpos y ρ h
    · rw [← hf]; linarith
  -- normalized functionals give elements of Sσ
  have hmemS : ∀ s : E, ∀ β : ℝ, 0 < β →
      (∀ y : E, ∀ ρ : ℝ, σ y ≤ (ρ : EReal) → 0 ≤ inner ℝ s y + β * ρ) → (-β⁻¹) • s ∈ Sσ := by
    intro s β hβ hsβ w
    by_cases hw : σ w = ⊤
    · rw [hw]; exact le_top
    · rw [hreal w hw, EReal.coe_le_coe_iff, real_inner_smul_left]
      have h1 := hsβ w (σ w).toReal (le_of_eq (hreal w hw))
      have h2 : -β⁻¹ * inner ℝ s w
          = (σ w).toReal - β⁻¹ * (inner ℝ s w + β * (σ w).toReal) := by
        field_simp; ring
      rw [h2]
      linarith [mul_nonneg (inv_pos.mpr hβ).le h1]
  -- nonemptiness
  have hne : Sσ.Nonempty := by
    obtain ⟨s, β, -, hsβ, hlt⟩ := hsep x₀ (ρ₀ - 1) (by
      rw [hreal x₀ hx₀.ne, EReal.coe_le_coe_iff]
      linarith)
    have h1 := hsβ x₀ ρ₀ hb₀
    have hβpos : 0 < β := by nlinarith
    exact ⟨_, hmemS s β hβpos hsβ⟩
  refine ⟨hne, fun x => ?_⟩
  obtain ⟨v₀, hv₀⟩ := hne
  apply le_antisymm
  · apply le_of_forall_lt
    intro c hc
    induction c using EReal.rec with
    | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe (inner ℝ v₀ x)) (le_sSup ⟨v₀, hv₀, rfl⟩)
    | top => exact absurd hc (not_lt_of_ge le_top)
    | coe r =>
      obtain ⟨s, β, hβ, hsβ, hlt⟩ := hsep x r (not_le.mpr hc)
      rcases eq_or_lt_of_le hβ with h0 | hβpos
      · -- vertical hyperplane: move along the direction `-s` from `v₀`
        subst h0
        simp only [zero_mul, add_zero] at hsβ hlt
        set d := - inner ℝ s x with hd
        have hdpos : 0 < d := by linarith
        set t := (|r - inner ℝ v₀ x| + 1) / d with ht
        have htnn : 0 ≤ t := by positivity
        have hv : v₀ - t • s ∈ Sσ := by
          intro w
          by_cases hw : σ w = ⊤
          · rw [hw]; exact le_top
          · have h1 := hsβ w (σ w).toReal (le_of_eq (hreal w hw))
            refine le_trans (EReal.coe_le_coe_iff.mpr ?_) (hv₀ w)
            rw [inner_sub_left, real_inner_smul_left]
            nlinarith
        refine lt_of_lt_of_le ?_ (le_sSup ⟨v₀ - t • s, hv, rfl⟩)
        rw [EReal.coe_lt_coe_iff, inner_sub_left, real_inner_smul_left]
        have h2 : t * inner ℝ s x = -(|r - inner ℝ v₀ x| + 1) := by
          rw [ht]
          have : d ≠ 0 := hdpos.ne'
          field_simp
          rw [hd]
          ring
        rw [h2]
        linarith [le_abs_self (r - inner ℝ v₀ x)]
      · refine lt_of_lt_of_le ?_ (le_sSup ⟨(-β⁻¹) • s, hmemS s β hβpos hsβ, rfl⟩)
        rw [EReal.coe_lt_coe_iff, real_inner_smul_left]
        have h2 : -β⁻¹ * inner ℝ s x = r - β⁻¹ * (inner ℝ s x + β * r) := by
          field_simp; ring
        rw [h2]
        have h3 : β⁻¹ * (inner ℝ s x + β * r) < 0 :=
          mul_neg_of_pos_of_neg (inv_pos.mpr hβpos) hlt
        linarith
  · apply sSup_le
    rintro _ ⟨v, hv, rfl⟩
    exact hv x

end FCA_chap_C_3_1_1
