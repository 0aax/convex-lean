import ConvexStarLib.Defs

/-!
# `RW_chap_9_12`

Source: Rockafellar & Wets, Variational Analysis.

Statement from the `convex-eval-v28-2h/RW_chap_9_12` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace RW_chap_9_12`, so the main result is `RW_chap_9_12.RW_chap_9_12`.
-/

namespace RW_chap_9_12

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] in
theorem RW_chap_9_12
  (C : Set E)
  (f : E → EReal)
  (κ : ℝ)
  (hC_ne : Set.Nonempty C)
  (hf_lip : IsLipschitzEReal f C κ) :
  let fbar : E → EReal :=
    fun x => sInf ((fun w : E => f w + ((κ * ‖x - w‖ : ℝ) : EReal)) '' C)
  ((∀ x ∈ C, fbar x = f x) ∧
    IsLipschitzEReal fbar Set.univ κ) ∧
  (sInf (f '' C) = sInf (fbar '' Set.univ)) ∧
  ({x : E | x ∈ C ∧ ∀ y ∈ C, f x ≤ f y} =
    C ∩ {x : E | ∀ y : E, fbar x ≤ fbar y}) := by
  intro fbar
  obtain ⟨hκ, hfin, hlip⟩ := hf_lip
  -- real-valued version of `f` on `C`
  set g : E → ℝ := fun w => (f w).toReal with hg
  have hfg : ∀ w ∈ C, f w = ((g w : ℝ) : EReal) := fun w hw =>
    (EReal.coe_toReal (hfin w hw).1 (hfin w hw).2).symm
  have hglip : ∀ x ∈ C, ∀ y ∈ C, g x ≤ g y + κ * ‖x - y‖ := by
    intro x hx y hy
    have h := hlip x y hx hy
    rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm] at h
    linarith [le_abs_self (g x - g y)]
  -- basic properties of `fbar` as an infimum
  have hfbar_le : ∀ x, ∀ w ∈ C, fbar x ≤ ((g w + κ * ‖x - w‖ : ℝ) : EReal) := by
    intro x w hw
    have h : fbar x ≤ f w + ((κ * ‖x - w‖ : ℝ) : EReal) := sInf_le ⟨w, hw, rfl⟩
    rwa [hfg w hw, ← EReal.coe_add] at h
  have hle_fbar : ∀ x, ∀ r : ℝ, (∀ w ∈ C, r ≤ g w + κ * ‖x - w‖) → (r : EReal) ≤ fbar x := by
    intro x r hr
    apply le_sInf
    rintro _ ⟨w, hw, rfl⟩
    show (r : EReal) ≤ f w + ((κ * ‖x - w‖ : ℝ) : EReal)
    rw [hfg w hw, ← EReal.coe_add]
    exact EReal.coe_le_coe_iff.mpr (hr w hw)
  obtain ⟨w0, hw0⟩ := hC_ne
  have hfbar_ne_top : ∀ x, fbar x ≠ ⊤ := fun x =>
    ne_top_of_le_ne_top (EReal.coe_ne_top _) (hfbar_le x w0 hw0)
  have hfbar_ne_bot : ∀ x, fbar x ≠ ⊥ := by
    intro x
    apply ne_bot_of_le_ne_bot (EReal.coe_ne_bot (g w0 - κ * ‖x - w0‖))
    apply hle_fbar
    intro w hw
    have h1 := hglip w0 hw0 w hw
    have h2 : ‖w0 - w‖ ≤ ‖w0 - x‖ + ‖x - w‖ := norm_sub_le_norm_sub_add_norm_sub w0 x w
    have h3 : ‖w0 - x‖ = ‖x - w0‖ := norm_sub_rev w0 x
    have h4 : κ * ‖w0 - w‖ ≤ κ * (‖x - w0‖ + ‖x - w‖) := by
      rw [← h3]; exact mul_le_mul_of_nonneg_left h2 hκ
    nlinarith
  -- real-valued version of `fbar`
  set F : E → ℝ := fun x => (fbar x).toReal with hF
  have hfbarF : ∀ x, fbar x = ((F x : ℝ) : EReal) := fun x =>
    (EReal.coe_toReal (hfbar_ne_top x) (hfbar_ne_bot x)).symm
  have hF_le : ∀ x, ∀ w ∈ C, F x ≤ g w + κ * ‖x - w‖ := by
    intro x w hw
    have h := hfbar_le x w hw
    rw [hfbarF x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hle_F : ∀ x, ∀ r : ℝ, (∀ w ∈ C, r ≤ g w + κ * ‖x - w‖) → r ≤ F x := by
    intro x r hr
    have h := hle_fbar x r hr
    rw [hfbarF x] at h
    exact EReal.coe_le_coe_iff.mp h
  have hFC : ∀ x ∈ C, F x = g x := by
    intro x hx
    apply le_antisymm
    · have h := hF_le x x hx
      simpa using h
    · apply hle_F
      intro w hw
      have h := hglip x hx w hw
      linarith
  have hpart1 : ∀ x ∈ C, fbar x = f x := by
    intro x hx
    rw [hfbarF x, hfg x hx, hFC x hx]
  have hFlip : ∀ x y, F x ≤ F y + κ * ‖x - y‖ := by
    intro x y
    have h : F x - κ * ‖x - y‖ ≤ F y := by
      apply hle_F
      intro w hw
      have h1 := hF_le x w hw
      have h2 : ‖x - w‖ ≤ ‖x - y‖ + ‖y - w‖ := norm_sub_le_norm_sub_add_norm_sub x y w
      have h3 : κ * ‖x - w‖ ≤ κ * (‖x - y‖ + ‖y - w‖) := mul_le_mul_of_nonneg_left h2 hκ
      linarith
    linarith
  refine ⟨⟨hpart1, hκ, fun x _ => ⟨hfbar_ne_top x, hfbar_ne_bot x⟩, ?_⟩, ?_, ?_⟩
  · intro x y _ _
    show ‖F x - F y‖ ≤ κ • dist x y
    rw [Real.norm_eq_abs, smul_eq_mul, dist_eq_norm, abs_le]
    have h1 := hFlip x y
    have h2 := hFlip y x
    rw [norm_sub_rev y x] at h2
    constructor <;> linarith
  · apply le_antisymm
    · apply le_sInf
      rintro _ ⟨x, _, rfl⟩
      apply le_sInf
      rintro _ ⟨w, hw, rfl⟩
      exact le_trans (sInf_le ⟨w, hw, rfl⟩)
        (le_add_of_nonneg_right (EReal.coe_nonneg.mpr (mul_nonneg hκ (norm_nonneg _))))
    · apply le_sInf
      rintro _ ⟨x, hx, rfl⟩
      rw [← hpart1 x hx]
      exact sInf_le ⟨x, Set.mem_univ _, rfl⟩
  · ext x
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hx, hmin⟩
      refine ⟨hx, fun y => ?_⟩
      rw [hfbarF x, hfbarF y]
      apply EReal.coe_le_coe_iff.mpr
      apply hle_F
      intro w hw
      have h := hmin w hw
      rw [hfg x hx, hfg w hw] at h
      have h' := EReal.coe_le_coe_iff.mp h
      rw [hFC x hx]
      have : 0 ≤ κ * ‖y - w‖ := mul_nonneg hκ (norm_nonneg _)
      linarith
    · rintro ⟨hx, hmin⟩
      refine ⟨hx, fun y hy => ?_⟩
      have h := hmin y
      rwa [hpart1 x hx, hpart1 y hy] at h

end RW_chap_9_12
