import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_3_1_i`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_3_1_i` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_3_1_i`, so the main result is `FCA_chap_C_1_3_1_i.FCA_chap_C_1_3_1_i`.
-/

namespace FCA_chap_C_1_3_1_i

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_C_1_3_1_i
  (σ₁ σ₂ : E → EReal)
  (t₁ t₂ : ℝ)
  (hσ : IsSublinear σ₁ ∧ IsSublinear σ₂)
  (ht : t₁ > 0 ∧ t₂ > 0) :
  let σ := fun x => t₁ * (σ₁) x + t₂ * (σ₂) x
  (∃ x, σ x ≠ ⊤) →
  (IsSublinear σ) ∧
  ((LowerSemicontinuous σ₁ ∧ LowerSemicontinuous σ₂)
    → LowerSemicontinuous σ) := by
  intro σ hne
  obtain ⟨⟨⟨hb₁, -, hc₁⟩, hh₁⟩, ⟨⟨hb₂, -, hc₂⟩, hh₂⟩⟩ := hσ
  obtain ⟨ht₁, ht₂⟩ := ht
  -- multiplication by a positive real keeps values above `⊥`
  have hmulbot : ∀ (t : ℝ), 0 < t → ∀ a : EReal, ⊥ < a → ⊥ < (t : EReal) * a := by
    intro t ht a ha
    induction a using EReal.rec with
    | bot => exact absurd ha (lt_irrefl _)
    | coe a => rw [← EReal.coe_mul]; exact EReal.bot_lt_coe _
    | top => rw [EReal.coe_mul_top_of_pos ht]; exact bot_lt_top
  have hbot : ∀ x, ⊥ < σ x := by
    intro x
    have h1 := hmulbot t₁ ht₁ _ (hb₁ x)
    have h2 := hmulbot t₂ ht₂ _ (hb₂ x)
    exact bot_lt_iff_ne_bot.2 (EReal.add_ne_bot_iff.2 ⟨h1.ne', h2.ne'⟩)
  -- if `σ x ≠ ⊤` then both `σ₁ x` and `σ₂ x` are real numbers
  have hfin : ∀ x, σ x ≠ ⊤ → ∃ u₁ u₂ : ℝ, σ₁ x = u₁ ∧ σ₂ x = u₂ := by
    intro x hx
    have h1 : σ₁ x ≠ ⊤ := by
      intro h
      apply hx
      show (t₁ : EReal) * σ₁ x + t₂ * σ₂ x = ⊤
      rw [h, EReal.coe_mul_top_of_pos ht₁]
      exact EReal.top_add_of_ne_bot (hmulbot t₂ ht₂ _ (hb₂ x)).ne'
    have h2 : σ₂ x ≠ ⊤ := by
      intro h
      apply hx
      show (t₁ : EReal) * σ₁ x + t₂ * σ₂ x = ⊤
      rw [h, EReal.coe_mul_top_of_pos ht₂]
      exact EReal.add_top_of_ne_bot (hmulbot t₁ ht₁ _ (hb₁ x)).ne'
    exact ⟨(σ₁ x).toReal, (σ₂ x).toReal, (EReal.coe_toReal h1 (hb₁ x).ne').symm,
      (EReal.coe_toReal h2 (hb₂ x).ne').symm⟩
  -- functional form of convexity for real-valued points
  have hconvf : ∀ f : E → EReal, ConvexEReal f → ∀ x y : E, ∀ u v : ℝ, f x = u → f y = v →
      ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 → f (a • x + b • y) ≤ ((a * u + b * v : ℝ) : EReal) := by
    intro f hf x y u v hu hv a b ha hb hab
    have hx : (x, u) ∈ epigraph f := by
      show f x ≤ u
      rw [hu]
    have hy : (y, v) ∈ epigraph f := by
      show f y ≤ v
      rw [hv]
    have := hf hx hy ha hb hab
    simpa [epigraph] using this
  have hconv : ConvexEReal σ := by
    intro p hp q hq a b ha hb hab
    obtain ⟨x, r⟩ := p
    obtain ⟨y, s⟩ := q
    change σ x ≤ r at hp
    change σ y ≤ s at hq
    obtain ⟨u₁, u₂, hu₁, hu₂⟩ := hfin x (ne_top_of_le_ne_top (EReal.coe_ne_top r) hp)
    obtain ⟨v₁, v₂, hv₁, hv₂⟩ := hfin y (ne_top_of_le_ne_top (EReal.coe_ne_top s) hq)
    have hp' : t₁ * u₁ + t₂ * u₂ ≤ r := by
      have : σ x = ((t₁ * u₁ + t₂ * u₂ : ℝ) : EReal) := by
        show (t₁ : EReal) * σ₁ x + t₂ * σ₂ x = _
        rw [hu₁, hu₂]; norm_cast
      rw [this] at hp
      exact_mod_cast hp
    have hq' : t₁ * v₁ + t₂ * v₂ ≤ s := by
      have : σ y = ((t₁ * v₁ + t₂ * v₂ : ℝ) : EReal) := by
        show (t₁ : EReal) * σ₁ y + t₂ * σ₂ y = _
        rw [hv₁, hv₂]; norm_cast
      rw [this] at hq
      exact_mod_cast hq
    have k₁ := hconvf σ₁ hc₁ x y u₁ v₁ hu₁ hv₁ a b ha hb hab
    have k₂ := hconvf σ₂ hc₂ x y u₂ v₂ hu₂ hv₂ a b ha hb hab
    show σ (a • x + b • y) ≤ ((a • r + b • s : ℝ) : EReal)
    calc σ (a • x + b • y)
        = (t₁ : EReal) * σ₁ (a • x + b • y) + t₂ * σ₂ (a • x + b • y) := rfl
      _ ≤ (t₁ : EReal) * ((a * u₁ + b * v₁ : ℝ) : EReal) + t₂ * ((a * u₂ + b * v₂ : ℝ) : EReal) := by
          gcongr
      _ = ((a * (t₁ * u₁ + t₂ * u₂) + b * (t₁ * v₁ + t₂ * v₂) : ℝ) : EReal) := by
          norm_cast; ring
      _ ≤ ((a • r + b • s : ℝ) : EReal) := by
          rw [EReal.coe_le_coe_iff, smul_eq_mul, smul_eq_mul]
          exact add_le_add (mul_le_mul_of_nonneg_left hp' ha) (mul_le_mul_of_nonneg_left hq' hb)
  have hhom : IsERealPosHomogeneous σ := by
    intro x t ht
    show (t₁ : EReal) * σ₁ (t • x) + t₂ * σ₂ (t • x) = t * ((t₁ : EReal) * σ₁ x + t₂ * σ₂ x)
    rw [hh₁ x t ht, hh₂ x t ht,
      EReal.left_distrib_of_nonneg_of_ne_top (EReal.coe_nonneg.2 ht.le) (EReal.coe_ne_top t),
      ← mul_assoc, ← mul_assoc, ← mul_assoc, ← mul_assoc, mul_comm (t₁ : EReal) t,
      mul_comm (t₂ : EReal) t]
  refine ⟨⟨⟨hbot, ?_, hconv⟩, hhom⟩, ?_⟩
  · obtain ⟨x, hx⟩ := hne
    exact ⟨x, lt_top_iff_ne_top.2 hx⟩
  · rintro ⟨hl₁, hl₂⟩
    have hmul : ∀ (t : ℝ), 0 < t → ∀ f : E → EReal, LowerSemicontinuous f →
        LowerSemicontinuous (fun x => (t : EReal) * f x) := by
      intro t ht f hf
      have hcont : Continuous (fun a : EReal => (t : EReal) * a) := by
        rw [continuous_iff_continuousAt]
        intro a
        exact EReal.Tendsto.const_mul Filter.tendsto_id (Or.inl (EReal.coe_ne_bot t))
          (Or.inl (EReal.coe_ne_top t))
      have hmono : Monotone (fun a : EReal => (t : EReal) * a) := fun a b hab =>
        mul_le_mul_of_nonneg_left hab (EReal.coe_nonneg.2 ht.le)
      exact hcont.comp_lowerSemicontinuous hf hmono
    apply LowerSemicontinuous.add' (hmul t₁ ht₁ σ₁ hl₁) (hmul t₂ ht₂ σ₂ hl₂)
    intro x
    apply EReal.continuousAt_add
    · right; exact (hmulbot t₂ ht₂ _ (hb₂ x)).ne'
    · left; exact (hmulbot t₁ ht₁ _ (hb₁ x)).ne'

end FCA_chap_C_1_3_1_i
