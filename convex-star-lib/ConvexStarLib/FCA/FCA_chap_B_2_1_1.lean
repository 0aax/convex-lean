import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_1_1`, so the main result is `FCA_chap_B_2_1_1.FCA_chap_B_2_1_1`.
-/

namespace FCA_chap_B_2_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_1_1
  {m : ℕ}
  (f : Fin m → (E → EReal))
  (t : Fin m → ℝ)
  (ht_positive : ∀ i, (t i) > 0)
  (hf_common_finite : ∃ x₀, ∀ i, (f i) x₀ < ⊤)
  (f_ne_bot : ∀ x₁ x₂, ⊥ < f x₁ x₂) :
  let g := fun x => ∑ i, (t i) * ((f i) x)
  ((∀ i, InConvRn ((f i))) → InConvRn g) ∧
  ((∀ i, InClosedConvRn ((f i))) → InClosedConvRn g) := by
  intro g
  have hg_def : ∀ x, g x = ∑ i, ((t i : ℝ) : EReal) * f i x := fun x => rfl
  -- each term is not `⊥`
  have hterm_ne_bot : ∀ i x, ((t i : EReal) * f i x) ≠ ⊥ := by
    intro i x
    have h1 := f_ne_bot i x
    generalize f i x = v at h1 ⊢
    induction v using EReal.rec with
    | bot => exact absurd h1 (lt_irrefl _)
    | coe r => rw [← EReal.coe_mul]; exact EReal.coe_ne_bot _
    | top => rw [EReal.coe_mul_top_of_pos (ht_positive i)]; exact top_ne_bot
  have hsum_ne_bot : ∀ (s : Finset (Fin m)) x, (∑ i ∈ s, (t i : EReal) * f i x) ≠ ⊥ := by
    intro s x
    exact Finset.sum_induction _ (· ≠ ⊥)
      (fun a b ha hb => EReal.add_ne_bot_iff.mpr ⟨ha, hb⟩) EReal.zero_ne_bot
      (fun i _ => hterm_ne_bot i x)
  have hg_ne_bot : ∀ x, ⊥ < g x := fun x => bot_lt_iff_ne_bot.mpr (hsum_ne_bot Finset.univ x)
  -- the coercion `ℝ → EReal` as an additive monoid hom
  let coeHom : ℝ →+ EReal := ⟨⟨(↑), EReal.coe_zero⟩, EReal.coe_add⟩
  -- value of `g` at a point where every `f i` is finite
  have hg_real : ∀ x, (∀ i, f i x ≠ ⊤) →
      g x = ((∑ i, t i * (f i x).toReal : ℝ) : EReal) := by
    intro x hx
    rw [hg_def]
    have h1 : ((∑ i, t i * (f i x).toReal : ℝ) : EReal) = coeHom (∑ i, t i * (f i x).toReal) := rfl
    rw [h1, map_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    show _ = ((t i * (f i x).toReal : ℝ) : EReal)
    rw [EReal.coe_mul, EReal.coe_toReal (hx i) (f_ne_bot i x).ne']
  have hg_fin : ∃ x, g x < ⊤ := by
    obtain ⟨x₀, hx₀⟩ := hf_common_finite
    refine ⟨x₀, ?_⟩
    rw [hg_real x₀ (fun i => (hx₀ i).ne)]
    exact EReal.coe_lt_top _
  -- if `g x ≠ ⊤` then each `f i x ≠ ⊤`
  have hfin_of : ∀ x, g x ≠ ⊤ → ∀ i, f i x ≠ ⊤ := by
    intro x hx i hi
    apply hx
    rw [hg_def, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), hi,
      EReal.coe_mul_top_of_pos (ht_positive i)]
    exact EReal.top_add_of_ne_bot (hsum_ne_bot _ x)
  have hconv : (∀ i, InConvRn (f i)) → ConvexEReal g := by
    intro hf
    rintro ⟨x, α⟩ hp ⟨y, β⟩ hq a b ha hb hab
    simp only [epigraph, Set.mem_setOf_eq] at hp hq ⊢
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    have hxt : ∀ i, f i x ≠ ⊤ := hfin_of x (ne_top_of_le_ne_top (EReal.coe_ne_top α) hp)
    have hyt : ∀ i, f i y ≠ ⊤ := hfin_of y (ne_top_of_le_ne_top (EReal.coe_ne_top β) hq)
    -- convexity of each `f i`
    have hzi : ∀ i, f i (a • x + b • y) ≤
        ((a * (f i x).toReal + b * (f i y).toReal : ℝ) : EReal) := by
      intro i
      have hc := (hf i).2.2
      have hxi : ((x, (f i x).toReal) : E × ℝ) ∈ epigraph (f i) := by
        show f i x ≤ ((f i x).toReal : EReal)
        rw [EReal.coe_toReal (hxt i) (f_ne_bot i x).ne']
      have hyi : ((y, (f i y).toReal) : E × ℝ) ∈ epigraph (f i) := by
        show f i y ≤ ((f i y).toReal : EReal)
        rw [EReal.coe_toReal (hyt i) (f_ne_bot i y).ne']
      have := hc hxi hyi ha hb hab
      simpa [epigraph] using this
    have hzt : ∀ i, f i (a • x + b • y) ≠ ⊤ := fun i =>
      ne_top_of_le_ne_top (EReal.coe_ne_top _) (hzi i)
    rw [hg_real _ hzt]
    rw [hg_real _ hxt] at hp
    rw [hg_real _ hyt] at hq
    rw [EReal.coe_le_coe_iff] at hp hq ⊢
    have hzi' : ∀ i, (f i (a • x + b • y)).toReal ≤ a * (f i x).toReal + b * (f i y).toReal := by
      intro i
      have := hzi i
      rw [← EReal.coe_toReal (hzt i) (f_ne_bot i _).ne', EReal.coe_le_coe_iff] at this
      exact this
    calc ∑ i, t i * (f i (a • x + b • y)).toReal
        ≤ ∑ i, t i * (a * (f i x).toReal + b * (f i y).toReal) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left (hzi' i) (ht_positive i).le
      _ = a * ∑ i, t i * (f i x).toReal + b * ∑ i, t i * (f i y).toReal := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
      _ ≤ a * α + b * β := by
          apply _root_.add_le_add
          · exact mul_le_mul_of_nonneg_left hp ha
          · exact mul_le_mul_of_nonneg_left hq hb
  -- lower semicontinuity
  have hlsc : (∀ i, LowerSemicontinuous (f i)) → LowerSemicontinuous g := by
    intro hf
    have hterm : ∀ i, LowerSemicontinuous (fun x => (t i : EReal) * f i x) := by
      intro i
      have hcont : Continuous (fun y : EReal => (t i : EReal) * y) := by
        rw [continuous_iff_continuousAt]
        intro y
        have h := EReal.continuousAt_mul (p := ((t i : EReal), y))
          (Or.inl (show ((t i : ℝ) : EReal) ≠ 0 by exact_mod_cast (ht_positive i).ne'))
          (Or.inl (show ((t i : ℝ) : EReal) ≠ 0 by exact_mod_cast (ht_positive i).ne'))
          (Or.inl (EReal.coe_ne_bot _))
          (Or.inl (EReal.coe_ne_top _))
        exact h.comp (Continuous.prodMk_right _).continuousAt
      have hmono : Monotone (fun y : EReal => (t i : EReal) * y) := by
        intro y z hyz
        exact mul_le_mul_of_nonneg_left hyz (by exact_mod_cast (ht_positive i).le)
      exact hcont.comp_lowerSemicontinuous (hf i) hmono
    have key : ∀ s : Finset (Fin m),
        LowerSemicontinuous (fun x => ∑ i ∈ s, (t i : EReal) * f i x) := by
      intro s
      induction s using Finset.induction_on with
      | empty => simpa using lowerSemicontinuous_const
      | insert j s hj IH =>
        simp only [Finset.sum_insert hj]
        refine (hterm j).add' IH (fun x => ?_)
        exact EReal.continuousAt_add (Or.inr (hsum_ne_bot s x)) (Or.inl (hterm_ne_bot j x))
    exact key Finset.univ
  constructor
  · intro hf
    exact ⟨hg_ne_bot, hg_fin, hconv hf⟩
  · intro hf
    exact ⟨⟨hg_ne_bot, hg_fin, hconv (fun i => (hf i).1)⟩, hlsc (fun i => (hf i).2)⟩

end FCA_chap_B_2_1_1
