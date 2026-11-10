import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex9`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex9` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex9`, so the main result is `FCA_chap_E_ex9.FCA_chap_E_ex9`.
-/

namespace FCA_chap_E_ex9

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex9
  {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x0 : EuclideanSpace ℝ (Fin n))
  (hK : IsClosed K ∧ Convex ℝ K ∧ IsCone K)
  (hx0 : x0 ∈ K)
  (hx0_dom : x0 ∈ effDom f)
  (hf_closed_convex : InClosedConvRn f)
  (hf_continuous : ContinuousAt f x0)
  (hf_bdd : BddBelow (f '' K))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  (sInf (Set.image f K)) =
  -1 * (sInf (Set.image (fun s => (conjugate f (-1 • s))) (polarCone K))) := by
  simp only [neg_smul, one_smul]
  rw [neg_one_mul]
  have hx0_lt : f x0 < ⊤ := hx0_dom
  set p := sInf (f '' K) with hp
  set d := sInf ((fun s => conjugate f (-s)) '' polarCone K) with hd
  -- weak duality
  have hweak : -p ≤ d := by
    apply le_sInf
    rintro _ ⟨s, hs, rfl⟩
    rw [EReal.neg_le]
    apply le_sInf
    rintro _ ⟨x, hx, rfl⟩
    rw [EReal.neg_le]
    have h1 : ((inner ℝ (-s) x : ℝ) : EReal) - f x ≤ conjugate f (-s) :=
      le_sSup ⟨x, Set.mem_univ _, rfl⟩
    refine le_trans ?_ h1
    have h2 : 0 ≤ inner ℝ (-s) x := by
      rw [inner_neg_left]; linarith [hs x hx]
    rcases eq_top_or_lt_top (f x) with htop | hlt
    · rw [htop]; simp
    · obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
        ⟨(f x).toReal, (EReal.coe_toReal hlt.ne (f_ne_bot x).ne').symm⟩
      rw [hr, ← EReal.coe_neg, ← EReal.coe_sub, EReal.coe_le_coe_iff]
      linarith
  have hpt : p < ⊤ := lt_of_le_of_lt (sInf_le (Set.mem_image_of_mem f hx0)) hx0_lt
  rcases eq_bot_or_bot_lt p with hbot | hbot
  · rw [hbot] at hweak ⊢
    rw [EReal.neg_bot, top_le_iff] at hweak
    rw [hweak, EReal.neg_top]
  · obtain ⟨p₀, hp₀⟩ : ∃ p₀ : ℝ, p = p₀ := ⟨p.toReal, (EReal.coe_toReal hpt.ne hbot.ne').symm⟩
    have hlow : ∀ x ∈ K, (p₀ : EReal) ≤ f x := by
      intro x hx
      rw [← hp₀]
      exact sInf_le (Set.mem_image_of_mem f hx)
    -- main claim
    obtain ⟨s₀, hs₀, hconj⟩ : ∃ s₀ ∈ polarCone K, conjugate f (-s₀) ≤ ((-p₀ : ℝ) : EReal) := by
      obtain ⟨r0, hr0⟩ : ∃ r0 : ℝ, f x0 = r0 :=
        ⟨(f x0).toReal, (EReal.coe_toReal hx0_lt.ne (f_ne_bot x0).ne').symm⟩
      have hconv : Convex ℝ (epigraph f) := hf_closed_convex.1.2.2
      have hW : f ⁻¹' Set.Iio (((r0 + 1/2 : ℝ)) : EReal) ∈ 𝓝 x0 := by
        apply hf_continuous.preimage_mem_nhds
        rw [hr0]
        exact Iio_mem_nhds (EReal.coe_lt_coe_iff.mpr (by linarith))
      have hint : ∀ t : ℝ, r0 + 1/2 < t →
          ((x0, t) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ interior (epigraph f) := by
        intro t ht
        rw [mem_interior_iff_mem_nhds]
        apply Filter.mem_of_superset (prod_mem_nhds hW (Ioi_mem_nhds ht))
        rintro ⟨x, τ⟩ ⟨hx, hτ⟩
        have hx' : f x < (((r0 + 1/2 : ℝ)) : EReal) := hx
        have hτ' : r0 + 1/2 < τ := hτ
        show f x ≤ (τ : EReal)
        exact le_of_lt (lt_trans hx' (EReal.coe_lt_coe_iff.mpr hτ'))
      have hdisj : Disjoint (interior (epigraph f)) (K ×ˢ Set.Iio p₀) := by
        rw [Set.disjoint_left]
        rintro ⟨x, t⟩ h1 ⟨h2, h3⟩
        have h4' : ((x, t) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ epigraph f := interior_subset h1
        have h4 : f x ≤ (t : EReal) := h4'
        have h5 := hlow x h2
        have h3' : t < p₀ := h3
        exact absurd (lt_of_le_of_lt (h5.trans h4) (EReal.coe_lt_coe_iff.mpr h3')) (lt_irrefl _)
      obtain ⟨L, u, hL1, hL2⟩ := geometric_hahn_banach_open hconv.interior isOpen_interior
        (hK.2.1.prod (convex_Iio p₀)) hdisj
      set c := L (0, 1) with hc_def
      have hL : ∀ (x : EuclideanSpace ℝ (Fin n)) (t : ℝ), L (x, t) = L (x, 0) + t * c := by
        intro x t
        have : ((x, t) : EuclideanSpace ℝ (Fin n) × ℝ)
            = (x, 0) + t • ((0 : EuclideanSpace ℝ (Fin n)), (1 : ℝ)) := by
          ext <;> simp
        rw [this, map_add, map_smul, smul_eq_mul]
      have hL1' : ∀ q ∈ epigraph f, L q ≤ u := by
        intro q hq
        have hne : (interior (epigraph f)).Nonempty := ⟨_, hint (r0 + 1) (by linarith)⟩
        have : q ∈ closure (interior (epigraph f)) := by
          rw [hconv.closure_interior_eq_closure_of_nonempty_interior hne]
          exact subset_closure hq
        exact closure_minimal (fun q hq => (hL1 q hq).le)
          (isClosed_le L.continuous continuous_const) this
      have hL2' : ∀ y ∈ K, ∀ t ≤ p₀, u ≤ L (y, t) := by
        intro y hy t ht
        have : ((y, t) : EuclideanSpace ℝ (Fin n) × ℝ) ∈ closure (K ×ˢ Set.Iio p₀) := by
          rw [closure_prod_eq, hK.1.closure_eq, closure_Iio]
          exact Set.mk_mem_prod hy ht
        exact closure_minimal hL2 (isClosed_le continuous_const L.continuous) this
      have h0K : (0 : EuclideanSpace ℝ (Fin n)) ∈ K := by
        have ht : Filter.Tendsto (fun k : ℕ => (1 / ((k : ℝ) + 1)) • x0) Filter.atTop
            (𝓝 ((0:ℝ) • x0)) :=
          tendsto_one_div_add_atTop_nhds_zero_nat.smul_const x0
        rw [zero_smul] at ht
        exact hK.1.mem_of_tendsto ht
          (Filter.Eventually.of_forall fun k => hK.2.2 x0 hx0 _ (by positivity))
      have hc : c < 0 := by
        set m := min p₀ (r0 + 1) with hm
        have hm1 : m ≤ p₀ := min_le_left _ _
        have hm2 : m ≤ r0 + 1 := min_le_right _ _
        have h1 := hL1 _ (hint (r0 + 1) (by linarith))
        have h2 := hL2' x0 hx0 (m - 1) (by linarith)
        rw [hL] at h1 h2
        nlinarith
      have hu : u ≤ p₀ * c := by
        have := hL2' 0 h0K p₀ le_rfl
        rw [hL] at this
        have h00 : L (0, 0) = 0 := map_zero L
        linarith
      have hsmul : ∀ (μ : ℝ) (y : EuclideanSpace ℝ (Fin n)), L (μ • y, 0) = μ * L (y, 0) := by
        intro μ y
        have : ((μ • y, (0:ℝ)) : EuclideanSpace ℝ (Fin n) × ℝ) = μ • (y, (0:ℝ)) := by simp
        rw [this, map_smul, smul_eq_mul]
      have hKpos : ∀ y ∈ K, 0 ≤ L (y, 0) := by
        intro y hy
        by_contra hneg
        push_neg at hneg
        have hB : L (y, 0) ≠ 0 := hneg.ne
        have hlam : 0 < (p₀ * c - u + 1) / (-L (y, 0)) := div_pos (by linarith) (by linarith)
        have h1 := hL2' _ (hK.2.2 y hy _ hlam) p₀ le_rfl
        rw [hL, hsmul] at h1
        have h3 : (p₀ * c - u + 1) / (-L (y, 0)) * L (y, 0) = -(p₀ * c - u + 1) := by
          field_simp
        linarith
      obtain ⟨w, hw⟩ : ∃ w : EuclideanSpace ℝ (Fin n), ∀ x, inner ℝ w x = L (x, 0) :=
        ⟨(InnerProductSpace.toDual ℝ _).symm (L.comp (ContinuousLinearMap.inl ℝ _ ℝ)),
          fun x => by rw [InnerProductSpace.toDual_symm_apply]; rfl⟩
      refine ⟨c⁻¹ • w, ?_, ?_⟩
      · intro y hy
        rw [real_inner_smul_left, hw]
        exact mul_nonpos_of_nonpos_of_nonneg (inv_lt_zero.mpr hc).le (hKpos y hy)
      · unfold conjugate
        apply sSup_le
        rintro _ ⟨x, -, rfl⟩
        dsimp only
        have hinner : inner ℝ (-(c⁻¹ • w)) x = -(c⁻¹ * L (x, 0)) := by
          rw [inner_neg_left, real_inner_smul_left, hw]
        rw [hinner]
        rcases eq_top_or_lt_top (f x) with htop | hlt
        · rw [htop]; simp
        · obtain ⟨r, hr⟩ : ∃ r : ℝ, f x = r :=
            ⟨(f x).toReal, (EReal.coe_toReal hlt.ne (f_ne_bot x).ne').symm⟩
          rw [hr, ← EReal.coe_sub, EReal.coe_le_coe_iff]
          have h1 := hL1' (x, r) (by show f x ≤ (r : EReal); rw [hr])
          rw [hL] at h1
          have hb : c * (c⁻¹ * L (x, 0)) = L (x, 0) := mul_inv_cancel_left₀ hc.ne _
          nlinarith
    apply le_antisymm
    · rw [EReal.le_neg]
      calc d ≤ conjugate f (-s₀) := sInf_le ⟨s₀, hs₀, rfl⟩
        _ ≤ ((-p₀ : ℝ) : EReal) := hconj
        _ = -p := by rw [hp₀, EReal.coe_neg]
    · exact EReal.neg_le.mp hweak

end FCA_chap_E_ex9
