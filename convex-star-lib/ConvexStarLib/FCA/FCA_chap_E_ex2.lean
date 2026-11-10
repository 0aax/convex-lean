import ConvexStarLib.Defs

/-!
# `FCA_chap_E_ex2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_ex2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_ex2`, so the main result is `FCA_chap_E_ex2.FCA_chap_E_ex2`.
-/

namespace FCA_chap_E_ex2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

set_option linter.unusedVariables false in
theorem FCA_chap_E_ex2
  (g : E → EReal)
  (h : E → ℝ)
  (S : Set E)
  (hg_nd : IsNondegenerate g)
  (hh_conv : InConvRn (liftRealtoEReal h))
  (hS : Set.Nonempty S) :
  let f : E → EReal := fun v => (g v) - (h v)
  let g_conj := conjugate g
  let h_conj := conjugate (liftRealtoEReal h)
  let α : EReal := sSup (Set.image (fun v => (h v : EReal)) S)
  (∀ (s : E),
  conjugate f s = sSup (Set.image
                        (fun p => (g_conj (s + p)) - (h_conj p))
                        (effDom h_conj))) ∧
  (sInf (Set.image (fun v => (f v)) Set.univ) =
  sInf (Set.image (fun p => (h_conj p) - (g_conj p))
  (effDom h_conj))) ∧
  (-(α : EReal) = sInf (Set.image
                  (fun s => (h_conj s) - (supportFunction S s))
                  (effDom h_conj))) := by
  intro f g_conj h_conj α
  have hneg : ∀ (A : Set E) (Ψ : E → EReal), sInf (Ψ '' A) = -sSup ((fun i => -Ψ i) '' A) := by
    intro A Ψ
    apply le_antisymm
    · rw [EReal.le_neg]
      apply sSup_le
      rintro _ ⟨i, hi, rfl⟩
      exact EReal.neg_le_neg_iff.2 (sInf_le ⟨i, hi, rfl⟩)
    · apply le_sInf
      rintro _ ⟨i, hi, rfl⟩
      rw [EReal.neg_le]
      exact le_sSup ⟨i, hi, rfl⟩
  have hconv : ConvexOn ℝ Set.univ h := by
    rw [convexOn_iff_convex_epigraph]
    have := hh_conv.2.2
    unfold ConvexEReal epigraph liftRealtoEReal at this
    simpa [EReal.coe_le_coe_iff] using this
  -- existence of subgradients of the finite convex function `h`
  have hsub : ∀ x, ∃ p : E, ∀ y, h x + inner ℝ p (y - x) ≤ h y := by
    intro x
    have hcont : Continuous h := hconv.locallyLipschitz.continuous
    set U : Set (E × ℝ) := {q | h q.1 < q.2} with hU_def
    have hU_open : IsOpen U := isOpen_lt (hcont.comp continuous_fst) continuous_snd
    have hU_conv : Convex ℝ U := by
      have := hconv.convex_strict_epigraph
      simpa using this
    have hx_notin : ((x, h x) : E × ℝ) ∉ U := by simp [hU_def]
    obtain ⟨Φ, hΦ⟩ := geometric_hahn_banach_open_point hU_conv hU_open hx_notin
    set c : ℝ := Φ (0, 1) with hc_def
    set L : StrongDual ℝ E := Φ.comp (ContinuousLinearMap.inl ℝ E ℝ) with hL_def
    have hΦ_eq : ∀ y t, Φ (y, t) = L y + t * c := by
      intro y t
      have : ((y, t) : E × ℝ) = (y, 0) + t • ((0 : E), (1 : ℝ)) := by simp
      rw [this, map_add, map_smul]
      simp [hL_def, hc_def, smul_eq_mul]
    have hc_neg : c < 0 := by
      have := hΦ (x, h x + 1) (by simp [hU_def])
      rw [hΦ_eq, hΦ_eq] at this
      linarith
    have key : ∀ y, L y + h y * c ≤ L x + h x * c := by
      intro y
      by_contra hcon
      push_neg at hcon
      set d := L y + h y * c - (L x + h x * c) with hd
      have hd_pos : 0 < d := by linarith
      have hmem : ((y, h y + d / (-c)) : E × ℝ) ∈ U := by
        simp only [hU_def, Set.mem_setOf_eq]
        have : 0 < d / (-c) := div_pos hd_pos (by linarith)
        linarith
      have := hΦ _ hmem
      rw [hΦ_eq, hΦ_eq] at this
      have hc0 : c ≠ 0 := ne_of_lt hc_neg
      have h1 : (h y + d / (-c)) * c = h y * c - d := by
        field_simp
        ring
      rw [h1] at this
      linarith
    refine ⟨(-c)⁻¹ • (InnerProductSpace.toDual ℝ E).symm L, fun y => ?_⟩
    rw [real_inner_smul_left, InnerProductSpace.toDual_symm_apply, map_sub]
    have hnc : 0 < -c := by linarith
    have := key y
    have : (-c)⁻¹ * (L y - L x) ≤ h y - h x := by
      rw [inv_mul_le_iff₀ hnc]
      nlinarith
    linarith
  have hA : ∀ p x, ((inner ℝ p x - h x : ℝ) : EReal) ≤ h_conj p := by
    intro p x
    apply le_sSup
    exact ⟨x, Set.mem_univ _, by simp [liftRealtoEReal]⟩
  have hB : ∀ x, ∃ p, h_conj p = ((inner ℝ p x - h x : ℝ) : EReal) := by
    intro x
    obtain ⟨p, hp⟩ := hsub x
    refine ⟨p, le_antisymm ?_ (hA p x)⟩
    apply sSup_le
    rintro _ ⟨y, -, rfl⟩
    simp only [liftRealtoEReal]
    rw [← EReal.coe_sub, EReal.coe_le_coe_iff]
    have := hp y
    rw [inner_sub_right] at this
    linarith
  have hC : ∀ p ∈ effDom h_conj, ∃ q : ℝ, h_conj p = q := by
    intro p hp
    have h1 : h_conj p ≠ ⊤ := ne_of_lt hp
    have h2 : h_conj p ≠ ⊥ := by
      have := hA p 0
      intro h3
      rw [h3] at this
      simp at this
    exact ⟨(h_conj p).toReal, (EReal.coe_toReal h1 h2).symm⟩
  have hD : ∀ p x, ((inner ℝ p x : ℝ) : EReal) - g x ≤ g_conj p := by
    intro p x
    exact le_sSup ⟨x, Set.mem_univ _, rfl⟩
  have hE : ∀ x, g x ≠ ⊤ → ∃ r : ℝ, g x = r := by
    intro x hx
    obtain ⟨s0, b, hb⟩ := hg_nd.2
    have h1 := hb x
    have h2 : g x ≠ ⊥ := by
      intro h3
      rw [h3] at h1
      rw [ge_iff_le, le_bot_iff] at h1
      exact EReal.coe_ne_bot _ (by rw [EReal.coe_sub]; exact h1)
    exact ⟨(g x).toReal, (EReal.coe_toReal hx h2).symm⟩
  have hmemB : ∀ x p, h_conj p = ((inner ℝ p x - h x : ℝ) : EReal) → p ∈ effDom h_conj := by
    intro x p hp
    show h_conj p < ⊤
    rw [hp]
    exact EReal.coe_lt_top _
  have claim1 : ∀ s, conjugate f s =
      sSup ((fun p => g_conj (s + p) - h_conj p) '' effDom h_conj) := by
    intro s
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      by_cases hgx : g x = ⊤
      · simp [f, hgx]
      · obtain ⟨r, hr⟩ := hE x hgx
        obtain ⟨p, hp⟩ := hB x
        refine le_trans ?_ (le_sSup (Set.mem_image_of_mem
          (fun p => g_conj (s + p) - h_conj p) (hmemB x p hp)))
        have h1 := hD (s + p) x
        rw [hr] at h1
        show ((inner ℝ s x : ℝ) : EReal) - (g x - (h x : EReal)) ≤ g_conj (s + p) - h_conj p
        rw [hr, hp]
        calc ((inner ℝ s x : ℝ) : EReal) - ((r : EReal) - (h x : EReal))
            = ((inner ℝ (s + p) x : ℝ) : EReal) - (r : EReal)
                - ((inner ℝ p x - h x : ℝ) : EReal) := by
              rw [inner_add_left]; norm_cast; ring_nf
          _ ≤ g_conj (s + p) - ((inner ℝ p x - h x : ℝ) : EReal) :=
              EReal.sub_le_sub h1 le_rfl
    · apply sSup_le
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨q, hq⟩ := hC p hp
      show g_conj (s + p) - h_conj p ≤ conjugate f s
      rw [hq]
      apply EReal.sub_le_of_le_add
      apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      by_cases hgx : g x = ⊤
      · simp [hgx]
      · obtain ⟨r, hr⟩ := hE x hgx
        show ((inner ℝ (s + p) x : ℝ) : EReal) - g x ≤ conjugate f s + q
        rw [hr]
        have h1 : ((inner ℝ s x - r + h x : ℝ) : EReal) ≤ conjugate f s := by
          refine le_trans ?_ (le_sSup (Set.mem_image_of_mem
            (fun x => ((inner ℝ s x : ℝ) : EReal) - f x) (Set.mem_univ x)))
          show ((inner ℝ s x - r + h x : ℝ) : EReal) ≤
            ((inner ℝ s x : ℝ) : EReal) - (g x - (h x : EReal))
          rw [hr]
          norm_cast
          linarith
        have h2 : ((inner ℝ p x - h x : ℝ) : EReal) ≤ q := hq ▸ hA p x
        calc ((inner ℝ (s + p) x : ℝ) : EReal) - r
            = ((inner ℝ s x - r + h x : ℝ) : EReal) + ((inner ℝ p x - h x : ℝ) : EReal) := by
              rw [inner_add_left]; norm_cast; ring_nf
          _ ≤ conjugate f s + q := add_le_add h1 h2
  refine ⟨claim1, ?_, ?_⟩
  · rw [hneg Set.univ f,
      hneg (effDom h_conj) (fun p => h_conj p - g_conj p)]
    congr 1
    have h0 : conjugate f 0 = sSup ((fun v => -f v) '' Set.univ) := by
      unfold conjugate
      congr 1
      apply Set.image_congr
      intro x _
      simp
    rw [← h0, claim1 0]
    congr 1
    apply Set.image_congr
    intro p hp
    obtain ⟨q, hq⟩ := hC p hp
    simp only [zero_add]
    rw [hq, EReal.neg_sub (Or.inl (EReal.coe_ne_bot q)) (Or.inl (EReal.coe_ne_top q)),
      sub_eq_add_neg, add_comm]
  · have hα : α = sSup ((fun s => supportFunction S s - h_conj s) '' effDom h_conj) := by
      apply le_antisymm
      · apply sSup_le
        rintro _ ⟨v, hv, rfl⟩
        obtain ⟨p, hp⟩ := hB v
        refine le_trans ?_ (le_sSup (Set.mem_image_of_mem
          (fun s => supportFunction S s - h_conj s) (hmemB v p hp)))
        show (h v : EReal) ≤ supportFunction S p - h_conj p
        rw [hp]
        have h1 : ((inner ℝ v p : ℝ) : EReal) ≤ supportFunction S p := le_sSup ⟨v, hv, rfl⟩
        calc (h v : EReal) = ((inner ℝ v p : ℝ) : EReal) - ((inner ℝ p v - h v : ℝ) : EReal) := by
              rw [real_inner_comm]; norm_cast; ring_nf
          _ ≤ supportFunction S p - ((inner ℝ p v - h v : ℝ) : EReal) :=
              EReal.sub_le_sub h1 le_rfl
      · apply sSup_le
        rintro _ ⟨p, hp, rfl⟩
        obtain ⟨q, hq⟩ := hC p hp
        show supportFunction S p - h_conj p ≤ α
        rw [hq]
        apply EReal.sub_le_of_le_add
        apply sSup_le
        rintro _ ⟨v, hv, rfl⟩
        have h1 : (h v : EReal) ≤ α := le_sSup ⟨v, hv, rfl⟩
        have h2 : ((inner ℝ p v - h v : ℝ) : EReal) ≤ q := hq ▸ hA p v
        calc ((inner ℝ v p : ℝ) : EReal) = (h v : EReal) + ((inner ℝ p v - h v : ℝ) : EReal) := by
              rw [real_inner_comm]; norm_cast; ring_nf
          _ ≤ α + q := add_le_add h1 h2
    rw [hα, hneg (effDom h_conj)
      (fun s => h_conj s - supportFunction S s)]
    congr 2
    apply Set.image_congr
    intro p hp
    obtain ⟨q, hq⟩ := hC p hp
    rw [hq, EReal.neg_sub (Or.inl (EReal.coe_ne_bot q)) (Or.inl (EReal.coe_ne_top q)),
      sub_eq_add_neg, add_comm]

end FCA_chap_E_ex2
