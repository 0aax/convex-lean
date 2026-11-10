import ConvexStarLib.Defs

/-!
# `FCA_chap_E_2_1_1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_E_2_1_1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_E_2_1_1`, so the main result is `FCA_chap_E_2_1_1.FCA_chap_E_2_1_1`.
-/

namespace FCA_chap_E_2_1_1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem FCA_chap_E_2_1_1
  (g : F → EReal)
  (A : F →ₗ[ℝ] E)
  (hg_nondegenerate : IsNondegenerate g)
  (h_nonempty_domain : Set.Nonempty ((linearRange A.adjoint) ∩ effDom ((conjugate g)))) :
  let h := imageFun A g
  IsNondegenerate h ∧
  ∀ s, conjugate h s = conjugate g (A.adjoint s) := by
  intro h
  obtain ⟨⟨x₀, hx₀⟩, -⟩ := hg_nondegenerate
  obtain ⟨z, ⟨s₀, hs₀⟩, hz⟩ := h_nonempty_domain
  -- for reals `a, m` and `t : EReal`: `a - t ≤ m ↔ a - m ≤ t`
  have key_sub : ∀ (a m : ℝ) (t : EReal), (a : EReal) - t ≤ m ↔ ((a - m : ℝ) : EReal) ≤ t := by
    intro a m t
    induction t using EReal.rec with
    | bot => simp [-EReal.coe_sub]
    | coe r =>
      rw [← EReal.coe_sub, EReal.coe_le_coe_iff, EReal.coe_le_coe_iff]
      constructor <;> intro hh <;> linarith
    | top => simp
  -- the conjugate of `g` never takes the value `⊥`
  have hconj_ne_bot : ∀ v, conjugate g v ≠ ⊥ := by
    intro v hv
    have h1 : ((inner ℝ v x₀ : ℝ) : EReal) - g x₀ ≤ conjugate g v :=
      le_sSup ⟨x₀, Set.mem_univ _, rfl⟩
    rw [hv, le_bot_iff] at h1
    generalize g x₀ = t at h1 hx₀
    induction t using EReal.rec with
    | bot => simp at h1
    | coe r => rw [← EReal.coe_sub] at h1; exact EReal.coe_ne_bot _ h1
    | top => exact hx₀ rfl
  -- Fenchel–Young type bound
  have hbound : ∀ (v : F) (m : ℝ), conjugate g v ≤ m →
      ∀ y, ((inner ℝ v y - m : ℝ) : EReal) ≤ g y := by
    intro v m hm y
    rw [← key_sub]
    have h1 : ((inner ℝ v y : ℝ) : EReal) - g y ≤ conjugate g v :=
      le_sSup ⟨y, Set.mem_univ _, rfl⟩
    exact h1.trans hm
  refine ⟨⟨⟨A x₀, ?_⟩, ?_⟩, ?_⟩
  · have : h (A x₀) ≤ g x₀ := sInf_le ⟨x₀, rfl, rfl⟩
    exact ne_top_of_le_ne_top hx₀ this
  · have hz' : conjugate g z < ⊤ := hz
    obtain ⟨m, hm⟩ : ∃ m : ℝ, conjugate g z = m :=
      ⟨_, (EReal.coe_toReal hz'.ne (hconj_ne_bot z)).symm⟩
    refine ⟨s₀, m, fun x => ?_⟩
    apply le_sInf
    rintro _ ⟨y, hy, rfl⟩
    have h2 := hbound z m hm.le y
    rw [← hs₀, LinearMap.adjoint_inner_left, hy] at h2
    rw [← EReal.coe_sub]
    exact h2
  · intro s
    apply le_antisymm
    · apply sSup_le
      rintro _ ⟨x, -, rfl⟩
      rcases eq_or_ne (conjugate g (A.adjoint s)) ⊤ with hM | hM
      · rw [hM]; exact le_top
      obtain ⟨m, hm⟩ : ∃ m : ℝ, conjugate g (A.adjoint s) = m :=
        ⟨_, (EReal.coe_toReal hM (hconj_ne_bot _)).symm⟩
      rw [hm, key_sub]
      apply le_sInf
      rintro _ ⟨y, hy, rfl⟩
      have h2 := hbound (A.adjoint s) m hm.le y
      rwa [LinearMap.adjoint_inner_left, hy] at h2
    · apply sSup_le
      rintro _ ⟨y, -, rfl⟩
      have h1 : h (A y) ≤ g y := sInf_le ⟨y, rfl, rfl⟩
      calc ((inner ℝ (A.adjoint s) y : ℝ) : EReal) - g y
          = ((inner ℝ s (A y) : ℝ) : EReal) - g y := by rw [LinearMap.adjoint_inner_left]
        _ ≤ ((inner ℝ s (A y) : ℝ) : EReal) - h (A y) := EReal.sub_le_sub le_rfl h1
        _ ≤ conjugate h s := le_sSup ⟨A y, Set.mem_univ _, rfl⟩

end FCA_chap_E_2_1_1
