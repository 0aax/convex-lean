import ConvexStarLib.Defs

/-!
# `FCA_chap_C_1_3_1_ii`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_1_3_1_ii` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_1_3_1_ii`, so the main result is `FCA_chap_C_1_3_1_ii.FCA_chap_C_1_3_1_ii`.
-/

namespace FCA_chap_C_1_3_1_ii

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem FCA_chap_C_1_3_1_ii
  {ι : Type*}
  (σ : ι → (E → EReal))
  (J : Set ι)
  (hJ : J.Nonempty)
  (hσ_sublinear : ∀ j ∈ J, IsSublinear ((σ j))) :
  let σ' := fun x => sSup (⋃ j ∈ J, {(σ j) x})
  (∃ x, σ' x ≠ ⊤) →
  (IsSublinear σ') ∧
  ((∀ j ∈ J, LowerSemicontinuous (σ j)) → (LowerSemicontinuous σ')) := by
  intro σ' hfin
  have hσ'_eq : ∀ x, σ' x = ⨆ j ∈ J, σ j x := by
    intro x
    show sSup (⋃ j ∈ J, {(σ j) x}) = ⨆ j ∈ J, σ j x
    simp only [sSup_iUnion, sSup_singleton]
  have hσ'_fun : σ' = fun x => ⨆ j ∈ J, σ j x := funext hσ'_eq
  obtain ⟨j₀, hj₀⟩ := hJ
  refine ⟨⟨⟨?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · -- ⊥ < σ' x
    intro x
    rw [hσ'_eq]
    exact lt_of_lt_of_le ((hσ_sublinear j₀ hj₀).1.1 x) (le_iSup₂ (f := fun j _ => σ j x) j₀ hj₀)
  · -- ∃ x, σ' x < ⊤
    obtain ⟨x, hx⟩ := hfin
    exact ⟨x, lt_top_iff_ne_top.mpr hx⟩
  · -- convexity of the epigraph: it is the intersection of the epigraphs
    intro p hp q hq a b ha hb hab
    show σ' (a • p + b • q).1 ≤ (a • p + b • q).2
    rw [hσ'_eq]
    refine iSup₂_le fun j hj => ?_
    have hpj : p ∈ epigraph (σ j) := by
      show σ j p.1 ≤ p.2
      have : σ' p.1 ≤ p.2 := hp
      rw [hσ'_eq] at this
      exact le_trans (le_iSup₂ (f := fun j _ => σ j p.1) j hj) this
    have hqj : q ∈ epigraph (σ j) := by
      show σ j q.1 ≤ q.2
      have : σ' q.1 ≤ q.2 := hq
      rw [hσ'_eq] at this
      exact le_trans (le_iSup₂ (f := fun j _ => σ j q.1) j hj) this
    exact (hσ_sublinear j hj).1.2.2 hpj hqj ha hb hab
  · -- positive homogeneity
    intro x t ht
    simp only [hσ'_eq]
    have hhom : ∀ j ∈ J, σ j (t • x) = (t : EReal) * σ j x :=
      fun j hj => (hσ_sublinear j hj).2 x t ht
    have ht0 : (0 : EReal) ≤ (t : EReal) := by exact_mod_cast ht.le
    have htinv0 : (0 : EReal) ≤ ((t⁻¹ : ℝ) : EReal) := by exact_mod_cast (inv_pos.mpr ht).le
    apply le_antisymm
    · refine iSup₂_le fun j hj => ?_
      rw [hhom j hj]
      exact mul_le_mul_of_nonneg_left (le_iSup₂ (f := fun j _ => σ j x) j hj) ht0
    · have h1 : (⨆ j ∈ J, σ j x) ≤ ((t⁻¹ : ℝ) : EReal) * ⨆ j ∈ J, σ j (t • x) := by
        refine iSup₂_le fun j hj => ?_
        calc σ j x = ((t⁻¹ : ℝ) : EReal) * ((t : EReal) * σ j x) := by
              rw [← mul_assoc, ← EReal.coe_mul, inv_mul_cancel₀ ht.ne', EReal.coe_one, one_mul]
          _ = ((t⁻¹ : ℝ) : EReal) * σ j (t • x) := by rw [hhom j hj]
          _ ≤ ((t⁻¹ : ℝ) : EReal) * ⨆ j ∈ J, σ j (t • x) :=
            mul_le_mul_of_nonneg_left (le_iSup₂ (f := fun j _ => σ j (t • x)) j hj) htinv0
      calc (t : EReal) * ⨆ j ∈ J, σ j x
          ≤ (t : EReal) * (((t⁻¹ : ℝ) : EReal) * ⨆ j ∈ J, σ j (t • x)) :=
            mul_le_mul_of_nonneg_left h1 ht0
        _ = ⨆ j ∈ J, σ j (t • x) := by
            rw [← mul_assoc, ← EReal.coe_mul, mul_inv_cancel₀ ht.ne', EReal.coe_one, one_mul]
  · -- lower semicontinuity: a supremum of lsc functions is lsc
    intro hlsc
    rw [hσ'_fun]
    exact lowerSemicontinuous_biSup (f := fun j _ => σ j) (fun j hj => hlsc j hj)

end FCA_chap_C_1_3_1_ii
