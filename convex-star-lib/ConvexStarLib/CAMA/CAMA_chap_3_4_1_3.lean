import ConvexStarLib.Defs

/-!
# `CAMA_chap_3_4_1_3`

Source: Hiriart-Urruty & Lemarechal, Convex Analysis and Minimization Algorithms.

Statement from the `convex-eval-v28-2h/CAMA_chap_3_4_1_3` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace CAMA_chap_3_4_1_3`, so the main result is `CAMA_chap_3_4_1_3.CAMA_chap_3_4_1_3`.
-/

namespace CAMA_chap_3_4_1_3

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem CAMA_chap_3_4_1_3
  (C₁ C₂ : Set E)
  (hC₁ : Set.Nonempty C₁ ∧ Convex ℝ C₁ ∧ IsClosed C₁)
  (hC₂ : Set.Nonempty C₂ ∧ Convex ℝ C₂ ∧ IsClosed C₂)
  (h_disjoint : C₁ ∩ C₂ = ∅) :
  (Bornology.IsBounded C₂) → (∃ (s : E),
    BddAbove ((fun y => inner ℝ s y) '' C₁) ∧
    BddBelow ((fun y => inner ℝ s y) '' C₂) ∧
    (∃ y₂ ∈ C₂, IsMinOn (fun y => inner ℝ s y) C₂ y₂) ∧
    sSup ((fun y => inner ℝ s y) '' C₁) < sInf ((fun y => inner ℝ s y) '' C₂)) := by
  intro hb
  obtain ⟨hne₁, hconv₁, hcl₁⟩ := hC₁
  obtain ⟨hne₂, hconv₂, hcl₂⟩ := hC₂
  haveI : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hcpt₂ : IsCompact C₂ := Metric.isCompact_of_isClosed_isBounded hcl₂ hb
  have hdisj : Disjoint C₁ C₂ := Set.disjoint_iff_inter_eq_empty.mpr h_disjoint
  obtain ⟨f, u, v, hfu, huv, hfv⟩ :=
    geometric_hahn_banach_closed_compact hconv₁ hcl₁ hconv₂ hcpt₂ hdisj
  set s : E := (InnerProductSpace.toDual ℝ E).symm f with hs
  have hsf : ∀ y, inner ℝ s y = f y := fun y => InnerProductSpace.toDual_symm_apply
  have hup : ∀ z ∈ (fun y => inner ℝ s y) '' C₁, z ≤ u := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((hsf y).trans_lt (hfu y hy)).le
  have hlo : ∀ z ∈ (fun y => inner ℝ s y) '' C₂, v ≤ z := by
    rintro _ ⟨y, hy, rfl⟩
    exact ((hfv y hy).trans_eq (hsf y).symm).le
  refine ⟨s, ⟨u, hup⟩, ⟨v, hlo⟩, ?_, ?_⟩
  · have hcont : Continuous (fun y => inner ℝ s y) := continuous_const.inner continuous_id
    exact hcpt₂.exists_isMinOn hne₂ hcont.continuousOn
  · have h1 : sSup ((fun y => inner ℝ s y) '' C₁) ≤ u := csSup_le (hne₁.image _) hup
    have h2 : v ≤ sInf ((fun y => inner ℝ s y) '' C₂) := le_csInf (hne₂.image _) hlo
    linarith

end CAMA_chap_3_4_1_3
