import ConvexStarLib.Defs

/-!
# `FCA_chap_C_ex1`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_C_ex1` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_C_ex1`, so the main result is `FCA_chap_C_ex1.FCA_chap_C_ex1`.
-/

namespace FCA_chap_C_ex1

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
theorem FCA_chap_C_ex1
  (C₁ C₂ : Set E)
  (S : Set E)
  (_hC_nonempty : Set.Nonempty C₁ ∧ Set.Nonempty C₂)
  (hC_convex : Convex ℝ C₁ ∧ Convex ℝ C₂)
  (hC_closed : IsClosed C₁ ∧ IsClosed C₂)
  (hS_nonempty : Set.Nonempty S)
  (hS : Bornology.IsBounded S) :
  ((setAdd C₁ S) = (setAdd C₂ S)) → (C₁ = C₂) := by
  intro h
  have key : ∀ A B : Set E, Convex ℝ B → IsClosed B → setAdd A S ⊆ setAdd B S → A ⊆ B := by
    intro A B hBc hBcl hAB x hxA
    by_contra hxB
    obtain ⟨f, u, hfB, hux⟩ := geometric_hahn_banach_closed_point hBc hBcl hxB
    have hbdd : BddAbove (f '' S) := (f.lipschitz.isBounded_image hS).bddAbove
    have hne : (f '' S).Nonempty := hS_nonempty.image f
    obtain ⟨_, ⟨s, hsS, rfl⟩, hs⟩ :=
      exists_lt_of_lt_csSup hne (show sSup (f '' S) - (f x - u) < sSup (f '' S) by linarith)
    have hxs : x + s ∈ setAdd A S := ⟨x, hxA, s, hsS, rfl⟩
    obtain ⟨b, hbB, s', hs'S, heq⟩ := hAB hxs
    have h1 : f (x + s) = f (b + s') := by rw [heq]
    have h2 : f s' ≤ sSup (f '' S) := le_csSup hbdd ⟨s', hs'S, rfl⟩
    have h3 := hfB b hbB
    rw [map_add, map_add] at h1
    linarith
  exact Set.Subset.antisymm (key C₁ C₂ hC_convex.2 hC_closed.2 h.le)
    (key C₂ C₁ hC_convex.1 hC_closed.1 h.ge)

end FCA_chap_C_ex1
