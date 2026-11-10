import ConvexStarLib.Defs

/-!
# `FCA_chap_B_2_1_2`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_2_1_2` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_2_1_2`, so the main result is `FCA_chap_B_2_1_2.FCA_chap_B_2_1_2`.
-/

namespace FCA_chap_B_2_1_2

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_2_1_2
  {ι : Type*}
  (J : Set ι)
  (hJ : J.Nonempty)
  (f : ι → E → EReal)
  (hx₀ : ∃ x₀, sSup {y | ∃ j ∈ J, f j x₀ = y} < ⊤)
  (f_ne_bot : ∀ j x, ⊥ < f j x) :
  let g := fun x => sSup {y | ∃ j ∈ J, f j x = y}
  ((∀ j ∈ J, ConvexEReal (f j)) → InConvRn g) ∧
    ((∀ j ∈ J, ConvexEReal (f j) ∧ LowerSemicontinuous (f j)) →
      InClosedConvRn g) := by
  intro g
  have hg : ∀ x, g x = ⨆ j ∈ J, f j x := by
    intro x
    show sSup ((fun j => f j x) '' J) = _
    rw [sSup_image]
  have part1 : (∀ j ∈ J, ConvexEReal (f j)) → InConvRn g := by
    intro hconv
    refine ⟨?_, hx₀, ?_⟩
    · intro x
      obtain ⟨j, hj⟩ := hJ
      calc ⊥ < f j x := f_ne_bot j x
        _ ≤ g x := le_sSup ⟨j, hj, rfl⟩
    · unfold ConvexEReal
      have hepi : epigraph g = ⋂ j ∈ J, epigraph (f j) := by
        ext p
        simp only [epigraph, Set.mem_setOf_eq, Set.mem_iInter]
        constructor
        · intro h j hj
          have hle : f j p.1 ≤ g p.1 := le_sSup ⟨j, hj, rfl⟩
          exact hle.trans h
        · intro h
          apply sSup_le
          rintro y ⟨j, hj, rfl⟩
          exact h j hj
      rw [hepi]
      exact convex_iInter₂ (fun j hj => hconv j hj)
  refine ⟨part1, ?_⟩
  intro h
  refine ⟨part1 (fun j hj => (h j hj).1), ?_⟩
  have hgeq : g = fun x => ⨆ j ∈ J, f j x := funext hg
  rw [hgeq]
  exact lowerSemicontinuous_biSup (fun j hj => (h j hj).2)

end FCA_chap_B_2_1_2
