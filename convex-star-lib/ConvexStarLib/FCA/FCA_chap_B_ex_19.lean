import ConvexStarLib.Defs

/-!
# `FCA_chap_B_ex_19`

Source: Hiriart-Urruty & Lemarechal, Fundamentals of Convex Analysis.

Statement from the `convex-eval-v28-2h/FCA_chap_B_ex_19` task of the convex-lean
evaluation. The proof is the one Claude Code (Opus 5.5) submitted in its 2-hour run
and the grader accepted. Shared definitions live in `ConvexStarLib.Defs`; everything
below is inside `namespace FCA_chap_B_ex_19`, so the main result is `FCA_chap_B_ex_19.FCA_chap_B_ex_19`.
-/

namespace FCA_chap_B_ex_19

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem FCA_chap_B_ex_19
  (m : ℕ)
  (fi : ℕ → E → ℝ)
  (hfi_convex : ∀ i ∈ Finset.range m, ConvexOn ℝ Set.univ (fi i))
  (hm : m ≥ 1) :
  let f := fun x => sInf {v | ∃ i ∈ Finset.range m, (fi i x) = v}
  ∃ (g h : E → ℝ),
    (ConvexOn ℝ Set.univ g) ∧ (ConvexOn ℝ Set.univ h) ∧
    (∀ x, f x = g x - h x) := by
  intro f
  have hne : (Finset.range m).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  -- a sum of the `fi j` over any subset of `range m` is convex
  have hsum : ∀ s ⊆ Finset.range m, ConvexOn ℝ Set.univ (fun x => ∑ j ∈ s, fi j x) := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simpa using (convexOn_const (0 : ℝ) convex_univ)
    | insert a s ha ih =>
      have h1 : ConvexOn ℝ Set.univ (fi a) := hfi_convex a (hs (Finset.mem_insert_self a s))
      have h2 := ih (fun y hy => hs (Finset.mem_insert_of_mem hy))
      have : (fun x => ∑ j ∈ insert a s, fi j x) = fun x => fi a x + ∑ j ∈ s, fi j x := by
        funext x; rw [Finset.sum_insert ha]
      rw [this]
      exact h1.add h2
  -- `min_i fi i = ∑ j, fi j - max_i ∑_{j ≠ i} fi j`
  refine ⟨fun x => ∑ j ∈ Finset.range m, fi j x,
    fun x => (Finset.range m).sup' hne (fun i => ∑ j ∈ (Finset.range m).erase i, fi j x),
    hsum _ subset_rfl, ?_, ?_⟩
  · have : (fun x => (Finset.range m).sup' hne (fun i => ∑ j ∈ (Finset.range m).erase i, fi j x))
        = (Finset.range m).sup' hne (fun i => fun x => ∑ j ∈ (Finset.range m).erase i, fi j x) := by
      funext x; rw [Finset.sup'_apply]
    rw [this]
    exact Finset.sup'_induction hne _ (fun a ha b hb => ha.sup hb)
      (fun i _ => hsum _ (Finset.erase_subset _ _))
  · intro x
    show sInf {v | ∃ i ∈ Finset.range m, fi i x = v} = ∑ j ∈ Finset.range m, fi j x -
      (Finset.range m).sup' hne (fun i => ∑ j ∈ (Finset.range m).erase i, fi j x)
    apply IsLeast.csInf_eq
    constructor
    · obtain ⟨i, hi, hmax⟩ :=
        Finset.exists_mem_eq_sup' hne (fun i => ∑ j ∈ (Finset.range m).erase i, fi j x)
      refine ⟨i, hi, ?_⟩
      rw [hmax, ← Finset.add_sum_erase _ _ hi]
      ring
    · rintro v ⟨i, hi, rfl⟩
      have := Finset.le_sup' (fun i => ∑ j ∈ (Finset.range m).erase i, fi j x) hi
      rw [← Finset.add_sum_erase _ _ hi]
      linarith

end FCA_chap_B_ex_19
