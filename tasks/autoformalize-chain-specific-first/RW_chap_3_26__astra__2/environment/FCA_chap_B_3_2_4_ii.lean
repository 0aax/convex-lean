import LeanWorkspace.Defs

open ConvexAnalysis

/-- Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*,
Proposition B.3.2.4, second part: for a proper closed convex function, existence of
a nonempty compact sublevel set, compactness of every sublevel set, and positivity
of the asymptotic function in every nonzero direction are equivalent. -/
theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    (hproper : IsProper f)
    (hconvex : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) :
    List.TFAE [
      ∃ r : ℝ, (sublevelSet f r).Nonempty ∧ IsCompact (sublevelSet f r),
      ∀ r : ℝ, IsCompact (sublevelSet f r),
      ∀ d : E, d ≠ 0 → 0 < asymptoticFunction f d
    ] := by
  sorry
