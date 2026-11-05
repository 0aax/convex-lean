import LeanWorkspace.Defs

open ConvexAnalysis

/-- Hiriart-Urruty and Lemaréchal, *Fundamentals of Convex Analysis*,
Proposition B.3.2.4, second part (PDF pp. 117–118).

For a proper lower semicontinuous convex function on a finite-dimensional real
normed space, the following are equivalent: some sublevel set is nonempty and
compact; every sublevel set is compact; the asymptotic function is strictly
positive in every nonzero direction. -/
theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal)
    (hproper : IsProper f)
    (hconvex : Convex ℝ (epigraph f))
    (hlsc : LowerSemicontinuous f) :
    List.TFAE
      [∃ r : ℝ, (sublevelSet f r).Nonempty ∧ IsCompact (sublevelSet f r),
       ∀ r : ℝ, IsCompact (sublevelSet f r),
       ∀ d : E, d ≠ 0 → 0 < asymptoticFunction f d] := by
  sorry
