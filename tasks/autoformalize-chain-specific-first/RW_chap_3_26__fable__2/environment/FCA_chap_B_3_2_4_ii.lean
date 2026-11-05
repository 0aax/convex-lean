import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Let `f ∈ \overline{Conv} ℝⁿ` be a closed (lower semicontinuous) proper convex function.
The following statements are equivalent:

* (i)   there is a level `r` for which the sublevel set `S_r(f)` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'∞(d) > 0` for every nonzero direction `d`,

where `f'∞` is the asymptotic (recession) function of `f`.

We state it for a finite-dimensional real normed space `E` in place of `ℝⁿ`
(finite dimension is essential for (iii) ⇒ (ii)).
-/

open ConvexAnalysis

theorem FCA_chap_B_3_2_4_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal)
    (hconv : IsConvexFun f) (hproper : IsProper f) (hclosed : LowerSemicontinuous f) :
    [∃ r : ℝ, (sublevelSet f r).Nonempty ∧ IsCompact (sublevelSet f r),
      ∀ r : ℝ, IsCompact (sublevelSet f r),
      ∀ d : E, d ≠ 0 → 0 < asymptoticFunction f d].TFAE := by
  sorry
