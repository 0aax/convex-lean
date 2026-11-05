import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Let `f ∈ Conv ℝⁿ`, i.e. `f : ℝⁿ → ℝ ∪ {+∞}` is closed (lower semicontinuous), convex and
proper.  The following statements are equivalent:

* (i)   there is `r` for which the sublevel set `S_r(f) = {x | f x ≤ r}` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'∞ d > 0` for all nonzero `d ∈ ℝⁿ`,

where `f'∞` is the asymptotic function of `f` (`asymptoticFun f`).

The statement is formalized for an arbitrary finite-dimensional real normed space `E` in place
of `ℝⁿ`; finite dimensionality is essential (compactness of closed bounded sets).
-/

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    (hconv : Convex ℝ (epigraph f)) (hlsc : LowerSemicontinuous f)
    (hbot : ∀ x, f x ≠ ⊥) (hdom : ∃ x, f x ≠ ⊤) :
    [ ∃ r : ℝ, ({x | f x ≤ r} : Set E).Nonempty ∧ IsCompact ({x | f x ≤ r} : Set E),
      ∀ r : ℝ, IsCompact ({x | f x ≤ r} : Set E),
      ∀ d : E, d ≠ 0 → 0 < asymptoticFun f d ].TFAE := by
  sorry
