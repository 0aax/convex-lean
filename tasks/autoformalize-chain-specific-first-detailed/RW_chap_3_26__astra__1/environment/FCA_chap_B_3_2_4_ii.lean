/-
Hiriart-Urruty & Lemaréchal, Fundamentals of Convex Analysis, Chapter B,
Section 3.2, Proposition 3.2.4, second part, printed pp. 107--108
(PDF pp. 117--118).

Source hypotheses, including standing assumptions:
* The ambient space is finite-dimensional real Euclidean space.
* f belongs to the class of closed convex functions denoted by overlined Conv ℝⁿ
  (B.1.2.7): f : ℝⁿ → ℝ ∪ {+∞} is convex, lower semicontinuous everywhere,
  and not identically +∞. The value -∞ is excluded (B.1.1.3).
* S_r(f) = {x | f(x) ≤ r}, for real r (B.1.1, beside equation (1.1.4)).
* f'_∞ is the asymptotic function of B.3.2.1--B.3.2.2, characterized by
  epi f'_∞ = (epi f)_∞. It is represented here by the shared `asymptoticFun`.

Exact conclusion: the following statements are equivalent:
(i) There exists r ∈ ℝ such that S_r(f) is nonempty and compact.
(ii) All the sublevel sets S_r(f), r ∈ ℝ, are compact.
(iii) f'_∞(d) > 0 for every nonzero d ∈ ℝⁿ.
-/

import LeanWorkspace.Defs

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- Function: proper, convex, and lower semicontinuous, as in overlined Conv ℝⁿ.
    (hf_proper : IsProperEReal f)
    (hf_convex : ConvexEReal f)
    (hf_lsc : LowerSemicontinuous f) :
    List.TFAE [
      (∃ r : ℝ, ({x : E | f x ≤ (r : EReal)}).Nonempty ∧
        IsCompact {x : E | f x ≤ (r : EReal)}),
      (∀ r : ℝ, IsCompact {x : E | f x ≤ (r : EReal)}),
      (∀ d : E, d ≠ 0 → (0 : EReal) < asymptoticFun f d)
    ] := by
  sorry
