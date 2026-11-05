import LeanWorkspace.Defs

/-
Hiriart-Urruty & Lemaréchal, Fundamentals of Convex Analysis,
Chapter B, Section 3.2, Proposition 3.2.4, second part
(printed pp. 107--108, PDF pp. 117--118).

Source hypotheses, including the standing assumptions:
* The ambient space is ℝⁿ, represented here by a finite-dimensional real
  inner-product space.
* f ∈ closed Conv ℝⁿ: f : ℝⁿ → ℝ ∪ {+∞} is convex, not identically +∞,
  and lower semicontinuous (Definitions B.1.1.3 and B.1.2.3,
  Notation B.1.2.7, and the opening of Section B.3.2).
* S_r(f) = {x | f(x) ≤ r}, with r ∈ ℝ (equation B.1.1.4).
* f'_∞ is the asymptotic function of Definition B.3.2.2, characterized by
  epi f'_∞ = (epi f)_∞. The shared definition uses the sequential horizon cone;
  it has no chosen base point.

Exact conclusion: the following statements are equivalent:
(i) There is r ∈ ℝ for which S_r(f) is nonempty and compact.
(ii) All sublevel sets S_r(f), r ∈ ℝ, are compact (including the empty ones).
(iii) f'_∞(d) > 0 for every nonzero d ∈ ℝⁿ.
The three entries of List.TFAE below follow this source order.
-/

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- Function: proper, convex, and lower semicontinuous.
    (hf_proper : IsProper f)
    (hf_convex : ConvexEReal f)
    (hf_lowerSemicontinuous : LowerSemicontinuous f) :
    List.TFAE [
      ∃ r : ℝ, {x : E | f x ≤ (r : EReal)}.Nonempty ∧
        IsCompact {x : E | f x ≤ (r : EReal)},
      ∀ r : ℝ, IsCompact {x : E | f x ≤ (r : EReal)},
      ∀ d : E, d ≠ 0 → (0 : EReal) < asymptoticFun f d
    ] := by
  sorry
