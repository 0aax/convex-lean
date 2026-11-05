import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Source statement (Chapter B, §3.2): let `f ∈ Conv̄ ℝⁿ`. [First part: all nonempty sublevel-sets
of `f` have the same asymptotic cone `{d : f'_∞(d) ≤ 0}`.] In particular, the following
statements are equivalent:
  (i)   there is `r` for which `S_r(f)` is nonempty and compact;
  (ii)  all the sublevel-sets of `f` are compact;
  (iii) `f'_∞(d) > 0` for all nonzero `d ∈ ℝⁿ`.

Hypotheses, including the standing ones:
* the space is `ℝⁿ` with its Euclidean structure; here an abstract finite-dimensional real
  inner-product space `E`;
* `f ∈ Conv̄ ℝⁿ` (Definition B.1.1.3 and Notation B.1.2.7): `f : ℝⁿ → ℝ ∪ {+∞}`, not
  identically `+∞` (`ProperEReal f`), convex (`ConvexEReal f`) and closed, i.e. lower
  semicontinuous (`LowerSemicontinuous f`).

Definitions used:
* sublevel-set at level `r ∈ ℝ` (§0.1.2): `S_r(f) := {x | f x ≤ r}`;
* asymptotic function (Proposition B.3.2.1, Definition B.3.2.2): the function whose epigraph
  is the asymptotic cone of `epi f`, i.e. `asymptoticFun f`.

Conclusion: (i), (ii) and (iii) are equivalent (`List.TFAE`).
-/

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- `f ∈ Conv̄ ℝⁿ`: values in `ℝ ∪ {+∞}`, not identically `+∞`, convex and closed
    (hf_proper : ProperEReal f)
    (hf_convex : ConvexEReal f)
    (hf_closed : LowerSemicontinuous f) :
    List.TFAE
      [ ∃ r : ℝ, {x | f x ≤ (r : EReal)}.Nonempty ∧ IsCompact {x | f x ≤ (r : EReal)},
        ∀ r : ℝ, IsCompact {x | f x ≤ (r : EReal)},
        ∀ d : E, d ≠ 0 → 0 < asymptoticFun f d ] := by
  sorry
