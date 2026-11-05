import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*,
# Chapter B, §3.2, Proposition 3.2.4 (second part), pp. 107–108 (PDF pp. 117–118)

## Source statement

Standing assumptions of Chapter B / §3.2 (and of the proposition itself):
* the ambient space is `ℝⁿ`, a Euclidean space (finite-dimensional, with a scalar product);
* `f ∈ Conv̄ ℝⁿ` (Notation B.1.2.7), i.e.
  - `f : ℝⁿ → ℝ ∪ {+∞}` is not identically `+∞` (Definition B.1.1.3; equivalently
    `dom f := {x | f x < +∞}` is nonempty, Definition B.1.1.4) — the value `-∞` is excluded
    "from the very beginning in the present book";
  - `f` is convex (Definition B.1.1.3; equivalently `epi f` is convex, Proposition B.1.1.6);
  - `f` is closed, i.e. lower semi-continuous everywhere, equivalently `epi f` closed,
    equivalently all sublevel sets closed (Definition B.1.2.3).

Definitions used:
* sublevel set `S_r(f) := {x ∈ ℝⁿ : f(x) ≤ r}` for `r ∈ ℝ` (B.(1.1.4));
* epigraph `epi f := {(x, r) ∈ ℝⁿ × ℝ : r ≥ f(x)}` (Definition B.1.1.5);
* asymptotic cone `C_∞` of a nonempty closed convex set (Definition A.2.2.2);
* asymptotic function `f'_∞` of `f ∈ Conv̄ ℝⁿ`: the function with `epi f'_∞ = (epi f)_∞`
  (Proposition B.3.2.1, Definition B.3.2.2), which the book also writes as
  `f'_∞(d) = sup_{t>0} (f(x₀ + td) - f(x₀)) / t = lim_{t→+∞} (f(x₀ + td) - f(x₀)) / t`
  for any `x₀ ∈ dom f` (B.(3.2.2)).

Conclusion (second part of Proposition B.3.2.4): the following statements are equivalent:
* (i)   there is `r` for which `S_r(f)` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'_∞(d) > 0` for all nonzero `d ∈ ℝⁿ`.

## Formalization notes

* The space is an abstract finite-dimensional real inner-product space `E`, isometric to
  some `ℝⁿ`.
* `f : E → EReal`; the class `Conv̄ ℝⁿ` is the three hypotheses `IsProperEReal f`
  (no value `-∞`, not identically `+∞`), `ConvexEReal f` (convex epigraph) and
  `LowerSemicontinuous f` (closed).
* `asymptoticFun f` is defined through the epigraph, `epi f'_∞ = (epi f)_∞`, with the
  sequential horizon cone (see `Defs.lean`); for a closed convex nonempty epigraph this is
  exactly the book's asymptotic cone, and no base point `x₀` enters.
* Sublevel sets are `sublevelSet f r = {x | f x ≤ r}` for real levels `r`, as in the book
  (so (ii) ranges over all `r ∈ ℝ`, including levels with empty sublevel set).
-/

open Filter Topology

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- `f ∈ Conv̄ ℝⁿ`: `f : ℝⁿ → ℝ ∪ {+∞}` not identically `+∞`, convex, and closed
    (hf_proper : IsProperEReal f)
    (hf_convex : ConvexEReal f)
    (hf_closed : LowerSemicontinuous f) :
    [ -- (i) there is `r` for which `S_r(f)` is nonempty and compact
      (∃ r : ℝ, (sublevelSet f r).Nonempty ∧ IsCompact (sublevelSet f r)),
      -- (ii) all the sublevel sets of `f` are compact
      (∀ r : ℝ, IsCompact (sublevelSet f r)),
      -- (iii) `f'_∞(d) > 0` for all nonzero `d`
      (∀ d : E, d ≠ 0 → (0 : EReal) < asymptoticFun f d) ].TFAE := by
  sorry
