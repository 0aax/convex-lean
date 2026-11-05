import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Source (Chapter B, §3.2 "Behaviour at Infinity", p. 107–108).

**Standing assumption of §3.2** (stated at the start of the section and in the proposition):
`f ∈ Conv̄ ℝⁿ`, i.e. (Def. B.1.1.3 and Notation B.1.2.7) `f : ℝⁿ → ℝ ∪ {+∞}` is
* not identically `+∞` (never `-∞` by its codomain) — properness,
* convex,
* closed, i.e. lower semicontinuous on `ℝⁿ` (equivalently `epi f` is closed, Prop. B.1.2.2).

Notation: `S_r(f) := {x ∈ ℝⁿ : f(x) ≤ r}` for `r ∈ ℝ` (§B.1.1); `f'_∞` is the asymptotic
function of `f`, defined by `epi f'_∞ = (epi f)_∞` (Prop. B.3.2.1, Def. B.3.2.2).

**Proposition 3.2.4 (second part).** Let `f ∈ Conv̄ ℝⁿ`. The following statements are
equivalent:
* (i) there is `r` for which `S_r(f)` is nonempty and compact;
* (ii) all the sublevel sets of `f` are compact;
* (iii) `f'_∞(d) > 0` for all nonzero `d ∈ ℝⁿ`.

The ambient space `ℝⁿ` is taken as an abstract finite-dimensional real inner-product space.
-/

open Set

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- `f ∈ Conv̄ ℝⁿ`: proper (not identically `+∞`), convex, closed
    (hf_proper : IsProperEReal f)
    (hf_convex : ConvexEReal f)
    (hf_lsc : LowerSemicontinuous f) :
    [ -- (i) some sublevel set is nonempty and compact
      ∃ r : ℝ, (sublevelSet f r).Nonempty ∧ IsCompact (sublevelSet f r),
      -- (ii) all sublevel sets are compact
      ∀ r : ℝ, IsCompact (sublevelSet f r),
      -- (iii) the asymptotic function is positive away from the origin
      ∀ d : E, d ≠ 0 → (0 : EReal) < asymptoticFun f d ].TFAE := by
  sorry
