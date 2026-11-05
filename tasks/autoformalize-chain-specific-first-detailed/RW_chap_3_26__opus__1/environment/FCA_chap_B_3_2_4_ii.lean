import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Chapter B, §3.2 "Behaviour at Infinity", p. 107–108.

Standing assumptions and definitions used:
* The space is `ℝⁿ` with its Euclidean structure; here an abstract finite-dimensional real
  inner-product space `E`.
* `§3.2` assumes `f ∈ Conv̄ ℝⁿ`, i.e. (Definitions B.1.1.3, B.1.2.3, Notation B.1.2.7)
  - `f : ℝⁿ → ℝ ∪ {+∞}` (the value `-∞` is excluded from the start),
  - `f` is not identically `+∞`,
  - `f` is convex,
  - `f` is closed, i.e. lower semicontinuous.
  The first two items together say that `f` is proper.
* Sublevel set at level `r ∈ ℝ`: `S_r(f) := {x ∈ ℝⁿ : f(x) ≤ r}`.
* Asymptotic function `f'_∞` (Proposition B.3.2.1, Definition B.3.2.2): the function whose
  epigraph is the asymptotic cone of `epi f`, `epi f'_∞ = (epi f)_∞`; here `asymptoticFun f`.

Statement (second part of Proposition B.3.2.4). For `f ∈ Conv̄ ℝⁿ` the following statements
are equivalent:
* (i)   there is `r` for which `S_r(f)` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'_∞(d) > 0` for all nonzero `d ∈ ℝⁿ`.
-/

theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- `f ∈ Conv̄ ℝⁿ`: values in `ℝ ∪ {+∞}` and not identically `+∞`, convex, closed
    (hf_proper : (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty)
    (hf_convex : ConvexEReal f)
    (hf_lsc : LowerSemicontinuous f) :
    List.TFAE
      [∃ r : ℝ, {x | f x ≤ (r : EReal)}.Nonempty ∧ IsCompact {x | f x ≤ (r : EReal)},
       ∀ r : ℝ, IsCompact {x | f x ≤ (r : EReal)},
       ∀ d : E, d ≠ 0 → 0 < asymptoticFun f d] := by
  sorry
