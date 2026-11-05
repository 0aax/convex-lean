import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Let `f ∈ Conv̄ ℝⁿ`, i.e. `f : ℝⁿ → ℝ ∪ {+∞}` is convex, closed (lower semicontinuous) and not
identically `+∞`. Its asymptotic function (Proposition B.3.2.1, formula (3.2.2)) is
`f'_∞(d) = sup_{t > 0} (f (x₀ + t d) - f x₀) / t`, where `x₀` is arbitrary in `dom f`
(the value does not depend on that choice). Then the following are equivalent:
* (i)   there is `r` for which the sublevel set `S_r(f) = {x | f x ≤ r}` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'_∞(d) > 0` for all nonzero `d`.

Formalization choices:
* `ℝⁿ` is generalized to a finite-dimensional real normed space `E` (finite dimension is
  essential; the Euclidean structure is not used).
* `f` takes values in `EReal`; `hf_bot` excludes the value `-∞`, so `f` is `ℝ ∪ {+∞}`-valued as
  in the book. Convexity is stated as convexity of the epigraph `{(x, r) ∈ E × ℝ | f x ≤ r}`,
  equivalent to the book's definition for such functions (Proposition B.1.1.6); closedness is
  lower semicontinuity (Proposition B.1.2.2).
* A point `x₀` with `f x₀ ≠ ⊤` (i.e. `x₀ ∈ dom f`, which also makes `f` proper) is fixed, and the
  asymptotic function is written out via formula (3.2.2) at `x₀`. The result is stated for
  every such `x₀`.
* The levels `r` range over `ℝ`, as in the book.
-/

/-- **Proposition B.3.2.4, second part.** For a closed proper convex function
`f : E → ℝ ∪ {+∞}` on a finite-dimensional real normed space, with `x₀ ∈ dom f`, the following are
equivalent: (i) some sublevel set of `f` is nonempty and compact; (ii) all sublevel sets of `f`
are compact; (iii) the asymptotic function
`f'_∞(d) = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t` is positive at every nonzero `d`. -/
theorem FCA_chap_B_3_2_4_ii {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → EReal)
    (hf_bot : ∀ x, f x ≠ ⊥)
    (hf_conv : Convex ℝ {p : E × ℝ | f p.1 ≤ p.2})
    (hf_lsc : LowerSemicontinuous f)
    (x₀ : E) (hx₀ : f x₀ ≠ ⊤) :
    List.TFAE
      [∃ r : ℝ, {x | f x ≤ r}.Nonempty ∧ IsCompact {x | f x ≤ r},
       ∀ r : ℝ, IsCompact {x | f x ≤ r},
       ∀ d : E, d ≠ 0 → 0 < ⨆ t > (0 : ℝ), (f (x₀ + t • d) - f x₀) / (t : EReal)] := by
  sorry
