import LeanWorkspace.Defs

/-!
# Hiriart-Urruty & Lemaréchal, *Fundamentals of Convex Analysis*, Proposition B.3.2.4 (second part)

Let `f ∈ \overline{Conv} ℝⁿ`, i.e. `f : ℝⁿ → ℝ ∪ {+∞}` is not identically `+∞`, convex in the
sense of Definition B.1.1.3, and closed (lower semicontinuous). Recall the sublevel sets
`S_r(f) = {x | f x ≤ r}` and the asymptotic function (Proposition B.3.2.1, Definition B.3.2.2)
`f'_∞(d) = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t`, where `x₀` is arbitrary in `dom f`.
Then the following statements are equivalent:
* (i)   there is `r` for which `S_r(f)` is nonempty and compact;
* (ii)  all the sublevel sets of `f` are compact;
* (iii) `f'_∞(d) > 0` for all nonzero `d`.

Formalization choices:
* `ℝⁿ` is replaced by an arbitrary finite-dimensional real normed space `E`.
* A function `ℝⁿ → ℝ ∪ {+∞}` is modelled as `f : E → EReal` that never takes the value `⊥`.
* The reference point `x₀ ∈ dom f` defining `f'_∞` is an arbitrary parameter of the theorem
  (so the equivalence holds whichever `x₀ ∈ dom f` is used). Its existence also gives that
  `f` is not identically `+∞`.
-/

/-- **Proposition B.3.2.4 (second part).** For a closed convex `f : E → ℝ ∪ {+∞}` and any
`x₀ ∈ dom f`, the following are equivalent: (i) some sublevel set `{x | f x ≤ r}` is nonempty and
compact; (ii) all sublevel sets are compact; (iii) the asymptotic function
`f'_∞(d) = sup_{t > 0} (f (x₀ + t • d) - f x₀) / t` is positive at every `d ≠ 0`. -/
theorem FCA_chap_B_3_2_4_ii
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (f : E → EReal)
    -- `f ∈ \overline{Conv} E`: `f` takes values in `ℝ ∪ {+∞}`, is convex and closed
    (hf_ne_bot : ∀ x, f x ≠ ⊥)
    (hf_convex : ∀ x x' : E, ∀ α : ℝ, 0 < α → α < 1 →
      f (α • x + (1 - α) • x') ≤ (α : EReal) * f x + ((1 - α : ℝ) : EReal) * f x')
    (hf_closed : LowerSemicontinuous f)
    -- an arbitrary point `x₀ ∈ dom f`, used to compute the asymptotic function `f'_∞`
    (x₀ : E) (hx₀ : f x₀ ≠ ⊤) :
    List.TFAE
      [ ∃ r : ℝ, {x | f x ≤ r}.Nonempty ∧ IsCompact {x | f x ≤ r},
        ∀ r : ℝ, IsCompact {x | f x ≤ r},
        ∀ d : E, d ≠ 0 →
          0 < ⨆ (t : ℝ) (_ : 0 < t), (f (x₀ + t • d) - f x₀) / (t : EReal) ] := by
  sorry
