# Formalize Theorem 9.20 (Bauschke & Combettes, Convex Analysis and Monotone Operator Theory in Hilbert Spaces)

Write a Lean 4 statement of **Theorem 9.20** from Bauschke & Combettes, *Convex Analysis and Monotone Operator Theory in Hilbert Spaces*, Chapter 9, Theorem 9.20 (every f ∈ Γ₀(H) has a continuous affine minorant) — PDF page 175 of `/app/corpus/convex_analysis_and_monotone_operator_theory_in_hilbert_spaces.pdf`.

Put it in `/app/autoformalize/LeanWorkspace/BC_chap_9_20.lean`, the file should have a theorem named `BC_chap_9_20` whose proof is `sorry`. Do not prove it. The project keeps its definitions in `/app/autoformalize/LeanWorkspace/Defs.lean`.

Formalize this at a suitable level of generality. Your statement will become part of a project that formalizes results from every source in the corpus. Follow the formalization guide below.

The project already contains formalizations of other results in the corpus. You may edit them, but the package must still build.

**Time.** 30 minutes. Whatever is on disk at the end is your submission.

## Environment

- `/app/corpus/` holds the books and papers as PDFs (titles in `/app/corpus/INDEX.md`).
- The Lake package is `/app/autoformalize/` (Lean v4.28.0, Mathlib prebuilt). Check your file with `lake env lean LeanWorkspace/BC_chap_9_20.lean` or `lake build LeanWorkspace` from there.
- Web access is permitted.
- `/app/scratch/` is for notes and extracted text; it is not assessed.

## Format (checked by `submit` and the grader)

We will check that `lake build LeanWorkspace` succeeds and the file has a single theorem `BC_chap_9_20` whose proof is `sorry`.

## Formalization guide

The steps below are the ones to follow when formalizing a result from one of the sources into the corpus. Each step gives the decision to make, the Lean pattern to write, and what to check.

### Step 1 — Read the source completely before writing anything

Find the result and read, in order: the result itself; the definitions it uses, where the source defines them (not from memory); and the chapter's standing assumptions, which the statement of the result usually leaves out. Standing assumptions are easy to miss and they change the statement. A chapter may fix a norm, a space or a class of functions once at its start. Hiriart-Urruty & Lemaréchal first define finite-valued convex functions on a convex set and then work mostly with functions into ℝ ∪ {+∞}, so check which one a result uses. Rockafellar–Wets' "proper" means never −∞ and not identically +∞. Bauschke–Combettes' `Γ₀(H)` bundles proper, lower semicontinuous and convex. Duchi's exercises may fix a probability measure for a whole sheet.

In a comment at the top of the file, write down the hypotheses the source states, including the standing ones, and the exact conclusion, with the source's indexing and constants. Everything you write afterwards is checked against this list.

### Step 2 — Choose the ambient setting

Choose the type of the space first; everything else depends on it.

- If the statement mentions coordinates, the standard basis, a matrix, or the dimension `n` as a quantity (a rate with `n` in it, a count of vectors), use `EuclideanSpace ℝ (Fin n)`.
- Otherwise, for Hiriart-Urruty & Lemaréchal (both books), Rockafellar–Wets and Renegar, which work in ℝⁿ, use an abstract finite-dimensional real inner-product space, `{E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]`, with a second space `F` of the same kind when the result involves a map between two spaces. Every such space is isometric to some ℝⁿ, so nothing is lost and the statement is not tied to coordinates.
- For Bauschke–Combettes, use a real Hilbert space: `[CompleteSpace E]` instead of `[FiniteDimensional ℝ E]`. Do not add finite dimension; the book's results are infinite-dimensional.
- For Bubeck and the SAG/SAGA sources, use an inner-product space as above in the Euclidean chapters, and `EuclideanSpace ℝ (Fin n)` where the dimension enters the rate or the algorithm acts on coordinates. Where a chapter works with a norm that need not come from an inner product, make that norm the space's own norm (`[NormedAddCommGroup E] [NormedSpace ℝ E]`, no inner product) and build everything else from the structure the source actually uses.
- For Duchi's exercises, use `EuclideanSpace ℝ (Fin n)` with Lebesgue measure, or the probability measure the exercise names.

Check that the setting supplies exactly the structure the source uses. Structure the source never uses (an inner product, coordinates, completeness, finite dimension) should not appear in the statement, and structure it does use must.

Instances: Mathlib's `gradient`, and everything built on it (Hessians, local norms), goes through the Riesz isomorphism and needs `[CompleteSpace E]`. A definition over an inner-product space that mentions `gradient` must take `[CompleteSpace E]` as an instance argument; a theorem that assumes `[FiniteDimensional ℝ E]` gets completeness automatically. Measurability of random iterates needs `[MeasurableSpace E] [BorelSpace E]`.

### Step 3 — Choose the value type of each function

If a function may take the value +∞ in the source's setting (indicator functions, conjugates, support functions, anything "proper" or "closed"), it is `f : E → EReal`, and:

- `effDom f := {x | f x < ⊤}`, and proper is `(∀ x, ⊥ < f x) ∧ (effDom f).Nonempty`.
- Convexity is convexity of the epigraph: `epigraph f := {p : E × ℝ | f p.1 ≤ p.2}` and `ConvexEReal f := Convex ℝ (epigraph f)`. This is correct for every extended-real function. The inequality `f (t • x + (1 - t) • y) ≤ t * f x + (1 - t) * f y` in `EReal` agrees with it only when `f` never takes `⊥`, so do not use the inequality as the definition. A hypothesis `∀ x, ⊥ < f x`, or properness, belongs in a statement only when the source assumes it, not as a way to make convexity behave.
- Lower semicontinuity is Mathlib's `LowerSemicontinuous`.
- A supremum or infimum is `sSup` or `sInf` of an image set, e.g. the conjugate `fun v => sSup ((fun x => ((inner ℝ v x : ℝ) : EReal) - f x) '' Set.univ)` and the support function `fun w => sSup ((fun v => ((inner ℝ v w : ℝ) : EReal)) '' A)`.
- The asymptotic (recession, horizon) function is defined through the epigraph: `asymptoticFun f := funFromSet (horizonCone (epigraph f))`, that is `epi f'_∞ = (epi f)^∞`, with the sequential horizon cone `horizonCone C := {x | ∃ xᵛ ∈ C, λᵛ ↘ 0, λᵛ • xᵛ → x}`. It has no base point. Difference-quotient formulas such as `sup_{t>0} (f (x₀ + t • d) − f x₀) / t` are theorems about it, not its definition.
- The proximal mapping is set-valued: `proximalMapping f lam x := {w | ∀ (z : E), f w + (2 * lam)⁻¹ * ‖w - x‖ ^ 2 ≤ f z + (2 * lam)⁻¹ * ‖z - x‖ ^ 2}`, and `moreauEnvelope f lam x` is the corresponding infimum. An algorithm's proximal step is this mapping applied to the gradient step.
- A real-valued function is passed to an `EReal` definition through `liftRealtoEReal f := fun x => (f x : EReal)`.

If the function is real-valued in the source (algorithms, smooth objectives), keep it `E → ℝ` and use Mathlib's `ConvexOn ℝ s f`, `StrictConvexOn ℝ s f`, `StrongConvexOn s m f`, `LipschitzWith (Real.toNNReal L) f` and `LipschitzOnWith`. `StrongConvexOn` uses the modulus convention `m/2 · a·b·‖x − y‖²`, so a source's "strongly convex with modulus c" in the `c/2` convention is `StrongConvexOn s c f`.

Never use `WithTop ℝ`, and never encode +∞ by a side condition on a real-valued function.

### Step 4 — For each concept, reuse, generalize, or define afresh

Aim for one definition per concept, shared by every source that uses it, and as few new definitions as possible. This is a judgement about what the concept is, not a check that two formulas match. For each concept in the statement, go through the following in order.

0. The project. Before anything else, read what the project already has: its shared definitions file and the existing results. A definition already there is the first candidate, and the comparison in item 2 applies to it as to any source's. Then see "Working in the existing project" below for what to do when the project's definition, or an existing result, does not fit.
1. Mathlib. If Mathlib has the concept, use it, even when its defining formula differs from the source's. The exceptions are a Mathlib definition that is a different concept under a similar name or shape, and one that does not cover the source's objects.
2. The other sources in the corpus. Find every source that defines the concept and compare what each definition covers, not how it is written.
   - If one source's definition is a special case of another's, use the general one; the special case is an instance of it.
   - If one definition covers a larger class and the sources prove that their formulas agree with it, use the larger one, even when a book presents the narrower formula first for teaching. Each book's formula is then a theorem of that book.
   - Keep two definitions separate only when neither is more general: they cover the same objects, and their agreement is a substantive theorem. Merging them would hide that theorem inside a definition.
3. State the result with the definitions chosen above, not with the source's own formula when that formula is a special case. The source's formula appears in the statement only when the result is about it, for instance when the result is the book's equivalence theorem. Likewise, when the source defines a method as an instance of a more general method in the corpus, state it as that instance.
4. Only then define something new. Make a new definition as general as the sources that use the concept require, and no more: do not generalize the ambient space, the value type or the quantification beyond what some source in the corpus uses.

Patterns for common kinds of concept:

- A multifunction is `T : E → Set E`. Its properties are stated on its graph, quantifying over `v₀ ∈ T x₀` and `v₁ ∈ T x₁`; its domain is `{x | (T x).Nonempty}`; restricting it to a set means making its values `∅` outside the set, not adding a set argument.
- A property of a function relative to a set `𝓧` (the source's function lives on `𝓧`) quantifies over `𝓧` only, `∀ y ∈ 𝓧, …`, not over the whole space.
- A set defined by an inequality (cone, polar cone, normal cone, face, sublevel set) is written as that set, e.g. `{s | ∀ y ∈ C, ⟪s, y - x⟫ ≤ 0}`.
- A projection is the set `{w ∈ C | ∀ z ∈ C, ‖w - x‖ ≤ ‖z - x‖}`, or the chosen point `pC x C hC₁ hC₂ hC₃` when closedness, convexity and nonemptiness are available as hypotheses.
- An algorithm is a predicate `Is<Method>Sequence` on its iterates `x : ℕ → E` (or `ℕ → Ω → E` when random) that lists the initialization and the step. Write an explicit step as an equation, `x (t + 1) = x t - η • gradient f (x t)`. Write an argmin step (a projection or a Bregman step) as `IsMinOn (fun z => …) 𝓧 (x (t + 1))`; this restricts nothing when the source proves the minimizer exists. A proximal step uses `proximalMapping` (Step 3). Step sizes and constants are parameters, and the values the source prescribes are passed where the theorem uses the predicate.

### Working in the existing project

The project is one formalization, not a set of files that happen to compile together. Definitions live in the project's shared definitions file; each result holds only its theorem. When your result shares a concept with results already in the project, the project should end with one definition of that concept, used by all of them.

- If the project's definition is a special case of the one your source needs, generalize the existing definition rather than adding a second one beside it, and restate the existing results that use it through the instance. A second definition of the same concept under a different name is the outcome to avoid.
- If the project's definition covers fewer objects than the larger-class definition of Step 4, item 2, switch to the larger one and restate the existing results; the narrower formula becomes a theorem, not a definition.
- If an existing result writes a concept out inline, as a formula in its hypotheses or conclusion, and your result needs the same concept, give it a definition in the shared definitions file and rewrite the existing result to use it.
- Keep each existing result faithful to its own source while you change it: the same hypotheses and conclusion, checked as in Step 5, only expressed through the shared definitions.
- Keep definitions separate only for the reasons in Step 4, item 2, never because changing an existing file is more work.

### Step 5 — Write the theorem

Order the binders: the spaces and their instances; the data (sets, functions, iterates, oracle outputs); the constants; the hypotheses, in groups with a one-line comment each (constraint set, function, algorithm, oracle); then the conclusion. Name each hypothesis after its object and property: `(hf_convex : ConvexOn ℝ 𝓧 f)`, `(h𝓧_compact : IsCompact 𝓧)`, `(hx_star : IsMinOn f 𝓧 x_star)`. Props are `UpperCamelCase`, usually `Is…`; data are `lowerCamelCase`.

Fidelity rules, each checked against the list from Step 1:

- Keep every hypothesis the source states, in the source's form, even when it is implied by another hypothesis or by a definition already assumed. Do not drop any, and do not add hypotheses the source does not have: no extra continuity, differentiability, finiteness or compactness.
- Keep the form of the conclusion. A quantity the source defines by an equation stays an equation, not a bound; a named minimizer `x*` stays a parameter with `IsMinOn f 𝓧 x_star` and `x_star ∈ 𝓧`; a supremum is `sSup` of the image set; an expectation is `∫ ω, … ∂μ`.
- Sequences are indexed from `0`. The source's `x₁` is `x 0`, the sum over `x₁ … x_t` is `∑ s ∈ Finset.range t, x s`, and schedules shift with the index: a step `2/(s+1)` for `s ≥ 1` becomes `fun s => 2 / (s + 2)` for `s ≥ 0`, and a bound `c/(t+1)` for `t ≥ 1` becomes `c/(t+2)` for `t ≥ 0`. Check every constant after the shift.
- Make casts explicit, `(t : ℝ)`, `(m : ℝ)`, and avoid natural-number subtraction in real expressions.

### Step 6 — Add the bookkeeping Lean needs, and audit for junk values

Lean makes partial operations total, so a statement can be true, or a hypothesis vacuous, for reasons the source never considered. Add the hypotheses that rule this out; they are part of what the source means, not additions to it. Go through the statement operation by operation:

- `sSup S` and `sInf S` are `0` when `S` is empty or unbounded. Either the hypotheses make `S` nonempty and bounded, or you are transcribing the source's own definition and a degenerate case only makes the hypotheses inconsistent; know which.
- The Bochner integral `∫ ω, g ω ∂μ` is `0` when `g` is not integrable, so a hypothesis `∫ … ≤ B` is vacuous without `Integrable`. Pair every expectation bound with its integrability hypothesis, or state the bound with the lower integral `∫⁻`. Every integrand in a conclusion needs an (ae-)measurability hypothesis unless it follows from the others; a function is not measurable just because it is convex on a set.
- `a / b` is `0` when `b = 0`. A step size or rate that divides by a constant needs that constant positive, and one that divides by `t − 1` needs `2 ≤ t`.
- `gradient f x` and `fderiv ℝ f x` are `0` where `f` is not differentiable, so every use needs a differentiability hypothesis at that point.
- `Real.sqrt` and `Real.log` are `0` outside their domains; check that their arguments are nonnegative or positive under the hypotheses.
- Random objects: iterates satisfy `∀ t, Measurable (x t)`; conditional expectations are taken only of integrable functions (`condExp` of a non-integrable function is `0`); independence and sampling laws are stated explicitly.

### Step 7 — Encode stochastic statements in the standard way

Work on a probability space `{Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]`. Iterates are `x : ℕ → Ω → E`, with `∀ t, Measurable (x t)` inside the sequence predicate. Random indices are `I : ℕ → Ω → Fin m` with `ProbabilityTheory.iIndepFun I μ`, the uniform law `∀ t i, μ (I t ⁻¹' {i}) = (m : ENNReal)⁻¹`, and independence of each sample from the current state, `ProbabilityTheory.IndepFun (I t) (fun ω => (x t ω, …)) μ`.

A conditional expectation given a random variable `y` is `μ[g | MeasurableSpace.comap y inferInstance]`. Condition on exactly what the source conditions on, neither a smaller nor a larger σ-algebra. A condition on a conditional expectation holds `∀ᵐ ω ∂μ`, since conditional expectations are defined only up to null sets, while the algorithm's own steps hold for every `ω`, as in the source. Expectations are Bochner integrals with their integrability hypotheses (Step 6).

### Step 8 — Compile and check

Your file must compile with no errors and exactly one `sorry` warning, at the theorem, and the whole package must build, so every file you changed still compiles. Then check that the theorem has the required name; every definition and auxiliary lemma is complete; there is no `axiom` or `opaque`; the placeholder statement is gone; the pinned package files are untouched; and the hypotheses and conclusion match the list from Step 1 item by item.

### Mistakes to avoid

- Transcribing the source's notation instead of its concepts: use the structure the source's definitions actually rely on, not the one its formulas happen to be written in.
- Writing a new definition for a concept Mathlib or the corpus already has, because its formula differs from the source's.
- Adding a general definition next to the project's narrower one instead of generalizing it, or leaving an existing result's inline formula in place when your result defines the same concept.
- Using a book's first-presented formula as the definition when the corpus has a definition of the same concept that covers more.
- Dropping a hypothesis because it is derivable, or adding one because it makes the proof easier.
- Forgetting the index shift, or shifting the iterate but not the step-size schedule or the constant.
- Expectation bounds without integrability; conclusions that integrate a function that need not be measurable; `sSup` over a set that can be empty.
- Restricting a result to a smaller setting than the source's (finite dimension where the source has a Hilbert space, coordinates where it has none).
