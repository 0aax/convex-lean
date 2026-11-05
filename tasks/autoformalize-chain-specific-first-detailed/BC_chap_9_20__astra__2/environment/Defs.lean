import Mathlib

/-!
Shared definitions for extended-real-valued convex analysis.

The effective domain, properness, and epigraph are defined for arbitrary
extended-real-valued functions, as in Rockafellar--Wets, Chapter 1, and
Bauschke--Combettes, Definition 1.4. Convexity is defined by the epigraph,
as in Bauschke--Combettes, Definition 8.1 and Rockafellar--Wets,
Proposition 2.4. Thus convexity itself does not impose properness.
-/

/-- The effective domain consists of the points where the value is below `+∞`. -/
def effDom {X : Type*} (f : X → EReal) : Set X :=
  {x | f x < ⊤}

/-- A proper function never takes the value `-∞` and has nonempty effective domain. -/
def IsProper {X : Type*} (f : X → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- The epigraph uses real heights, including when the function has infinite values. -/
def epigraph {X : Type*} (f : X → EReal) : Set (X × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- An extended-real-valued function is convex when its epigraph is convex. -/
def ConvexEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)
