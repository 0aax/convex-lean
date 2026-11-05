import Mathlib

/-!
Shared definitions for extended-real-valued convex analysis.

The effective domain, epigraph, and properness follow the conventions of
Rockafellar--Wets, Chapter 1, and Bauschke--Combettes, Definition 1.4.
Convexity is defined by the epigraph, as in Bauschke--Combettes, Definition 8.1;
properness is a separate property.
-/

/-- The effective domain of an extended-real-valued function. -/
def effDom {E : Type*} (f : E → EReal) : Set E :=
  {x | f x < ⊤}

/-- The epigraph has a real, rather than extended-real, height coordinate. -/
def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p | f p.1 ≤ (p.2 : EReal)}

/-- A proper function never takes the value `−∞` and has nonempty effective domain. -/
def IsProperEReal {E : Type*} (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧ (effDom f).Nonempty

/-- Convexity of an extended-real-valued function is convexity of its epigraph. -/
def ConvexEReal {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

/-- The convex subdifferential, defined by global affine support at a point where
the function is finite. This is the extended-valued notion of FCA, Section E.1.4,
and Bauschke--Combettes, Definition 16.1. It is defined without assuming convexity
and is distinct from the limiting subdifferential for nonconvex functions. -/
def convexSubdifferential {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (f : E → EReal) (x : E) : Set E :=
  {s | ⊥ < f x ∧ x ∈ effDom f ∧
    ∀ y : E, f x + ((inner ℝ s (y - x) : ℝ) : EReal) ≤ f y}
