import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsFaceOf {E : Type*} [AddCommGroup E] [Module ℝ E]
  (F K : Set E) : Prop :=
  Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ K F

noncomputable def Set.affineFinrank {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (S : Set E) : ℕ :=
  Module.finrank ℝ (affineSpan ℝ S).direction

structure Polytope (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] where
  m : ℕ
  a : Fin m → E
  b : Fin m → ℝ

def Polytope.carrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set E :=
  {x : E | ∀ i, inner ℝ (P.a i) x ≤ P.b i}

def Polytope.IsFullDimensional {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Prop :=
  affineSpan ℝ P.carrier = ⊤

def Polytope.faces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E | IsFaceOf F P.carrier}

def Polytope.facets {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E |
    F ∈ P.faces ∧
    Set.affineFinrank F + 1 = Set.affineFinrank P.carrier}

theorem FCA_chap_C_ex2 {n : ℕ}
  (P : Polytope (EuclideanSpace ℝ (Fin n)))
  (hn : n > 0)
  (hP_bounded : Bornology.IsBounded P.carrier)
  (hP_full : P.IsFullDimensional) :
  ∃ S : Finset (Set (EuclideanSpace ℝ (Fin n))),
    (∀ F ∈ S, F ∈ P.facets) ∧ S.card ≥ n + 1 := by
  sorry
