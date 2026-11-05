import Mathlib

def IsFaceOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (F K : Set E) : Prop :=
  Convex ℝ F ∧ F.Nonempty ∧ IsExtreme ℝ K F

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

def Polytope.IsCentrallySymmetric {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Prop :=
  ∀ x ∈ P.carrier, -x ∈ P.carrier

def Polytope.faces {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E | IsFaceOf F P.carrier}

def kalai_3d : Prop :=
  ∀ (d : ℕ) (P : Polytope (EuclideanSpace ℝ (Fin d))),
    0 < d →
    Bornology.IsBounded P.carrier →
    P.IsFullDimensional →
    P.IsCentrallySymmetric →
    3 ^ d ≤ P.faces.ncard

theorem kalai_3d_POS : kalai_3d := by
  sorry

theorem kalai_3d_NEG : ¬ kalai_3d := by
  sorry
