import Mathlib

def IsFaceOf {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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

def Polytope.vertices {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set E :=
  {v : E | IsFaceOf {v} P.carrier}

def Polytope.Vertex {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Type _ :=
  {v : E // v ∈ P.vertices}

def Polytope.edges {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set (Set E) :=
  {F : Set E |
    F ∈ P.faces ∧
    Set.affineFinrank F = 1}

def Polytope.vertexEdgeGraph {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) :
  SimpleGraph P.Vertex :=
  SimpleGraph.fromRel fun v w =>
    ∃ (F : Set E),
      F ∈ P.edges ∧
      (v.1 : E) ∈ F ∧
      (w.1 : E) ∈ F

def polynomial_hirsch : Prop :=
  ∃ (q : MvPolynomial (Fin 2) ℕ),
    ∀ (d n : ℕ) (P : Polytope (EuclideanSpace ℝ (Fin d))),
      Bornology.IsBounded P.carrier →
      P.IsFullDimensional →
      P.facets.ncard = n →
      P.vertexEdgeGraph.ediam ≤ (q.eval ![n, d] : ℕ∞)
