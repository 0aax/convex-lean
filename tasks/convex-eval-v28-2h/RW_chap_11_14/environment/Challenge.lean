import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

structure Polytope (E : Type*)
  [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] where
  m : ℕ
  a : Fin m → E
  b : Fin m → ℝ

def Polytope.carrier {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (P : Polytope E) : Set E :=
  {x : E | ∀ i, inner ℝ (P.a i) x ≤ P.b i}

def IsPolyhedral {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (C : Set E) : Prop :=
  ∃ P : Polytope E, P.carrier = C

def IsPiecewiseLinearOn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  (D : Set E) (G : E → F) : Prop :=
  ∃ (n : ℕ),
    ∃ (P : Fin n → Set E),
    ∃ (A : Fin n → E →L[ℝ] F),
    ∃ (a : Fin n → F),
      (D = ⋃ i : Fin n, P i) ∧
      (∀ i : Fin n, IsPolyhedral (P i)) ∧
      (∀ i : Fin n, ∀ x ∈ P i, G x = A i x + a i)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

def IsPiecewiseLinear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∃ (g : E → ℝ),
    IsPiecewiseLinearOn (effDom f) g ∧
    ∀ x ∈ effDom f, f x = (g x : EReal)

def IsPiecewiseLinearQuadratic {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  ∃ (n : ℕ),
    ∃ (P : Fin n → Set E),
    ∃ (A : Fin n → E →L[ℝ] E),
    ∃ (a : Fin n → E),
    ∃ (α : Fin n → ℝ),
      effDom f = ⋃ i : Fin n, P i ∧
      (∀ i : Fin n, IsPolyhedral (P i)) ∧
      (∀ i : Fin n, P i ⊆ effDom f) ∧
      (∀ i : Fin n, ∀ x ∈ P i,
        f x =
          (((1 / 2 : ℝ) * inner ℝ x (A i x) +
              inner ℝ (a i) x +
              α i) : EReal))

def IsProper {E : Type*} (f : E → EReal) : Prop :=
  (∀ (x : E), ⊥ < f x) ∧ (Set.Nonempty (effDom f))

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem RW_chap_11_14
  (f : E → EReal)
  (hf_proper : IsProper f)
  (hf_lsc : LowerSemicontinuous f)
  (hf_convex : ConvexEReal f) :
  (IsPiecewiseLinear f ↔ IsPiecewiseLinear (conjugate f)) ∧
  (IsPiecewiseLinearQuadratic f ↔
    IsPiecewiseLinearQuadratic (conjugate f)) := by
  sorry
