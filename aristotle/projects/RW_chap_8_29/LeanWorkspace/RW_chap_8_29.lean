import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

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

def setAdd {E : Type*} [NormedAddCommGroup E]
    (C : Set E) (K : Set E)
    : Set E
    := {v : E | ∃ c ∈ C, ∃ k ∈ K, v = c + k}

def setNeg {E : Type*} [NormedAddCommGroup E] (A : Set E) : Set E :=
  {x : E | -x ∈ A}

def setSub {E : Type*} [NormedAddCommGroup E] (A B : Set E) : Set E :=
  setAdd A (setNeg B)

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

def supportInterior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (C : Set E) : Set E :=
  {x : E | ∀ v : E, v ≠ 0 → (((inner ℝ x v) : ℝ) : EReal) < supportFunction C v}

theorem RW_chap_8_29
  (C C₁ C₂ : Set E)
  (hC : Convex ℝ C)
  (hC₁ : Convex ℝ C₁)
  (hC₂ : Convex ℝ C₂)
  (hC_ne : C.Nonempty)
  (hC₁_ne : C₁.Nonempty)
  (hC₂_ne : C₂.Nonempty) :
  (((interior C).Nonempty ↔
      ¬ ∃ v : E, v ≠ 0 ∧ supportFunction C v = - supportFunction C (-v)) ∧
    (interior C = supportInterior C)) ∧
  (((0 : E) ∈ interior (setSub C₁ C₂) ↔
      ¬ ∃ v : E, v ≠ 0 ∧ supportFunction C₁ v ≤ - supportFunction C₂ (-v))) ∧
  ((IsPolyhedral (closure C) ↔ IsPiecewiseLinear (supportFunction C))) ∧
  ((C.Nonempty ∧ Bornology.IsBounded C) ↔
      ∀ (v : E), supportFunction C v < ⊤) := by
  sorry
