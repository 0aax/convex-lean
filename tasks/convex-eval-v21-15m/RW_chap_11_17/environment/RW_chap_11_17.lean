import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def IsPointedCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Prop :=
  (0 : E) ∈ K ∧
  ∀ x ∈ K, ∀ t : ℝ, 0 ≤ t → t • x ∈ K

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

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem RW_chap_11_17
  (C K : Set E)
  (hC_nonempty : C.Nonempty)
  (hC_closed : IsClosed C)
  (hC_convex : Convex ℝ C)
  (hK_closed : IsClosed K)
  (hK_convex : Convex ℝ K)
  (hK_cone : IsPointedCone K) :
  ((IsPolyhedral C ↔ IsPiecewiseLinear (supportFunction C)) ∧
    (IsPolyhedral K ↔ IsPolyhedral (polarCone K))) := by
  sorry
