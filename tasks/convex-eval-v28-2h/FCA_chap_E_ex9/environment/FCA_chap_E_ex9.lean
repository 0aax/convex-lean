import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def ConvexEReal {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  Convex ℝ (epigraph f)

def InConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∀ x, ⊥ < f x) ∧
  (∃ x, f x < ⊤) ∧
  ConvexEReal f

def InClosedConvRn {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  InConvRn f ∧
  LowerSemicontinuous f

def IsCone {E : Type*} [AddCommMonoid E] [SMul ℝ E]
  (K : Set E) : Prop :=
  ∀ x ∈ K, ∀ (s : ℝ), s > 0 → s • x ∈ K

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

def polarCone {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (K : Set E) : Set E :=
  {s : E | ∀ x ∈ K, inner ℝ s x ≤ 0}

theorem FCA_chap_E_ex9
  {n : ℕ}
  (K : Set (EuclideanSpace ℝ (Fin n)))
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (x0 : EuclideanSpace ℝ (Fin n))
  (hK : IsClosed K ∧ Convex ℝ K ∧ IsCone K)
  (hx0 : x0 ∈ K)
  (hx0_dom : x0 ∈ effDom f)
  (hf_closed_convex : InClosedConvRn f)
  (hf_continuous : ContinuousAt f x0)
  (hf_bdd : BddBelow (f '' K))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  (sInf (Set.image f K)) =
  -1 * (sInf (Set.image (fun s => (conjugate f (-1 • s))) (polarCone K))) := by
  sorry
