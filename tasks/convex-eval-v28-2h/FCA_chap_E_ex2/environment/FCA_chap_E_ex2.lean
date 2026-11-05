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

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

theorem FCA_chap_E_ex2
  (g : E → EReal)
  (h : E → ℝ)
  (S : Set E)
  (hg_nd : IsNondegenerate g)
  (hh_conv : InConvRn (liftRealtoEReal h))
  (hS : Set.Nonempty S) :
  let f : E → EReal := fun v => (g v) - (h v)
  let g_conj := conjugate g
  let h_conj := conjugate (liftRealtoEReal h)
  let α : EReal := sSup (Set.image (fun v => (h v : EReal)) S)
  (∀ (s : E),
  conjugate f s = sSup (Set.image
                        (fun p => (g_conj (s + p)) - (h_conj p))
                        (effDom h_conj))) ∧
  (sInf (Set.image (fun v => (f v)) Set.univ) =
  sInf (Set.image (fun p => (h_conj p) - (g_conj p))
  (effDom h_conj))) ∧
  (-(α : EReal) = sInf (Set.image
                  (fun s => (h_conj s) - (supportFunction S s))
                  (effDom h_conj))) := by
  sorry
