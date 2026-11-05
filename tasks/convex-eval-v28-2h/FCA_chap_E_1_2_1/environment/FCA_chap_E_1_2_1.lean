import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def epigraph {E : Type*} (f : E → EReal) : Set (E × ℝ) :=
  {p : E × ℝ | f p.1 ≤ p.2}

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

noncomputable def supportFunction {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (A : Set E) (w : E) : EReal :=
  sSup ((fun v : E => ((inner ℝ v w : ℝ) : EReal)) '' A)

def vecHead {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n)
  := (WithLp.equiv 2 _).symm (fun i => x (Fin.castSucc i))

def vecLast {n : ℕ}
  (x : EuclideanSpace ℝ (Fin (n + 1))) : ℝ
  := x (Fin.last n)

theorem FCA_chap_E_1_2_1 {n : ℕ}
  (f : EuclideanSpace ℝ (Fin n) → EReal)
  (hf_nondegenerate : IsNondegenerate f) :
  let f' := f
  let f_conj := fun s => conjugate f' s
  let f_epi_supportfun := fun (s : EuclideanSpace ℝ (Fin n)) (u : ℝ) =>
    supportFunction {z | (vecHead z, vecLast z) ∈ epigraph f'}
      ((WithLp.equiv 2 _).symm (Fin.snoc s.ofLp (-u)))
  let f_dom_supportfun := fun s => supportFunction {z | z ∈ effDom f'} s
  (conjugate f' =
    fun s => sSup {z : EReal | ∃ (x : EuclideanSpace ℝ (Fin n)) (r : ℝ),
      (z = (((inner ℝ s x) - r : ℝ) : EReal)) ∧ ((x, r) ∈ epigraph f')}) ∧
  f_epi_supportfun = (fun s (u : ℝ) =>
    if u > 0 then (u : EReal) * f_conj (u⁻¹ • s)
    else if u = 0 then f_dom_supportfun s
    else ⊤) := by
  sorry
