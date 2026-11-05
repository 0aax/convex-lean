import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def IsNondegenerate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal) : Prop :=
  (∃ x, f x ≠ ⊤) ∧
  (∃ (s : E) (b : ℝ), ∀ x, f x ≥ inner ℝ s x - b)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

def parallelSubspace {E : Type*} [NormedAddCommGroup E]
  (S : Set E) : Set E :=
  {v : E | ∃ x, ∃ y, (x ∈ S) ∧ (y ∈ S) ∧ (v = x - y)}

theorem FCA_chap_E_1_3_4
  (f : E → EReal)
  (V : Subspace ℝ E)
  (hf_nondegenerate : IsNondegenerate f)
  (hV_contains_affdom : parallelSubspace (affineSpan ℝ (effDom f)) ⊆
                        (V : Set E)) :
  let U := Vᗮ
  let pV : E → E :=
  fun x => Submodule.orthogonalProjection V x
  let pU : E → E :=
  fun x => Submodule.orthogonalProjection U x
  ∀ z ∈ affineSpan ℝ (effDom f), ∀ s,
  conjugate f s = inner ℝ (pU s) z + conjugate f (pV s) := by
  sorry
