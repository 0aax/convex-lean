import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

noncomputable def conjugate {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (f : E → EReal) (v : E) : EReal :=
  sSup (Set.image (fun x => ((inner ℝ v x : ℝ) : EReal) - f x) Set.univ)

theorem FCA_chap_E_3_3_1
  (k : ℕ)
  (s : ℕ → E)
  (b : ℕ → ℝ)
  (hk : k ≥ 1) :
  let f := fun x => sSup (Set.image (fun i => inner ℝ (s i) x - b i) (Finset.range k))
  (effDom ((conjugate (liftRealtoEReal f))) =
  convexHull ℝ (Set.image s (Finset.range k))) ∧
  (∀ v ∈ convexHull ℝ (Set.image s (Finset.range k)),
  (conjugate (liftRealtoEReal f) v) =
  sInf {r : EReal | ∃ (α : ℕ → ℝ),
                    (∀ i ∈ Finset.range k, α i ≥ 0) ∧
                    (∑ i ∈ Finset.range k, α i = 1) ∧
                    (∑ i ∈ Finset.range k, α i • s i = v) ∧
                    (r = (∑ i ∈ Finset.range k, α i * b i : ℝ))}) := by
  sorry
