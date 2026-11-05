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

noncomputable def lscHull {E : Type*} [TopologicalSpace E]
  (f : E → EReal)
  (x : E) : EReal
  := Filter.liminf f (𝓝 x)

def effDom {E : Type*} (f : E → EReal) : Set E := {x : E | f x < ⊤}

theorem FCA_chap_B_1_2_5
  (f : E → EReal)
  (x₀ : E)
  (hf_convex : InConvRn f)
  (hx : x₀ ∈ intrinsicInterior ℝ (effDom f))
  (f_ne_bot : ∀ x, ⊥ < f x) :
  ∀ x, Filter.Tendsto (fun (t : ℝ) => f (x + t • (x₀ - x))) (𝓝[>] 0) (𝓝 (lscHull f x)) := by
  sorry
