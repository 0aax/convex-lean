import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal
open Filter Topology Set

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable def differenceQuotient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) (t : ℝ) : EReal :=
  (f (x + t • d) - f x) / t

def liftRealtoEReal {E : Type*}
  (f : E → ℝ) :
  E → EReal
  := fun x => (f x : EReal)

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

theorem FCA_chap_D_6_2_5
  (f : E → ℝ)
  (hf_convex : ConvexOn ℝ Set.univ f) :
  ∀ (x : E),
  ∀ (d : E),
  directionalDeriv (liftRealtoEReal f) x d =
  Filter.limsup (fun y => directionalDeriv (liftRealtoEReal f) y d) (𝓝 x) := by
  sorry
