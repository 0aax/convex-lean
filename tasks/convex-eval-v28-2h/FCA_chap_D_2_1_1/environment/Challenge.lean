import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat MeasureTheory Pointwise ENNReal NNReal

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

def IsFiniteEReal (a : EReal) : Prop :=
  ∃ r : ℝ, a = (r : EReal)

noncomputable def directionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → EReal)
  (x : E)
  (d : E) : EReal :=
  limUnder (𝓝[>] 0) (fun t => differenceQuotient f x d t)

noncomputable def realDirectionalDeriv {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  (f : E → ℝ)
  (x : E)
  (d : E) : ℝ :=
  (directionalDeriv (liftRealtoEReal f) x d).toReal

theorem FCA_chap_D_2_1_1 (f : E → ℝ) (x : E) (hf_convex : ConvexOn ℝ Set.univ f) :
  let f'_ereal := fun (d : E) => directionalDeriv (liftRealtoEReal f) x d
  let f'_real := fun (d : E) => realDirectionalDeriv f x d
  (∀ x, IsFiniteEReal (f'_ereal x)) ∧
  (∀ x, (f'_ereal x) = (f'_real x : EReal)) ∧
  (∀ (ε : ℝ), (ε > 0) → ∃ δ > 0,
  ∀ (h : E), ‖h‖ ≤ δ →
  abs (f (x + h) - f x - realDirectionalDeriv f x h) ≤ ε • ‖h‖) := by
  sorry
